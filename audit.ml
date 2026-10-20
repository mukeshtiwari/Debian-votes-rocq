(* Audit a devotee results file line by line.

   Each line of the results file that states something about the count is
   turned into claims (Devote.claim): a pairwise count, an option reaching or
   failing the quorum, its majority ratio, it passing or failing the majority,
   a defeat, the complete list of defeats, the Schwartz set, the winners. Each
   claim is checked by the extracted function audit, which is proved in Rocq to
   accept a claim exactly when it holds under Appendix A.5 (audit_correct).
   Reading the lines into claims, and the wording of the report, are not
   verified.

   The rules of the vote are determined without devotee's output, as in
   recount: the number of developers stated on the vote page, the majority
   requirements of data/majority_requirements.txt, and the majority rule in
   force (strict before 2016).

   Usage:
     audit <year> <vote>      e.g. audit 2026 002
     audit --all              every vote with a devotee results file
     audit --files <results.txt> <tally.txt> <developers> <ratio_1,...> [strict]
                              any results file, e.g. devotee's output on
                              test/devotee_*_tally.txt *)

open Devote

(* ---------- reading a results file into claims ---------- *)

let re s = Str.regexp_case_fold s
let matches r s = try ignore (Str.search_forward r s 0); true with Not_found -> false
let grp i s = int_of_string (Str.matched_group i s)

type line_claims = { line : int; text : string; claims : int claim list }

(* options are numbered from 1 in the file and from 0 in the counter; the
   default option is the last one *)
let parse lines =
  let n = Array.length lines in
  let opt_line = re "^Option \\([0-9]+\\) \"" in
  let m = Array.fold_left (fun a l ->
      if Str.string_match opt_line l 0 then max a (grp 1 l) else a) 0 lines in
  if m = 0 then failwith "no options found";
  let d = m - 1 in
  let out = ref [] in
  let add i cs = if cs <> [] then out := { line = i + 1; text = lines.(i); claims = cs } :: !out in
  let in_matrix = ref false and defeats = ref [] and defeat_lines = ref [] in
  let set_after header =
    (* the options listed on the lines after a header, up to a blank line *)
    let rec go i acc =
      if i >= n || String.trim lines.(i) = "" then List.rev acc
      else if Str.string_match (re "^[ \t]*Option \\([0-9]+\\)") lines.(i) 0
      then go (i + 1) ((grp 1 lines.(i) - 1) :: acc)
      else List.rev acc in
    go (header + 1) [] in
  let seen_schwartz = ref false in
  Array.iteri (fun i l ->
      if matches (re "tally\\[row x\\]") l then in_matrix := true
      else if !in_matrix && Str.string_match (re "^Option \\([0-9]+\\)\\([ 0-9]+\\)$") l 0 then begin
        let r = grp 1 l - 1 in
        let vals = List.filter_map (fun t -> if t = "" then None else Some (int_of_string t))
            (String.split_on_char ' ' (Str.matched_group 2 l)) in
        if List.length vals = m - 1 then begin
          let cols = List.filter (fun c -> c <> r) (List.init m (fun c -> c)) in
          add i (List.map2 (fun c v -> CMatrix (r, c, v)) cols vals)
        end;
        if r = m - 1 then in_matrix := false
      end
      else if Str.string_match (re "^Option \\([0-9]+\\).*reached quorum: *\\([0-9]+\\)") l 0 then begin
        let x = grp 1 l - 1 in
        add i [CQuorum (x, true); CMatrix (x, d, grp 2 l)]
      end
      else if Str.string_match (re "^Dropping Option ?\\([0-9]+\\).*because of quorum") l 0 then
        add i [CQuorum (grp 1 l - 1, false)]
      else if Str.string_match (re "^\\(Dropping \\)?Option ?\\([0-9]+\\).*\\(because of\\|passes\\) majority") l 0 then begin
        let x = grp 2 l - 1 and pass = (Str.matched_group 3 l |> String.lowercase_ascii) = "passes" in
        let cs = [CMajority (x, pass)] in
        let cs =
          if matches (re "(\\([0-9]+\\)/\\([0-9]+\\)) *[<>]=? *\\([0-9]+\\)") l then
            let a = grp 1 l and b = grp 2 l and r = grp 3 l in
            cs @ [CMatrix (x, d, a); CMatrix (d, x, b); CRatio (x, r)]
          else cs in
        add i cs
      end
      else if matches (re "Option \\([0-9]+\\) defeats Option \\([0-9]+\\) by ( *\\([0-9]+\\) *- *\\([0-9]+\\))") l then begin
        let a = grp 1 l - 1 and b = grp 2 l - 1 and va = grp 3 l and vb = grp 4 l in
        defeats := (a, b) :: !defeats; defeat_lines := (i + 1) :: !defeat_lines;
        add i [CDefeat (a, b); CMatrix (a, b, va); CMatrix (b, a, vb)]
      end
      else if matches (re "^The Schwartz Set contains") l && not !seen_schwartz then begin
        seen_schwartz := true;
        add i [CSchwartz (set_after i)]
      end
      else if matches (re "^The winners? \\(are\\|is\\)") l then
        add i [CWinners (set_after i)]) lines;
  let per_line = List.rev !out in
  (* the defeat lines, taken together, claim to list every defeat *)
  let whole =
    if !defeats = [] then []
    else [{ line = List.fold_left min max_int !defeat_lines; text = "(all the defeat lines together)";
            claims = [CDefeats (List.rev !defeats)] }] in
  (m, per_line @ whole, List.sort_uniq compare !defeat_lines)

(* ---------- describing claims ---------- *)

let set l = "{" ^ String.concat "," (List.map (fun x -> string_of_int (x + 1)) (List.sort compare l)) ^ "}"

let describe = function
  | CMatrix (x, y, v) -> Printf.sprintf "V(%d,%d) = %d" (x + 1) (y + 1) v
  | CQuorum (x, b) -> Printf.sprintf "option %d %s the quorum" (x + 1) (if b then "reaches" else "fails")
  | CRatio (x, r) -> Printf.sprintf "option %d needs a %d:1 majority" (x + 1) r
  | CMajority (x, b) -> Printf.sprintf "option %d %s the majority requirement" (x + 1) (if b then "passes" else "fails")
  | CDefeat (a, b) -> Printf.sprintf "option %d defeats option %d" (a + 1) (b + 1)
  | CDefeats l -> Printf.sprintf "these %d defeats are all the defeats" (List.length l)
  | CSchwartz l -> "the Schwartz set is " ^ set l
  | CWinners l -> "the winners are " ^ set l

(* ---------- auditing ---------- *)

type summary = { n_lines : int; n_claims : int; n_violated : int }

let audit_file ~label ~results ~ballots ~ndev ~ratios ~strict ~verbose =
  let lines = Array.of_list (String.split_on_char '\n' (Votes.read_file results)) in
  let m, items, _ = parse lines in
  let c = Tally.context ~m ~strict ballots (9 * ndev) 4 (List.mapi (fun i r -> (i + 1, r)) ratios) in
  let check cl = audit c.cands c.dec c.default c.rl c.vm cl in
  Printf.printf "%s: %s\n" label results;
  Printf.printf "  rules: %d developers (quorum %.4f), majority ratios %s, %s\n" ndev
    (1.5 *. sqrt (float_of_int ndev)) (String.concat "," (List.map string_of_int ratios))
    (if strict then "rule of Constitution v1.0-1.5" else "rule of Constitution v1.6+");
  let nclaims = ref 0 and nviol = ref 0 in
  List.iter (fun it ->
      let bad = List.filter (fun cl -> not (check cl)) it.claims in
      nclaims := !nclaims + List.length it.claims;
      nviol := !nviol + List.length bad;
      if bad <> [] then begin
        Printf.printf "  line %3d  VIOLATES  %s\n" it.line (String.trim it.text);
        List.iter (fun cl -> Printf.printf "            step %d: false: %s\n"
                      (claim_step cl) (describe cl)) bad
      end else if verbose then begin
        let steps = List.sort_uniq compare (List.map claim_step it.claims) in
        Printf.printf "  line %3d  OK  (step%s %s)  %s\n" it.line (if List.length steps > 1 then "s" else "")
          (String.concat "," (List.map string_of_int steps))
          (match it.claims with
           | [cl] -> describe cl
           | cls when List.for_all (function CMatrix _ -> true | _ -> false) cls ->
             Printf.sprintf "%d pairwise counts" (List.length cls)
           | cl :: _ -> describe cl ^ ", with its counts"
           | [] -> "")
      end) items;
  Printf.printf "  %d lines with claims, %d claims: %s\n" (List.length items) !nclaims
    (if !nviol = 0 then "all hold" else Printf.sprintf "%d violated" !nviol);
  { n_lines = List.length items; n_claims = !nclaims; n_violated = !nviol }

let audit_vote ~verbose year vote =
  let vid = "vote_" ^ vote in
  let d = Filename.concat Votes.data year in
  let results = Filename.concat d (vid ^ "_results.txt") in
  if not (Sys.file_exists results) then None
  else begin
    let page = Filename.concat d vid in
    let tally = Filename.concat d (Votes.tally_name year vid) in
    let key = Votes.key year vid in
    let ratios = match Hashtbl.find_opt Votes.requirements key with
      | Some r -> r | None -> failwith ("no majority requirement for " ^ key) in
    Some (audit_file ~label:key ~results ~ballots:(Tally.read_ballots tally)
            ~ndev:(Votes.developer_count page) ~ratios ~strict:(Votes.strict_of_year year) ~verbose)
  end

let () =
  match Array.to_list Sys.argv |> List.tl with
  | [year; vote] ->
    (match audit_vote ~verbose:true year vote with
     | Some s -> exit (if s.n_violated = 0 then 0 else 1)
     | None -> prerr_endline "no devotee results file for this vote"; exit 2)
  | ["--all"] ->
    let years = List.sort compare (Array.to_list (Sys.readdir Votes.data)) in
    let total = ref { n_lines = 0; n_claims = 0; n_violated = 0 } and nvotes = ref 0 in
    List.iter (fun year ->
        let votes = List.sort compare (Array.to_list (Sys.readdir (Filename.concat Votes.data year))) in
        List.iter (fun f ->
            if Str.string_match (Str.regexp "^vote_\\([0-9][0-9][0-9]\\)_results\\.txt$") f 0 then
              match audit_vote ~verbose:false year (Str.matched_group 1 f) with
              | Some s ->
                incr nvotes;
                total := { n_lines = !total.n_lines + s.n_lines; n_claims = !total.n_claims + s.n_claims;
                           n_violated = !total.n_violated + s.n_violated }
              | None -> ()) votes) years;
    Printf.printf "\n%d results files, %d lines with claims, %d claims: %s\n" !nvotes !total.n_lines !total.n_claims
      (if !total.n_violated = 0 then "all hold" else Printf.sprintf "%d violated" !total.n_violated);
    exit (if !total.n_violated = 0 then 0 else 1)
  | "--files" :: results :: tally :: ndev :: ratios :: rest ->
    let s = audit_file ~label:(Filename.basename results) ~results ~ballots:(Tally.read_ballots tally)
        ~ndev:(int_of_string ndev) ~ratios:(List.map int_of_string (String.split_on_char ',' ratios))
        ~strict:(rest = ["strict"]) ~verbose:true in
    exit (if s.n_violated = 0 then 0 else 1)
  | _ -> prerr_endline "usage: see the head of audit.ml"; exit 2
