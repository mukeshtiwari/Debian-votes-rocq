(* Recount every Debian vote with the verified counter and compare with the
   published outcome.

   For each vote page data/debian.org/vote/<year>/vote_NNN this program
     1. parses the published outcome (from vote_NNN_results.txt when present,
        else from the HTML page): options, beat matrix, quorum threshold,
        per-option majority ratio and decision, pairwise defeats, Schwartz set,
        winners;
     2. runs the extracted counter on the tally sheet with rules determined
        independently of devotee's output: the quorum R = 3 sqrt(n) / 2 from
        the number n of developers stated on the page (exactly, as R^2 = 9n/4),
        the majority ratios from data/majority_requirements.txt, and the
        majority rule of the Constitution in force (strict before 2016);
     3. compares the beat matrix, devotee's quorum and ratios, the dropped
        options, the defeats, the Schwartz set and the winners. A field that
        cannot be compared must be listed, with its reason, in not_compared.
   Writes recount_summary.json and recount_table.md. With --devotee-batch
   <file>, also writes every counted vote, with its published quorum and
   ratios, as a batch for devotee/run_devotee.pl (see devotee_diff.ml).
   Usage: recount [--verbose] [--devotee-batch <file>] *)

let root = Filename.dirname Sys.executable_name
let data = Filename.concat root "data/debian.org/vote"

(* tally sheets of the first years have descriptive names *)
let tally_name year vid =
  match year, vid with
  | "2003", "vote_0003" -> "gr_sec415_tally.txt"
  | "2004", "vote_001" -> "leader2004_tally.txt"
  | "2004", "vote_002" -> "gr_non_free_tally.txt"
  | "2004", "vote_003" -> "gr_editorial_tally.txt"
  | "2004", "vote_004" -> "gr_sarge_tally.txt"
  | "2005", "vote_001" -> "leader2005_tally.txt"
  | ("2003" | "2004"), _ -> "none"
  | _ -> vid ^ "_tally.txt"

(* majority ratios that the published page states in prose but whose
   per-option lines are lost to an HTML escaping error on the page (the text
   from the first '<' of the devotee output is missing). The second component
   says whether the loss also removed the published dropping decisions, so that
   the set of dropped options cannot be compared. *)
(* Fields of the published outcome that cannot be compared, with the reason.
   Every other field must be compared, or the vote is reported as NOT
   COMPARED. *)
let not_compared year vid =
  let truncated = "the page is truncated after the first '<' of devotee's majority section" in
  let no_schwartz = "the page does not list the Schwartz set" in
  match year, vid with
  | "2004", "vote_001" | "2004", "vote_003" | "2005", "vote_001" -> ["schwartz", no_schwartz]
  | "2004", "vote_002" ->
    ["schwartz", no_schwartz;
     "ratios", "devotee's '<=' is unescaped in the HTML page and lost as a tag"]
  | "2004", "vote_004" -> ["dropped", truncated; "defeats", truncated; "schwartz", truncated]
  | _ -> []

(* Fields in which the published record contradicts itself, with the
   explanation. They are reported, not counted as recount mismatches. *)
let record_inconsistent year vid =
  let quorum stated used = Printf.sprintf
      "devotee applied the quorum for %d developers, the page states %d" used stated in
  match year, vid with
  | "2006", "vote_002" -> ["quorum", quorum 972 984]
  | "2018", "vote_001" -> ["quorum", quorum 1001 882]
  | "2023", "vote_002" -> ["quorum", quorum 1004 949]
  | _ -> []

(* ---------- text utilities ---------- *)

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

let ends_with s suf =
  let n = String.length s and k = String.length suf in
  n >= k && String.sub s (n - k) k = suf

let find_from s pat start =
  try Some (Str.search_forward (Str.regexp_string pat) s start) with Not_found -> None

let find s pat = find_from s pat 0

let sub_from s i = String.sub s i (String.length s - i)
let take s n = String.sub s 0 (min n (String.length s))

(* all matches of a regexp with the given number of groups *)
let all_matches re ngroups s =
  let rec go pos acc =
    match (try Some (Str.search_forward re s pos) with Not_found -> None) with
    | None -> List.rev acc
    | Some i ->
      let gs = List.init ngroups (fun g ->
          try Some (Str.matched_group (g + 1) s) with Not_found -> None) in
      let e = Str.match_end () in
      go (if e > i then e else i + 1) (gs :: acc)
  in go 0 []

let unescape s =
  let s = Str.global_replace (Str.regexp "&lt;") "<" s in
  let s = Str.global_replace (Str.regexp "&gt;") ">" s in
  let s = Str.global_replace (Str.regexp "&quot;") "\"" s in
  let s = Str.global_replace (Str.regexp "&#39;\\|&apos;") "'" s in
  let s = Str.global_replace (Str.regexp "&nbsp;") " " s in
  let s = Str.global_substitute (Str.regexp "&#\\([0-9]+\\);")
      (fun t -> let c = int_of_string (Str.matched_group 1 t) in
        if c < 128 then String.make 1 (Char.chr c) else "?") s in
  Str.global_replace (Str.regexp "&amp;") "&" s

(* the published outcome as plain lower-case text *)
let text_of path =
  let s = read_file path in
  let s =
    if ends_with path ".txt" then s
    else begin
      let i = match find (String.lowercase_ascii s) "quorum" with Some i -> i | None -> 0 in
      let s = sub_from s (max 0 (i - 200)) in
      let s = Str.global_replace (Str.regexp "<[^>]+>") " " s in
      let s = unescape s in
      Str.global_replace (Str.regexp "[ \t]+") " " s
    end in
  String.lowercase_ascii s

let is_digits t = t <> "" && String.for_all (fun c -> c >= '0' && c <= '9') t
let is_space c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

(* ---------- the rules of each vote ---------- *)

(* data/majority_requirements.txt: "<year>-<vote> r1,...,r(m-1) | source" *)
let requirements =
  let t = Hashtbl.create 64 in
  let ic = open_in (Filename.concat root "data/majority_requirements.txt") in
  (try
     while true do
       let l = input_line ic in
       if l <> "" && l.[0] <> '#' then
         match String.split_on_char ' ' l with
         | key :: rs :: _ -> Hashtbl.replace t key (List.map int_of_string (String.split_on_char ',' rs))
         | _ -> ()
     done
   with End_of_file -> ());
  close_in ic; t

(* the number of developers that the vote page states *)
let developer_count page =
  let s = String.lowercase_ascii (read_file page) in
  try
    ignore (Str.search_forward (Str.regexp "current developer count = *\\([0-9]+\\)") s 0);
    int_of_string (Str.matched_group 1 s)
  with Not_found -> failwith ("no developer count on " ^ page)

(* ---------- the published outcome ---------- *)

type outcome = {
  options : (int * string) list;
  quorum : string option;
  quorum_dropped : int list;
  ratios : (int * int) list;
  maj_dropped : int list;
  beat : int array array option;
  defeats : (int * int) list;
  schwartz : int list;
  winners : int list;
}

let group = function Some g -> g | None -> raise Not_found
let int_group g = int_of_string (group g)
let sorted_unique l = List.sort_uniq compare l

(* read k integer tokens, each followed by white space, starting at i *)
let read_ints s i k =
  let n = String.length s in
  let rec skip i = if i < n && is_space s.[i] then skip (i + 1) else i in
  let rec token i = if i < n && not (is_space s.[i]) then token (i + 1) else i in
  let rec go i k acc =
    if k = 0 then Some (List.rev acc)
    else
      let i = skip i in
      let j = token i in
      let t = String.sub s i (j - i) in
      if is_digits t && j < n && is_space s.[j] then go j (k - 1) (int_of_string t :: acc)
      else None
  in go i k []

let parse_beat txt opts =
  let start = match find txt "beat matrix" with
    | Some i -> Some i | None -> find txt "tally[row x][col y]" in
  match start with
  | None -> None
  | Some i ->
    let seg = take (sub_from txt i) 20000 in
    let candidates = match opts with
      | [] -> List.init 14 (fun k -> 15 - k)
      | _ -> [List.fold_left (fun a (i, _) -> max a i) 0 opts] in
    let re = Str.regexp "option \\([0-9]+\\)\\|default" in
    let try_size m_opts =
      let rows = Hashtbl.create 16 in
      let rec go pos =
        if Hashtbl.length rows < m_opts then
          match (try Some (Str.search_forward re seg pos) with Not_found -> None) with
          | None -> ()
          | Some i ->
            let e = Str.match_end () in
            let r = (try int_of_string (Str.matched_group 1 seg) with Not_found -> m_opts) in
            (if r <= m_opts && not (Hashtbl.mem rows r) then
               match read_ints seg e (m_opts - 1) with
               | Some vals -> Hashtbl.replace rows r vals
               | None -> ());
            go (max e (i + 1))
      in go 0;
      if Hashtbl.length rows < m_opts then None
      else begin
        let bm = Array.make_matrix m_opts m_opts 0 in
        Hashtbl.iter (fun r vals ->
            let k = ref 0 in
            for c = 1 to m_opts do
              if c <> r then begin bm.(r - 1).(c - 1) <- List.nth vals !k; incr k end
            done) rows;
        Some bm
      end in
    List.fold_left (fun acc m -> match acc with Some _ -> acc | None -> try_size m) None candidates

let parse_outcome txt =
  let options =
    List.fold_left (fun acc g ->
        let i = int_group (List.nth g 0) in
        if List.mem_assoc i acc then acc else (i, group (List.nth g 1)) :: acc)
      [] (all_matches (Str.regexp "option \\([0-9]+\\) \"\\([^\"]*\\)\"") 2 txt) in
  let quorum =
    match all_matches (Str.regexp "reached quorum:[ \t]*\\([0-9]+\\)[ \t]*>=?[ \t]*\\([0-9.]+\\)") 2 txt with
    | g :: _ -> Some (group (List.nth g 1)) | [] -> None in
  let quorum_dropped =
    List.map (fun g -> int_group (List.hd g))
      (all_matches (Str.regexp "dropping option \\([0-9]+\\) because of quorum") 1 txt) in
  let passes =
    all_matches (Str.regexp "option \\([0-9]+\\) passes majority\\.[ \t\n\r]*[0-9.]+ (\\([0-9]+\\)/\\([0-9]+\\))[ \t\n\r]*>=?[ \t\n\r]*\\([0-9]+\\)") 4 txt in
  let ratios = List.map (fun g -> (int_group (List.nth g 0), int_group (List.nth g 3))) passes in
  let drops =
    all_matches (Str.regexp "dropping option \\([0-9]+\\) because of majority\\.\\([^\n]*\\)") 2 txt in
  let maj_dropped, ratios =
    List.fold_left (fun (md, rs) g ->
        let i = int_group (List.nth g 0) in
        let line = group (List.nth g 1) in
        let rs =
          try
            ignore (Str.search_forward (Str.regexp "(\\([0-9]+\\)/\\([0-9]+\\))[ \t]*<[ \t]*\\([0-9]+\\)") line 0);
            (i, int_of_string (Str.matched_group 3 line)) :: rs
          with Not_found -> rs in
        (i :: md, rs)) ([], ratios) drops in
  let beat = parse_beat txt options in
  let defeats =
    List.map (fun g -> (int_group (List.nth g 0), int_group (List.nth g 1)))
      (all_matches (Str.regexp "option \\([0-9]+\\) defeats option \\([0-9]+\\) by") 2 txt) in
  let options_after h =
    match find txt h with
    | None -> []
    | Some j ->
      let seg = ref (take (sub_from txt j) 2000) in
      List.iter (fun stop ->
          match find_from !seg stop 10 with
          | Some k when k > 0 -> seg := take !seg k
          | _ -> ()) ["the winners"; "the winner"; "debian uses"; "-=-="; "the total"];
      List.map (fun g -> int_group (List.hd g)) (all_matches (Str.regexp "option \\([0-9]+\\)") 1 !seg) in
  let schwartz = options_after "the schwartz set contains" in
  let winners =
    let w = options_after "the winners are" in
    let w = if w <> [] then w else options_after "the winners" in
    if w <> [] then w
    else match all_matches (Str.regexp "the winner is:[ \t\n\r]*option \\([0-9]+\\)") 1 txt with
      | g :: _ -> [int_group (List.hd g)]
      | [] ->
        match all_matches (Str.regexp "the winner of the election is[ \t]+\\([^\n.]+\\)") 1 txt with
        | g :: _ ->
          let name = String.trim (group (List.hd g)) in
          List.filter_map (fun (i, n) -> if String.trim n = name then Some i else None) options
        | [] -> [] in
  { options; quorum; quorum_dropped = sorted_unique quorum_dropped; ratios;
    maj_dropped = sorted_unique maj_dropped; beat; defeats = sorted_unique defeats;
    schwartz = sorted_unique schwartz; winners = sorted_unique winners }

(* fields missing from the results file are taken from the HTML page *)
let merge a b =
  let l x y = if x = [] then y else x in
  { options = l a.options b.options;
    quorum = (match a.quorum with Some _ -> a.quorum | None -> b.quorum);
    quorum_dropped = l a.quorum_dropped b.quorum_dropped;
    ratios = l a.ratios b.ratios; maj_dropped = l a.maj_dropped b.maj_dropped;
    beat = (match a.beat with Some _ -> a.beat | None -> b.beat);
    defeats = l a.defeats b.defeats; schwartz = l a.schwartz b.schwartz;
    winners = l a.winners b.winners }

(* ---------- output ---------- *)

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n" | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'; Buffer.contents b
let json_ints l = "[" ^ String.concat ", " (List.map string_of_int l) ^ "]"
let json_check = function None -> "null" | Some b -> string_of_bool b
let json_list l = "[" ^ String.concat ", " l ^ "]"

type row = {
  year : string; vote : string; source : string; mutable status : string;
  mutable fields : (string * string) list;   (* further JSON fields, in order *)
  mutable title : string; mutable ballots : int; mutable options : int;
  mutable dropped : int list; mutable winner : int list;
}

let page_title page =
  let s = read_file page in
  try
    ignore (Str.search_forward (Str.regexp "<title>\\([^<]*\\)</title>") s 0);
    String.trim (Str.global_replace (Str.regexp "[ \t\n\r]+") " " (Str.matched_group 1 s))
  with Not_found -> ""

let () =
  let verbose = Array.exists (fun a -> a = "--verbose") Sys.argv in
  let batch =
    let rec go i = if i + 1 >= Array.length Sys.argv then None
      else if Sys.argv.(i) = "--devotee-batch" then Some (open_out Sys.argv.(i + 1)) else go (i + 1) in
    go 1 in
  let years = List.sort compare (List.filter (fun d -> Sys.is_directory (Filename.concat data d))
                                   (Array.to_list (Sys.readdir data))) in
  let is_vote f = Str.string_match (Str.regexp "^vote_[0-9][0-9][0-9][0-9]?$") f 0 in
  let rows = ref [] in
  List.iter (fun year ->
      let d = Filename.concat data year in
      let votes = List.sort compare (List.filter is_vote (Array.to_list (Sys.readdir d))) in
      List.iter (fun vid ->
          let page = Filename.concat d vid in
          let results = Filename.concat d (vid ^ "_results.txt") in
          let src = if Sys.file_exists results then results else page in
          let tally = Filename.concat d (tally_name year vid) in
          let row = { year; vote = vid; source = Filename.basename src; status = ""; fields = [];
                      title = ""; ballots = 0; options = 0; dropped = []; winner = [] } in
          rows := row :: !rows;
          if not (Sys.file_exists tally) then begin
            let p = String.lowercase_ascii (read_file page) in
            row.status <- if find p "withdrawn" <> None then "withdrawn (no ballots)" else "no tally sheet"
          end else begin
            let pub = parse_outcome (text_of src) in
            let pub = if pub.beat = None && src <> page then merge pub (parse_outcome (text_of page)) else pub in
            let key = Printf.sprintf "%s-%s" year (String.sub vid 5 (String.length vid - 5)) in
            let m = match pub.beat with
              | Some bm -> Array.length bm
              | None -> List.fold_left (fun a (i, _) -> max a i) 0 pub.options in
            if m = 0 then row.status <- "could not parse outcome"
            else begin
              (* the rules, independently of devotee's output: the quorum from the
                 published number of developers, the majority ratios from
                 data/majority_requirements.txt, the majority rule by date *)
              let ndev = developer_count page in
              let ratios = match Hashtbl.find_opt requirements key with
                | Some rs when List.length rs = m - 1 -> List.mapi (fun i r -> (i + 1, r)) rs
                | _ -> failwith ("no majority requirement for " ^ key) in
              let strict = int_of_string year <= 2015 in
              let res = Tally.count_file ~strict tally (9 * ndev) 4 ratios in
              Option.iter (fun oc ->
                  Printf.fprintf oc "P %s %d %s %s %d\n" key m
                    (match pub.quorum with Some q -> q | None -> "0")
                    (String.concat "," (List.map (fun (_, r) -> string_of_int r) ratios)) ndev;
                  List.iter (fun b -> output_string oc (b ^ "\n")) (Tally.read_ballots tally);
                  output_string oc "E\n") batch;
              let res_beat = Array.map Array.copy res.beat in
              let rem = res.remaining in
              let check_beat = match pub.beat with
                | Some bm -> Some (bm = res_beat && Array.length bm = res.m) | None -> None in
              (* devotee's published quorum against 3 sqrt(n) / 2 *)
              let check_quorum = match pub.quorum with
                | Some q -> Some (Float.abs (float_of_string q -. 1.5 *. sqrt (float_of_int ndev)) < 1e-6)
                | None -> None in
              (* the published ratios, where devotee printed them, against ours *)
              let check_ratios =
                if pub.ratios = [] then None
                else Some (List.for_all (fun (i, r) -> List.assoc_opt i ratios = Some r) pub.ratios) in
              let pub_dropped = sorted_unique (pub.maj_dropped @ pub.quorum_dropped) in
              let check_dropped = Some (pub_dropped = sorted_unique res.dropped) in
              let pub_def_rem = List.filter (fun (a, b) -> List.mem a rem && List.mem b rem) pub.defeats in
              let check_defeats =
                if pub.defeats <> [] then Some (pub_def_rem = sorted_unique res.defeats)
                else if List.length rem <= 1 then Some (res.defeats = [])  (* nothing to defeat *)
                else None in
              let check_schwartz =
                if pub.schwartz = [] then None else Some (pub.schwartz = sorted_unique res.schwartz0) in
              let check_winners =
                if pub.winners = [] then None else Some (pub.winners = sorted_unique res.winners) in
              let checks = ["matrix", check_beat; "quorum", check_quorum; "ratios", check_ratios;
                            "dropped", check_dropped; "defeats", check_defeats;
                            "schwartz", check_schwartz; "winners", check_winners] in
              (* a field that is not compared is an error unless it is listed,
                 with the reason, in not_compared *)
              let excused = not_compared year vid and inconsistent = record_inconsistent year vid in
              let checks = List.map (fun (f, c) -> (f, if List.mem_assoc f excused then None else c)) checks in
              let failed = List.filter_map (fun (f, c) ->
                  if c = Some false && not (List.mem_assoc f inconsistent) then Some f else None) checks in
              let missing = List.filter_map (fun (f, c) -> if c = None && not (List.mem_assoc f excused)
                                                then Some f else None) checks in
              (* an explanation that is not needed is an error too *)
              let stale = List.filter (fun (f, _) -> List.assoc_opt f checks <> Some (Some false)) inconsistent in
              row.status <- (if failed <> [] then "MISMATCH in " ^ String.concat ", " failed
                             else if missing <> [] then "NOT COMPARED: " ^ String.concat ", " missing
                             else if stale <> [] then "STALE EXCEPTION: " ^ String.concat ", " (List.map fst stale)
                             else if inconsistent <> [] then "OK (published record inconsistent: "
                                                             ^ String.concat ", " (List.map fst inconsistent) ^ ")"
                             else if excused <> [] then "OK (published record incomplete)" else "OK");
              row.title <- page_title page; row.ballots <- res.n_ballots; row.options <- m;
              row.dropped <- res.dropped; row.winner <- res.winners;
              row.fields <- [
                "title", json_string row.title;
                "ballots", string_of_int res.n_ballots;
                "options", string_of_int m;
                "developers", string_of_int ndev;
                "quorum", (match pub.quorum with Some q -> json_string q | None -> "null");
                "majority_rule", json_string (if strict then "v1.0-1.5: V(A,D) > N V(D,A)"
                                              else "v1.6+: V(A,D) >= N V(D,A) and V(A,D) > V(D,A)");
                "ratios", "{" ^ String.concat ", " (List.map (fun (i, r) ->
                    Printf.sprintf "\"%d\": %d" i r) ratios) ^ "}";
                "ratios_pub", "{" ^ String.concat ", " (List.map (fun (i, r) ->
                    Printf.sprintf "\"%d\": %d" i r) (List.sort compare pub.ratios)) ^ "}";
                "dropped", json_ints res.dropped;
                "winner_pub", (if pub.winners = [] then "null" else json_ints pub.winners);
                "winner_ours", json_ints res.winners ]
                @ List.map (fun (f, c) -> ("check_" ^ f, json_check c)) checks
                @ [ "not_compared", "{" ^ String.concat ", " (List.map (fun (f, why) ->
                      json_string f ^ ": " ^ json_string why) excused) ^ "}";
                    "record_inconsistent", "{" ^ String.concat ", " (List.map (fun (f, why) ->
                      json_string f ^ ": " ^ json_string why) inconsistent) ^ "}";
                    "defeats_listed_for_dropped", string_of_bool (List.length pub.defeats > List.length pub_def_rem);
                    "rounds", string_of_int res.rounds;
                    "schwartz0", json_ints res.schwartz0;
                    "schwartz_pub", json_ints pub.schwartz ]
            end
          end;
          if verbose || not (String.length row.status >= 2 && String.sub row.status 0 2 = "OK") then
            Printf.printf "%s/%s: %s%s\n" year vid row.status
              (if row.ballots > 0 then Printf.sprintf " (ballots %d, winner%s)" row.ballots (Tally.ints row.winner) else "")
        ) votes) years;
  let rows = List.rev !rows in
  let is_ok r = String.length r.status >= 2 && String.sub r.status 0 2 = "OK" in
  let ok = List.length (List.filter is_ok rows) in
  Printf.printf "\n%d votes; OK=%d; %s\n" (List.length rows) ok
    (String.concat "; " (List.filter_map (fun r ->
         if is_ok r then None else Some (Printf.sprintf "%s/%s: %s" r.year r.vote r.status)) rows));
  (* JSON summary *)
  let oc = open_out (Filename.concat root "recount_summary.json") in
  output_string oc (json_list (List.map (fun r ->
      let base = ["year", json_string r.year; "vote", json_string r.vote;
                  "source", json_string r.source; "status", json_string r.status] in
      "\n {" ^ String.concat ", " (List.map (fun (k, v) -> json_string k ^ ": " ^ v) (base @ r.fields)) ^ "}") rows));
  output_string oc "\n"; close_out oc;
  (* markdown table *)
  let oc = open_out (Filename.concat root "recount_table.md") in
  output_string oc "| Year | Vote | Title | Ballots | Options | Dropped (quorum/majority) | Winner | Published outcome |\n|---|---|---|---|---|---|---|---|\n";
  List.iter (fun r ->
      if r.ballots = 0 then Printf.fprintf oc "| %s | %s | | | | | | %s |\n" r.year r.vote r.status
      else Printf.fprintf oc "| %s | %s | %s | %d | %d | %s | %s | %s |\n" r.year r.vote r.title
          r.ballots r.options
          (if r.dropped = [] then "-" else String.trim (Tally.ints r.dropped))
          (String.trim (Tally.ints r.winner)) r.status) rows;
  close_out oc;
  Option.iter close_out batch
