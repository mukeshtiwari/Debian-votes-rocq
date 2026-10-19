(* Differential test: the verified counter against devotee, the program Debian
   uses to count its votes. devotee's counting routine is run unmodified by
   devotee/run_devotee.pl (fetch it first with scripts/fetch_devotee.sh).

   Usage:
     devotee_diff real <batch>            the batch written by
                                          recount --devotee-batch <batch>
     devotee_diff random <n> <seed>       n random profiles with majority
                                          cycles, as in random_cycles; no
                                          quorum, majority ratio 1
     devotee_diff random-last <n> <seed>  as random, but every ballot ranks the
                                          default option strictly last and
                                          ranks every other option, so steps
                                          2 and 3 drop nothing and only steps
                                          4-8 are compared

   For every profile both counters report the dropped options, the Schwartz
   set before any dropping, the number of rounds of step 7 and the winners;
   the program tabulates where they disagree, compares both with the Schulze
   beatpath winners, and prints the smallest disagreeing profiles. Set
   DVT_RSLT to run another copy of dvt-rslt (e.g. one with a bug fixed). *)

let root = Filename.dirname Sys.executable_name

type profile = Tally.profile = {
  id : string; m : int;
  quorum : string;      (* devotee's quorum K, as published *)
  ndev : int;           (* number of developers: R = 3 sqrt(ndev) / 2; 0 for no quorum *)
  ratios : int list; ballots : string list }

type outcome = { dropped : int list; schwartz0 : int list; rounds : int; winners : int list;
                 beatpath : int list; (* Schulze beatpath winners; verified side only *)
                 beat : int array array (* the pairwise matrix; verified side only *) }

(* ---------- profiles ---------- *)

let random_profiles ~last n seed =
  Random.init seed;
  List.init n (fun k ->
      let m = 3 + Random.int 5 and nb = 5 + Random.int 11 in
      let ballot () =
        if last then Tally.random_ranks ~p_unranked:0.0 (m - 1) ^ "9"
        else Tally.random_ranks m in
      { id = string_of_int k; m; quorum = "0"; ndev = 0; ratios = List.init (m - 1) (fun _ -> 1);
        ballots = List.init nb (fun _ -> ballot ()) })

let read_batch = Tally.read_batch

(* ---------- the two counters ---------- *)

let verified p =
  (* real votes under the majority rule then in force, random profiles under
     the current one (Tally.strict_of_id) *)
  let r = Tally.count_strings ~m:p.m ~strict:(Tally.strict_of_id p.id) p.ballots (9 * p.ndev) 4
      (List.mapi (fun i r -> (i + 1, r)) p.ratios) in
  let rem = List.map (fun c -> c - 1) r.remaining in
  { dropped = r.dropped; schwartz0 = r.schwartz0; rounds = r.rounds; winners = r.winners;
    beatpath = List.sort compare (List.map (fun c -> c + 1) (Tally.schulze_wv r.beat rem));
    beat = r.beat }

let write_batch file profs =
  let oc = open_out file in
  List.iter (fun p ->
      Printf.fprintf oc "P %s %d %s %s %d\n" p.id p.m p.quorum
        (String.concat "," (List.map string_of_int p.ratios)) p.ndev;
      List.iter (fun b -> output_string oc (b ^ "\n")) p.ballots;
      output_string oc "E\n") profs;
  close_out oc

let devotee profs =
  let batch = Filename.temp_file "devotee" ".batch" and out = Filename.temp_file "devotee" ".out" in
  write_batch batch profs;
  let cmd = Printf.sprintf "perl %s %s %s > %s"
      (Filename.quote (Filename.concat root "devotee/run_devotee.pl"))
      (Filename.quote (match Sys.getenv_opt "DVT_RSLT" with
                       | Some f -> f | None -> Filename.concat root "devotee/src/dvt-rslt"))
      (Filename.quote batch) (Filename.quote out) in
  if Sys.command cmd <> 0 then failwith "run_devotee.pl failed (run scripts/fetch_devotee.sh?)";
  let tbl = Hashtbl.create 1024 in
  let ic = open_in out in
  (* devotee numbers options in base 36: 1..9, A, B, ... *)
  let b36 t = String.fold_left (fun a c ->
      36 * a + (if c >= '0' && c <= '9' then Char.code c - 48 else Char.code c - 55)) 0 t in
  let opts s = if s = "" then [] else List.map b36 (String.split_on_char ',' s) in
  (try
     while true do
       let l = input_line ic in
       match String.split_on_char ' ' l with
       | ["R"; id; d; r; s; w] ->
         let v pre s = let k = String.length pre in String.sub s k (String.length s - k) in
         Hashtbl.replace tbl id
           { dropped = opts (v "dropped=" d); rounds = int_of_string (v "rounds=" r);
             schwartz0 = opts (v "schwartz0=" s); winners = opts (v "winners=" w); beatpath = [];
             beat = [||] }
       | _ -> ()
     done
   with End_of_file -> ());
  close_in ic; Sys.remove batch; Sys.remove out;
  tbl

(* ---------- comparison ---------- *)

let sort = List.sort_uniq compare

let () =
  let profs, label = match Array.to_list Sys.argv |> List.tl with
    | ["real"; f] -> (read_batch f, "real votes")
    | ["random"; n; s] -> (random_profiles ~last:false (int_of_string n) (int_of_string s), "random")
    | ["random-last"; n; s] ->
      (random_profiles ~last:true (int_of_string n) (int_of_string s), "random, default last")
    | _ -> prerr_endline "usage: devotee_diff (real <batch> | random <n> <seed> | random-last <n> <seed>)"; exit 2 in
  let dv = devotee profs in
  let n = List.length profs in
  let agree = ref 0 and missing = ref 0 in
  let kinds = Hashtbl.create 8 in
  let examples = ref [] in
  let entered = ref 0 and rounds2 = ref 0 and bp_v = ref 0 and bp_d = ref 0 in
  List.iter (fun p ->
      let v = verified p in
      if v.rounds > 0 then incr entered;
      if v.rounds > 1 then incr rounds2;
      if sort v.winners = v.beatpath then incr bp_v;
      match Hashtbl.find_opt dv p.id with
      | None -> incr missing
      | Some d ->
        let same_drop = sort v.dropped = sort d.dropped in
        let same_win = sort v.winners = sort d.winners in
        if sort d.winners = v.beatpath then incr bp_d;
        if same_drop && same_win then incr agree
        else begin
          let kind =
            if not same_drop then begin
              (* options dropped by one counter only, and V(A,D), V(D,A) for each *)
              let dflt = p.m - 1 in
              let diff = List.filter (fun a -> List.mem a v.dropped <> List.mem a d.dropped)
                  (List.init (p.m - 1) (fun i -> i + 1)) in
              if List.for_all (fun a -> v.beat.(a - 1).(dflt) = v.beat.(dflt).(a - 1)
                                        && List.mem a v.dropped) diff
              then "steps 2-3: V(A,D) = V(D,A), devotee keeps A"
              else "steps 2-3: other difference"
            end
            else if d.winners = [] then "steps 5-8: devotee declares no winner"
            else if List.for_all (fun w -> List.mem w v.winners) d.winners then
              "steps 5-8: devotee's winners a strict subset"
            else if List.for_all (fun w -> List.mem w d.winners) v.winners then
              "steps 5-8: devotee's winners a strict superset"
            else "steps 5-8: other difference" in
          Hashtbl.replace kinds kind (1 + Option.value ~default:0 (Hashtbl.find_opt kinds kind));
          examples := (List.length p.ballots, p, v, d, kind) :: !examples
        end) profs;
  Printf.printf "%s: %d profiles; verified counter entered step 7 in %d (more than one round in %d)\n"
    label n !entered !rounds2;
  Printf.printf "agree %d; disagree %d; devotee produced no result %d\n"
    !agree (n - !agree - !missing) !missing;
  Printf.printf "beatpath winners: equal to the verified counter's in %d, to devotee's in %d\n" !bp_v !bp_d;
  Hashtbl.iter (fun k c -> Printf.printf "  %5d  %s\n" c k) kinds;
  let shown = Hashtbl.create 8 in
  List.iter (fun (_, p, v, d, kind) ->
      let c = Option.value ~default:0 (Hashtbl.find_opt shown kind) in
      if c < 2 then begin
        Hashtbl.replace shown kind (c + 1);
        Printf.printf "\n[%s] profile %s, %d options (default %d), ballots: %s\n" kind p.id p.m p.m
          (String.concat " " p.ballots);
        Printf.printf "  verified: dropped%s schwartz0%s rounds %d winners%s\n"
          (Tally.ints v.dropped) (Tally.ints v.schwartz0) v.rounds (Tally.ints v.winners);
        Printf.printf "  devotee:  dropped%s schwartz0%s rounds %d winners%s\n"
          (Tally.ints d.dropped) (Tally.ints d.schwartz0) d.rounds (Tally.ints d.winners);
        Printf.printf "  beatpath winners%s\n" (Tally.ints v.beatpath)
      end) (List.sort compare !examples)
