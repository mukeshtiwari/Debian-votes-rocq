(* Command-line driver for the extracted Debian vote counter.

   Usage: devote_main <tally.txt> <developers> <ratio_1,...,ratio_m> [strict]
   The quorum is R = 3 sqrt(developers) / 2 (0 developers: no quorum), applied
   exactly as R^2 = 9 developers / 4; ratio_i is the majority ratio (S for S:1)
   of option i (ignored for the default option, which is the last one); with
   "strict", the majority rule of Constitution versions before 1.6 is used.
   Prints the beat matrix, the dropped options, the pairwise defeats and the
   winners.

   Usage: devote_main --batch <batch>
   Reads a batch in the format of devotee/run_devotee.pl (see there) and
   prints, for every profile, the same line as run_devotee.pl:
     R <id> dropped=<opts> rounds=<n> schwartz0=<opts> winners=<opts>
   so that the two outputs can be compared with diff. The quorum is
   3 sqrt(n) / 2 for the profile's number of developers n; a profile whose id
   starts with a year before 2016 is counted under the strict majority rule. *)

let batch file =
  let opts l = String.concat "," (List.map string_of_int (List.sort compare l)) in
  List.iter (fun (p : Tally.profile) ->
      let r = Tally.count_strings ~m:p.m ~strict:(Tally.strict_of_id p.id) p.ballots
          (9 * p.ndev) 4 (List.mapi (fun i r -> (i + 1, r)) p.ratios) in
      Printf.printf "R %s dropped=%s rounds=%d schwartz0=%s winners=%s\n"
        p.id (opts r.dropped) r.rounds (opts r.schwartz0) (opts r.winners))
    (Tally.read_batch file)

let single file ndev ratios strict =
  let ratios = List.mapi (fun i s -> (i + 1, int_of_string s)) (String.split_on_char ',' ratios) in
  let r = Tally.count_file ~strict file (9 * ndev) 4 ratios in
  Printf.printf "ballots %d options %d\n" r.n_ballots r.m;
  Printf.printf "beat matrix (row x, col y: voters ranking x above y):\n";
  Array.iter (fun row -> Array.iter (Printf.printf "%5d") row; print_newline ()) r.beat;
  Printf.printf "remaining:%s\n" (Tally.ints r.remaining);
  Printf.printf "dropped:%s\n" (Tally.ints r.dropped);
  Printf.printf "defeats:%s\n"
    (String.concat "" (List.map (fun (a, b) -> Printf.sprintf " %d>%d" a b) r.defeats));
  Printf.printf "winners:%s\n" (Tally.ints r.winners);
  Printf.printf "rounds: %d\n" r.rounds;
  Printf.printf "schwartz0:%s\n" (Tally.ints r.schwartz0)

let () =
  match Array.to_list Sys.argv |> List.tl with
  | ["--batch"; file] -> batch file
  | [file; ndev; ratios] -> single file (int_of_string ndev) ratios false
  | [file; ndev; ratios; "strict"] -> single file (int_of_string ndev) ratios true
  | _ ->
    prerr_endline "usage: devote_main <tally.txt> <developers> <ratio_1,...> [strict]\n       devote_main --batch <batch>";
    exit 2
