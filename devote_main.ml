(* Command-line driver for the extracted Debian vote counter.
   Usage: devote_main <tally.txt> <quorum_num> <quorum_den> <ratio_1,...,ratio_m>
   Quorum R = quorum_num / quorum_den; ratio_i is the majority ratio (S for S:1)
   of option i (ignored for the default option, which is the last one). Prints
   the beat matrix, the dropped options, the pairwise defeats and the winners. *)

let () =
  let file = Sys.argv.(1) in
  let qn = int_of_string Sys.argv.(2) and qd = int_of_string Sys.argv.(3) in
  let ratios = List.mapi (fun i s -> (i + 1, int_of_string s))
      (String.split_on_char ',' Sys.argv.(4)) in
  let r = Tally.count_file file qn qd ratios in
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
