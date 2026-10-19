(* Exercise step 7 (dropping the weakest defeats) on random profiles with
   majority cycles, and cross-check the verified counter against the Schulze
   beatpath winners computed with winning-votes strength; Schulze (2011) proves
   that the two rules elect the same options. No quorum; majority ratio 1 for
   every option. The beatpath computation (Tally.schulze_wv) is written independently
   from the definition and shares no code with the extracted counter.
   Usage: random_cycles [profiles] [seed] *)

let n_prof = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 2000
let seed = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1

let () =
  Random.init seed;
  let rounds_gt0 = ref 0 and max_rounds = ref 0 and multi = ref 0 and agree = ref 0 in
  let disagree = ref [] in
  for _ = 1 to n_prof do
    let m = 3 + Random.int 5 and n = 5 + Random.int 11 in
    let ballots = List.init n (fun _ -> Tally.random_ranks m) in
    let r = Tally.count_strings ~m ballots 0 1 [] in
    if r.rounds > 0 then incr rounds_gt0;
    if r.rounds > !max_rounds then max_rounds := r.rounds;
    if List.length r.winners > 1 then incr multi;
    let rem = List.map (fun c -> c - 1) r.remaining in
    let sw = List.sort compare (List.map (fun c -> c + 1) (Tally.schulze_wv r.beat rem)) in
    if sw = List.sort compare r.winners then incr agree
    else disagree := (ballots, r.winners, sw, r.rounds) :: !disagree
  done;
  Printf.printf "profiles %d; entered step 7: %d; max rounds %d; several winners: %d; agree %d; disagree %d\n"
    n_prof !rounds_gt0 !max_rounds !multi !agree (List.length !disagree);
  List.iteri (fun i (bs, w, sw, k) ->
      if i < 5 then
        Printf.printf "DISAGREE ballots [%s] counter%s beatpath%s rounds %d\n"
          (String.concat " " bs) (Tally.ints w) (Tally.ints sw) k) !disagree
