(* Exercise step 7 (dropping the weakest defeats) on random profiles with
   majority cycles, and cross-check the verified counter against the Schulze
   beatpath winners computed with winning-votes strength; Schulze (2011) proves
   that the two rules elect the same options. No quorum; majority ratio 1 for
   every option. The beatpath computation below is written independently from
   the definition and shares no code with the extracted counter.
   Usage: random_cycles [profiles] [seed] *)

let n_prof = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 2000
let seed = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1

(* a random ballot: a random permutation with random ties and unranked options *)
let ranks_string m =
  let perm = Array.init m (fun i -> i) in
  for i = m - 1 downto 1 do
    let j = Random.int (i + 1) in
    let t = perm.(i) in perm.(i) <- perm.(j); perm.(j) <- t
  done;
  let s = Bytes.make m '-' in
  let r = ref 1 in
  Array.iter (fun o ->
      if Random.float 1.0 >= 0.15 then begin
        Bytes.set s o (Char.chr (Char.code '0' + min !r 9));
        if Random.float 1.0 > 0.2 then incr r
      end) perm;
  Bytes.to_string s

(* beatpath with winning votes: the strength of a defeat (a,b) with
   V(a,b) > V(b,a) is the pair (V(a,b), -V(b,a)), compared lexicographically;
   a path's strength is its weakest link; p.(i).(j) is the strongest path *)
let schulze_wv (beat : int array array) rem =
  let str a b = if beat.(a).(b) > beat.(b).(a) then Some (beat.(a).(b), - beat.(b).(a)) else None in
  let n = Array.length beat in
  let p = Array.init n (fun a -> Array.init n (fun b -> if a = b then None else str a b)) in
  let ge x y = match x, y with
    | _, None -> true | None, _ -> false | Some x, Some y -> compare x y >= 0 in
  let min x y = if ge x y then y else x in
  List.iter (fun k -> List.iter (fun i -> List.iter (fun j ->
      if i <> j && i <> k && j <> k then
        match p.(i).(k), p.(k).(j) with
        | Some _, Some _ ->
          let w = min p.(i).(k) p.(k).(j) in
          if not (ge p.(i).(j) w) then p.(i).(j) <- w
        | _ -> ()) rem) rem) rem;
  List.filter (fun a -> List.for_all (fun b -> b = a || ge p.(a).(b) p.(b).(a)) rem) rem

let () =
  Random.init seed;
  let rounds_gt0 = ref 0 and max_rounds = ref 0 and multi = ref 0 and agree = ref 0 in
  let disagree = ref [] in
  for _ = 1 to n_prof do
    let m = 3 + Random.int 5 and n = 5 + Random.int 11 in
    let ballots = List.init n (fun _ -> ranks_string m) in
    let r = Tally.count_strings ~m ballots 0 1 [] in
    if r.rounds > 0 then incr rounds_gt0;
    if r.rounds > !max_rounds then max_rounds := r.rounds;
    if List.length r.winners > 1 then incr multi;
    let rem = List.map (fun c -> c - 1) r.remaining in
    let sw = List.sort compare (List.map (fun c -> c + 1) (schulze_wv r.beat rem)) in
    if sw = List.sort compare r.winners then incr agree
    else disagree := (ballots, r.winners, sw, r.rounds) :: !disagree
  done;
  Printf.printf "profiles %d; entered step 7: %d; max rounds %d; several winners: %d; agree %d; disagree %d\n"
    n_prof !rounds_gt0 !max_rounds !multi !agree (List.length !disagree);
  List.iteri (fun i (bs, w, sw, k) ->
      if i < 5 then
        Printf.printf "DISAGREE ballots [%s] counter%s beatpath%s rounds %d\n"
          (String.concat " " bs) (Tally.ints w) (Tally.ints sw) k) !disagree
