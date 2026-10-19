(* Reading Debian tally sheets and running the extracted counter on them.
   A tally sheet has lines 'V: <ranks> <hmac>' where <ranks> has one character
   per option: a digit (1 = highest preference) or '-' for unranked. The default
   option is the last one. Options are numbered from 1 in the results, as on
   debian.org. *)
open Devote

type result = {
  n_ballots : int;
  m : int;                       (* number of options including the default *)
  beat : int array array;        (* beat.(x).(y): voters ranking x above y; 0-based *)
  remaining : int list;          (* 1-based *)
  dropped : int list;
  defeats : (int * int) list;    (* (a, b): a defeats b, among remaining options *)
  winners : int list;
  rounds : int;                  (* rounds of A.5.7 performed *)
  schwartz0 : int list;          (* the Schwartz set before any dropping *)
}

let read_ballots file =
  let ic = open_in file in
  let ballots = ref [] in
  (try
     while true do
       let line = input_line ic in
       if String.length line > 3 && String.sub line 0 3 = "V: " then begin
         let rest = String.trim (String.sub line 3 (String.length line - 3)) in
         let ranks = List.hd (String.split_on_char ' ' rest) in
         let ranks = List.hd (String.split_on_char '\t' ranks) in
         ballots := ranks :: !ballots
       end
     done
   with End_of_file -> ());
  close_in ic;
  List.rev !ballots

(* ballots: rank strings; quorum = qn/qd; ratios: majority ratio of option i
   (1-based, missing = 1). *)
let count_strings ?(m = 0) ballots qn qd ratios =
  let m = if m > 0 then m else String.length (List.hd ballots) in
  let cands = List.init m (fun i -> i) in
  let default = m - 1 in
  let dec (a : int) b = (a = b) in
  let to_ballot s i =
    if i >= String.length s then 0
    else let c = s.[i] in if c = '-' then 0 else Char.code c - Char.code '0' in
  let bs = List.map to_ballot ballots in
  let vm = v bs in
  let ratio i = match List.assoc_opt (i + 1) ratios with Some r -> r | None -> 1 in
  let rl = { quorum_num = qn; quorum_den = qd; ratio } in
  let rep = count cands dec default rl vm in
  let rem = rep.rep_remaining in
  let rec rounds defs k =
    match inner cands dec rem defs with
    | [] -> k
    | _ -> rounds (drop_weakest cands dec vm rem defs) (k + 1) in
  let up = List.map (fun c -> c + 1) in
  { n_ballots = List.length ballots; m;
    beat = Array.init m (fun x -> Array.init m (fun y -> if x = y then 0 else vm x y));
    remaining = up rem;
    dropped = up (List.filter (fun c -> not (List.mem c rem)) cands);
    defeats = List.map (fun (a, b) -> (a + 1, b + 1)) rep.rep_defeats;
    winners = up rep.rep_winners;
    rounds = rounds rep.rep_defeats 0;
    schwartz0 = up (schwartz cands dec rem rep.rep_defeats) }

let count_file file qn qd ratios = count_strings (read_ballots file) qn qd ratios

let ints l = String.concat "" (List.map (Printf.sprintf " %d") l)
