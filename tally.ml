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

(* The context of a count: the options 0..m-1 (the default is m-1), the
   pairwise matrix of the ballots, and the rules. The quorum is given by its
   square, R^2 = qn/qd (9n/4 for Debian, n the number of developers); ratios
   gives the majority ratio of option i (1-based, missing = 1); strict selects
   the majority rule of Constitution versions before 1.6 (December 2015). *)
type ctx = { cands : int list; dec : int -> int -> bool; default : int;
             rl : int rules; vm : int -> int -> int }

let context ?(m = 0) ?(strict = false) ballots qn qd ratios =
  let m = if m > 0 then m else String.length (List.hd ballots) in
  let to_ballot s i =
    if i >= String.length s then 0
    else let c = s.[i] in if c = '-' then 0 else Char.code c - Char.code '0' in
  let bs = List.map to_ballot ballots in
  let mat = Array.init m (fun x -> Array.init m (fun y -> v bs x y)) in
  let ratio i = match List.assoc_opt (i + 1) ratios with Some r -> r | None -> 1 in
  { cands = List.init m (fun i -> i); dec = (fun (a : int) b -> a = b); default = m - 1;
    rl = { quorum_num = qn; quorum_den = qd; ratio; strict_majority = strict };
    vm = (fun x y -> mat.(x).(y)) }

let count_strings ?(m = 0) ?(strict = false) ballots qn qd ratios =
  let c = context ~m ~strict ballots qn qd ratios in
  let m = List.length c.cands in
  let rep = count c.cands c.dec c.default c.rl c.vm in
  let rem = rep.rep_remaining in
  let rec rounds defs k =
    match inner c.cands c.dec rem defs with
    | [] -> k
    | _ -> rounds (drop_weakest c.cands c.dec c.vm rem defs) (k + 1) in
  let up = List.map (fun c -> c + 1) in
  { n_ballots = List.length ballots; m;
    beat = Array.init m (fun x -> Array.init m (fun y -> if x = y then 0 else c.vm x y));
    remaining = up rem;
    dropped = up (List.filter (fun x -> not (List.mem x rem)) c.cands);
    defeats = List.map (fun (a, b) -> (a + 1, b + 1)) rep.rep_defeats;
    winners = up rep.rep_winners;
    rounds = rounds rep.rep_defeats 0;
    schwartz0 = up (schwartz c.cands c.dec rem rep.rep_defeats) }

let count_file ?(strict = false) file qn qd ratios =
  count_strings ~strict (read_ballots file) qn qd ratios

let ints l = String.concat "" (List.map (Printf.sprintf " %d") l)

(* a random ballot over m options: a random permutation, with each option left
   unranked with probability p_unranked (default 0.15) and each ranked option
   tied with the next with probability 0.2 *)
let random_ranks ?(p_unranked = 0.15) m =
  let perm = Array.init m (fun i -> i) in
  for i = m - 1 downto 1 do
    let j = Random.int (i + 1) in
    let t = perm.(i) in perm.(i) <- perm.(j); perm.(j) <- t
  done;
  let s = Bytes.make m '-' in
  let r = ref 1 in
  Array.iter (fun o ->
      if Random.float 1.0 >= p_unranked then begin
        Bytes.set s o (Char.chr (Char.code '0' + min !r 9));
        if Random.float 1.0 > 0.2 then incr r
      end) perm;
  Bytes.to_string s

(* a decimal such as "45.2741648183597" as an exact fraction *)
let fraction_of s =
  match String.index_opt s '.' with
  | None -> (int_of_string s, 1)
  | Some i ->
    let frac = String.sub s (i + 1) (String.length s - i - 1) in
    let den = int_of_float (10. ** float_of_int (String.length frac)) in
    (int_of_string (String.sub s 0 i ^ frac), den)

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

(* ---------- certificates (produced here, untrusted; checked by the
   extracted check_certificate) ---------- *)

(* breadth-first search along defeats from a list of sources: parent.(x) is
   -1 for a source, -2 if x is not reached, else the predecessor of x *)
let bfs m defs sources =
  let parent = Array.make m (-2) in
  let q = Queue.create () in
  List.iter (fun s -> if parent.(s) = -2 then (parent.(s) <- -1; Queue.add s q)) sources;
  while not (Queue.is_empty q) do
    let u = Queue.pop q in
    List.iter (fun (a, b) -> if a = u && parent.(b) = -2 then (parent.(b) <- u; Queue.add b q)) defs
  done;
  parent

let path_to parent x =
  let rec go x acc = if parent.(x) = -1 then x :: acc else go parent.(x) (x :: acc) in
  go x []

(* the certificate of one round: Schwartz set, paths from it to every other
   remaining option, and for each member a root with paths to and from it *)
let scert_of c rem defs =
  let m = List.length c.cands in
  let s = schwartz c.cands c.dec rem defs in
  let from_s = bfs m defs s in
  let out = List.filter_map (fun x ->
      if List.mem x s then None else Some (x, path_to from_s x)) rem in
  let reach = List.map (fun r -> (r, bfs m defs [r])) s in
  let reaches r y = (List.assoc r reach).(y) <> -2 in
  let in_ = List.map (fun y ->
      let r = List.find (fun r -> reaches r y && reaches y r) s in
      (y, (r, (path_to (List.assoc r reach) y, path_to (List.assoc y reach) r)))) s in
  { sc_set = s; sc_out = out; sc_in = in_ }

let certificate c =
  let rem = remaining c.cands c.dec c.default c.vm c.rl in
  let rec go defs acc =
    let sc = scert_of c rem defs in
    match inner c.cands c.dec rem defs with
    | [] -> List.rev (sc :: acc)
    | _ -> go (drop_weakest c.cands c.dec c.vm rem defs) (sc :: acc) in
  go (initial_defeats c.cands c.dec c.default c.vm c.rl) []

let check c cert = check_certificate c.cands c.dec c.default c.rl c.vm cert

(* text form, with options numbered from 1:
     round
     schwartz 1 2 3
     out 4 : 1 4
     in 2 root 1 : 1 2 | 2 3 1
     end *)
let cert_to_string cert =
  let b = Buffer.create 256 in
  let ns l = String.concat " " (List.map (fun x -> string_of_int (x + 1)) l) in
  List.iter (fun sc ->
      Buffer.add_string b "round\n";
      Buffer.add_string b ("schwartz " ^ ns sc.sc_set ^ "\n");
      List.iter (fun (x, p) -> Buffer.add_string b (Printf.sprintf "out %d : %s\n" (x + 1) (ns p))) sc.sc_out;
      List.iter (fun (y, (r, (p1, p2))) ->
          Buffer.add_string b (Printf.sprintf "in %d root %d : %s | %s\n" (y + 1) (r + 1) (ns p1) (ns p2))) sc.sc_in;
      Buffer.add_string b "end\n") cert;
  Buffer.contents b

let cert_of_string s =
  let ints t = List.filter_map (fun w -> if w = "" then None else Some (int_of_string w - 1))
      (String.split_on_char ' ' t) in
  let rounds = ref [] and cur = ref None in
  List.iter (fun line ->
      let line = String.trim line in
      let w = String.split_on_char ' ' line in
      match w, !cur with
      | ["round"], _ -> cur := Some { sc_set = []; sc_out = []; sc_in = [] }
      | "schwartz" :: _, Some sc ->
        cur := Some { sc with sc_set = ints (String.sub line 8 (String.length line - 8)) }
      | "out" :: x :: ":" :: _, Some sc ->
        let i = String.index line ':' in
        let p = ints (String.sub line (i + 1) (String.length line - i - 1)) in
        cur := Some { sc with sc_out = sc.sc_out @ [(int_of_string x - 1, p)] }
      | "in" :: y :: "root" :: r :: ":" :: _, Some sc ->
        let i = String.index line ':' in
        let rest = String.sub line (i + 1) (String.length line - i - 1) in
        let j = String.index rest '|' in
        let p1 = ints (String.sub rest 0 j) and p2 = ints (String.sub rest (j + 1) (String.length rest - j - 1)) in
        cur := Some { sc with sc_in = sc.sc_in @ [(int_of_string y - 1, (int_of_string r - 1, (p1, p2)))] }
      | ["end"], Some sc -> rounds := sc :: !rounds; cur := None
      | [""], _ -> ()
      | _ -> failwith ("bad certificate line: " ^ line))
    (String.split_on_char '\n' s);
  List.rev !rounds

(* ---------- batches of profiles (see devotee/run_devotee.pl) ---------- *)

type profile = {
  id : string; m : int;
  quorum : string;      (* devotee's quorum K, as published *)
  ndev : int;           (* number of developers: R = 3 sqrt(ndev) / 2; 0 for no quorum *)
  ratios : int list; ballots : string list }

let read_batch file =
  let ic = open_in file in
  let profs = ref [] and cur = ref None and bs = ref [] in
  (try
     while true do
       let l = input_line ic in
       if String.length l > 2 && String.sub l 0 2 = "P " then begin
         match String.split_on_char ' ' l with
         | [_; id; m; q; rs; n] ->
           cur := Some (id, int_of_string m, q, int_of_string n,
                        List.map int_of_string (List.filter ((<>) "") (String.split_on_char ',' rs)));
           bs := []
         | _ -> failwith ("bad batch line: " ^ l)
       end else if l = "E" then begin
         match !cur with
         | Some (id, m, quorum, ndev, ratios) ->
           profs := { id; m; quorum; ndev; ratios; ballots = List.rev !bs } :: !profs
         | None -> ()
       end else if l <> "" then bs := l :: !bs
     done
   with End_of_file -> ());
  close_in ic;
  List.rev !profs

(* real votes are counted under the majority rule then in force: strict
   before 2016 (Constitution v1.6, 13 December 2015) *)
let strict_of_id id =
  match String.index_opt id '-' with
  | Some i -> (try int_of_string (String.sub id 0 i) <= 2015 with _ -> false)
  | None -> false

let context_of_profile p =
  context ~m:p.m ~strict:(strict_of_id p.id) p.ballots (9 * p.ndev) 4
    (List.mapi (fun i r -> (i + 1, r)) p.ratios)
