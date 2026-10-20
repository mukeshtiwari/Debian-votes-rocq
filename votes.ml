(* Where the data of each Debian vote lives, and the rules of each vote,
   determined without devotee's output: the number of developers stated on
   the vote page, the majority requirements of data/majority_requirements.txt,
   and the majority rule in force (strict before 2016). Shared by recount and
   audit. *)

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

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

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

(* "2026-002" for data/debian.org/vote/2026/vote_002 *)
let key year vid = Printf.sprintf "%s-%s" year (String.sub vid 5 (String.length vid - 5))

(* the majority rule changed with Constitution v1.6 (13 December 2015) *)
let strict_of_year year = int_of_string year <= 2015
