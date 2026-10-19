(* Certificates for Debian votes. A certificate is produced by the untrusted
   code in tally.ml and checked by check_certificate, extracted from the Rocq
   development, whose soundness theorem (check_certificate_sound) says that an
   accepted certificate determines the outcome of Appendix A.5.

   Usage:
     certify make  <tally> <developers> <ratio_1,...> <strict 0|1>
         print a certificate for the vote
     certify check <tally> <developers> <ratio_1,...> <strict 0|1> <certificate>
         check a certificate and print the winners it establishes
     certify write-all <batch> <dir>
         write <dir>/<vote>.cert for every vote of a batch
     certify test-real <batch>         (batch from recount --devotee-batch)
     certify test-random <n> <seed>
         for every profile: produce a certificate, check it, compare with the
         counter, then corrupt it in six ways and check that every corrupted
         certificate is rejected or still establishes the correct winners *)

open Devote

let up l = List.sort compare (List.map (fun x -> x + 1) l)

let read_file f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

let ctx_of_args tally ndev ratios strict =
  let ratios = List.mapi (fun i s -> (i + 1, int_of_string s)) (String.split_on_char ',' ratios) in
  Tally.context ~strict:(strict = "1") (Tally.read_ballots tally) (9 * int_of_string ndev) 4 ratios

(* ---------- corruptions ---------- *)

let map_first f = function [] -> [] | x :: l -> f x :: l
let map_last f l = match List.rev l with [] -> [] | x :: r -> List.rev (f x :: r)
let drop_last l = match List.rev l with [] -> [] | _ :: r -> List.rev r

(* each corruption returns None when it does not apply to the certificate *)
let corruptions (c : Tally.ctx) : (string * (int scert list -> int scert list option)) list =
  let rem cert = match cert with [] -> [] | sc :: _ -> List.map fst sc.sc_out @ sc.sc_set in
  [ "remove a member of a Schwartz set", (fun cert ->
        match cert with
        | sc :: _ when sc.sc_set <> [] ->
          Some (map_first (fun sc -> { sc with sc_set = List.tl sc.sc_set }) cert)
        | _ -> None);
    "add a non-member to a Schwartz set", (fun cert ->
        match cert with
        | sc :: _ -> (match List.find_opt (fun x -> not (List.mem x sc.sc_set)) (rem cert) with
            | Some x -> Some (map_first (fun sc -> { sc with sc_set = x :: sc.sc_set }) cert)
            | None -> None)
        | [] -> None);
    "delete the witness path of an outside option", (fun cert ->
        match cert with
        | sc :: _ when sc.sc_out <> [] -> Some (map_first (fun sc -> { sc with sc_out = List.tl sc.sc_out }) cert)
        | _ -> None);
    "shorten a witness path", (fun cert ->
        match cert with
        | sc :: _ -> (match List.find_opt (fun (_, p) -> List.length p > 1) sc.sc_out with
            | Some (x, p) ->
              Some (map_first (fun sc -> { sc with sc_out = (x, drop_last p) :: List.remove_assoc x sc.sc_out }) cert)
            | None -> None)
        | [] -> None);
    "claim the default option as the only winner", (fun cert ->
        if cert = [] then None
        else Some (map_last (fun sc -> { sc with sc_set = [c.default];
                                                 sc_in = [(c.default, (c.default, ([c.default], [c.default])))] }) cert));
    "omit the last round", (fun cert ->
        if List.length cert > 1 then Some (drop_last cert) else None) ]

(* ---------- tests ---------- *)

let test profs label =
  let n = List.length profs and ok = ref 0 and lines = ref 0 and maxl = ref 0 and rounds = ref 0 in
  let applied = Hashtbl.create 8 and rejected = Hashtbl.create 8 and wrong = ref 0 in
  let t_count = ref 0. and t_check = ref 0. in
  List.iter (fun (p : Tally.profile) ->
      let c = Tally.context_of_profile p in
      let t0 = Sys.time () in
      let rep = count c.cands c.dec c.default c.rl c.vm in
      let t1 = Sys.time () in
      let cert = Tally.certificate c in
      let text = Tally.cert_to_string cert in
      let cert' = Tally.cert_of_string text in          (* round trip through the text form *)
      let t2 = Sys.time () in
      let res = Tally.check c cert' in
      let t3 = Sys.time () in
      t_count := !t_count +. (t1 -. t0); t_check := !t_check +. (t3 -. t2);
      let nl = List.length (String.split_on_char '\n' text) - 1 in
      lines := !lines + nl; maxl := max !maxl nl;
      if List.length cert > 1 then incr rounds;
      (match res with
       | Some w when up w = up rep.rep_winners -> incr ok
       | _ -> Printf.printf "NOT ACCEPTED: %s\n" p.id);
      List.iter (fun (name, f) ->
          match f cert with
          | None -> ()
          | Some bad ->
            Hashtbl.replace applied name (1 + Option.value ~default:0 (Hashtbl.find_opt applied name));
            match Tally.check c bad with
            | None -> Hashtbl.replace rejected name (1 + Option.value ~default:0 (Hashtbl.find_opt rejected name))
            | Some w when up w = up rep.rep_winners -> ()
            | Some _ -> incr wrong; Printf.printf "WRONG OUTCOME ACCEPTED: %s, %s\n" p.id name)
        (corruptions c)) profs;
  Printf.printf "%s: %d profiles; certificates accepted with the counter's winners: %d\n" label n !ok;
  Printf.printf "  more than one round: %d; certificate lines: mean %.1f, max %d\n"
    !rounds (float_of_int !lines /. float_of_int (max 1 n)) !maxl;
  Printf.printf "  time: counting %.3fs, checking %.3fs\n" !t_count !t_check;
  List.iter (fun (name, _) ->
      let a = Option.value ~default:0 (Hashtbl.find_opt applied name) in
      let r = Option.value ~default:0 (Hashtbl.find_opt rejected name) in
      Printf.printf "  %-46s applied %6d, rejected %6d, accepted (correct winners) %6d\n" name a r (a - r))
    (corruptions (Tally.context_of_profile (List.hd profs)));
  Printf.printf "  corrupted certificates accepted with wrong winners: %d\n" !wrong

let () =
  match Array.to_list Sys.argv |> List.tl with
  | ["make"; tally; ndev; ratios; strict] ->
    print_string (Tally.cert_to_string (Tally.certificate (ctx_of_args tally ndev ratios strict)))
  | ["check"; tally; ndev; ratios; strict; cert] ->
    let c = ctx_of_args tally ndev ratios strict in
    (match Tally.check c (Tally.cert_of_string (read_file cert)) with
     | Some w -> Printf.printf "accepted; winners:%s\n" (Tally.ints (up w))
     | None -> print_endline "REJECTED"; exit 1)
  | ["write-all"; batch; dir] ->
    List.iter (fun (p : Tally.profile) ->
        let oc = open_out (Filename.concat dir (p.id ^ ".cert")) in
        output_string oc (Tally.cert_to_string (Tally.certificate (Tally.context_of_profile p)));
        close_out oc) (Tally.read_batch batch)
  | ["test-real"; batch] -> test (Tally.read_batch batch) "real votes"
  | ["test-random"; n; seed] ->
    Random.init (int_of_string seed);
    let profs = List.init (int_of_string n) (fun k ->
        let m = 3 + Random.int 5 and nb = 5 + Random.int 11 in
        { Tally.id = string_of_int k; m; quorum = "0"; ndev = 0; ratios = List.init (m - 1) (fun _ -> 1);
          ballots = List.init nb (fun _ -> Tally.random_ranks m) }) in
    test profs "random"
  | _ -> prerr_endline "usage: see the head of certify.ml"; exit 2
