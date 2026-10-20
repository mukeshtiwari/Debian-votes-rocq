(* Extraction of the verified Debian vote counter to OCaml. *)
From Stdlib Require Import List.
Require Import DebianVote.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.

Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "devote.ml" count count_ballots V schwartz inner weakest drop_weakest tdef remaining initial_defeats check_certificate audit claim_step.
