# debian-votes-rocq

A Rocq formalisation of the Debian vote-counting procedure (Debian Constitution,
Appendix A.5), an extracted verified counter, a recount of every published
Debian vote, a differential test of devotee (the program Debian counts its
votes with), and a verified checker for outcome certificates.

## The specification (Constitution A.5)

1. Each ballot ranks the options; equal ranks are allowed; unranked options rank
   equal to each other and below every ranked option.
2. Quorum: with quorum R, a non-default option A is dropped unless V(A,D) >= R,
   where D is the default option and V(A,D) is the number of voters ranking A
   above D.
3. Majority: a non-default option A with majority ratio N is dropped unless
   V(A,D) >= N * V(D,A) and V(A,D) > V(D,A). (Until version 1.6 of the
   Constitution, 13 December 2015: unless V(A,D) > N * V(D,A).)
4. Among undropped options, A defeats B if V(A,B) > V(B,A).
5. A transitively defeats C if A defeats C, or A defeats some B that
   transitively defeats C.
6. The Schwartz set: options A such that for every B, A transitively defeats B
   or B does not transitively defeat A.
7. If there are defeats between options in the Schwartz set, drop the weakest
   such defeats (all of them if tied) and return to 5. (A,X) is weaker than
   (B,Y) if V(A,X) < V(B,Y), or V(A,X) = V(B,Y) and V(X,A) > V(Y,B).
8. Otherwise the options in the Schwartz set win (the elector with the casting
   vote chooses if there are several).

## What is proved (`DebianVote.v`, 55 definitions, 104 lemmas, no axioms)

| | Rocq |
|---|---|
| ballots, `above`, the pairwise matrix `V` (A.5.1, A.5.4) | `above`, `V`, `above_antisym` |
| quorum (stored exactly as R², since Debian's R = 3√n/2 is irrational) and majority in both versions (A.5.2, A.5.3), as booleans and as propositions | `passes_quorum`, `passes_majority`, `Quorum`, `Majority`, `remaining_in`, `default_remaining` |
| transitive defeat (A.5.5) as an inductive relation, and a boolean reachability computation proved sound and complete | `TDef`, `tdef`, `tdef_iff` |
| the Schwartz set (A.5.6), and its nonemptiness | `schwartz`, `schwartz_in`, `schwartz_nonempty` |
| weakest defeats and dropping (A.5.7); the weakest set is nonempty; dropping shortens the defeat list | `weaker`, `weakest`, `drop_weakest`, `weakest_nonempty`, `drop_weakest_shorter` |
| steps 5-8 on lists, and the implementation `cssd` | `cssd_spec`, `cssd`, `cssd_correct`, `cssd_spec_functional` |
| **the whole of A.5 as a specification on sets** (no lists, enumeration of options, or fuel) | `SSD`, `debian_outcome` |
| the counter computes the outcome, and the outcome is unique | `count_correct`, `debian_outcome_unique`, `count_complete` |
| the default option is never dropped; there is always a winner; winners are remaining options | `count_default`, `count_nonempty`, `count_winners_remaining` |
| a Condorcet winner among the remaining options is the unique winner | `count_condorcet` |
| sequential dropping only elects options of the initial Schwartz set | `count_winners_in_schwartz` |
| a Condorcet loser never wins (unless it is the only remaining option) | `count_condorcet_loser` |
| the winners do not depend on the order in which the options are listed | `count_order_independent` |
| an accepted certificate determines the outcome | `check_certificate_sound`, `check_certificate_count` |

`Print Assumptions` reports every theorem as closed under the global context.

## Building and running

First developed with Rocq 9.0.1 and OCaml 5.2.1; the current version is
checked with Rocq 9.3.0 and OCaml 4.14.2.

    make
    ./devote_main data/debian.org/vote/2019/vote_002_tally.txt 1011 1,1,1,1,1,1,1

`make` checks the proofs, extracts `devote.ml`, and builds five OCaml programs
against it: `devote_main`, `recount`, `random_cycles`, `devotee_diff` and
`certify`. Everything is OCaml (and Perl, to run devotee); there is no other
runtime.

The driver reads a Debian tally sheet (`V: <ranks> <hmac>` lines; the default
option is the last column), the number of developers (the quorum is
R = 3√n/2), the majority ratio of each option, and optionally `strict` for the
majority rule before 2016; it prints the beat matrix, the dropped options, the
pairwise defeats and the winners.

    ./devote_main --batch test/devotee_cases.batch

reads instead a batch of profiles in the input format of
`devotee/run_devotee.pl` and prints one line per profile in that program's
output format, so that the two can be compared with `diff`.

## Data

    sh scripts/fetch_debian_votes.sh

downloads the tally sheet and outcome page of every vote from
https://www.debian.org/vote/ into `data/debian.org/vote/<year>/`.

## Recounting every vote

    ./recount [--verbose] [--devotee-batch <file>]

runs the verified counter on every tally sheet with rules determined
independently of devotee's output:

- the quorum from the number of developers stated on the vote page;
- the majority ratio of every option from `data/majority_requirements.txt`,
  which quotes the secretary's "Majority Requirement" section of each page;
- the majority rule in force (strict before 2016).

It compares the beat matrix, devotee's quorum and ratios, the dropped options,
the pairwise defeats, the Schwartz set and the winners with the published
outcome. A field that cannot be compared is an error unless `not_compared`
lists it with a reason; a published record that contradicts itself is listed
in `record_inconsistent`. It writes `recount_summary.json` and
`recount_table.md`.

Result (October 2026): 59 vote pages, 2004 to 2026; 5 were withdrawn before a
ballot; all 54 that went to a ballot (24 DPL elections, 30 general
resolutions, 18,477 ballots) agree with the published outcome. The matrix and
the winners are compared for all 54 votes; the dropped options, defeats and
ratios for 53; the Schwartz set for 49 (four early pages do not list it). The
2004-004 page is truncated after the first `<` of devotee's majority section.
In 2006-002, 2018-001 and 2023-002 devotee applied the quorum for a different
number of developers than the page states (984, 882, 949 against 972, 1001,
1004); no option was near either threshold.

## Differential test of devotee

    sh scripts/fetch_devotee.sh     # devotee at a pinned commit, into devotee/src
    sh devotee/run_variants.sh      # about five minutes; writes devotee/results.txt

`devotee/run_devotee.pl` runs devotee's counting routine (`winner` in
`dvt-rslt`) unmodified on batches of profiles; `devotee_diff` compares it with
the verified counter, and with the Schulze beatpath winners as a third opinion.
On the 54 real votes devotee and the counter agree. On random profiles they do
not, because of three defects in devotee, each removed by one patch in
`devotee/patches/`:

- `fix-closure.patch`: the transitive defeats are computed only in the first
  round of step 7 (a flag is never reset), so from the second round on the
  Schwartz set is computed from direct defeats only. Every profile that needs
  two or more rounds is miscounted, usually with no winner at all.
- `fix-weakest.patch`: when two defeats have equal winning votes, a stronger
  one (fewer losing votes) met later is added to the weakest defeats and
  dropped as well.
- `fix-majority.patch`: an option with V(A,D) = V(D,A) passes the majority
  requirement, which since 2016 requires V(A,D) > V(D,A).

With all three patches devotee agrees with the counter on all 40,000 random
profiles. None of the defects affected a real vote: step 7 has never run, and
no option has ever had V(A,D) = V(D,A).

## Random cross-check

    ./random_cycles 20000 7

checks that the winners of the verified counter coincide with the Schulze
beatpath winners (winning-votes strength, losing-votes tiebreak) on random
profiles with frequent cycles. With 20,000 profiles and seed 7 (OCaml 4.14;
the random generator of OCaml 5 differs): 345 profiles entered step 7, at most
4 rounds, 1,763 produced tied winners, and all 20,000 agree.

## Certificates

    ./certify make  <tally> <developers> <ratios> <strict 0|1>  > vote.cert
    ./certify check <tally> <developers> <ratios> <strict 0|1> vote.cert

A certificate names, for every round of step 7, the Schwartz set, a path of
defeats from it to every other remaining option, and for each member a root
with paths to and from it. The verified checker (`check_certificate`, extracted)
checks these paths and performs the dropping itself; it never computes a
transitive closure. `certificates/` holds the certificates of all 54 votes.
`./certify test-real <batch>` and `./certify test-random 20000 7` check that
every certificate is accepted and that corrupted certificates are rejected or
still establish the correct winners.

## Layout

| | |
|---|---|
| `DebianVote.v` | the formalisation |
| `Extraction.v` | extraction of the counter and the certificate checker to `devote.ml` |
| `tally.ml` | tally sheets, the counting context, the certificate producer |
| `devote_main.ml` | the command-line driver |
| `recount.ml` | recount and compare with the published outcomes |
| `data/majority_requirements.txt` | the majority requirement of every option |
| `random_cycles.ml` | random cross-check against the beatpath method |
| `devotee_diff.ml`, `devotee/` | differential test of devotee |
| `certify.ml`, `certificates/` | certificates |
| `scripts/` | download the vote pages and devotee |
| `recount_summary.json`, `recount_table.md`, `devotee/results.txt` | results |
| `test/` | small hand-made tally sheets |
