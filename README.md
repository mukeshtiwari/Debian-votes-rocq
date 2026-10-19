# debian-votes-rocq

A Rocq formalisation of the Debian vote-counting procedure (Debian Constitution,
Appendix A.5), an extracted verified counter, and a recount of every published
Debian vote against the published outcomes.

## The specification (Constitution A.5)

1. Each ballot ranks the options; equal ranks are allowed; unranked options rank
   equal to each other and below every ranked option.
2. Quorum: with quorum R, a non-default option A is dropped unless V(A,D) >= R,
   where D is the default option and V(A,D) is the number of voters ranking A
   above D.
3. Majority: a non-default option A with majority ratio N is dropped unless
   V(A,D) >= N * V(D,A) and V(A,D) > V(D,A).
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

## What is proved (`DebianVote.v`, 60 lemmas, no axioms)

| | Rocq |
|---|---|
| ballots, `above`, the pairwise matrix `V` (A.5.1, A.5.4) | `above`, `V`, `above_antisym` |
| quorum and majority (A.5.2, A.5.3) | `passes_quorum`, `passes_majority`, `remaining`, `default_remaining` |
| transitive defeat (A.5.5) as an inductive relation, and a boolean reachability computation proved sound and complete | `TDef`, `tdef`, `tdef_iff` |
| the Schwartz set (A.5.6), and its nonemptiness | `schwartz`, `schwartz_in`, `schwartz_nonempty` |
| weakest defeats and dropping (A.5.7); the weakest set is nonempty; dropping shortens the defeat list | `weaker`, `weakest`, `drop_weakest`, `weakest_nonempty`, `drop_weakest_shorter` |
| steps 5-8 as an inductive specification | `cssd_spec` |
| the implementation `cssd` satisfies the specification; the specification is functional | `cssd_correct`, `cssd_spec_functional` |
| the whole procedure: `count` (from a pairwise matrix), `count_ballots` (from ballots) | `count`, `count_spec`, `count_unique` |
| the default option is never dropped; there is always a winner; winners are remaining options | `count_default`, `count_nonempty`, `count_winners_remaining` |
| a Condorcet winner among the remaining options is the unique winner | `count_condorcet` |

`Print Assumptions` reports every theorem as closed under the global context.

## Building and running

Tested with Rocq 9.0.1 and OCaml 5.2.1.

    make
    ./devote_main data/debian.org/vote/2019/vote_002_tally.txt 48 1 1,1,1,1,1,1,1,1

`make` checks the proofs, extracts `devote.ml`, and builds three OCaml programs
against it: `devote_main`, `recount` and `random_cycles`. Everything is OCaml;
there is no other runtime.

The driver reads a Debian tally sheet (`V: <ranks> <hmac>` lines; the default
option is the last column), the quorum R as a fraction, and the majority ratio
of each option, and prints the beat matrix, the dropped options, the pairwise
defeats and the winners.

## Data

    sh scripts/fetch_debian_votes.sh

downloads the tally sheet and outcome page of every vote from
https://www.debian.org/vote/ into `data/debian.org/vote/<year>/`.

## Recounting every vote

    make recount        # or ./recount [--verbose]

runs the verified counter (linked in directly, not through the command line)
on every tally sheet under `data/` with the quorum and majority ratios stated
on the published outcome page, and compares the
beat matrix, the dropped options, the pairwise defeats and the winners with the
published outcome. It writes `recount_summary.json` (one record per vote) and
`recount_table.md`.

Result (October 2026): 59 vote pages, 2004 to 2026; 5 were withdrawn before a
ballot; all 54 that went to a ballot (24 DPL elections, 30 general
resolutions, 18,477 ballots) agree with the published outcome. One page
(2004-004, the sarge release GR) is truncated on debian.org after the first
`<` of the majority section; the verified recount reproduces everything the
page still shows. The 2004-002 page loses the `< 3` of its one majority line
the same way; the ratio (3:1 for option 1) is taken from the page's prose.

Findings from the recount:

- 30 options were dropped by the majority requirement, none by quorum.
- The Schwartz set was a singleton with no internal defeat in every vote, so
  step 7 (dropping the weakest defeats) has never run on a real Debian vote.
  Every winner was a Condorcet winner among the remaining options.
- The closest supermajority decision was 2022-001 option 2: 185 votes for and
  183 needed (61 against, ratio 3:1).

## Random cross-check

    ./random_cycles 20000 7

generates random profiles with few voters and many options so that cycles are
common, and checks that the winners of the verified counter coincide with the
winners of the Schulze beatpath method (winning-votes strength, losing-votes
tiebreak), as the two are known to be equivalent. With 20,000 profiles and seed
7: 337 profiles entered the step 7 loop (at most 4 rounds), 1,819 produced tied
winners, and all 20,000 agree. The beatpath computation shares no code with the
extracted counter.

## Layout

| | |
|---|---|
| `DebianVote.v` | the formalisation |
| `Extraction.v` | extraction of `count`, `count_ballots` and helpers to `devote.ml` |
| `tally.ml` | reads a tally sheet and runs the extracted counter on it |
| `devote_main.ml` | the command-line driver |
| `recount.ml` | recount and compare with the published outcomes |
| `random_cycles.ml` | random cross-check against the beatpath method |
| `scripts/fetch_debian_votes.sh` | mirror the vote pages and tally sheets |
| `recount_summary.json`, `recount_table.md` | results of the recount |
| `test/` | small hand-made tally sheets |
