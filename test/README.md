# Test tally sheets

| file | what it is |
|---|---|
| `dpl2013_tally.txt`, `dpl2024_tally.txt`, `gr2019_init_tally.txt` | small hand-made tally sheets |
| `devotee_closure_tally.txt` | devotee defect 1: transitive defeats computed only in the first round of step 7 |
| `devotee_weakest_tally.txt` | devotee defect 2: a stronger defeat dropped as one of the weakest |
| `devotee_majority_tally.txt` | devotee defect 3: an option that ties the default option passes step 3 |
| `devotee_cases.batch` | the three devotee cases as a batch for `devotee/run_devotee.pl` |
| `devotee_results/` | devotee's own results files for the three cases |

The default option is the last column of every ballot. No quorum, majority
ratio 1 for every option.

## Both counters on the same input

The batch file is read by both programs, which print one line per case in
the same format:

    ./devote_main --batch test/devotee_cases.batch
    perl devotee/run_devotee.pl devotee/upstream/dvt-rslt.pl test/devotee_cases.batch

The verified counter prints

    R closure dropped= rounds=2 schwartz0=1,2,3,4,5 winners=4,5
    R weakest dropped= rounds=1 schwartz0=2,3,4,6 winners=3,4,6
    R majority dropped=1 rounds=0 schwartz0=2 winners=2

and devotee prints

    R closure dropped= rounds=1 schwartz0=1,2,3,4,5 winners=
    R weakest dropped= rounds=1 schwartz0=2,3,4,6 winners=2,3,4,6
    R majority dropped= rounds=0 schwartz0=1,2 winners=1,2

that is: no winner instead of {4, 5}; option 2 wrongly among the winners;
option 1 kept, and tying with the default, instead of being dropped.

The tally sheets can also be counted one at a time:

    ./devote_main test/devotee_closure_tally.txt  0 1,1,1,1,1,1
    ./devote_main test/devotee_weakest_tally.txt  0 1,1,1,1,1,1,1
    ./devote_main test/devotee_majority_tally.txt 0 1,1

## Auditing devotee's output

`devotee_results/` holds devotee's results files for the three cases,
produced with

    DVT_KEEP=test/devotee_results perl devotee/run_devotee.pl devotee/upstream/dvt-rslt.pl test/devotee_cases.batch

The verified audit names the lines that violate Appendix A.5 and says why
(line 70 of the closure case: the Schwartz set after the first round; line 78
of the weakest case: a defeat that is not among the weakest; line 26 of the
majority case: an option that only ties the default option):

    ./audit --files test/devotee_results/closure_results.txt  test/devotee_closure_tally.txt  0 1,1,1,1,1
    ./audit --files test/devotee_results/weakest_results.txt  test/devotee_weakest_tally.txt  0 1,1,1,1,1,1
    ./audit --files test/devotee_results/majority_results.txt test/devotee_majority_tally.txt 0 1
