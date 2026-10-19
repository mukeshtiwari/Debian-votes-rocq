#!/bin/sh
# Download the public record of every Debian vote: the outcome page (HTML,
# content-negotiated English), the tally sheet (ballots), the results graph
# and the statistics page, for every year since 2000.
#
# Run this on a machine with normal internet access, from the repository root:
#     sh scripts/fetch_debian_votes.sh
# It writes into data/debian.org/vote/<year>/ and is safe to re-run.
set -e
cd "$(dirname "$0")/.."
mkdir -p data
cd data
wget -r -l 3 -np -nH -N -e robots=off --wait=0.5 \
     -P debian.org \
     -A 'index.en.html,vote_???,vote_???.en.html,vote_???_tally.txt,vote_???_results.dot,vote_???_quorum.txt,vote_???_majority.txt,vote_???_results.txt,tally.txt,suppl_???_stats,suppl_???_stats.en.html' \
     https://www.debian.org/vote/
echo "done; tally sheets:"; find debian.org -name '*tally*.txt' | sort | wc -l
