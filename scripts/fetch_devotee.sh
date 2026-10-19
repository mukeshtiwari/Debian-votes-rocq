#!/bin/sh
# Fetch devotee, the program Debian uses to count its votes, at a pinned
# commit, for the differential test (devotee_diff). devotee is GPL-2+ and is
# not redistributed here; it lands in devotee/src, which is not tracked.
#
# Run from anywhere:
#     sh scripts/fetch_devotee.sh
set -e
cd "$(dirname "$0")/.."
REPO=https://salsa.debian.org/debian/devotee.git
COMMIT=f5b727caa1d3cb5f9399d86c084eb92a21374ae8   # 2023-12-27, current master
if [ ! -d devotee/src/.git ]; then
  git clone -q "$REPO" devotee/src
fi
git -C devotee/src fetch -q origin
git -C devotee/src checkout -q "$COMMIT"
echo "devotee at $(git -C devotee/src log -1 --format='%h %ad' --date=short)"
