#!/bin/sh
# Check that devotee/upstream holds unmodified files from devotee, the program
# Debian uses to count its votes, at the pinned commit: clone the upstream
# repository into a temporary directory and compare.
#
#     sh scripts/fetch_devotee.sh
set -e
cd "$(dirname "$0")/.."
REPO=https://salsa.debian.org/debian/devotee.git
COMMIT=f5b727caa1d3cb5f9399d86c084eb92a21374ae8   # 2023-12-27, master
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
git clone -q "$REPO" "$tmp/devotee"
git -C "$tmp/devotee" checkout -q "$COMMIT"
for f in dvt-rslt lib/Devotee.pm COPYING LICENSE; do
  cmp "$tmp/devotee/$f" "devotee/upstream/$f"
done
echo "devotee/upstream matches devotee $(git -C "$tmp/devotee" log -1 --format='%h %ad' --date=short)"
