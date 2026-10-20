# devotee (upstream copy)

Unmodified files from devotee, the program Debian uses to count its votes:

    repository: https://salsa.debian.org/debian/devotee
    commit:     f5b727caa1d3cb5f9399d86c084eb92a21374ae8 (2023-12-27, master)

| file | role |
|---|---|
| `dvt-rslt.pl` | upstream's `dvt-rslt`, renamed: `winner` computes the outcome of a vote |
| `lib/Devotee.pm` | devotee's configuration module, needed only to run `dvt-rslt` on its own |

devotee is Copyright 2003, 2004 Manoj Srivastava and others, and is
distributed under the GNU General Public License, version 2 (`COPYING`,
`LICENSE`). These files are distributed here under that license, unchanged;
they are not covered by the license of the rest of this repository.

`devotee/run_devotee.pl` loads `dvt-rslt` and calls `winner`;
`devotee/patches/` holds our fixes, which are applied to temporary copies only.
`sh scripts/fetch_devotee.sh` checks that these files are identical to the
upstream commit.

To run `dvt-rslt` on its own, as Debian does, give it a devotee configuration
(see the upstream `examples/devotee.conf`) and switch off signing:

    perl -I devotee/upstream/lib devotee/upstream/dvt-rslt.pl --config_file=vote.conf \
         --noneed_gpg --noneed_pgp --noneed_ldap --nosign_ack
