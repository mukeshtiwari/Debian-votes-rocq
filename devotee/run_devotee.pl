#!/usr/bin/perl -w
# Run devotee's counting routine, unmodified, on a batch of profiles.
#
# devotee's dvt-rslt is a script whose sub `winner` does the whole count; it
# reads a tally sheet and a quorum file named in a configuration object and
# writes a plain-text results file. We load dvt-rslt verbatim except for three
# lines that drive it as a program (`use Devotee;`, `&main;`, `exit 0;`), and
# call `winner` with a stub configuration object, so no line of the counting
# code is changed.
#
# Usage: run_devotee.pl <dvt-rslt> <batch>
# The batch file has one block per profile:
#     P <id> <options incl. default> <quorum> <ratio_1,...,ratio_{m-1}> [<n>]
#     <rank string>          (one line per ballot, as in a tally sheet)
#     E
# (n, the number of developers, is used only by the verified side.)
# For each profile one line is printed:
#     R <id> dropped=<opts> rounds=<n> schwartz0=<opts> winners=<opts>
# with options numbered from 1 as on debian.org.

use strict;
use File::Temp qw(tempdir);

package DvtStub;
sub new { my ($class, %h) = @_; return bless {%h}, $class; }
sub get_config_ref { my $self = shift; return {%$self}; }

package main;

my ($rslt, $batch) = @ARGV;
die "usage: run_devotee.pl <dvt-rslt> <batch>\n" unless defined $batch;

open(my $src, '<', $rslt) or die "cannot read $rslt: $!";
my $code = do { local $/; <$src> };
close $src;
my $n = 0;
$n += ($code =~ s/^use Devotee;$//m);
$n += ($code =~ s/^&main;$//m);
$n += ($code =~ s/^exit 0;$//m);
die "dvt-rslt does not have the expected driver lines\n" unless $n == 3;
eval "package main; no warnings; $code; 1" or die "loading dvt-rslt: $@";

sub b36 { my $i = shift; return $i <= 9 ? "$i" : chr(ord('A') + $i - 10); }

my $dir = tempdir(CLEANUP => 1);

sub run_one {
  my ($id, $m, $quorum, $ratios, $ballots) = @_;
  my $tally = "$dir/tally.txt";
  open(my $t, '>', $tally) or die;
  my $k = 0;
  print $t "V: $_ h", $k++, "\n" for @$ballots;
  close $t;
  open(my $q, '>', "$dir/quorum.txt") or die;
  print $q "Quorum (K) = $quorum\n";
  close $q;
  my %cfg = (Quorum_File => "$dir/quorum.txt", Tally_File => $tally,
             Results => "$dir/results.txt", HTML_Result => "$dir/r.html",
             HTML_Quorum => "$dir/q.html", HTML_Majority => "$dir/m.html",
             Graph => "$dir/g.dot", Vote_Ref => "vote", File_Mask => 0644);
  for my $i (1 .. $m) {
    $cfg{"Option_" . b36($i)} = "O$i";
    $cfg{"Majority_" . b36($i)} = $ratios->[$i - 1] // 1 if $i < $m;
  }
  {
    no warnings;
    local *STDOUT; open(STDOUT, '>', '/dev/null');
    winner('Configuration' => DvtStub->new(%cfg));
    # winner leaves its bareword handles open; close them to flush the output
    close($_) for (*main::RESULTS, *main::RSLT_OUT, *main::QURM_OUT,
                   *main::MJRT_OUT, *main::GRAPH, *main::TALLY, *main::QUORUM);
  }
  open(my $r, '<', "$dir/results.txt") or die;
  my (@dropped, @winners, @schwartz0, $rounds, $in_w, $in_s);
  $rounds = 0;
  my $first_s = 1;
  while (<$r>) {
    if (/Dropping Option ?(\w+)/) { push @dropped, $1; next; }
    if (/^The Schwartz Set contains/) { $in_s = $first_s; $first_s = 0; next; }
    if (/^Weakest Defeat/) { $rounds++; next; }
    if (/^The winners are/) { $in_w = 1; next; }
    if (/^\s+Option (\w+) "/) {
      push @schwartz0, $1 if $in_s;
      push @winners, $1 if $in_w;
      next;
    }
    $in_s = 0 if /^\s*$/ && $in_s && @schwartz0;
    $in_w = 0 if /^-=/ && @winners;
  }
  close $r;
  print "R $id dropped=", join(',', @dropped), " rounds=$rounds",
    " schwartz0=", join(',', @schwartz0), " winners=", join(',', @winners), "\n";
}

open(my $b, '<', $batch) or die "cannot read $batch: $!";
my ($id, $m, $quorum, $ratios, @ballots);
while (<$b>) {
  chomp;
  if (/^P (\S+) (\d+) (\S+) (\S*)(?: \d+)?$/) {
    ($id, $m, $quorum) = ($1, $2, $3);
    $ratios = [split /,/, $4];
    @ballots = ();
  } elsif ($_ eq 'E') {
    run_one($id, $m, $quorum, $ratios, [@ballots]);
  } elsif (length) {
    push @ballots, $_;
  }
}
close $b;
