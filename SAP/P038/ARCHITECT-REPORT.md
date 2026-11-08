P038: **1 whole, 0 restricted, 0 refuted, 0 omitted**. One target is proved;
there are no open glue tasks. The only unit target is P038-T1, packaged as
`SAP.P038.T1`.

P038-T1 concerns footnote 2, third sentence, first value (PDF p. 3), Fig. 1's
election-hours panel and caption, and Methods (PDF p. 2) of *Driving Fatalities
on US Presidential Election Days: A Reanalysis* (2016). The canonical claim is
already a conditional corrected statement. Its single credited row,
`AronowAudit.P038.corrected_election_hours_window`, has final status `ok` and
supports all four mathematical clauses:

- Two outside points among fifty give 2/50 = 1/25 = 0.04, with discrepancy
  1/50 from the printed 0.06.
- The exact equality and rounding characterizations require three outside
  points for 0.06 and two for 0.04, both for integer counts and for the actual
  25-week empirical proportion.
- Counts are monotone over nested windows. Under the explicit 25-week tail-set
  hypothesis {-14, 7}, the 12-week count is one and the 25-week count is two;
  the proportions and rounding bounds are all retained.
- Counting election day as one extra tail point gives 3/51 = 1/17 for 25 weeks
  and 2/25 = 0.08 for 12 weeks, with all stated rounding bounds. Neither this
  convention nor the reference-only convention yields both printed values.

No target is restricted or omitted, and no credited row is unused. The SAP
statement was compared textually with the complete credited theorem type:
every clause agrees after ignoring whitespace and resolving the SAP names.

The route uses shared Mathlib-only definitions in `SAP/P038/Defs/Part1.lean`,
imported through `SAP/P038/Defs.lean` by both sides. They define the reference
window, strict outside predicate, tail set and count, empirical proportion,
rounding bin, alternative proportion, and the complete target proposition.
The Challenge imports only these definitions. Its root imports only its part.

`SAP/P038/Bridge.lean` imports the shared definitions and the existing project
module. Its seven correspondences (`referenceWeeks_eq`, `moreExtreme_eq`,
`tailWeeks_eq`, `tailCount_eq`, `empiricalP_eq`, `roundsTo_eq`, and
`electionDayAdjustedP_eq`) are each proved by `rfl`. The Solution unfolds the
shared proposition and rewrites the SAP quantities using these equalities to
apply the single credited row. The predicate correspondence is available but
unnecessary separately because the tail-set correspondence already includes
it. There is no new mathematical argument.

The figure-tail hypotheses remain conditional. The theorem does not certify
the raster reading, supply FARS counts, or determine which published output
reflects the final data. In particular, merely having two tails does not imply
that their weeks are {-14, 7}; the statement keeps those hypotheses separate.
Positivity of the election RR and the relevant reference RRs is preserved.
Empirical proportions occur only at positive windows 12 and 25, so no
zero-denominator branch is used. The specified half-open rounding convention
is retained exactly, and values of the total RR function outside the relevant
windows do not enter the conclusions.

Validation used `/home/ubuntu/sap/tools/sap-lean` on the definitions part and
root, Bridge, Challenge part and root, Solution, and the scratch dependency
check, in dependency order. All compiled successfully. The dependency check
in `scratch/P038Axioms.lean` reports for `SAP.P038.T1` exactly `propext`,
`Classical.choice`, and `Quot.sound`. A separate scratch file checks all seven
Bridge correspondences. Every SAP file has the required implicit-variable
options and is below 300 lines. The generated JSON files parse and the
manifest and comparator list exactly the unit target and its theorem.

`SAP/P038/comparator.json` specifies the required modules, theorem, permitted
dependencies, and external kernel commands. External Palomar Comparator
certification has not been run here; no Comparator invocation was supplied
and the named external kernel executables were not found on PATH. The
compilation and dependency checks above succeeded, and every listed theorem
has a Solution proof.
