P003a packages all 18 assigned targets: 18 whole, 0 restricted, 0 refuted, and 0 omitted.
Every target has one proved Challenge/Solution pair under its original fully qualified name.
No target from the other unit is included. Open glue tasks: none.

The input to declaration review round 3 already contained the upgraded WholeW1,
WholeW2 and WholeW3 statements and their proved WH exports for the 13 formerly
restricted targets. Those existing proofs supply the additional clauses. This revision
corrects T1's two descriptions and adds two definitional equivalences to T14 by
reflexivity. It introduces no mathematical argument.

There are no restricted or omitted targets. The current decisions supersede the
historical restrictions described in earlier review rounds. The canonical claims for
T1, T4, T9 and T11 already assert refutations; their complete counterexamples are whole,
under the brief's distinction between a refutation claim and a refuted positive claim.

| Target | Current statement | Existing whole export, where upgraded |
| --- | --- | --- |
| P003-T29 | T29Statement | Original exact coverage export. |
| P003-T1 | T1WholeStatement | WH.W1.T1_whole |
| P003-T2 | T2Statement | Original balanced missingness and coupling exports. |
| P003-T3 | T3Statement | Original completion and coverage exports. |
| P003-T4 | T4WholeStatement | WH.W1.T4_whole |
| P003-T5 | T5WholeStatement | WH.W2.T5_whole |
| P003-T11 | T11WholeStatement | WH.W2.T11_whole |
| P003-T12 | T12WholeStatement | WH.W2.T12_whole |
| P003-T13 | T13Statement | Original SATE and two witness exports. |
| P003-T14 | T14WholeStatement | WH.W2.T14_whole, with two reflexivity conjuncts. |
| P003-T9 | T9WholeStatement | WH.W2.T9_whole |
| P003-T10 | T10Statement | Original independent smoothing and parity exports. |
| P003-T15 | T15WholeStatement | WH.W3.T15_whole |
| P003-T16 | T16WholeStatement | WH.W3.T16_whole |
| P003-T17 | T17WholeStatement | WH.W3.T17_whole |
| P003-T21 | T21WholeStatement | WH.W1.T21_whole |
| P003-T22 | T22WholeStatement | WH.W1.T22_whole |
| P003-T23 | T23WholeStatement | WH.W1.T23_whole |

All names in the last column begin SAP.P003a. The manifest records the original
credited rows, existing proved leaves and assemblies, their unused-row explanations,
and the dependencies printed for each final theorem.

The package uses the shared-definition route. Defs parts and the WholeW modules
import Mathlib and earlier SAP definitions. Challenge imports those definitions only;
Solution imports the Bridge and existing project/WH proofs. Both sides therefore use
the same compiled SAP definitions.

Bridges are representation glue:

- Bridge/Part1 converts count records field by field. Inverse and scalar identities
  use reflexivity; enumerations use map/flatMap/filterMap identities. Tail counts,
  p-values, acceptance and interval hulls follow by simplification and transport.
- Bridge/Part2 transports missingness laws and finite probabilities through those
  enumerations. Count, variance, standard-error and unit formulas agree field by field.
  The minimum-base scan agrees by structural induction on its list.
- Bridge/Part3 transports recursive searches by induction on fuel and table scans by
  induction on lists; endpoint projections agree after splitting existing branches.
- Bridge/Part4 decodes arbitrary inputs and closed witnesses, transports quantifiers
  and finite images, and unfolds definitionally equal SD, uniform-law and unit notions.

The existing WH proof modules supply the upgraded components. This revision changes
only T14's assembly, inserting `(fun _ => Iff.rfl)` and `Iff.rfl`. Its pmf, pushforward,
first-moment and mean proofs are reused unchanged.

Endpoint and probability conventions remain explicit. Empty accepted sets give empty
interval hulls; missingness intervals guard their extrema. Positive observed arm sizes
and population sizes exclude zero statistical denominators. Lattice rescaling assumes
k>0; its general mean identities require the existing first-moment condition. Corrected
SD includes its finite-first-moment condition. Fuel and optional search outputs retain
their stated conventions. No new assumption was introduced to obtain a missing clause.

## Referee findings — revision 2

The initial referees supplied 36 target assessments. A had no adverse finding; B's
T14 restriction finding had two valid points: the old statement supplied no separate
source lattice law, and its normalization already belonged to its IsMass premise.
Both were disclosed at that time. The later supplied whole exports now provide the
source law, pushforward, moment and mean correspondence, so that former restriction
is historical. The canonical source-law clause remains the standard
([work.json](/home/ubuntu/sap/wt/ARCH-P003a/work.json:1238)).

## Declaration review round 1

T4's minor incomplete-restriction finding was accepted. The old restriction was
extended to disclose the absent 144 possible-vector count, 12870 assignments and
two estimator atoms with 6435 assignments each and their distance 1/16
([finding](/home/ubuntu/sap/wt/ARCH-P003a/fw/round1/T4/r2g1/findings.json:53)).
The supplied T4WholeStatement and WH.W1.T4_whole now include those assertions,
the traces, candidate/search domains, first tests and all part-(D) examples. The
former restricted classification is superseded by that existing complete proof.

## Declaration review round 2

T23's major label finding and missing-disclosure issue were accepted. Its old abstract
sentinel property was relabelled restricted because it did not identify Algorithm
4.5's endpoint, decisions and trace or compare them with the exact endpoint
([finding](/home/ubuntu/sap/wt/ARCH-P003a/fw/round2/T23/r3g4/findings.json:31)).
The supplied T23WholeStatement and WH.W1.T23_whole now add that application,
including chronological fresh batches, whole compatibility blocks and existence of
the exact balanced endpoint on its lattice. The current whole decision follows the
upgraded statement, rather than the old unrestricted label.

## Declaration review round 3

Both adverse findings were checked against their canonical claims and actual Lean
statements. Both reviewers are right; all four issues are addressed.

1. **T1, not_faithful/minor, issues 1 and 2: accepted.** The Challenge and duplicated
   definition docstrings omitted the effect constraint from the maximum-p-value
   sentence. The canonical claim and actual universal bound restrict to tables
   possible for the upper completion with tau>=-3/20
   ([current bound](/home/ubuntu/sap/wt/ARCH-P003a/SAP/P003a/Defs/WholeW1/Part3.lean:152),
   [finding](/home/ubuntu/sap/wt/ARCH-P003a/fw/round3/T1/r5g1/findings.json:20)).
   Both descriptions now state that constraint and identify maximizers (8,0,3,9)
   and (9,0,3,8). The maximum is not asserted outside that region. T1's mathematical
   statement, proof and whole decision are unchanged.
2. **T14, label_wrong/minor, issues 1 and 2: accepted and repaired by glue.** The
   old whole statement's general source-law component contained only pmf,
   pushforward, moment and mean assertions. Adjacent lattice symmetry/SD definitions
   were absent from its dependency closure, so its whole label and descriptions
   overstated the clauses actually stated
   ([finding](/home/ubuntu/sap/wt/ARCH-P003a/fw/round3/T14/r5g2/findings.json:53)).
   The existing positive-k source-pmf component now also asserts, for every integer
   twice-center c2, the equivalence of W2LatticeSymmetric f c2 with
   f(w2Point k (c2-j))=f(w2Point k j) for every integer j, and the equivalence of
   W2LatticeSD f with IsSD(w2Rescale f)
   ([statement](/home/ubuntu/sap/wt/ARCH-P003a/SAP/P003a/Defs/WholeW2.lean:221)).
   Both equivalences unfold existing definitions; the existing assembly supplies
   them by reflexivity
   ([assembly](/home/ubuntu/sap/wt/ARCH-P003a/SAP/P003a/WH/W2/Leaves.lean:116)).
   This restores the omitted canonical clauses, so T14 remains whole. Both
   docstrings now specify symmetry at physical center c2/(2k) and SD through g.

There is no disagreement with either reviewer and no unresolved finding. The other
four entries in each supplied findings file have no adverse issue.

The shared definition T14WholeStatement was strengthened. **SAP.P003a.T14 must be
reviewed again with its expanded definition closure.** The two symmetry/SD definitions
themselves are unchanged. No other Challenge theorem depends on T14WholeStatement;
all other mathematical statements retain their input bodies.

The inherited WholeW1 definition file and T1_L5 proof file exceeded 300 lines.
They were split at declaration boundaries into three and two parts, retaining their
original root import modules and all declaration names. Reconstructing the parts
recovers the input definition bodies and T1 proof source exactly after ignoring
only the corrected documentation. W2/Leaves documentation was reflowed to keep that
file within 300 lines; its only proof change is the two T14 reflexivity conjuncts.
No new mathematical proof was written. REPORT.md was condensed to describe the
current package and preserve the earlier findings and their resolutions.

## Validation

All 75 SAP Lean modules compiled successfully with sap-lean in dependency order,
one Lean process at a time. The scratch Axioms file inspected all 18 final theorems;
each uses only propext, Classical.choice and Quot.sound. Exact output is in
scratch/axioms.log. Both JSON files parse, the manifest and Comparator contain
exactly the 18 assigned targets, and every theorem retains its fully qualified name.

Every SAP Lean file sets both implicit-variable options immediately after imports.
Every SAP source and configuration file is at most 300 lines. Defs and Challenge
import boundaries and the forbidden-token rules are checked. Existing project
sources, work.json, examples and all reviewer reports remain unchanged.

The inherited T12 manifest entry listed finite_tail_repair as both used and unused.
Its upgraded T12_L1 proof invokes that export; the obsolete unused entry was removed.
All original credited rows are accounted for without used/unused overlap.
The upgraded T23 proof also uses Classical.choice; its manifest dependency list now
matches the fresh printed result.

The input snapshot had a successful three-kernel certificate for all 18 theorems at
20261104T173846Z
([certificate](/home/ubuntu/sap/wt/ARCH-P003a/SAP/P003a/verification/comparator-result.json)).
All 70 input SAP Lean sources matched that snapshot before this revision. The stored
certificate is historical evidence; it does not certify T14's added clauses or the
new file layout. This revision runs fresh Lean compilation and dependency checks.
No fresh external Comparator run is claimed. The Comparator configuration is
regenerated from the manifest and retains the same 18 theorem names and three
permitted logical dependencies.
