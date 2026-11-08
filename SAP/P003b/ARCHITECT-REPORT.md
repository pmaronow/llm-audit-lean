# P003b Challenge package

4 whole, 11 restricted, 2 refuted, 0 omitted. All 17 listed theorems are proved; there are no open glue tasks.

The package states exactly this unit's 17 targets from `work.json`. It contains no Challenge for a target assigned to P003a.

The whole targets are P003-T24, P003-T31, P003-T33 and P003-T34. T24 includes the corrected sum expression, the mean and every reflected point mass. T31 includes the nonempty-accepted-set condition from the canonical endpoint domain. T33 imposes both discordance conditions. T34 keeps both probability bounds and their separate parameter conditions.

The refuted targets are P003-T26 and P003-T27. T26 supplies the deterministic 20-subject, 3-treated counterexample, its legal masks, nonempty accepted sets for both extremal completions in every possible state, and exact coverage 297/380 below 1-109/500. T27 negates the literal printed universal endpoint-and-evaluation contract. This does not assert that its numerical cap is separately false.

## Restricted targets

- **P003-T25**: Retains the two balanced lattice equalities and the exported n=4 impossible-table and nonlattice witnesses. Omits the separate all-design J=K and hull/lattice inclusion assertions, the explicit candidate set, the mirrored impossible table (1,2,0,1), uniqueness and p=1/3 for the possible endpoint table, all five maximal p-values, and equality of the printed unrestricted set with the full candidate lattice. The example accepted effects and endpoints are represented by the exact integer-numerator list and rational endpoint calculation.

- **P003-T8**: Uses a real critical value z in the displayed rational enclosure; it does not identify z with the normal 0.975 quantile or prove that quantile enclosure. Omits the extensions to every sqrt(2)<=z<=2 and every z>=1.95, the pointwise variance lower bound V_k>=1/50, the sharper pointwise HC1 width bound 2*z*sqrt(1/50), and the sharper pointwise HC0 width bound 2*z*sqrt(12/625). Retains both exact coverage fractions, both design medians, the HC0 classification and 0.54 bound, and the finite-run sharp median bound and reported-pair incompatibility for the enclosed critical values. The statement uses the explicit two-type Wald formulas without a separate labeled-assignment-to-k derivation. The design conclusions certify the displayed values as medians without asserting uniqueness.

- **P003-T19**: States the independent weak-composition count model directly. Omits an explicit linear-independence assertion for the two stratum equations, correspondence with labeled potential-outcome tables and their fixed covariates, the count 256 of labeled tables, and a cardinality assertion for a separately defined total-only eight-coordinate set. Retains the stratum totals, both four-cell and stratified cardinality formulas, the uniform degree-six bound, the convolution identity and the 100-versus-330 numerical witness.

- **P003-T20**: Retains count-distribution invariance, the four-coordinate update, all four B.8 equivalences, the corrected line identity and the parity relation. Omits the minimum-feasible-choice conclusions k>=0 and k>0 when u differs from v, the explicit failure with the printed index, and the same-assignment example with estimates 1 and -1. Labeled treatment sets represent corrected assignment vectors; there is no separate theorem about the repeated-symbol spelling in (2.3).

- **P003-T30**: Retains estimate membership in the accepted set and exact interval and both endpoint inequalities. Omits the specified possible count vector (0,n11+n00,n10+n01,0), its p-value exactly one, and the corresponding explicit table witness.

- **P003-T7**: Retains both final joint-probability inclusions and the pathwise upper-search termination and D-test budget for the corrected search. Omits the separate conditional-history one-test bounds, the one-endpoint bad-event probability bounds, deterministic endpoint comparisons for every outcome path, the separate reflected lower-endpoint assertions, and the midpoint-count and zero-midpoint decomposition of D. Those are proof steps, not hypotheses of this Challenge.

- **P003-T32**: Retains both exact endpoint returns and the total 4*n*log2(n) permutation-test bound, using the corrected sentinel search. Omits the separately stated equivalence for the compatibility oracle and its initial-segment characterization, the individual nonzero/zero-query test bounds, the individual endpoint D budgets, and the standalone inequality B.10. It makes no claim that the literal printed B.1 search is correct.

- **P003-T6**: Retains the valid-data facts, both exact rational intervals, all three positive-probability trace witnesses A/B/D, both probability inequalities E, and the aggregate lower bound and exponential comparison F. Omits the separately listed candidate-lattice/search-domain identities, every individual tested-vector p-value and full displayed list of tested vectors, and the approximate numerical probability values in E. This is a restriction of the canonical refutation of the intermediate proof claims; it does not refute the final bounds of Lemma B.15.

- **P003-T35**: The confidence set is the explicitly defined corrected procedure that loops over every j and uses the actual correlated reuse updates. This does not certify literal Algorithm 5.3 with its omitted j loop. Retains coverage for every positive K and arbitrary real estimand/statistic and the one-step uniform reuse law. Omits the separately displayed universal plus-one rank-validity assertion (5.4) and the explicit every-possible-vector-is-tested and true-table-possibility assertions; no such conclusion is assumed.

- **P003-T36**: The operation count is for the explicitly defined full-j-loop procedure, rather than a certification of literal Algorithm 5.3 with its omitted j loop. It is the stipulated arithmetic cost model, with constant-time estimand/statistic evaluations and linear-cost fresh draws. Retains finite draw/update counts, one uniform finite constant for all positive n and K, and the joint Big-O bound. It does not assert a bound on execution of the exhaustive finite minimum/table enumeration used to define the Lean procedure.

- **P003-T18**: Retains the conditional balanced O(n^2*log(n)^2) operation bound with the ceiling budget, the positive-probability and expected full-shuffle lower bounds, failure of every linear-polylogarithmic expected bound on the stated dyadic family, and the logarithm comparison for n>=15. Omits the unbalanced O(K*n^3) assertion, the separate finite product/envelope inequality 4*c*K*n^2*log2(n), and the separate draw-count bound and O(n*log(n)^2) rate. The test-count and per-draw cost bounds remain the explicit premises of canonical clause (i); no algorithmic cost conclusion is added as a premise. The negative order bound quantifies over nonnegative real exponents c.

## Definition and bridge route

The Challenge imports only the shared SAP definitions. Defs parts import Mathlib and earlier Defs parts. Both the Challenge and Solution import the same compiled definitions, including the SAP count and search-result structures. No project declaration is copied under its original fully qualified name.

- `Bridge/Part1.lean`: inverse four-field count adapters, field identities, mapped finite state/table enumerations, finite probabilities and means, accepted sets, extrema, rational inversions, and labeled-table quantities. Proofs use field reduction, list maps, membership equivalences and finite-set extensionality.
- `Bridge/Part2.lean`: line minima, candidate lists, query/endpoint trace adapters, exact and Monte Carlo searches, and shuffle costs. The recursive correspondences use structural induction over lists or fuel. This adds no search-correctness or statistical argument.
- `Bridge/Part3.lean`: missingness masks/laws/probabilities, weak-composition enumeration, reused samples, the general confidence set, and operation counts. Finite-set cardinalities are transported through injective record adapters; sample recursion and existential witnesses are transported structurally.
- `Bridge/Part4.lean`: numerical-data adapters and trace indexing. The nonempty endpoint guard for T26 is assembled from the eleven existing rational interval certificates and the existing real-extrema transfer, by cases on the already certified ten-state list. The Solution uses those certificates underlying the credited refutation; it does not reprove a statistical inequality.
- `Bridge/Part5.lean`: definitionally equal logarithm and ceiling budgets, structural correspondence for the literal printed execution, and Monte Carlo pool aliases. Final transports sometimes use `convert` followed by reflexivity to normalize implicit finite-space instances.

The only algebra beyond these correspondences is the corrected balanced sum normalization in T24 and transitivity of the two exported finite operation bounds in T36. Other proofs instantiate and combine the existing declarations.

## Verification

All Defs parts and root, Bridge parts and root, Challenge part and root, and Solution compiled with `/home/ubuntu/sap/tools/sap-lean` in dependency order. No dependency rebuild was run. Challenge stubs are the only intentional proof placeholders.

A scratch file ran `#print axioms` for each of the 17 Solution theorems. Every theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`. The recorded output is in `scratch/p003b_axioms.log`. The manifest contains the observed lists, and its proof plans are null because there are no open tasks.

Both JSON files parse. Their target/theorem inventories agree with `work.json`; every credited row is accounted for as used or not used. Every package file is at most 300 lines. The Challenge and Solution theorem types reference the same shared SAP statement constants.

`comparator.json` has the requested modules, theorem list, empty definition list, permitted dependencies and external-kernel commands. External Comparator certification was not run: no Comparator, con-ron or nanoda executable was available on PATH or through the connected tools. Compilation and the dependency audit are complete; three-kernel certification is not claimed.

## Review boundaries

Coverage judgments and diagnostic notes do not replace the canonical claim. In particular, T30, T7 and T32 are restricted despite covering their headline results, because the canonical packets also state additional witness or proof-component assertions. T25 omits the second numerical counterexample and other unstated clauses explicitly.

The canonical wording of T35/T36 does not itself amend the missing j loop. Their Challenge definitions identify the full-j-loop procedure, and both targets are therefore restricted. T18's cost premises are already in canonical clause (i); no desired theorem is introduced as an assumption. T8 is conditional on its exact real critical-value enclosure and does not certify a normal quantile. T19 does not identify abstract weak compositions with labeled tables through an unproved correspondence.

Empty inversion sets are represented by empty interval hulls. Endpoint statements either carry nonemptiness or have it guaranteed by the existing balanced result; the T26 counterexample separately certifies all endpoint inversions nonempty. Positive design and draw-count hypotheses exclude invalid denominators in the probability statements.

## Whole versions (new proofs)

The nine switches below supersede their earlier restricted classifications in this report. The package now has 13 whole, 2 restricted and 2 refuted targets. The remaining restricted targets are P003-T8 and P003-T35.

- **P003-T18** (`SAP.P003b.T18`): `SAP.P003b.T18WholeStatement`, proved by `SAP.P003b.WH.W1.T18_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW1.lean`, `SAP/P003b/WH/W1/Leaves.lean`, `SAP/P003b/WH/W1/P/T18_L1.lean`, `SAP/P003b/WH/W1/P/T18_L2.lean`, `SAP/P003b/WH/W1/P/T18_L3.lean`, `SAP/P003b/WH/W1/Proofs/T18.lean`.

  Removed restriction: Retains the conditional balanced O(n^2*log(n)^2) operation bound with the ceiling budget, the positive-probability and expected full-shuffle lower bounds, failure of every linear-polylogarithmic expected bound on the stated dyadic family, and the logarithm comparison for n>=15. Omits the unbalanced O(K*n^3) assertion, the separate finite product/envelope inequality 4*c*K*n^2*log2(n), and the separate draw-count bound and O(n*log(n)^2) rate. The test-count and per-draw cost bounds remain the explicit premises of canonical clause (i); no algorithmic cost conclusion is added as a premise. The negative order bound quantifies over nonnegative real exponents c.

- **P003-T7** (`SAP.P003b.T7`): `SAP.P003b.T7WholeStatement`, proved by `SAP.P003b.WH.W1.T7_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW1.lean`, `SAP/P003b/WH/W1/Leaves.lean`, `SAP/P003b/WH/W1/P/T7_L1.lean`, `SAP/P003b/WH/W1/P/T7_L2.lean`, `SAP/P003b/WH/W1/P/T7_L3.lean`, `SAP/P003b/WH/W1/Proofs/T7.lean`.

  Removed restriction: Retains both final joint-probability inclusions and the pathwise upper-search termination and D-test budget for the corrected search. Omits the separate conditional-history one-test bounds, the one-endpoint bad-event probability bounds, deterministic endpoint comparisons for every outcome path, the separate reflected lower-endpoint assertions, and the midpoint-count and zero-midpoint decomposition of D. Those are proof steps, not hypotheses of this Challenge.

- **P003-T32** (`SAP.P003b.T32`): `SAP.P003b.T32WholeStatement`, proved by `SAP.P003b.WH.W1.T32_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW1.lean`, `SAP/P003b/WH/W1/Leaves.lean`, `SAP/P003b/WH/W1/Proofs/T32.lean`.

  Removed restriction: Retains both exact endpoint returns and the total 4*n*log2(n) permutation-test bound, using the corrected sentinel search. Omits the separately stated equivalence for the compatibility oracle and its initial-segment characterization, the individual nonzero/zero-query test bounds, the individual endpoint D budgets, and the standalone inequality B.10. It makes no claim that the literal printed B.1 search is correct.

- **P003-T6** (`SAP.P003b.T6`): `SAP.P003b.T6WholeStatement`, proved by `SAP.P003b.WH.W1.T6_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW1.lean`, `SAP/P003b/WH/W1/Leaves.lean`, `SAP/P003b/WH/W1/P/T6_L1.lean`, `SAP/P003b/WH/W1/P/T6_L2.lean`, `SAP/P003b/WH/W1/Proofs/T6.lean`.

  Removed restriction: Retains the valid-data facts, both exact rational intervals, all three positive-probability trace witnesses A/B/D, both probability inequalities E, and the aggregate lower bound and exponential comparison F. Omits the separately listed candidate-lattice/search-domain identities, every individual tested-vector p-value and full displayed list of tested vectors, and the approximate numerical probability values in E. This is a restriction of the canonical refutation of the intermediate proof claims; it does not refute the final bounds of Lemma B.15.

- **P003-T36** (`SAP.P003b.T36`): `SAP.P003b.T36WholeStatement`, proved by `SAP.P003b.WH.W2.T36_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW2.lean`, `SAP/P003b/WH/W2/Leaves.lean`, `SAP/P003b/WH/W2/P/T36_L1.lean`, `SAP/P003b/WH/W2/P/T36_L2.lean`, `SAP/P003b/WH/W2/Proofs/T36.lean`.

  Removed restriction: The operation count is for the explicitly defined full-j-loop procedure, rather than a certification of literal Algorithm 5.3 with its omitted j loop. It is the stipulated arithmetic cost model, with constant-time estimand/statistic evaluations and linear-cost fresh draws. Retains finite draw/update counts, one uniform finite constant for all positive n and K, and the joint Big-O bound. It does not assert a bound on execution of the exhaustive finite minimum/table enumeration used to define the Lean procedure.

- **P003-T25** (`SAP.P003b.T25`): `SAP.P003b.T25WholeStatement`, proved by `SAP.P003b.WH.W2.T25_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW2.lean`, `SAP/P003b/WH/W2/Leaves.lean`, `SAP/P003b/WH/W2/Proofs/T25.lean`.

  Removed restriction: Retains the two balanced lattice equalities and the exported n=4 impossible-table and nonlattice witnesses. Omits the separate all-design J=K and hull/lattice inclusion assertions, the explicit candidate set, the mirrored impossible table (1,2,0,1), uniqueness and p=1/3 for the possible endpoint table, all five maximal p-values, and equality of the printed unrestricted set with the full candidate lattice. The example accepted effects and endpoints are represented by the exact integer-numerator list and rational endpoint calculation.

- **P003-T19** (`SAP.P003b.T19`): `SAP.P003b.T19WholeStatement`, proved by `SAP.P003b.WH.W2.T19_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW2.lean`, `SAP/P003b/WH/W2/Leaves.lean`, `SAP/P003b/WH/W2/P/T19_L1.lean`, `SAP/P003b/WH/W2/Proofs/T19.lean`.

  Removed restriction: States the independent weak-composition count model directly. Omits an explicit linear-independence assertion for the two stratum equations, correspondence with labeled potential-outcome tables and their fixed covariates, the count 256 of labeled tables, and a cardinality assertion for a separately defined total-only eight-coordinate set. Retains the stratum totals, both four-cell and stratified cardinality formulas, the uniform degree-six bound, the convolution identity and the 100-versus-330 numerical witness.

- **P003-T20** (`SAP.P003b.T20`): `SAP.P003b.T20WholeStatement`, proved by `SAP.P003b.WH.W2.T20_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW2.lean`, `SAP/P003b/WH/W2/Leaves.lean`, `SAP/P003b/WH/W2/Proofs/T20.lean`.

  Removed restriction: Retains count-distribution invariance, the four-coordinate update, all four B.8 equivalences, the corrected line identity and the parity relation. Omits the minimum-feasible-choice conclusions k>=0 and k>0 when u differs from v, the explicit failure with the printed index, and the same-assignment example with estimates 1 and -1. Labeled treatment sets represent corrected assignment vectors; there is no separate theorem about the repeated-symbol spelling in (2.3).

- **P003-T30** (`SAP.P003b.T30`): `SAP.P003b.T30WholeStatement`, proved by `SAP.P003b.WH.W2.T30_whole`.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Defs/WholeW2.lean`, `SAP/P003b/WH/W2/Leaves.lean`, `SAP/P003b/WH/W2/P/T30_L1.lean`, `SAP/P003b/WH/W2/Proofs/T30.lean`.

  Removed restriction: Retains estimate membership in the accepted set and exact interval and both endpoint inequalities. Omits the specified possible count vector (0,n11+n00,n10+n01,0), its p-value exactly one, and the corresponding explicit table witness.


Other Solution proofs do not reference any switched theorem, so no dependent-proof repairs were required. Their statements, proofs, docstrings and manifest entries are unchanged.


Verification: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P003b` passed from scratch, rebuilding all 53 modules with a clean forbidden-token scan. Then `scratch/p003b_switched_axioms.lean`, importing only `SAP.P003b.Solution`, ran `#print axioms` for all nine switched theorems. Each reported exactly `propext`, `Classical.choice` and `Quot.sound`. Logs: `scratch/p003b_switched_rebuild.log` and `scratch/p003b_switched_axioms.log`. Lean invocations were sequential; no `lake` command was run.


## Whole versions (new proofs)

- **P003-T35** (`SAP.P003b.T35`): switched to `SAP.P003b.T35WholeStatement`, proved by `SAP.P003b.WH.W1.T35_whole`, with decision `refuted`. The literal Algorithm 5.3 has joint coverage exactly 1/2 < 3/4 for the explicit n=2, m=1 counterexample and every positive K. This supersedes the earlier restricted classification of T35; the package now has 13 whole, 1 restricted and 3 refuted targets.

  Files: `SAP/P003b/Challenge/Part1.lean`, `SAP/P003b/Solution.lean`, `SAP/P003b/manifest.json`, `SAP/P003b/Defs/WholeW1.lean`, `SAP/P003b/WH/W1/Leaves.lean`, `SAP/P003b/WH/W1/P/T35_L1.lean`, `SAP/P003b/WH/W1/Proofs/T35.lean`, `SAP/P003b/WH/W1/T35Exports.lean`, `SAP/P003b/WH/W1/ProbabilityGlue.lean`. Only the Challenge, Solution and manifest were changed; the whole statement and its proof files were already supplied.

  Removed restriction: The confidence set is the explicitly defined corrected procedure that loops over every j and uses the actual correlated reuse updates. This does not certify literal Algorithm 5.3 with its omitted j loop. Retains coverage for every positive K and arbitrary real estimand/statistic and the one-step uniform reuse law. Omits the separately displayed universal plus-one rank-validity assertion (5.4) and the explicit every-possible-vector-is-tested and true-table-possibility assertions; no such conclusion is assumed.

No other Solution proof uses T35, so no dependent-proof repairs were required. All other target statements, docstrings, proofs and manifest entries remain unchanged.

Verification for P003-T35: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P003b` rebuilt all 53 modules from scratch with a clean forbidden-token scan. `scratch/p003b_t35_axioms.lean`, importing only `SAP.P003b.Solution`, ran `#print axioms SAP.P003b.T35` and reported exactly `propext`, `Classical.choice` and `Quot.sound`. Logs: `scratch/p003b_t35_rebuild.log` and `scratch/p003b_t35_axioms.log`. All Lean invocations were sequential; no `lake` command was run. The switch result is recorded in `switched.json`.
