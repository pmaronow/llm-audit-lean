# P028 statement audit

Audited 10 targets and 9 theorem stubs. Verdicts: **3 correct_whole, 6 correct_restricted, 1 omission_ok**. All other verdict counts are zero; every severity is none. There are no adverse findings or requested fixes.

The blind expansion was saved in [reading.md](/home/ubuntu/sap/tasks/CHFID-P028-b/reading.md) before claims.json was opened. [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P028-b/claim-stage.json) was saved before record.json was opened. No claim-stage verdict was changed after reading the record. The canonical statement, definitions_needed and standing assumptions determined the claims; audit-history notes supplied no additional clauses or exemptions.

| Target | Verdict | Assessment of the record |
|---|---|---|
| P028-T1 | correct_restricted | Exact finite witnesses and nonidentification are retained. Completion formulas/parameters, conditional Bernoulli construction and separately asserted always-/never-taker probabilities are omitted, as disclosed in the Challenge docstring, lines 9–12. |
| P028-T2 | correct_restricted | The separation counterexample for cellwise versus armwise response mean equality, and attainment/sharpness of the four source-law sensitivity endpoints, are omitted, as disclosed at lines 18–20. |
| P028-T3 | omission_ok | Explicitly marked no_lean in claims.json; the omitted passage reports an empirical inference and estimates. Its identification reading is addressed by T1 and its mathematical repair by T2. The counterexample does not establish that the actual estimates 0.43 and 0.72 are false. |
| P028-T4 | correct_whole | Includes the full corrected algebra, both substitutions, endpoint translations and strict weakening of the printed residual constraint for 0<p<1. |
| P028-T5 | correct_restricted | Omits E5's complete feasible coordinate sets and the specified details of E6's construction; retains admissible inputs, E1–E4 and all four endpoints. Disclosed at lines 32–35. |
| P028-T6 | correct_restricted | Omits an explicit p=1 witness, the positive-pure-cell specialization and the separate empty-cell zero-product assertion. Both compliance branches, joint-moment formulas, inequalities and singleton endpoints remain. Disclosed at lines 41–43. |
| P028-T7 | correct_whole | Gives the exact randomized full-compliance witness, null events, zero proof denominators/numerators, failure of the mixture equations to determine a noncomplier mean, and correct singleton intervals. |
| P028-T8 | correct_whole | Includes interval validity and sharpness for every compatible triple, attainment of every coordinate value, and full compliance. |
| P028-T9 | correct_restricted | Adds globally measurable, integrable potential outcomes through CausalModel. Positive cells express existence of the four ordinary cell means. All corollary formulas and the noncomplier ratio remain. Disclosed at lines 61–64. |
| P028-T10 | correct_restricted | The universal identities require globally measurable, integrable potentials. The bounded existential pair retains the full nonidentification assertion. Disclosed at lines 70–73. |

All docstring line references above are to [SAP/P028/Challenge/Part1.lean](/home/ubuntu/sap/tasks/CHFID-P028-b/SAP/P028/Challenge/Part1.lean).

## Definition and truth checks

Principal strata encode precisely the three monotone binary treatment patterns; observed treatment/outcome encode consistency and exclusion. Independence concerns the joint stratum/potential-outcome variable, so the required mixture identities follow under random assignment. Finite-law assignment is explicitly a product with both response potentials included in the latent atom.

Measure.real is an ENNReal-to-real conversion, but probability mass is always finite here. Both assignment denominators are strictly positive. Nonzero first stage equals positive complier mass under the encoded monotonicity. Potential outcomes are globally integrable within CausalModel, hence so are the observed outcome, restricted integrals, differences and bounded-response products used in the statements. No assertion relies on the zero value of a nonintegrable Bochner integral.

T1 asserts positivity of every conditioning event it uses. T2's response positivity assumptions match the relevant ordinary means; its empty-cell reweighting explicitly omits those cells, and its sensitivity inequalities use product moments. T6 uses an unnormalized contribution and only gives a noncomplier conditional mean in the p<1 branch. T7 expresses the undefined conditional means through null events and failed denominator conditions, without assigning a probabilistic meaning to 0/0. T9 has four positive cells and therefore positive noncomplier mass. There are no truncated subtractions, infinite suprema or empty finite index types.

The mean equalities assumed in T2 are exactly the canonical response conditions; they do not assume the complier identification conclusion. An explicit model below satisfies all of them simultaneously. The compatibility condition in T8 is necessary for any bounded randomized model and does not remove any realizable input triple.

The T9/T10 integrability restrictions are substantive and accurately disclosed. For example, let S be uniform on the three strata, Z an independent fair coin, and H independent with P(H=n)=1/(n(n+1)) for n≥1. Set (Y₀,Y₁)=(H,0) on always-takers, (0,H) on never-takers, and (0,1) on compliers. All observed outcomes are 0 or 1, the four treatment cells are positive, and the observed and complier moments are finite. Yet both potential outcomes have infinite absolute expectation because E[H]=Σₙ1/(n+1)=∞. This model satisfies the ordinary observed-moment premises but is excluded by CausalModel.integrableY.

The witnesses T1, T5 and T7 assert their canonical counterexample claims. They are not labelled as refutations of those canonical assertions. T1 concerns a point-identification reading of the application; T5 concerns the printed intermediate system; T7 concerns an unqualified proof step and explicitly does not contradict the corollary's ordinary premise. The record makes no inappropriate refuted decision.

## Nonvacuity and independent verification

[scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P028-b/scratch/Check.lean) was compiled successfully with the prescribed sap-lean command. It imports only SAP.P028.Defs, and uses no Challenge theorem. It constructs a CausalModel on Bool with fair assignment, everyone a complier, Y₀=0,Y₁=1, proves bounded outcomes and p=1, and checks the printed scalar candidate and its failure of the mixture system. The final compiler log is empty and the exit code was 0. Lean processes were run sequentially; lake was never run.

For the positive-cell and response hypotheses in T2/T9, use Ω={A,N,C}×{0,1}, mass 1/6 at every point, S the first coordinate, Z the second, constant potentials Y₀=0,Y₁=1, and R=1. Then p=q=r=1/3, e₀=1/3,e₁=2/3. The pure joint cells have mass 1/6 each and the other two have mass 1/3 each. Every required response event is positive; response independence and all mean equalities hold. In T6 this also realizes the p<1 branch, with contribution 1/3 and noncomplier mean 1/2.

For T5/T10, on Bool×Bool take half compliers, half never-takers and independent fair assignment. Give both complier potentials the value t and both never-taker potentials 3/2−t. For t=1/2 and t=1 these are bounded models with the same p=1/2,e₀=e₁=3/4,CACE=0 and different complier levels. The t=1 model is also the required admissible realization in T5.

For T8, if p<1, give mass p to compliers with constant potentials (x₁−(e₁−e₀)/p,x₁) and mass 1−p to never-takers with both potentials (e₁−p x₁)/(1−p), independently of fair assignment. The stated interval ensures all these numbers lie in [0,1]. This realizes each treated coordinate, and translating the coordinate realizes each control value. At p=1 use only compliers with potentials (e₀,e₁). Thus full compliance and all claimed coordinate attainments have concrete nonempty probability laws.

[scratch/finite_check.py](/home/ubuntu/sap/tasks/CHFID-P028-b/scratch/finite_check.py) independently parses the finite tables and uses Python Fraction arithmetic. It verifies all positive masses and their sums, monotonicity, complier/stratum probabilities, every recorded and missing cell, equality of the entire observed law, all relevant positive denominators, both complier pairs, the full/response Corollary comparisons and all eight T2 values. It completed successfully; its exact output is [scratch/finite_results.json](/home/ubuntu/sap/tasks/CHFID-P028-b/scratch/finite_results.json).

The final per-target judgments and explicit nonvacuity instances are in [findings.json](/home/ubuntu/sap/tasks/CHFID-P028-b/findings.json).
