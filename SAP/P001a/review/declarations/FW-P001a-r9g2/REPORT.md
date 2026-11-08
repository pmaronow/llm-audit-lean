# Declaration fidelity review

All five declarations are **faithful**, with severity **none**. T7 and T9
faithfully state the disclosed restricted refutations; T6, T8 and T10 cover
the whole corrected claims.

| Declaration | Record decision | Result |
|---|---|---|
| SAP.P001a.T6 | whole | All corrected consistency, envelope and uniform Gram bounds covered. |
| SAP.P001a.T7 | refuted | Genuine fixed-covariate wrong-target example; omissions accurately disclosed. |
| SAP.P001a.T8 | whole | Averaged KL identity, optimizer equivalence, consistency and identification covered. |
| SAP.P001a.T9 | refuted | Genuine unrestricted-mixture nonattainment witness; omissions accurately disclosed. |
| SAP.P001a.T10 | whole | General positive-sample unboundedness and compact-restriction attainment covered. |

The blind reading was saved as `reading.md` before claims or record were
opened. Every declaration in each closure was inspected, including all
generated proof auxiliaries. `claim-stage.json` was saved before opening
`record.json`; no claim-stage conclusion changed afterward. T6 slightly
generalizes exact interval support to almost-sure compact containment.

For T7, the printed reading asserts convergence of pooled ML to the unique
conditional-KL target at a fixed supported covariate value. The four-atom
witness satisfies its probability, iid, model-normalization, positive
conditioning-mass, unique-target, attained-MLE and finiteness conditions.
Its limit is 1/2 instead of either 1/4 or 3/4. The omitted KL derivatives
and exact averaged-KL gap are disclosed in the docstring and record.

For T9, the printed reading asserts existence of a global maximizer for
the displayed mixture over its unrestricted admissible domain on a positive
sample. The sample (1,2,3) is positive and nonempty; every positive-scale
path parameter is admissible. A positive C/scale likelihood lower bound
diverges while every admissible likelihood is finite. This refutes the
stated existence assertion. The omitted quantitative bounds, explicit scale
choice and general-sample path are disclosed. Neither refutation violates
an independence condition or relies on an undefined quantity.

The definitions use genuine conditional laws, squared-error least squares,
the Euclidean operator norm and the correct component densities. T8 excludes
log-zero defaults and infinite-to-real KL defaults explicitly. The compact
envelope is nonempty and bounded. Zero-sample division defaults occur only
outside positive-sample assertions or at irrelevant initial terms. No
placeholder, conclusion-assuming hypothesis or junk-value defect was found.

`scratch/Nonvacuity.lean` compiles actual iid data for T6 and T7, genuine
conditional models and a complete simultaneous instance of T8's consistency
hypotheses, plus admissible mixture parameters and a nonempty T10 restriction.
For T6's full growing-degree instance, the remaining Legendre, rate and Gram
conditions are justified mathematically in `scratch/AuditNotes.md`, rather
than claimed as a compiled construction. That file also contains the detailed
clause comparisons and condition-by-condition refutation checks.

Validation used `/home/ubuntu/sap/tools/sap-lean` on `scratch/Inspect.lean`
and `scratch/Nonvacuity.lean`, both successful. The nonvacuity proofs import
only definitions. No `lake` command was run; at most two Lean processes ran
at once. `findings.json` was parsed and checked against all five closure
fingerprints and the required schema. The SAP sources were not modified.
