# P001f declaration review

All 18 reviewed declarations are **faithful / none**, relative to their recorded scopes. This is a statement-fidelity review; it performs no acceptance or registration and does not infer paper fidelity from the proofchecking certificate.

The blind reading in `reading.md` was saved before opening claims, record or binding. `claim-stage.json` was then saved before opening record or binding. No stage-2 conclusion was changed after reading the record. The record's narrower scopes for T102 and T98, and partial refutations for T103 and T104, agree with the independently saved claim comparisons. Input files were not edited.

| Target | Decision reviewed | Independent assessment |
|---|---|---|
| T100 | whole | Correct normalized ATT, propensity mean, weighted-effect identities and equality exception; integrable effect suffices. Both treatment probabilities are positive. |
| T101 | whole | Relative complement uses U, all exceptional-case equivalences and the numerical sets are correct. |
| T102 | restricted | Distributional uniqueness of globally differentiable CEF extensions can fail at a mean in a support gap, even with joint density and exact range/PDF-positive-set saturation. The fixed chosen extension and discrete slopes are expressly outside this result. The plug-in conjunct is honestly described as definitional. |
| T103 | refuted, scope A | A one-observation positive sample has unbounded likelihood along proper normal mixtures with positive scale tending to zero. This contradicts actual universal maximizer existence, with the omitted consistency/efficiency claims disclosed. |
| T104 | refuted, countable equivalence | Equal positive-mass arm supports do not imply a common epsilon bound. The example below directly violates printed B; the docstring accurately discloses that the formal proposition negates the equivalence and does not separately present all A–C or regional examples. |
| T106 | whole | All linearity, variance, standard-deviation and standardized Chebyshev clauses, with ordinary finite-moment domains. |
| T107 | whole | Iterated expectation, total variance, the complete prediction decomposition, nonnegative remainder and minimum risk. Finite prediction/residual risks do not get replaced by a global second-moment assumption on Y. |
| T108 | whole | Every finite positive-size iid family on its existing space; separate first- and second-moment conclusions and exact Chebyshev bound. |
| T109 | whole | Literal PMF/PDF positive-set interval support, genuine degree-wise population minimizers and eventual approximation for every minimizing family. There is a nondegenerate PDF instance. |
| T110 | whole | Every nonempty binary sample, unique maximum including the endpoints, and 2/3 example. Natural subtraction and 0^0 have their legitimate likelihood meanings. |
| T111 | whole | MCAR, vector/discrete MAR, positive-support sum, empirical formulas and worked values. Population regression integrability is concluded; it is not a hidden added premise. |
| T112 | whole | Balance, MAR preservation and positive conditional response score without a Y-moment assumption. |
| T113 | whole | Complete augmented score and both correctness alternatives; full-score expectation exists, without a separate nuisance-regression integrability premise. |
| T114 | whole | Interval, width, every-value observable-law sharpness, individual imputations and all worked means/endpoints. Same-space fixed-treatment witnesses suffice. |
| T96 | whole | Exact individual-realizable eighteen-unit sample, genuine unique logit ML fit, both estimates, scores, fitted/observed fractions and gap. |
| T97 | whole | Actual individuals, exactly observed cells, both arm formulas, saturation and the iff for **all** individual outcome vectors; 4/9 example. |
| T98 | restricted | All retained weight expectation assertions; omitted stabilized estimator, fitted-score convergence and efficiency, and the pointwise infinite-sequence conditions, are all disclosed. |
| T99 | whole | Genuine two-atom law satisfies CIA and both positivity bounds, and separates the unnormalized mean 1/4 from ATT 1 while restoring 1 by normalization. |

The claim includes its statement, definitions and standing assumptions. Audit notes and unused-row history were not treated as extra clauses, as authorization to drop a clause, or as independent evidence of fidelity. Definitions of random assignment or strong ignorability in a list of needed notions were not mistaken for blanket hypotheses on every causal theorem (which would contradict, for example, the bounds-without-ignorability and overlap-failure settings). Almost-sure versions and the usual existence/measurability conditions are read as stipulated in the brief.

## Adversarial checks and nonvacuity

Every declaration and all 153 closure entries (including repeated entries and generated elaboration helpers in their enclosing source expressions) were read. There is no SAP definition that simply encodes an asserted conclusion as a hypothesis. ConditionalMean expands to measurable/integrable conditional set-integral identities, conditional independence to bounded event-indicator conditional expectations, densities to actual `withDensity` laws, and the finite estimators to their individual sums. Detailed quantifier order and totalization audits are in `reading.md`; explicit per-target hypothesis witnesses are in `findings.json`.

For T102, take X uniform on [-2,-1] union [1,2], Y an independent uniform variable on [-1,1], and the sample space their product with exactly that X range. The marginal density is 1/2 on the closed two-interval set and the joint density 1/4 on its product with [-1,1]. The mean is zero. Both m0=0 and m1(x)=x(1-x²)² for |x|<1, zero elsewhere, are globally differentiable genuine CEF versions. Their derivatives at zero are 0 and 1. Both value and first derivative vanish at ±1. This satisfies exact support saturation, finite moments and ordinary differentiability; it is not an interior null-set artifact. It establishes only the expressly stated distribution-only reading, not that differentiation of a fixed chosen extension is false. The canonical text's audit note was not used to promote this reading into an additional printed assertion.

For T103, the printed reading of A is: every positive-size sample in the displayed valid mixture model admits a likelihood maximizer. Its conditions are ordinary nonnegative normalized weights, positive scales/rate, real locations, iid sampling, and well-defined observations/densities. With n=1 and y=1, theta=(1,0,1,s,0,1,1), s>0, meets all of them and has likelihood 1/(s sqrt(2 pi)). The likelihood is unbounded, whereas it is finite at every valid candidate. Independence is automatic for one observation; the argument is valid for any positive realized y with the corresponding Gaussian mean. No undefined density value or nonmeasurable witness is used.

For T104, the printed unhedged B says that failure of a uniform two-sided propensity bound forces unequal conditional-arm positive supports. Let s_k=2^(-(k+1)), p_k=1/(k+2), t_k=s_k p_k, c_k=s_k(1-p_k). These positive summable joint masses sum jointly to one, both arms have positive mass, both conditional PMF-positive supports are all natural-number covariate cells, and their propensity ratios tend to zero. There is no uniform epsilon. Thus all probability/support conditions hold and B is contradicted directly. Moreover uniform positivity implies equal supports on this domain by elementary nonnegative-mass algebra, so the formal negated equivalence cannot fail solely through A. No unspecified condition for hedged C is being invented or claimed refuted.

The T96 grouped data are realizable by actual units and by a positive-probability iid sample under a correctly specified logit CIA population. Its log-likelihood Hessian is negative definite everywhere, since its quadratic form is minus the positive-weight sum of (h0+z h1)² at z=-1,0,1. The stationary scores therefore certify an actual unique global maximum, not merely a formal score solution. For T97 the order is equality for every individual outcome vector iff cell saturation, not equality for one conveniently chosen outcome.

The PMF branch of T109 cannot put positive mass at every point of a nondegenerate real interval, as its literal printed support definition requires; this is a property of that domain, not a hidden replacement by topological support. The PDF branch is substantive: X uniform [-1,1], Y=X² plus independent bounded zero-mean noise, m=x²; degree zero/one minimizers are 1/3 and all degrees at least two fit m exactly. The singleton PMF case is also satisfiable. T107 admits integrable heavy-tailed Y with infinite second moment but finite CEF/predictor residual risks, as the detailed witness explains.

The finite exact-rational program `scratch/finite_checks.py` ran successfully. It independently constructs individual sample data and probability laws, checks finite conditional independence/means and verifies T96/97/99/100/101/106/107/108/110/111/112/113/114 computations. This is a finite arithmetic/fixture check, not a proof of the universal Lean propositions. Analytic and infinite-product witnesses for T102/103/104/109/98 are explicit mathematical arguments, not numerical simulations. No theorem's result was inferred from the success or failure of another theorem.

## Method limits and integrity

No additional Lean nonvacuity example was compiled successfully. The installed local Lean reports version 4.34.1, but an actual `import Mathlib` attempt using the supplied build path failed with `unknown module prefix 'Mathlib'` (exit 1). No Mathlib directory was found at the task package location or either checked standard sap-lean package location. No older-RC local AronowAudit source was used.

The one authorized remote clarification attempt was blocked at SSH connection by the execution sandbox: `Operation not permitted` (exit 255). No credential change, denial workaround or remote write was attempted. The exact scoped command for the parent, if a rerun in an authorized execution context is wanted, is:

```sh
ssh -o BatchMode=yes -o StrictHostKeyChecking=yes -o ConnectTimeout=10 dbl-ws 'cat /home/ubuntu/sap/tools/sap-lean; cat /home/ubuntu/sap/assure/independent-fw-20261105/P001f/declarations/lean_path.txt'
```

The brief permits a mathematical nonvacuity argument when compilation is infeasible; that is the method used here, with the additional finite calculations described above. The provided proofchecking certificate establishes proofchecking only. Fingerprint checks here compare each copied closure fingerprint with its binding entry, target and record; they do not recompute Lean elaboration or a proofchecking certificate.

Both inventories were verified before any claims were opened: 37 of 37 entries matched in each task. Final integrity verification repeats all input hashes, checks the JSON schema/count/target bijection and all 18 fingerprints against closure and binding, and checks that `reading.md` and `claim-stage.json` stayed unchanged after their respective stages. The final exact findings/report hashes are returned with the completed review.
