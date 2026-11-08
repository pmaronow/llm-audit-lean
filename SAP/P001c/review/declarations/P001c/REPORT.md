# Independent P001c semantic review

All 19 targets are **faithful / none**, judged with their accurately disclosed scope. The claim-stage comparison found 16 whole statements and three narrower statements. The final record correctly labels 16 whole, two restricted (T40, T56), and one refuted with a disclosed restriction (T44). There are no requested fixes. No stage-2 conclusion changed after reading the record.

The blind reading covers all 19 actual target types, their docstrings, every closure entry, and all supplied Lean source files. `reading.md` was saved before opening the claims. Its SHA-256 at that boundary was `62b974126ea4e57eb539a59f0cb68a02dd62d744d22849db911886dffdb7dfc9`. `claim-stage.json` was then saved and parsed with 19 entries before either the record or binding was decoded; its boundary SHA-256 was `beb9b5f7a836874f15f948c695cb65a78a5853336bb8d7e83e6ee86ac70f1b59`. These two artifacts remain unchanged.

The three reductions are correct and disclosed:

- **T40:** Challenge/Part1.lean:24 and record P001-T40 omit the first-order calculation and certification of the drawn curve. Defs/Part4.lean:33 retains the general MSE identities, unique minimum, coin moments, all specified values and doubled-loss polynomial.
- **T44:** Challenge/Part1.lean:56 and Defs/Part4.lean:105 give a genuine counterexample to the canonical printed uniqueness assertion. For X=Y taking +/-1 equiprobably, g0(x)=x and g1(x)=x+1 both have covariance one with X, and losses zero and one. The zero-loss candidate is a BLP by nonnegativity. All printed hypotheses are met, including positive variance and finite moments. Challenge/Part1.lean:62 and the record explicitly retain only counterexample (a); this also makes clear that the other illustration and general theorems are not exported by this target. Thus “refuted” is justified, despite the narrower retained evidence.
- **T56:** Challenge/Part2.lean:70 and the record list the omitted CDF computations and quadratic-example properties. Defs/Part6.lean:13 retains differentiability, the constant example's exclusion of every positive-variance normal limit, the quadratic second-moment identity and its probability limit. A genuine IID Bernoulli product supplies the hypotheses even though the statement does not construct that realization.

T41 meets the full three-point pointwise-equality counterexample, including its null outcome and positive variances. T53 constructs genuinely independent heavy-tail observations and challenges only the finite-variance inference for their squares; it explicitly retains the true sample-variance theorem. The other whole statements include the theorems in `definitions_needed`, rather than reviewing only their headline formulas. In particular, T43 includes both variance branches and the CEF/residual conclusions; T47 separates the moment conditions of the independence clauses; T49 defines minimization without assuming residual identities; T55 includes the unbiased sample-mean variance estimator; and T57 constructs the empirical-process limit and covers the specified arbitrary tangent subspace, Gaussian derivative law and both variance cases.

| Theorem | Claim stage | Record decision | Final verdict / severity |
|---|---|---|---|
| SAP.P001c.T39 | whole | whole | faithful / none |
| SAP.P001c.T40 | narrower | restricted | faithful / none |
| SAP.P001c.T41 | whole | whole | faithful / none |
| SAP.P001c.T42 | whole | whole | faithful / none |
| SAP.P001c.T43 | whole | whole | faithful / none |
| SAP.P001c.T44 | narrower | refuted | faithful / none |
| SAP.P001c.T45 | whole | whole | faithful / none |
| SAP.P001c.T46 | whole | whole | faithful / none |
| SAP.P001c.T47 | whole | whole | faithful / none |
| SAP.P001c.T48 | whole | whole | faithful / none |
| SAP.P001c.T49 | whole | whole | faithful / none |
| SAP.P001c.T50 | whole | whole | faithful / none |
| SAP.P001c.T51 | whole | whole | faithful / none |
| SAP.P001c.T52 | whole | whole | faithful / none |
| SAP.P001c.T53 | whole | whole | faithful / none |
| SAP.P001c.T54 | whole | whole | faithful / none |
| SAP.P001c.T55 | whole | whole | faithful / none |
| SAP.P001c.T56 | narrower | restricted | faithful / none |
| SAP.P001c.T57 | whole | whole | faithful / none |

I reviewed finite/extended moment distinctions, conditional-mean versions, real division, square roots, natural-number indexing/casts, empirical n=0/1 conventions, CDF embeddings/default extensions, derivative defaults, and real infima/suprema. The stated hypotheses or explicit finite-size guards keep the relevant quantities in their intended domains. The n=0/1 defaults occur only outside the finite-sample assertions or in irrelevant initial terms of sequences. No definition was found to encode a conclusion, assume an orthogonality, or replace an intended object with a junk value.

No scratch Lean was compiled: this Mac has no `lean` on PATH and lacks the supplied Linux helper/dependency paths. The one authorized read-only SSH preflight failed with `ssh: connect to host 18.224.107.152 port 22: Operation not permitted`, before authentication, remote reads or remote writes. Consequently no resource preconditions for remote Lean were established and no remote Lean command was attempted. The exact scoped command for a parent with an approved runtime is:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 dbl-ws 'cd /home/ubuntu/sap/assure/independent-fw-20261105/P001c && pwd && df -BG . && cat /home/ubuntu/sap/tools/sap-lean && cat /home/ubuntu/sap/tools/lean_path.txt'
```

The permitted alternative was used: explicit mathematical constructions satisfy every hypothesis for every target; details are in each finding. These include both positive and zero variance regression cases, singular and intercept-only multivariate designs, actual infinite product IID laws, a valid root-n limit/variance-estimator pair, and a Bernoulli empirical process with a tight one-dimensional bridge and a nonzero evaluation derivative. `scratch/finite-audit.py` also ran successfully with exact fractions for the finite T40/T41/T44/T50 calculations, geometric-series parameters and moments for T53, and the binomial moment identity at every n=1,...,40 for T56. The analytic all-n fourth-moment calculation is given in the nonvacuity discussion; those 40 checks are corroboration, not a proof of an infinite family. Gaussian density/moment and general functional-analytic arguments were reviewed mathematically, not re-proved in Lean. Generated closure `_proof_*` source origins were read, but compiled auxiliary proof terms were not printed.

All 43 inventoried files passed the initial and final SHA-256 checks. Binding was used solely as identity metadata: its 12 source file hashes and all 19 declaration fingerprints agree with the packet and closure. No other path named in that metadata or in the record was followed. The supplied accepted-certificate status was not used as evidence of semantic fidelity. No old review, handoff, external integration narrative, web search, delegation, credential change, build, commit or publication was used.

Final validation parses both JSON outputs, requires exactly one entry per closure target, checks each exact theorem/target/fingerprint triple, checks all required fields and verdict/severity/issue constraints, and rechecks the frozen stage hashes and input inventory. The final output SHA-256 hashes (including this report) are returned with the review.

- `reading.md`: `62b974126ea4e57eb539a59f0cb68a02dd62d744d22849db911886dffdb7dfc9`
- `claim-stage.json`: `beb9b5f7a836874f15f948c695cb65a78a5853336bb8d7e83e6ee86ac70f1b59`
- `findings.json`: `2358abfb6c5b24d2d49b73d006ea2c795e78730d9d0ade8a1879234c3f3e4587`
