The five declarations are faithful to their recorded scope: T22–T24 are whole, T25 is a genuine refutation of a canonical conjunct, and T26 is accurately restricted. No current defect remains from the supplied earlier issues.

I saved `reading.md` before opening the canonical claims or review history, saved `claim-stage.json` before opening the record, and read every closure declaration, including all 33 distinct generated auxiliaries. Those auxiliaries supply only numeral/index instances. The record caused no change to the mathematical readings saved at step 2. There, “different” for T25 and T26 records a negated assertion versus the canonical positive assertion; their respective refutation and restricted labels are assessed below.

| Declaration | Canonical content and scope check |
|---|---|
| T22 | Every fair-sign moment, probability, ratio atom, bias, consistency assertion, and absolute-error identity/bound/limit is present. Indexing by n+1 covers every positive sample size. The witness is explicitly distinguished from the chapter's estimators. |
| T23 | All six table comparisons and (b1)–(b4) are present. The general implication assumes nonnegative estimated variance, positive true variance, vanishing true variance, and the stated mean-SE limit. Finite spaces agree with the standing finite-design setting. |
| T24 | Nested means weight groups equally. All five effects, both regime mixture means, guarded direct-effect ordering/ratio, and the arbitrary-schedule decomposition are present. Arbitrary real baselines generalize the printed algebra without losing its intended cases. |
| T25 | The current negation targets the within-group Bernoulli assertion itself. It cannot succeed merely by choosing an unsuitable first-stage law. |
| T26 | The theorem negates a universal conjunction for the explicit singleton-drop statistic; it does not assert which conjunct fails. The restricted label and docstring disclose both the changed domain/statistic and the omitted defined-domain guarantee and numerical-identification clause. |

For T25, the printed reading is: under partial interference and independent Bernoulli assignment within a group, its observed arm mean, conditional on that arm being nonempty, is unbiased for the average of the individual marginal potential outcomes in that arm.

The independently compiled witness has two units, p=1/2, arm=true, and each fixed outcome is 1 precisely when both units are treated, otherwise 0. Its conditions check as follows:

- Finite population and fixed real potential outcomes: two units and four assignment vectors; all functions and moments are defined.
- Partial interference: the schedule uses only this group's assignment; it can be placed in an otherwise independent two-stage experiment with a uniform first stage.
- Independent second-stage draws: `bernoulli (1/2)` assigns each of the four vectors mass 1/4.
- Correct marginal outcomes: conditional on either unit's own treatment, the other treatment remains fair, giving marginal outcome 1/2.
- Correct nonempty-arm conditioning: this event has probability 3/4; its arm mean has conditional expectation 1/3.

Thus T25 contradicts the actual within-group conjunct, which suffices to refute the printed conjunction. All three earlier T25 issues are fixed by `Defs/Part5.lean:11–15` and `Challenge/Part2.lean:6–9`.

For T26, the printed guarantee concerns the cited variance estimator where every required arm sample variance exists. A singleton arm violates that condition. The current theorem therefore receives acceptance only under its explicitly restricted software reading. The earlier domain objection is fixed by the changed classification and disclosure in `Challenge/Part2.lean:11–14` and `record.json`; the mathematical counterexample does not refute the defined-domain guarantee.

Scratch files import only `SAP.P045b.Defs`, without relying on Challenge stubs. `scratch/Nonvacuity.lean` checks T22's positive one-unit experiment, constructs T24 data with positive unequal group sizes and positive baseline, and independently proves T25's negation. `scratch/SeqInstance.lean` constructs all hypotheses of T23's general implication simultaneously using a fair two-point law, T_n=sign/(n+1), and Vhat_n=1/(n+1)^2; it also checks the nonvanishing witness and inequality domains. `scratch/T26Instance.lean` proves the restricted negation using G=C=2, two units per group, one treated, and a=b=(0,1), with E(Vhat)=0 and Var(T)=1/2. Separately, `scratch/exact_checks.py` enumerates all 14,580 equally likely outcomes of the six-by-three toy design with a=b=(0,1,2), obtaining total mass 1, E(Vhat)=1/3 and Var(T)=1/2.

The only consequential totalization is the explicitly disclosed singleton-drop rule in T26. Other divisions and square roots have appropriate domains on every positive-mass event. Empty-arm values in T25 are excluded by conditioning. None of the five statements is vacuous or encodes its conclusion in a substitute definition.

The matching table entries and assignment discussion were also checked against the [paper's public preprint](https://arxiv.org/pdf/2001.05444); the supplied canonical claims govern the published pagination and audited scope.
