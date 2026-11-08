# Delta statement review

Reviewed all 14 current targets against `reading.md`, `claims.json`,
`record2.json`, and `architect-report.md`.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 5 |
| `correct_restricted` | 6 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 3 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: **11 none, 2 minor, 1 major**. The sole earlier adverse finding is
**fixed**; none is partly fixed or unfixed. There are three new concerns about
the changed refutation labels/openings. No Lean proposition was found false or
vacuous.

The output uses the original findings vocabulary, as requested. Successful
full and limited refutations receive `correct_whole` and `correct_restricted`
according to their coverage of the canonical target; `refuted` is the separate
architect decision being reviewed.

## Earlier finding: T6 — fixed

The previous first conjunct required separation before giving the OLS/sandwich
representation. The revision restores its general scope. In
[Defs/Part6.lean:94](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part6.lean:94),
the hypotheses before that representation are now only c≥0 and both arm counts
at least one, with an arbitrary real array D. Zero diagonal and off-diagonal
separation first appear in the nested
[HC0 specialization](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part6.lean:102).
The revised docstring and record accurately describe this scope. The remaining
geometric restrictions and numerical omissions are unchanged and disclosed.

The new mathematical reading of this conjunct is: for every N, assignment z,
data M, array D and nonnegative cutoff c, with both arm counts at least one,
the weighted-contrast, OLS weight/residual and sandwich-to-score-HAC identities
hold. For every additional zero-diagonal and separation premise, the three HC0
identities follow. The other conjuncts retain their previous reading.

An independent Lean check uses z=0011, M=(0,2,4,6), D_ij=|2i−2j| and c=12/5.
Both arms have size two, the Gram matrix is invertible, separation fails, and
both the sandwich entry and score HAC equal 1/2. Thus the newly covered regime
is meaningful and actually includes off-diagonal pairs.

## New finding: T5 — not_faithful, minor

The new [opening](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Challenge/Part1.lean:52)
says “The printed claim is false.” The theorem is a correct counterexample to
the **outcome-effect-range reading**, which must be identified explicitly.

In the example, an intervention affects outcomes only within radius one, but
the node contributions at distance two have covariance 1/4. A cutoff of one
therefore misses covariance. This does not contradict the literal printed
instruction to choose a cutoff covering dependence: the chosen cutoff fails
that instruction's dependence requirement. The canonical T5 note expressly
distinguishes the natural reading of the illustration from the printed
instruction. The new unqualified opening loses that distinction.

Fix the opening and record to say exactly which reading is refuted: covering
the outcome-effect range need not cover dependence of node-level linearization
contributions. Preserve the literal printed guidance about contribution
dependence. The finite theorem needs no mathematical repair.

## New finding: T7 — not_faithful, major

The previous `restricted` counting result has been relabelled `refuted`, with
the new [printed-claim-false opening](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Challenge/Part1.lean:74).
Its domain has not changed.

The arrays [riskM](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part4.lean:60)
and [companionRiskM](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part4.lean:66)
are means on labelled 40000-cell samples. `T7Statement` contains no Euclidean
spatial model or identification of these arrays with that model's circle
averages and spatial AMRs. The restriction paragraph explicitly omits that
realization and circle identification.

The finite conclusions are true: the normalized difference is −321/40000,
the unweighted sum is −321/10000, and the companion sum −4 cannot be a
probability difference. But to refute the printed assertion about **spatial**
AMRs, a counterexample must also belong to the paper's spatial domain. The
missing realization cannot be supplied merely by changing the decision label.
It was acceptable to state these arithmetic facts as an expressly limited
counting result in round 1; the new refutation claim requires more.

The smallest repair is to restore `restricted` and remove the new false-claim
opening, retaining the accurate existing limitations. To retain `refuted`,
establish the spatial realization and circle-average correspondence, or supply
another admissible binary spatial witness whose four-radius AMR sum is −4.
That witness must have meaningful circle averages and an actual design and
observation with both treatment arms present.

## New finding: T9 — not_faithful, minor

The new [opening](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Challenge/Part1.lean:100)
declares the printed claim false while citing article p.145 and the toy table.
The theorem's correct refutation concerns the **later archived-code rule**
`cutoff + position` and its claimed agreement with the user's physical cutoff.

The same spatial contrast receiving variances 1 and 1/2 refutes that code
correctness reading. The sixth-row zero variance also proves that the archived
rule cannot reproduce the printed positive width. Neither result proves that
the article's general cutoff instruction or a printed interval is false: the
original release can use a different rule. The canonical T9 note explicitly
states that the article's sentence is correct as printed and that the original
release is unavailable.

Scope the opening and record to the transcribed archived-code assertion and
the incompatibility with the printed table. The spatial theorem and its
disclosed omissions remain sound.

## Coverage of changed and unchanged targets

Comparison with the saved mathematical reading found one changed proposition,
T6. Six other targets have changed decisions/openings, with their propositions
unchanged. The remaining seven targets retain both their mathematical reading
and their decisions.

| Target | Delta | Assessment |
| --- | --- | --- |
| T1 | `restricted` → `refuted`; new opening | Accepted for the canonical reading that count and observation determine the reference law. Fixed labelling is disclosed; no actual Uganda p-value is established. |
| T2 | None | Retained restrictions remain accurate. |
| T3 | `whole` → `refuted`; new opening | Valid spatial sharp-null counterexample: rejection probability 1/3 at nominal 1/20 for the specified interpolated-percentile rule. |
| T4 | None | Retained restrictions remain accurate. |
| T5 | `whole` → `refuted`; new opening | Correct natural-reading counterexample; new opening needs the qualification above. |
| T6 | Broader representation; revised disclosure | Earlier issue fixed; correctly restricted. |
| T7 | `restricted` → `refuted`; new opening | Counting facts still lack the spatial witness needed for the new refutation claim. |
| T8 | None | Retained restrictions remain accurate. |
| T9 | `restricted` → `refuted`; new opening | Correct archived-code counterexample; new opening overstates its article-level attribution. |
| T10 | None | Retained restrictions remain accurate. |
| T11 | None; `whole` retained | Matches all exact printed-number and rounding clauses (a)–(c) in the canonical formal content. The supporting empirical reconstruction is distinguished in the canonical note. |
| T12 | `whole` → `refuted`; new opening | Valid refutation of the printed-grid/output combination: the prescribed range selects no distance and every sum/percentile is zero. |
| T13 | None; `whole` retained | All corrected-grid clauses remain present. |
| T14 | None; `whole` retained | Corrected mean identity, printed-product characterization and numerical witness remain present. |

## Junk values, nonvacuity and validation

No definition beneath the statements has a changed mathematical interpretation.
The positive finite masses and relevant integrability assumptions, nonempty
arms, normalized finite laws, positive conditioning probabilities and nonempty
quantile samples retain their earlier checks. The risk thresholds are 400 or
1000 before treatment and 79 or 679 afterward, so natural subtraction never
truncates. T12's empty selected set is the demonstrated grid defect.

For T6, both positive arm counts make X'X nonsingular; dropping separation from
the representation does not introduce a singular-inverse convention. The
geometric integrand still vanishes on each excluded circle by the triangle
inequality. The new concerns in T5, T7 and T9 concern what their results refute,
not zero denominators or inconsistent premises.

Checks completed against the revised imports:

* `sap-lean scratch/DeltaCheck.lean` — passed. It independently checks the
  four-node arm counts, Gram matrix and inverse, nonzero residual and score
  vectors, failure of separation, and sandwich/HAC values 1/2. A separate
  structural projection checks the revised representation needs no separation
  premise; that projection is not used as the independent nonvacuity proof.
* `sap-lean scratch/Check.lean` — passed again, including the positive-radius
  spatial, conditional-design, integrability and IID witnesses.
* `python3 scratch/check_finite.py` — passed again; output is retained in
  `scratch/finite-check2.json`.
* `findings2.json` parses and covers exactly the 14 canonical targets with the
  required fields, theorem names and allowed verdicts. Counts match this report.

At most two Lean processes ran concurrently. No `lake` command was run, and no
Solution, Bridge, other referee's files, or external project proof sources
were inspected. The architect's descriptions of proof dependencies do not
replace the statement checks above.
