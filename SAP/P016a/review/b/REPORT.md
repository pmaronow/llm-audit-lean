# Palomar statement audit: P016a

| Verdict | Targets |
|---|---:|
| correct_whole | 8 |
| correct_restricted | 2 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| **Total** | **11** |

Severity counts: none 11, minor 0, major 0. There are no items outside
`correct_*` and `omission_ok` requiring a correction.

## Sequence and scope

`reading.md` was saved after inspecting the definitions and all ten theorem
stubs, before opening `claims.json` or `record.json`. It expands the SAP
definitions, quantifiers, hypotheses and conclusions. `claim-stage.json` was
then saved and parsed before opening `record.json`. No step-2 verdict was
changed at the record stage. Claim comparisons use the canonical statements
and transcribed paper passages in `claims.json`.

| Target | Record decision | Audit |
|---|---|---|
| P016-T1 | whole | correct_whole |
| P016-T2 | whole | correct_whole |
| P016-T3 | whole | correct_whole |
| P016-T4 | restricted | correct_restricted |
| P016-T5 | omitted | omission_ok |
| P016-T6 | restricted | correct_restricted |
| P016-T7 | whole | correct_whole |
| P016-T8 | whole | correct_whole |
| P016-T9 | whole | correct_whole |
| P016-T10 | whole | correct_whole |
| P016-T11 | whole | correct_whole |

## Restrictions and omission

T4 states the algebraic model consistency, standardization, regression
invariance, similarity/distance orientation and finite discrepancy witnesses.
Its docstring and record accurately disclose the omitted identification with
the complete application and simulation procedures, including the saved bank
size, reference-draw count, directional application tails, projected bounds
and figure/coefficient/rectangle association. In particular the theorem is
not a certification of those computations.

The extra fixed-treated-count condition is imposed on the entire orientation
conjunct, including its raw-sum identity, and the docstring says so. The raw
identity mathematically needs only the current assignment's count; this
unnecessary bank condition is a disclosed narrowing. The two positive-SD
premises for the standardized sign identity are also disclosed. The second
is redundant because hS=-hD/2 implies sS=sD/2, but it is satisfiable and does
not create an undisclosed restriction.

T6 proves the finite-design cancellation consequence explicitly permitted by
the canonical target's note and the defining equivalence for the strict
cutoff. The record and docstring accurately limit unit variance to across-unit
sample variance with divisor n-1 on every design index, and exclude the full
regression/testing procedure and empirical rejection proportions. The
quantified g is any vector-valued function meeting that variance condition;
the theorem does not identify a unique centering/scaling formula. This
general cancellation result includes ordinary standardized raw distance
exposures on nondegenerate designs. It makes no claim that these are the
coded application exposures. The generating-model antecedent in T4 and T6
is appropriate for the canonical consistency assertion; neither theorem
deduces a statistical performance conclusion from an assumption of that
conclusion.

T5 is a defensible conservative omission. The printed prose supplies no
definition of joint information or cross-group correlation. Its precise
beyond-margins reading is addressed by T2's general margin invariance and
the retained T1 examples. A fact about invariance at fixed group margins
alone need not settle a broader comparison of reference distributions. The
record therefore withholds extra credit for that prose comparison. The
source row's `wrong_credit` label cannot itself be checked from the permitted
files; my acceptance of the omission rests on the ambiguous printed content
and the sound, explicitly stated content retained in T1/T2. It does not
claim that the canonical precise reading lacks a formalizable refutation.

## Mathematical checks

For simple regression the objective decomposes as

Q(u,(1,z);(a,b)) = R(u,z)
  + n0*(a-m0)^2 + n1*(a+b-m1)^2.

Positive group sizes give exactly the claimed coefficients and minimum.
The total/within/between decomposition then yields
R=TSS-(n0*n1/n)*Delta^2; its coefficient is strictly positive, so fixed-count
SSR order is exactly reverse order of absolute mean differences. The
weighted group-mean and ECDF identities give their covariance identities
under arbitrary finite probability weights. Equality of group multisets
preserves all group means, second moments and ECDFs.

The general least-squares objective is nonnegative and its range is
nonempty for every matrix, even with zero columns. A finite-dimensional
column space is closed, so orthogonal projection gives attainment and the
unique fitted vector; coefficients need not be unique. Consequently the
real `sInf` in `lsRSS` has the intended infimum meaning.

With positive group sizes, ECDF differences lie in [-1,1]. Between successive
distinct observed outcomes they are constant, and below all observations
they are zero. At a largest observation both ECDFs equal one. Thus the
finite maximum equals the threshold supremum, including ties; the zero
seed also leaves the signed maximum unchanged in these nonempty examples.
The `sSup` range is nonempty and bounded. No default for an unbounded or
empty set affects either extremum.

For positive sample SD, standardization is an invertible affine change of
an exposure column. With an intercept it preserves the regression column
space, and its coordinate sum and sample variance are zero and one. For
defined scores, S=J-I-D/2, giving Sz=m-z-Dz/2. Under the stated common bank
counts, conditional bank centering cancels m-z and gives hS=-hD/2.

For T8, true-parameter adjustment fixes the entire baseline outcome vector.
The observed and reference statistics therefore use the same fixed score
function under the same probability law. For any finite score function,
the event that its inclusive upper-tail probability is at most alpha is
either empty or an upper score set whose mass is at most alpha. This
establishes calibration with arbitrary weights, ties and zero-weight atoms;
no effect-increasing premise is needed.

The signed-KS, pooled-mean, omitted-intercept and directional-monotonicity
witnesses refute their precisely stated literal readings. They do not claim
failure of the intended randomization method, an error in reported figure
values, or a general bias theorem. The recorded-table determinant is exact
arithmetic on the canonical rational entries; the theorem is not an
independent certificate of external data-file provenance.

## Nonvacuity and reproducible evidence

`scratch/Nonvacuity.lean` compiles with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` (exit 0).
It checks positive group sizes, fixed counts and bank coverage, a nonempty
T4 support with positive exposure variance and nonzero effect coefficients,
an inhabitant of Balanced(8,4), and the general nonempty/bounded-below
least-squares range. Its T6 instance uses the line-distance matrix
[[0,1,2],[1,0,1],[2,1,0]], two distinct assignments, centered raw exposures
(-1,0,1) and (1,0,-1), and nonzero direct and indirect effects. Thus the
model premises are jointly satisfiable on a genuine nonempty design.

For every finite law, nonnegative weights sum to one; an empty underlying
type is impossible. In the bank statements, coverage forces every
conditional denominator to be positive. All standardizations used in the
fixed witnesses have positive variance, and all KS/SSR group denominators
in those witnesses have positive group sizes. The sample-variance divisor
n-1 is real subtraction, positive under n>=2. The unrestricted n=0 cases
of additive adjustment are algebraic vector identities, not artificial
statistical examples.

`python3 scratch/exact_checks.py` passes 2,338 exact-rational checks,
including 114 generic two-group instances, both four-unit design tables,
the covariance and tail values, exposure-bank arithmetic, both determinants,
and all stated regression minima. It enumerates all 70 balanced eight-unit
assignments: the corrected signed and absolute KS rejection probabilities
are respectively 1/70 and 1/35, while both literal raw-versus-adjusted
comparisons reject with probability one. Results are saved in
`scratch/exact-checks.json`. These finite checks supplement the mathematical
audit of universal clauses; they are not a proof of those universal clauses.

`claim-stage.json` and `findings.json` were parsed with Python, and target
coverage and theorem-name consistency were checked against the input files.
