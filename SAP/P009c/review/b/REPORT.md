# Palomar statement audit: P009c

| Verdict | Count |
| --- | ---: |
| correct_whole | 12 |
| correct_restricted | 4 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| **Total targets** | **17** |

Severity counts: none 17; minor 0; major 0. There are no adverse findings.

The blind mathematical reading was saved in `reading.md` before opening
`claims.json`. The 16 per-theorem comparisons were saved in `claim-stage.json`
before opening `record.json`. No step-2 reading or verdict was changed after
reading the record. `findings.json` covers all 17 canonical targets, including
the omitted target.

## Record and disclosure checks

The 12 decisions marked whole agree with the blind reading and canonical
claims. Each of the four restricted theorem docstrings states its full
restriction accurately:

| Target | Restriction actually implemented and disclosed |
| --- | --- |
| T41 | Retains HT consistency and its full EATE rate; drops both Hájek conclusions. |
| T43 | Retains HT conclusions for both design regimes and Hájek conclusions for complete randomization; drops Bernoulli Hájek conclusions. |
| T45 | Requires attained global maximal observed and potential moment exponents, allowing moment-bound constants to vary with the exponent; retains the complete three-term HT rate and makes both Hájek conclusions conditional on nonempty arms on every supported assignment. |
| T46 | Uses the observed maximum at the common fixed k and any admissible potential exponent; retains the complete two-term HT rate and makes both Hájek conclusions conditional on nonempty supported arms. |

T40's omission is justified on the supplied evidence. The record identifies
its only row as `wrong_credit` and expressly excludes component extraction.
The mathematical reason for treating its Hájek completion as material can be
checked directly: let the design put mass 1/2 each on the all-control and
all-treated assignments, and set
Y_i(z)=(1/2)z_0(2z_i-1). This has interior marginals, uniformly bounded
outcomes, dAvg=n, EATE=1/2, and HT=Z_0. On every supported assignment one
Hájek denominator is zero. Completing the estimator by zero gives a constant
error -1/2; completing it by 1/2 gives zero error. Thus a completed Hájek
statement cannot silently stand for the printed arbitrary-design claim.
The stated credit status itself cannot be independently verified from the
permitted Defs/Challenge files; the omission assessment uses the record's
reported status and the independently checkable domain problem.

## Definition and truth checks

Full-cube potential outcomes, structural interference (including its
mandatory diagonal), common-source dependence, and all design formulas
match the canonical definitions. Setting the own coordinate to zero in
`maskedOthers` generates the same information as deleting that coordinate.
On a finite space, the event-set definition of alpha generates exactly the
required sigma-algebra events. The explicit mixing convention gives 0^0=0.
The transport definition is the paper's first-order cost with an L_r ground
distance.

Every relevant population size is positive. Dependence degrees, average
dependence, and RMS dependence are at least one. Count maxima are over
nonempty finite sets; the Rayleigh set is nonempty and bounded; alpha's set
is nonempty and bounded; and product couplings give a nonempty transport
cost set bounded below by zero. No invalid supremum, infimum, power,
truncated subtraction, or zero denominator supplies a conclusion.
Conditional means and pairwise conditional covariances are used only with
positive conditioning probabilities. Every Hájek conclusion has nonempty
arms on the design support, through complete or paired design or the
explicit supported-arm condition. All stated stochastic rates are positive.
No hypothesis assumes its estimator conclusion.

In particular, T47 needs no extra restricted-interference assumption: its
centered scaled error is exactly (n VBER-a_n)/dAvg, and the finite variance
bound is at most 4 k^8/(n dAvg), which tends to zero. T48--T50 use the actual
iterated-limit definition of conservativeness, including existence of each
inner limit. Their hypotheses yield vanishing lower-tail probabilities at
each fixed positive threshold, so that requirement introduces no defect.
T51 asserts weak convergence to the three-point law and its separate finite
Chebyshev equality; it makes no unsupported assertion about convergence of
finite-sample tail probabilities at discontinuities.

## Nonvacuity and verification

Every target has an explicit instance or domain explanation in its
`findings.json` entry. Useful common nonzero examples have sizes
n_t=2(t+1) and outcomes Y_i(z)=z_i. Independent fair treatment, uniformly
balanced complete randomization, and independent one-treated-per-pair
randomization realize the three design regimes. Their structural dependence
is the identity. The paired example has eAvg=1 and rSum=0. The balanced
complete example has alphaExt(1)=1/4 and alphaInt(1)=0, bounded outcomes
give attained moment maxima at infinity, and both arms exist everywhere
on its support. Hence even the stronger T45 premises are jointly satisfiable.

The following checks passed, using only the authorized scratch compiler
and at most two concurrent Lean processes:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`: finite probability
  laws, interior marginals, Bernoulli regularity, no interference, bounded
  effects, positive-mass empty Bernoulli arms, complete and paired designs,
  supported nonempty arms, and the three-point Chebyshev equalities.
* `/home/ubuntu/sap/tools/sap-lean scratch/Sequence.lean`: a growing positive
  population sequence, a genuine uniform Bernoulli law for every size,
  common regularity, restricted interference, identity dependence,
  dAvg=dMax=lambdaMax=1, zero variance heterogeneity, and attained infinite
  moment maxima. This file has only a stylistic instance-declaration warning.
* `python3 scratch/finite_checks.py`: all 4,165 diagonal-one binary
  interference graphs of sizes one through four satisfy the full T36 chain.
  Another 120 exact rational experiments satisfy the Bernoulli estimand
  identity, T47 expectation decomposition, total-variation bound, and r=1
  Lipschitz bound.

The finite checks corroborate the readings; they do not replace proofs of
the universal or asymptotic statements. Both output JSON files were parsed
and checked with Python, including target coverage and verdict counts.
