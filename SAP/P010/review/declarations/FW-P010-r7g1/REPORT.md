# P010 declaration review

All five declarations are **faithful, severity none**. Every statement dependency in `closure.json`, including all 22 distinct generated auxiliaries, was read. `reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved before opening `record.json`. The record required no change to a claim-stage conclusion.

| Declaration | Canonical coverage | Record decision | Result |
|---|---|---|---|
| SAP.P010.T1 | Exact unweighted preference-overlap counterexample | refuted | Correct |
| SAP.P010.T2 | Complete corrected comparison, including fractional trimming | whole | Correct |
| SAP.P010.T3 | Both specified continuous, same-observable counterexamples | refuted | Correct |
| SAP.P010.T4 | Complete corrected finite branch, attainment and integral forms | whole | Correct |
| SAP.P010.T5 | Specified full-support counterexample to infinite sharpness | refuted | Correct |

## Refutation checks

**T1 printed reading:** The unweighted lower-to-upper estimated-bound intervals overlap across all three treatments for both outcomes, either pairwise or at a common point.

Conditions checked: the three treatment labels, sample sizes, failure counts, passing binary-outcome counts, and strict empirical-CDF trimming rules all match the canonical inputs. These are the intervals between the lower and upper point estimates. Exact computation gives preference intervals [0,61/285], [87/281,27/47], [56/139,1]. The first is disjoint from each other interval, contradicting both specified overlap assertions. The definition computes the genuine binary tail means from counts; its natural subtraction clips the number of retained ones correctly. Every retained-count denominator is positive. The docstring accurately describes this refutation.

**T3 printed reading:** Under Assumptions 1–3, positive always-passer mass, continuous unbounded observed outcomes and existing means, a trimming ratio below one makes the displayed outcome-tail means, conditioned on assignment alone, sharp lower and upper bounds on the always-passer potential mean.

Conditions checked separately for both witnesses:

- SUTVA is built into observed outcome/check selection from the potential vectors.
- The mixture uses independent fair assignment in every stratum, hence satisfies both the printed per-arm ignorability and the witness's stronger joint assignment independence.
- Passing rates are 1/2 and 3/4; the always-passer mass is 1/4.
- Exponential/Laplace components give atomless observed outcomes, full real support and all finite absolute moments.
- The relevant trimming ratio is 1/2, and the passing-law median is the finite value zero.
- All conditioning events have positive mass and all means are integrable.

The printed tail means are -3/4 and 3/4. The two always-passer means are -1 and 1; the respective inequalities fail. The product/mixture definitions also give the required identical observable laws and corrected endpoints -1 and 1. This contradicts the printed assertion with its own conditions satisfied. The docstring is accurate.

**T5 printed reading:** Under Assumptions 1–3, positive always-passer mass, continuous unbounded observed outcomes and existing means, a trimming ratio at least one makes minus infinity and plus infinity the sharp extrema over compatible populations.

Conditions checked: the common-check, common-outcome beta/heavy-tail mixture realizes the specified independent latent-variable construction and fair independent assignment; passing rates and always-passer mass are 1/3. Its observed-response density is the stated mixture, continuous and strictly positive everywhere. The heavy-tail component ensures full real support. Its first, second and third absolute moments have the specified finite values; the tail formula is correct. Both trimming ratios are 2. Thus the printed else-branch applies.

Every compatible always-passer mean lies strictly between 0 and 1: always-passers are potential passers, and ignorability transfers the observed passing support (0,1) to each potential passing outcome. The four-stratum family preserves the observable law and has positive always-passer mass. Its lower means lie in (0,t), with reflected upper means; consequently the sharp infimum and supremum are 0 and 1. The theorem explicitly denies infinite sharp extrema. Its docstring correctly refers to sharpness; the universally valid infinite outer inequalities are insufficient for the printed sharpness assertion.

## Complete corrected statements

T2 states each formal clause (a)–(d): both outcomes' exact intervals, approval overlap, preference overlap of arms 1 and 2, separation from arm 0, positive difference endpoints, and the fractional-trimming formulas and gaps. Its universal integer-cutoff clauses use exactly the helper's strict inequalities. The counts are canonical supplied inputs. The docstring accurately summarizes the result.

T4 has precisely the canonical hypotheses: probability, per-arm ignorability, positive assignment/passing, positive always-passer mass, atomless selected passing distribution, integrable passing response and ratio below one. Its compatibility definition preserves the full (Y,S,Z) law and imposes the same assumptions. It states both bounds, attainment, bounds on every compatible mean, the L identity and equivalence, zero-trimming equality, and both quantile-integral forms. There is no hidden independence of the full potential vector. The docstring accurately describes the complete finite branch.

## Defaults and verification

No operative junk-value defect was found. T1/T2 use positive rational denominators and the correct natural clipping of binary counts. Probability and positive event masses protect conditional normalizations in T3–T5. Integrability in T4 transfers to always-passers and compatible means through ignorability and the observed passing law. In T4, extended-real quantiles correctly handle trimming zero; mapping infinite endpoint quantiles to zero affects only endpoints of Lebesgue integrals. T5's extended compatible set embeds ordinary finite means, so its greatest lower bound and least upper bound are genuine sharp extrema of a nonempty set.

Successful Lean checks, using only `sap-lean`:

- `scratch/ClosureAux.lean`: prints every generated declaration in the closures.
- `scratch/Statements.lean`: prints the elaborated statements and checks the relevant Mathlib conventions.
- `scratch/Check.lean`: independently computes both endpoint vectors, fractional endpoints, positive retained counts and valid count ranges; verifies an inhabited cutoff range in each arm; instantiates both T3 populations; constructs a T4 instance satisfying every hypothesis; and instantiates the T5 endpoint family at t=1/2 with means 11/32 and 21/32 and a nonempty compatible set.

The continuous-population certificates in the last check explicitly use the Comparator-certified T3/T5 statements. They are consistency and instantiation checks, accompanied here by direct inspection of the probability constructions, rather than independent reproving of those analytic theorems. T4 itself is not used to establish its hypothesis instance. No challenge or definition source was changed.
