# Declaration review

All five declarations are **faithful**, with severity **none**, relative to their
declared scope. The blind reading was saved in `reading.md` before opening the
canonical claims. `claim-stage.json` was saved before opening `record.json`.
No claim-stage conclusion changed after reading the record.

| Declaration | Record decision | Assessment |
| --- | --- | --- |
| `SAP.P008b.T20` | restricted | Covers the eight-neighbour boundary definition, the 25/16/9 cell counts, the continuous frontier characterization, and the explicit contrast/AMR witness. The omitted smoothing sentence is disclosed. Nonempty continuous frontier is already canonical; nonempty raster boundary ensures the means exist. |
| `SAP.P008b.T21` | restricted | Exactly the printed inequality −0.0321 < −0.0304. The docstring expressly omits the law, quantiles, inference and empirical conclusions. |
| `SAP.P008b.T22` | refuted | A genuine spatial sharp-null counterexample refutes the canonical calibration assertion under the specified type-7 convention. The nominal decision for the printed numbers is separately retained. |
| `SAP.P008b.T23` | restricted | Exactly the covariance identity, with its substantive zero-covariance premise explicit. The table, dependence-accounting interpretation and empirical comparisons are expressly omitted. |
| `SAP.P008b.T25` | whole | Both circle-average identities, their AMR consequence, and both uniform four-node computing formulas are present. Circle existence conditions agree with the canonical claim. |

For T22, the printed reading being refuted is: **under the sharp null and the
correct finite assignment law, exhaustive enumeration makes the strict two-sided
percentile test calibrated at its stated error rate, using the specified quantile
convention.** The paper describes the percentile rule and the six-assignment
setting; the type-7 convention is fixed by the supplied canonical assumptions
S9(i). [Paper, sections 2.3, 3 and 5](https://arxiv.org/pdf/2106.15081).

The witness passes each applicable condition:

- Four binary intervention nodes and real potential outcomes on all assignments:
  nodes at (10i,0), with outcomes independent of treatment, on the plane.
- Usual measure conditions and existing circles: twenty atoms at
  (10i+(j+1)/10,0), total measure 20; each required circle has exactly one atom,
  mass one and an integrable outcome. The outcome function is a bounded Borel
  step function.
- Sharp null: every potential outcome is assignment-invariant.
- Correct general design and exhaustive enumeration: all six two-treated
  assignments, uniformly distributed, with two nodes in each Hajek arm. S2 allows
  this restricted design. This tests the general assertion (i); it does not claim
  to reconstruct the printed toy outcomes. Separately, the six-state probability
  bound addresses the six-permutation calibration asserted in (ii).
- Specified statistic and rule: the actual spatial Hajek values are
  (−2,−1,0,0,1,2). Type-7 cutoffs at 1/40 and 39/40 are ±15/8, so strict
  rejection occurs on two of six assignments, with probability 1/3 > 1/20.
  The sum over the five radii multiplies the values and cutoffs by five.
- Replicate conditions: this is full enumeration, not a collection of Monte Carlo
  replicate draws. No independence condition is evaded by repeating one draw.

The general probability bound also shows that any nonempty deterministic
rejection set on six equally likely assignments has probability at least 1/6.
The numerical decision 12.38 > 7.97 is true; its nominal 0.05 calibration is what
fails. Thus the refutation concerns the canonical assertion itself.

All closure declarations were read, including the generated auxiliaries printed
in `scratch/PrintClosure.out`. The finite-law definitions are normalized finite
probability sums. Own-treatment replacement correctly marginalizes over the
unconditional law of the other assignments, as S3 requires. The spatial
definitions use actual metric circles, measure restriction and normalized Bochner
integrals. None encodes a conclusion or substitutes a placeholder.

Division by zero, infinite-mass `toReal`, nonintegrable-integral defaults,
empty-frontier distance and out-of-range quantile indexing do not drive any
assertion. Zero-weight integrability exceptions in T25 are immaterial zero terms.
The arbitrary real distance array in T23 strengthens the algebraic identity
without adding a hypothesis to the spatial case.

Independent checks were compiled using the permitted `sap-lean` command, without
importing Challenge in the nonvacuity files: `scratch/Nonvacuity.lean` checks all
five targets' premises or retained numerical content; `scratch/SpatialEvidence.lean`
checks T22's spatial realization, including all twenty circle restrictions.
The T23 checks include positive variance and actual pairs beyond the cutoff;
the T25 instance has a treatment effect of one. Full evidence is recorded per
declaration in `findings.json`.
