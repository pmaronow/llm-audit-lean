Both declarations are faithful, with severity `none`.

The blind reading of both declarations and every closure dependency was saved
in `reading.md` before either canonical claims or architect decisions were
opened. The comparison with `claims.json` was then saved in
`claim-stage.json` before opening `record.json`. Both recorded decisions are
`whole`; neither required changing the independent claim-stage conclusion.

For **SAP.P009c.T50**, `Defs/Part4.lean:38–46` includes both alternatives of
Proposition 10 and the separate finite spectral bounds. The Rayleigh
supremum represents the largest eigenvalue and spectral radius because the
structural dependence matrix is symmetric and entrywise nonnegative.
`Conservative` (`Defs/Part2.lean:109–116`) matches the printed iterated limit,
including existence of each positive-threshold inner limit. Uniform moments,
interior marginals, the two rate alternatives, and the mean squared expected
effect all have the required meanings. The docstring at
`Challenge/Part1.lean:104–106` accurately describes the statement.

For **SAP.P009c.T51**, `Defs/Part4.lean:48–65` preserves the designs and
population sizes, chooses one outcome family satisfying all conclusions,
includes every admissible alpha and exponent, and includes the stronger
maximum-degree bound when the exponent is zero. Its weak-convergence
statement matches the proposition's printed restatement. The finite
three-point equality is exactly Lemma A30. No convergence of tail
probabilities at an atom is asserted or needed for this canonical claim.
The docstring at `Challenge/Part1.lean:109–111` correctly distinguishes
convergence to the law from the law's finite Chebyshev equality.

All relevant expectations are finite sums over genuine normalized probability
laws. Positive population sizes and the mandatory interference diagonal keep
the scaling denominators positive. Both treatment marginals are positive;
square-root and real-power arguments have their intended domains. Degree and
Rayleigh suprema are over nonempty bounded sets. No default value trivializes
either theorem.

`scratch/Nonvacuity.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`, importing only the
definitions. It constructs a growing fair Bernoulli study with outcomes
`y_i(z)=2z_i-1`, proves uniform regularity with `(k,q,s)=(2,4,1)`, and
proves both T50 alternatives simultaneously: `dAvg=lambdaMax=1` and
`msq=4`. It also checks every T51 input premise at `alpha=1/2,x=0`, the
nondegenerate finite sharp law and its equalities, and the identity between
its mass-defined CDF and `sharpCDF` at every real threshold for every
admissible alpha. These checks use no Challenge stubs.

The existential outcomes in T51 have a further explicit mathematical
nonvacuity check. Take `h=t+2`, `n=h²`, fair assignments, and
`f(z)=1_{z0=true}(2*1_{z1=true}-1)`. Put `a=2-1/h` and, for the first h
units, set `y_i(z)=(sqrt(a)/2)(2*1_{zi=true}-1)f(z)`; set the other outcomes
to zero. Every active outcome depends on coordinate 0, while no active
outcome depends on an inactive coordinate. Thus the dependence matrix is
an h-clique and isolated diagonal entries, yielding `dAvg=a` and `dMax=h`.
The outcomes have absolute value below 1, and the normalized centered HT
variable equals f exactly, with masses `(1/4,1/2,1/4)`. This verifies a
genuine outcome witness for the strongest bounded-average case; it is a
mathematical check, not a Lean re-proof of the existential conclusion.
