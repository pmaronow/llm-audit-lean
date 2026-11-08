All three declarations are faithful to their canonical claims. Their `whole`
decisions are correct; no restriction, label, definition or docstring needs repair.

The blind reading was saved in `reading.md` before opening `claims.json` or
`record.json`. All 86 distinct closure declarations were reviewed, including
the 24 generated numeral-proof auxiliaries, whose bodies were printed in
`scratch/BlindInspect.lean`. `claim-stage.json` records three `whole`
comparisons. Reading the record did not change any conclusion.

For **SAP.P029a.T11**, the reading challenged is that every binary
constant-effect SEM law with a linear first stage, zero instrument/error
correlation and nonzero instrument/receipt covariance satisfies all five IV
assumptions. The SEM conditions require finite second moments and positive
variances for the correlation. Both witnesses meet every antecedent:
their outcomes and first stages have the required equations, their residual
arm means vanish, and their correlation variance products are respectively
(3/16)² and 5/8. Relevance covariances are 3/32 and 1/8. Witness A has
independent assignment but defier probability 1/4; witness B has no defiers
but assignment depends on the magnitude of Y₀. The extra arm means, Wald
ratios and conditional magnitude probabilities match every canonical A/B
clause. These are finite population laws under the canonical population-moment
reading, with no undefined-correlation escape. See
`Defs/Part4.lean:131–168` and `Defs/Part6.lean:16–44`.

For **SAP.P029a.T12**, each direction of non-nesting is supplied independently.
The SEM witnesses supply failures of the IV assumptions. The other witness
has four equally weighted atoms, independent fair assignment, D=Z, all units
compliers, and effects 1 and 2 with equal probability. It satisfies every IV
condition; its ATE, LATE and Wald ratio are 3/2. The universal SEM identity
uses the same Q and u in both potential outcomes, exactly as canonical
part (b) requires. Subtraction therefore forces constant effect. This is the
specified causal interpretation of the SEM equations. Its premises also have
a compiled nonempty instance. See `Defs/Part4.lean:170–183` and
`Defs/Part6.lean:46–58`.

For **SAP.P029a.T13**, the reading challenged is unbiasedness of the saturated
ML compliance score with boundary fits evaluated in the stated closure.
The required conditions are one covariate stratum, the nested receipt model,
interior true parameters, independent observations from the two arms, and
maximization over 0≤q≤p≤1 with natural powers. Every condition is met:
the population has type masses (complier, always-taker, never-taker)
=(1/2,1/4,1/4), satisfies IV and latent ignorability, has score 1/2>1/4,
and has true nested parameters (3/4,1/3). The two observations are from
independent units; their joint receipt law is the product of the correct
arm marginals. Every displayed fit is a global likelihood maximizer. The
fitted-score expectation is 9/16, giving bias 1/16, while the raw difference
has expectation 1/2. The independent five-per-arm binomial law and every
number in canonical part (iv) also match. Boundary fits and 0^0=1 are
expressly canonical conditions, so they introduce no undisclosed restriction.
See `Defs/Part4.lean:193–219` and `Defs/Part6.lean:60–76`.

All conditional events used have positive probability; T12's Wald denominator
is 1. All spaces admit finite discrete probability measures, so measurability,
integrability and σ-finiteness hold automatically. Generic zero-denominator
defaults and negative-argument square-root defaults do not affect these
statements. The binomial natural subtraction is within range because
k≤n; all sample sizes used are positive. The fit table and residual definitions
are legitimate constructions whose substantive properties are separately
asserted, rather than placeholders encoding those properties.

Independent Lean verification succeeded with:

* `/home/ubuntu/sap/tools/sap-lean scratch/BlindInspect.lean`
* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`
* `/home/ubuntu/sap/tools/sap-lean scratch/LikelihoodCheck.lean`

The witness checks import only `SAP.P029a.Defs` and use no Challenge stubs or
`sorry`. The comparison uses the canonical statements, definitions and standing
assumptions supplied in `claims.json`, without treating notes or audit history
as amendments. The paper's identity was checked against its
[publisher DOI page](https://doi.org/10.1093/pan/mpt013); the supplied
transcriptions provide the relevant paper passages. Final fingerprints are
copied directly from `closure.json`.
