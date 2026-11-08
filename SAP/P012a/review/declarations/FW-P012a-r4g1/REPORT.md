All five declarations are faithful to their recorded scope, with severity
`none`. T1–T4 state their complete canonical claims. T5 accurately discloses
its one omission: the assertion about the paper's reporting and the
recoverability of the three recruitment-edge count triples. It retains the
complete mathematical minimum and its attainment.

| Declaration | Record | Verdict | Severity |
|---|---|---|---|
| SAP.P012a.T1 | whole | faithful | none |
| SAP.P012a.T2 | whole | faithful | none |
| SAP.P012a.T3 | whole | faithful | none |
| SAP.P012a.T4 | whole | faithful | none |
| SAP.P012a.T5 | restricted | faithful | none |

The blind expansion is in `reading.md`, saved before opening the claims or
record. `claim-stage.json` records the assessment made before reading the
record; no assessment changed afterwards. Every dependency in each closure
was read, including all 47 distinct generated declarations, which are
numeral proofs and ordinary pattern-match eliminators. The full checks of
the two refutations' printed readings and witness conditions are in
`claim-review.md`.

For T1, the reading being refuted is that the printed mechanisms execute
and return compatible pairs from compatible inputs. The four witnesses
meet the admissible-history, simple augmented graph, compatibility,
branch-selection and freshness conditions. Their asserted input statistics
are defined. In particular, line 22 executes outside the sampled-endpoint
block, the original pools are used, isolated sampled seeds are permitted,
and the empty trait pool is a permitted boundary case. The outputs or
failure to choose contradict the printed mechanisms themselves.

For T3, the reading being refuted is that each printed interval encloses
every compatible homophily value using the observed RDS data alone.
The private-leaf completion preserves every compatibility condition and
has a positive homophily denominator. Its 3972 vertices are allowed:
compatibility fixes no population size. Its value is below all three lower
endpoints, even allowing four-decimal rounding. No assertion about the
unavailable data or optimization code is required.

The following Lean files compiled successfully with `sap-lean`:

* `scratch/Nonvacuity.lean`: all four T1 inputs and incompatible outputs,
  the first input's exact homophily and preferential values, printed runs
  for either coin outcome, every corrected proposal branch, shared
  replacement endpoints, empty trait pools, and both T5 regularity cases.
* `scratch/PublishedInstance.lean`: an admissible 527-subject, six-seed
  forest with degree total 4487, recruitment counts (260,261,0), spare
  total 3445, and an actual greatest lower bound.
* `scratch/EndpointWitness.lean`: T4's complete converse antecedent with
  observed degree total 4026, nomination degree total 4487, and minimum
  -539551/767814 within 1/20000 of -0.7027.

The last two files use certified T5 only to supply the infimum after
independently checking their data, counts and numerical conditions.
Independent exact arithmetic in `scratch/arithmetic_check.py` also checks
all 136503 integer triples, the polynomial certificate, both maximizing
triples and all three exact gaps.

No conclusion depends on a junk value: admissibility prevents spare-degree
subtraction from truncating; Option guards exclude undefined statistics;
the endpoint formulas have positive denominators on their stated domains;
and `IsLeast`/`IsGLB` assert actual order properties rather than totalized
infima. Inactive trait values and renaming unsampled identities do not
change the relevant objects or values. The canonical excerpts of the
[published paper](https://academic.oup.com/aje/article-pdf/187/1/153/25333289/kwx208.pdf)
and its supplement in `claims.json` supply the operative printed readings.
