# Review of SAP.P026a.T11 and SAP.P026a.T12

Both declarations are **faithful**, with severity **none**. Every statement
dependency listed in `closure.json` was read, including the generated numerical
proof declarations. The blind expansion was saved in `reading.md` before
opening `claims.json`; `claim-stage.json` was saved before opening `record.json`.
The record confirms the independently reached `whole` classifications.

## SAP.P026a.T11

`Defs/Part15.lean:14-18` states the exact arm variance, covering canonical
clause (b) and the treatment/control variance definitions. Lines 19-29 give the
exact bound gap, unbiased bound estimation, conservativeness, and the conditional
full-support equality, covering (c)-(f). Lines 30-37 state unbiased equation
[31], covering (a). Boolean arm quantification includes both treatment and
control. The Challenge docstring at `Challenge/Part1.lean:136-137` accurately
describes this content.

The separation hypothesis is required by the canonical standing cluster
setting. The law, partition, totals, observed response, ordered-pair sums, and
restored cluster indicators have the intended meanings. The general bounds
allow zero joint probabilities and signed outcomes. Every division has a
nonzero denominator wherever its value is used in the theorem. No additional
restriction or junk-value dependence was found.

## SAP.P026a.T12

`Defs/Part16.lean:14-20` covers equation [20]; lines 21-36 cover both intermediate
expansions of [21] and the arm formulas [21]-[22]. Lines 37-42 give the full
covariance expansion of [23], and lines 48-50 its split form. Lines 43-47 give
the entire corrected equation [24] when the numerical definitions are expanded.
The split includes every zero-joint ordered pair, including diagonal pairs and
unavailable directed off-diagonal pairs, with the correct signs. The Challenge
docstring at `Challenge/Part1.lean:140-141` accurately describes these equations.

The probability law and fixed outcome vectors match the standing setting.
There is no independence or pair-support assumption. Positive marginals and
the inhabited unit type protect every denominator, including the squared unit
count. No extra restriction or definition mismatch was found.

## Compiled checks

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0.
The file imports only `SAP.P026a.Defs` and constructs all hypotheses directly.
It checks two clusters of sizes two and one, full same-arm support, and a
complementary-allocation law with zero same-arm joints. For the latter, the
treatment HT-total variance is 36 and the expected bound estimator is 40.
A separate directed-zero covariance check gives both the direct and split
covariance as 1/2 and the HT contrast variance as 21/8. The generated dependency
proofs were inspected with `scratch/Blind.lean`; each is just the numerical
typeclass fact `(1+1).AtLeastTwo`.
