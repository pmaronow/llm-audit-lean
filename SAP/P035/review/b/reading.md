# Blind mathematical reading

This file was written and saved after reading all the supplied Defs and Challenge
sources and before opening either `claims.json` or `record.json`. The readings
below are of the theorem types, not of the proofs or the docstrings' promises.
There are exactly two Challenge theorem stubs. Neither has parameters, hypotheses,
typeclass assumptions, or an implication before its conclusion.

## Objects and expansion of every SAP definition

`Year` is the three-element type {2012, 2014, 2015}; `years` contains each of
these three elements once. A porch assignment z, campaign status a, and outcome b
are each Boolean. Write false as 0 and true as 1. The intended labels are comparison
versus Obama porch package, initiative absent versus present, and candy versus
raisins, respectively. These labels add no mathematical assumptions.

A potential-outcome model Y is an arbitrary total function

    Y : Year × {0,1} × {0,1} × ℕ → {0,1}.

Here the order of arguments is year y, assignment z, campaign status a, and latent
type r. The numerical value v(b) (`fruitValue`) is the rational 0 or 1, and
`bit(b)` is the natural number 0 or 1. No other person's assignment is an argument.

The following table expands `enrolled` e, `completeCases` n, `fruitCounts` k,
`releasedFrequency` p = k/n, `reducedDenominator` d = n/gcd(k,n), `latentSize` N,
and `threshold` t. All entries k,n,e,N,t,d are natural numbers; p is rational.

| y | z | e | n | k | p | d | N | t |
| --- | --- | ---: | ---: | ---: | --- | ---: | ---: | ---: |
| 2012 | 0 | 69 | 69 | 14 | 14/69 | 69 | 6555 | 1330 |
| 2012 | 1 | 96 | 95 | 24 | 24/95 | 95 | 6555 | 1656 |
| 2014 | 0 | 265 | 265 | 58 | 58/265 | 265 | 41605 | 9106 |
| 2014 | 1 | 157 | 157 | 37 | 37/157 | 157 | 41605 | 9805 |
| 2015 | 0 | 444 | 444 | 113 | 113/444 | 444 | 7104 | 1808 |
| 2015 | 1 | 192 | 192 | 61 | 61/192 | 192 | 7104 | 2257 |

The latent population S_y (`latentPopulation`) is the finite set of natural
numbers {1,...,N_y}, with both endpoints included. It is not the enrolled sample.
Let Δ_y be the natural subtraction t_y1 - t_y0 (truncated at zero by its type).
The explicit models, with `decide` taking the Boolean truth value of the displayed
inequality, are

    D(y,z,a,r) = 1 iff r ≤ t_y0 + bit(z) Δ_y;
    C(y,z,a,r) = 1 iff r ≤ t_y0 + bit(a) bit(z) Δ_y.

They are defined even for r outside S_y. In particular their values at r=0 are 1;
r=0 is not included in any mean or observed law. The fixed constants have
t_y0 ≤ t_y1, so Δ_y has the ordinary intended difference.

For a rational function f on ℕ, `uniformMean(y,f)` is

    (1/N_y) Σ_{r∈S_y} f(r).

`outcomeMean(Y,y,z,a)` is this mean of v(Y(y,z,a,r)). `successCount(Y,y,z)`
is the cardinality of {r∈S_y : Y(y,z,1,r)=1}, always at campaign present.
`campaignDifference(Y,y,z,r)` is the rational difference

    δ_Y(y,z,r) = v(Y(y,z,1,r)) - v(Y(y,z,0,r)),

which may be -1, 0, or 1 for an arbitrary model. `campaignMean(Y,y,z)` is
m_Y(y,z) = (1/N_y) Σ_{r∈S_y} δ_Y(y,z,r). `exactEffect` E_y is, respectively,
326/6555, 699/41605, and 449/7104. These literals are rational divisions.

Write ECount_y = e_y0 + e_y1 = 165,422,636. The fixed design definitions are

    yearMass q_y = ECount_y/1223;
    assignmentMass α_yz = e_yz/ECount_y;
    latentMass ℓ_y = 1/N_y;
    conditionalMass h_yzr = α_yz/N_y;
    jointMass j_yzr = q_y h_yzr.

These are rational-valued functions. The last three functions have the stated
formulas even outside S_y; they are used as masses only on the specified finite
support. `latentMass` is not otherwise used by either theorem.

For **any** rational weight function w : Year × {0,1} × ℕ → ℚ,
`observedLawWith(Y,w)` is the function on (y,z,b) with value

    L^w_Y(y,z,b) = Σ_{r∈S_y} w(y,z,r) 1{Y(y,z,1,r)=b}.

`observedRealLawWith` has exactly the same formula with any real-valued w and a
real-valued sum. No positivity, normalization, independence, or support hypothesis
is imposed on these arbitrary weights. `observedLaw(Y)` is L_Y = L^j_Y using the
fixed design above. All these laws evaluate outcomes only at campaign present.
An equality of laws is equality of functions, hence equality at every y,z,b.

`Calibrated(Y)` means, with quantifier order ∀y ∀z,

    (1/N_y) Σ_{r∈S_y} v(Y(y,z,1,r)) = p_yz.

The overall campaign effect `overallCampaignEffect(Y)` is the rational

    G_Y = Σ_{y∈{2012,2014,2015}} q_y(α_y0 m_Y(y,0) + α_y1 m_Y(y,1)).

`CampaignIdentified` is the proposition, with the quantifier/implication order
shown explicitly,

    ∀U ∀V : PotentialOutcome,
      Calibrated(U) → Calibrated(V) → L_U=L_V →
      ∀y, m_U(y,1)=m_V(y,1).

It is identification of the three assignment-1 campaign means within this fixed
finite calibrated model class. It is not a claim that every individual effect is
identified, or a statement about arbitrary uncalibrated laws or actual outcomes.

The Mathlib leaves have their usual exact meanings. `Finset.Icc` for ℕ is the
inclusive interval (`Mathlib/Order/Interval/Finset/Nat.lean`, its locally finite
order instance and `card_Icc`). `Finset.filter` selects the elements satisfying
the predicate (`Mathlib/Data/Finset/Filter.lean`); `.card` counts them. The sum
notation is finite `Finset.sum`, defined using the multiset sum
(`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`); no infinite-series or
integrability convention occurs. `Nat.gcd` and `Nat.lcm` are the ordinary natural
gcd/lcm, as in `Mathlib/Data/Nat/GCD/Basic.lean`. Natural division in d is integer
division, whereas casts followed by `/` and all division in ℚ use the rational
field operations (`Mathlib/Data/Rat/Defs.lean` and its imported rational
structure). Natural subtraction is truncated; rational subtraction is signed.
All denominators in this package are explicit positive integers. The only ℝ
operations are finite weighted sums in the arbitrary-real-weights clause.

## `SAP.P035.T1`

This is the unconditional proposition `T1Statement`. It asserts the conjunction
of **all** the following, in the order in the definition. Quantified r and s have
type ℕ; s is restricted to S_y by a finite sum, whereas a bare ∀r ranges over all
natural numbers. Quantified y and z range over all three years and both Booleans.

1. For every y, N_y = lcm(d_y0,d_y1).
2. For every y, N_y>0 and t_y0≤t_y1≤N_y.
3. For every y then z, t_yz = N_y p_yz as an equality in ℚ.
4. For every y then z then r,

       h_yzr = (Σ_{s∈S_y} h_yzs)(h_y0r+h_y1r).

   On the finite support this expresses the conditional-on-year factorization
   of the assignment and latent-type masses.
5. For every y then z then r, j_yzr≥0; and

       Σ_y (Σ_{r∈S_y} j_y0r + Σ_{r∈S_y} j_y1r) = 1.

6. For every y then z then r, C(y,z,1,r)=D(y,z,1,r).
7. For every y then z, the success counts of D and C are both t_yz, and the
   rational success count of D divided by N_y is p_yz.
8. D is calibrated and C is calibrated, with each predicate expanded above.
9. For every y, the difference of D's assignment-1 and assignment-0 outcome
   means at campaign present equals E_y and is strictly positive.
10. For every y then z then r, δ_D(y,z,r)=0.
11. For every y then r, δ_C(y,0,r)=0.
12. For every y, m_C(y,1)=E_y, E_y=Δ_y/N_y (casting Δ_y to ℚ before division),
    and m_C(y,1)>0.
13. G_D=0.
14. G_C=(96/1223)(326/6555)+(157/1223)(699/41605)+(192/1223)(449/7104),
    G_C=83755728/5240292055, and G_C>0. All terms are rational.
15. For every rational w : Year × {0,1} × ℕ → ℚ, L^w_D=L^w_C as functions
    on y,z,b. The universal w is outside the function equality.
16. For every real w : Year × {0,1} × ℕ → ℝ, the analogous real laws of D and
    C are equal as functions on y,z,b.
17. `CampaignIdentified` is false: equivalently, there exist calibrated models
    U,V with L_U=L_V and a year y whose assignment-1 campaign means differ.
18. There does not exist a function f : (Year × {0,1} × {0,1} → ℚ) → ℚ such
    that, for **every** potential-outcome model Y, calibration of Y implies
    f(L_Y)=G_Y. The order is ¬∃f ∀Y (Calibrated(Y) → ...).

Thus this theorem supplies a particular pair of indistinguishable finite models
with different campaign effects and numerical certificates. It has no premises
asserting calibration, indistinguishability, positivity, or nonidentification;
those are all conclusions. It makes no assertion about the initiative's actual
effect in the sampled children and no statistical significance assertion.

## `SAP.P035.T2`

This is the unconditional proposition `T2Statement`. Its first conjunct begins
with ∃U ∃V : PotentialOutcome. The same two witnesses must simultaneously satisfy:

1. U is calibrated.
2. V is calibrated.
3. L_U=L_V for the fixed rational design.
4. For every y then z then r, δ_U(y,z,r)=0, including r outside S_y.
5. For every y, m_V(y,1)>0, m_V(y,1)=p_y1-p_y0, and m_V(y,1)=E_y.
6. For every y then r, V(y,1,0,r)=V(y,0,0,r), including r outside S_y.

The second conjunct, outside the existential, is ¬CampaignIdentified with the
definition expanded above. In particular, the absence-of-campaign porch equality
is individual equality, whereas the presence-of-campaign contrast and campaign
effect equalities in item 5 are equalities of means. T2 has no explicit clause
requiring V's campaign effect on assignment 0 to vanish. Together, calibration,
the assignment-1 campaign-mean equation, and item 6 imply that its assignment-0
campaign **mean** vanishes, but not that each individual's effect there vanishes.
The theorem does not quantify over a message mediator, fitted regression,
statistical test, or textual change to a publication. It does not assert a
causal conclusion about actual porch assignment or actual initiative exposure.
