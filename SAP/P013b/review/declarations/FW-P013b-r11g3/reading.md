# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: the three
docstrings and declarations in `SAP/P013b/Challenge/Part1.lean`, every source
declaration listed in their closures in `closure.json`, and Lean `#print` output
for all 76 distinct closure entries, including generated proof declarations.
The inspection script and its complete output are `scratch/ClosureCheck.lean`
and `scratch/closure-print.txt`. No claim or architect metadata was used below.

## SAP.P013b.T27

The docstring describes a formal reading of Section 10: binary wearing outcomes,
consistent observation, four contrasts of proportions, and unbiased HT estimators.

### Objects, hypotheses, and quantifier order

Universally quantify a type Ω with a finite enumeration, natural numbers N,M,
and a function w:Ω→ℝ with w(z)>0 for every z and Σ_z w(z)=1. This is the full
meaning of `Design`, its constructor, and its weight projection. Next assume
N>0. Universally quantify an injective function a:Fin N→Fin M, then functions
s:Fin M→Fin 56, H:Ω→Fin 56→Bool, A:Ω→Fin M→Bool,
G:Fin M→Finset(Fin M), and y:Fin N→Fin 5→ℝ. Assume, in this order:

1. For every i,d, y(i,d)=0 or y(i,d)=1.
2. For every j:Fin M, j∉G(j).
3. For all j,k:Fin M, k∈G(j) iff j∈G(k).
4. For all j,k:Fin M, k∈G(j) implies s(j)=s(k).
5. For every i:Fin N and d:Fin 5, p(i,d)>0, with p defined below.

`Fin n` is the set of natural numbers strictly below n. For z,i set h=H(z,s(a(i))),
o=A(z,a(i)), and t=true iff there exists j∈G(a(i)) with A(z,j)=true.
`section10Exposure` gives the following element D(z,i) of Fin 5:

| h | o | t | D |
|---|---|---|---|
| false | either | either | 0 |
| true | false | false | 1 |
| true | false | true | 2 |
| true | true | false | 3 |
| true | true | true | 4 |

`section10Population` is precisely the pair of functions (D,y).
`Population` carries no other axioms: its exposure and outcome projections just
select these functions. For a condition B, write 1[B] for the real number 1 if
B holds and 0 otherwise. The remaining definitions unfold to

- `indicator`: 1[D(z,i)=d].
- `pi`: p(i,d)=Σ_z w(z)1[D(z,i)=d].
- `observed`: Y(z,i)=y(i,D(z,i)).
- `potentialTotal`: T(d)=Σ_i y(i,d).
- `potentialMean`: μ(d)=T(d)/(N:ℝ).
- `causalEffect`: τ(d,e)=μ(d)−μ(e).
- `htTotal`: T̂(d,z)=Σ_i 1[D(z,i)=d] y(i,d)/p(i,d).
- `htEffect`: τ̂(d,e,z)=(T̂(d,z)−T̂(e,z))/(N:ℝ).
- `expectation`: E_w X=Σ_z w(z)X(z).

For every such collection of objects satisfying all the hypotheses, the theorem
concludes the conjunction of:

1. For every z:Ω and i:Fin N, Y(z,i)=Σ_{d:Fin 5}1[D(z,i)=d]y(i,d).
2. For every d:Fin 5, if d≠0, then both
   τ(d,0)=(Σ_i y(i,d))/N−(Σ_i y(i,0))/N and
   Σ_z w(z)τ̂(d,0,z)=τ(d,0).

Thus the four selected exposures are exactly 1,2,3,4 against baseline 0.
No particular school lottery, student sample size, empirical score, numerical
estimate, variance claim, or confidence interval is asserted. There is no
independence hypothesis on H and A; the assertion quantifies any finite law
having the stated exposure positivity. Conditional assertions about h and A in
unhosted schools are absent.

### Junk values and boundary cases

The definitions of means and HT totals use real division, so in isolation Lean
assigns x/0=0. Here N>0 and every p(i,d)>0 exclude every denominator zero.
An empty Ω cannot admit w because its total would be 0=1. N>0 together with the
injection into Fin M ensures M>0. All five exposure values are strictly within
Fin 5; generated `NeZero 5` proofs only justify ordinary finite numerals. No
wrapping finite numeral affects the exposure codes. The neighbor filter may be
empty, in which case its nonemptiness test is false and the peer indicator is
false, with its ordinary intended meaning. Positivity rules out data in which
an analyzed unit can never attain a peer-exposed category. An empty neighbor
set for some unanalyzed student is permitted.

All sums have finite index sets and real-valued summands; no nonintegrability,
Bochner integral convention, infinite expectation, ENNReal `toReal`, real log,
square root, real power, infimum/supremum, limit superior/inferior, partial
function default, or truncated natural subtraction occurs. Natural-to-real
casts are exact. The displayed subtractions are real subtractions.

## SAP.P013b.T26

The docstring describes two specified school laws, their support counts and
inclusion, marginal/joint laws and differences, and student exposure preservation
and nonhosting formulas.

### Definitions unfolded

A school is a pair (b,k)∈Fin 14×Fin 4: 14 blocks of four schools each. Let
U=Fin 14×Fin 4 and write B for the finite set of functions z:Fin 14→Finset(Fin 4)
such that each z(b) is a two-element subset of Fin 4. These are exactly
`schoolBlockChoices` (the two-element powerset of the four-element universal
set) and `schoolBSupport` (the finite Cartesian product of these choices).
Let C be the finite set of all 28-element subsets of U (`schoolCSupport`).
For z∈B, L(z)={(b,k):k∈z(b)} is `blockSchoolHosts`.
`schoolBHosts(z,(b,k))` is the Bool k∈z(b); `schoolCHosts(z,a)` is the Bool a∈z.
Let W={(b,k):b.val<7}; this is `schoolBadHosts`.

For any finite set S and real function X on its ambient type, define
E_S X=(Σ_{z∈S}X(z))/(|S|:ℝ). For any decidable predicate A,
P_S(A)=|{z∈S:A(z)}|/|S|, with real casts on both cardinalities.
These are the full meanings of `uniformSchoolMean` and
`uniformSchoolProbability`. Use their respective host predicates for B and C.

`schoolHostedExposure(h,c)` is 0 if h=false and the finite value c.val+1 if
h=true, for c:Fin 4. Given any type Ξ with a finite enumeration, N:ℕ,
Q:Ξ→ℝ, a school map s:Fin N→U, and c:Ξ→Fin N→Fin 4, define
D(z,x,i)=0 when the school of i is unhosted and D(z,x,i)=c(x,i)+1 otherwise.
This completely unfolds `schoolStudentExposure`. For either school support S,
the definition `schoolStudentJoint` is

J_S(i,j,d,e)=(1/|S|)Σ_{z∈S}Σ_{x:Ξ}Q(x)1[D(z,x,i)=d and D(z,x,j)=e].

`schoolStudentMarginal` is m_S(i,d)=J_S(i,i,d,d). Thus the joint law is
explicitly a product of a uniform school draw and the same independent student
draw x. No independence between different students' codes is assumed.

### Complete statement and quantifier order

There are no outer data hypotheses. The statement is the conjunction of:

1. |B|=6^14=78364164096 and |C|=choose(56,28)=7648690600760440.
2. For every z, z∈B implies L(z)∈C.
3. For every a∈U, P_B(a hosted)=1/2.
4. For every a∈U, P_C(a hosted)=1/2.
5. For every a,b∈U, assuming a≠b, P_B(a,b hosted) is 1/6 if their
   first coordinates agree and 1/4 otherwise.
6. For every distinct a,b∈U, P_C(a,b hosted)=27/110.
7. The real identities 27/110−1/6=13/165 and 27/110−1/4=−1/220.
8. For every distinct a,b, put p=1/6 for the same block, 1/4 for different
   blocks. Under B, the four probabilities (neither hosted, only b hosted,
   only a hosted, both hosted) are (p,1/2−p,1/2−p,p).
9. For every distinct a,b, the same four probabilities under C are
   (27/110,14/55,14/55,27/110).
10. Universally quantify a finite Ξ and N:ℕ; assume N>0; quantify Q:Ξ→ℝ;
    assume Q(x)≥0 for all x and Σ_x Q(x)=1; quantify s and c as above.
    Then for every i,d, m_B(i,d)=m_C(i,d), and for every i,j,d,e,
    s(i)=s(j) implies J_B(i,j,d,e)=J_C(i,j,d,e).
11. For every h:Bool and c:Fin 4, the hosted-exposure code is 0 iff h=false.
12. Universally quantify a finite Ξ, N:ℕ, Q, Q≥0, Σ_xQ(x)=1, s and c,
    in that order, with no N>0 assumption in this conjunct. For all i,
    m_B(i,0)=m_C(i,0)=1/2. For all i,j, if s(i)≠s(j),
    J_B(i,j,0,0) is 1/6 or 1/4 according as their schools share a block or
    do not, whereas J_C(i,j,0,0)=27/110.
13. W∈C and for every z∈B, L(z)≠W.
14. The arithmetic/counting identities choose(4,2)=6,
    choose(4,2)^14=6^14, 3·6^13/6^14=1/2,
    choose(55,27)/choose(56,28)=28/56, 28/56=1/2,
    6^13/6^14=1/6, 3²·6^12/6^14=1/4,
    choose(54,26)/choose(56,28)=(28·27)/(56·55), and
    (28·27)/(56·55)=27/110. Binomial coefficients/powers in the counting
    statements are natural; cardinality ratios and the explicitly real powers
    are exact real casts or real arithmetic.
15. For every distinct a,b, P_C(a,b hosted)−P_B(a,b hosted) is 13/165
    in the same block and −1/220 in different blocks; furthermore the two
    joint probabilities are unequal.

L(B)⊂C follows from the inclusion and explicit missing W, although it is not
written as a `StrictSubset` predicate. These formulas specify a comparison of
two given finite laws. They do not identify any empirical script by themselves.

### Junk values and boundary cases

E_∅ and P_∅ would both be zero because real division assigns 0/0=0. B and C
are nonempty concrete sets: the constant choice {0,1} in each block is in B,
and its image has 28 schools and is in C; W is another C witness. No probability
in the conclusion uses an empty school support. The denominators in the
arithmetic identities (6^14, choose(56,28),56,56·55 and the displayed rational
denominators) are positive. The count-to-real casts do not truncate.

The hypotheses on Q exclude empty Ξ, because the empty sum cannot equal 1.
N>0 in clause 10 gives actual student indices; clause 12 also allows N=0,
whose pointwise statements have no indices, but equally includes nonempty N.
No substantive conclusion is obtained from empty student indices. Codes c.val+1
are between 1 and 4, proved by the generated bound proof, and no finite-numeral
wrapping is used. Other generated `_proof_*` declarations are `AtLeastTwo` or
`NeZero` proofs for ordinary numerals, not additional stochastic assumptions.
The subtractions are in ℝ. Empty filters encode events with probability zero.
There are no integrals, infinities, logs, roots, real powers, order extrema,
limsup/liminf, truncated subtraction, or partial-function defaults.

## SAP.P013b.T25

The docstring describes a canonical counterexample to identifying the two
specified lotteries: different supports and biased variance inputs, using a
56-school population with precisely two nonzero hosted outcomes.

### Definitions unfolded

Here independently let U=Fin 14×Fin 4, the 56 schools. Let B be all functions
z assigning a two-element subset z(b)⊆Fin 4 to each b∈Fin 14, and C all
28-element subsets of U. These are the finite Cartesian product of two-element
powersets and the 28-element powerset, respectively. Let
L(z)={(b,k):k∈z(b)} and W={(b,k):b.val<7}. The B-host Bool at (b,k) is k∈z(b),
and the C-host Bool at i is i∈z. These unfold `School`, `schoolBlockChoices`,
`schoolBSupport`, `schoolCSupport`, `blockSchoolHosts`, `schoolBadHosts`,
`schoolBHosts`, and `schoolCHosts`.

For every finite S in any ambient type α and real X:α→ℝ,
E_SX=(Σ_{z∈S}X(z))/|S|,
P_S(A)=|{z∈S:A(z)}|/|S|,
and V_SX=E_S(X²)−(E_SX)², all divisions in ℝ.
These unfold `uniformSchoolMean`, `uniformSchoolProbability`, and
`uniformSchoolVariance`.

For a,b,i∈U define v_ab(i)=1 if i=a, else 1 if i=b, else 0.
`schoolActiveOutcome` is v_ab. `schoolPotentialOutcome` is
Y_ab(i,true)=v_ab(i) and Y_ab(i,false)=0. For any host function
h:α→U→Bool, write H_i(z)=1 if h(z,i)=true, else 0 (`schoolHostBit`).
`schoolExampleObserved` is Y_ab(i,h(z,i)). The estimators are the finite sums

T_ab(z)=Σ_{i∈U}H_i(z)[v_ab(i)/(1/2)],

V_ab(q,z)=Σ_i H_i(z)(1−1/2)[v_ab(i)/(1/2)]²
 +Σ_iΣ_{j∈U,j≠i}H_i(z)H_j(z)[(q−(1/2)(1/2))/q]
                         [v_ab(i)/(1/2)][v_ab(j)/(1/2)].

These are exactly `schoolTwoHT` and `schoolTwoVarianceInput`. The second
summation is over ordered distinct pairs. The input q is supplied for every
off-diagonal pair; because only a,b have nonzero outcomes, all other terms
vanish. In the moment clauses its marginal inputs really are 1/2, and the
correct input q is the pair probability p.

### Complete statement and quantifier order

There are no outer assumptions. The theorem conjoins:

1. |W|=28, W∈C, and ∀z∈B, L(z)≠W. Under C the event z=W has probability
   1/7648690600760440, which is positive. Under B the event L(z)=W has probability 0.
2. For all a,b∈U, assume a≠b. Then all Y_ab(i,d) are 0 or 1, their hosted
   total is 2, all unhosted outcomes are 0, and for every type α, host function
   h:α→U→Bool, z:α and i∈U, the observed outcome equals H_i(z)v_ab(i).
3. For every type α, h, a,b with a≠b, and z:α,
   T_ab(z)=2(H_a(z)+H_b(z)) and Σ_i v_ab(i)=2.
4. For every type α, h, distinct a,b, q:ℝ and z:α, if q>0 then
   V_ab(q,z)=2(H_a+H_b)+8H_aH_b(q−1/4)/q.
5. For every type α, finite S⊆α, h, distinct a,b, p,q:ℝ, assuming
   P_S(H_a=1)=1/2, P_S(H_b=1)=1/2, P_S(H_a=H_b=1)=p, and q>0,
   conclude E_ST_ab=2, V_ST_ab=8p, and E_SV_ab(q)=2+8p(q−1/4)/q.
6. For every type α, finite S, h, distinct a,b and p:ℝ, assuming p>0,
   the same two marginal equations and the same joint equation, conclude
   E_SV_ab(p)=V_ST_ab.
7. With h the actual respective membership host maps:

   | Law | active pair | mean HT | variance HT | mean V(27/110) |
   |---|---|---|---|---|
   | B | (0,0),(0,1) | 2 | 4/3 | 160/81 |
   | B | (0,0),(1,0) | not separately stated here | 2 | 53/27 |
   | C | (0,0),(0,1) | not separately stated here | 108/55 | 108/55 |

   Also E_BV_(0,0),(1,0)(27/110)<V_BT_(0,0),(1,0).
8. The respective B variance biases in the first two rows are exactly
   52/81 and −1/27.
9. For every a∈U, under both B and C the hosting and nonhosting probabilities
   are each 1/2.
10. P_B((0,0),(0,1) hosted)=1/6,
    P_B((0,0),(1,0) hosted)=1/4,
    and P_C((0,0),(0,1) hosted)=27/110.
11. The exact real identity 1/choose(56,28)=1/7648690600760440.

The counterexample concerns equality of the two specific school lotteries and
using C pair inputs under B. It does not assert that an estimator using the
correct school pair inputs is biased; clause 6 states the opposite.

### Junk values and boundary cases

The generic finite-mean/probability definitions assign zero on the empty set
through 0/0=0. In clauses 5 and 6 the marginal equation 0=1/2 would be impossible
for empty S, so these hypotheses force S nonempty. The concrete B and C sets
are nonempty, witnessed respectively by constant {0,1} and its host set (or W
for C). Their sizes are positive mathematical cardinalities, not defaults.

The generic variance input uses q in a real denominator and would have a
zero-convention value if q=0. Every use in this statement has q>0, p>0 with
q=p, or q=27/110>0. The inverse marginal is always 1/(1/2). The reciprocal
binomial denominator is positive. All count-to-real casts are exact and all
subtractions real. In clauses 2–6 a=b is excluded, so there are exactly two
active schools; without this hypothesis v_aa would have only one active school.
Concrete schools (0,0),(0,1),(1,0) are distinct in their specified pairs and
are represented by in-range finite numerals. The generated numeral proofs
(`AtLeastTwo`/`NeZero`) have no other content.

Quantification over an arbitrary empty α makes the purely pointwise z-clauses
empty, but the theorem also asserts all concrete nonempty-support facts and
has ordinary nonempty generic instances. There are no integrals, infinite
quantities, `toReal`, logs, roots, real powers, empty/unbounded extrema,
limsup/liminf, truncated subtraction, or partial-function defaults.
