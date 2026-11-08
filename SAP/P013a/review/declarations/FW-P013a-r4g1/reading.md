# Blind statement reading

This file was written before opening `claims.json` or `record.json`. I read the
Challenge docstrings and all source declarations in the five elaborated
dependency closures in `closure.json`. The 42 generated declarations at line 0
were additionally inspected with Lean in `scratch/ClosurePrint.lean` (output in
`scratch/ClosurePrint.out`). They supply numeral typeclass instances, finite
index bounds, positivity of weights, and normalization of weights; they add no
statistical assumptions. The union of the five closures contains 142 distinct
declarations. Constructors and projections have their ordinary structure
meaning as expanded below.

## Common expansions used in the five readings

All sample spaces in the audited statements are finite types. A design on a
finite type Ω is a function w:Ω→ℝ with w(z)>0 for every z and Σ_z w(z)=1.
Consequently Ω is nonempty. Write

* E_w X = Σ_z w(z)X(z),
* Pr_w(A) = Σ_z (if A(z) then w(z) else 0),
* Cov_w(X,Y) = E_w(XY)−E_w(X)E_w(Y), and
* Var_w X = E_w(X²)−(E_w X)².

A population of size N with K exposure labels is an arbitrary exposure map
D:Ω→Fin N→Fin K and an arbitrary fixed real table y:Fin N→Fin K→ℝ.
Here Fin n is the integers 0,…,n−1. For i,j∈Fin N and d,e∈Fin K let

* I_id(z)=1 if D(z,i)=d, otherwise 0;
* p_id=Σ_z w(z)I_id(z), and p_ij,de=Σ_z w(z)I_id(z)I_je(z);
* Yobs_i(z)=y_i,D(z,i), T_d=Σ_i y_id, μ_d=T_d/N;
* τ_de=μ_d−μ_e and H_d(z)=Σ_i I_id(z)y_id/p_id;
* τhat_de(z)=(H_d(z)−H_e(z))/N.

The predicate called positivity at d is **0<p_id<1 for every i**; in particular
it excludes certainty exposure as well as zero exposure probability.

Here are the variance-estimator definitions, including their ordered indices:

* B_ij,de(z)=I_id(z)I_je(z)((p_ij,de−p_id p_je)/p_ij,de)
  (y_id/p_id)(y_je/p_je).
* Q_d(z)=Σ_i I_id(z)(1−p_id)(y_id/p_id)²
  +Σ_i Σ_{j≠i} B_ij,dd(z).
* A_d(z)=Σ_i Σ_{j≠i,p_ij,dd=0}
  [I_id(z)y_id²/(2p_id)+I_jd(z)y_jd²/(2p_jd)].
* C_de(z)=Σ_i Σ_{j≠i,p_ij,de>0} B_ij,de(z)
  −Σ_i Σ_{j,p_ij,de=0}
  [I_id(z)y_id²/(2p_id)+I_je(z)y_je²/(2p_je)].
* Vhat_de(z)=[Q_d(z)+A_d(z)+Q_e(z)+A_e(z)−2C_de(z)]/N².

Every sum here is a Mathlib finite sum; j≠i means `Finset.univ.erase i`.
No division is a partial operation in Lean: a/0=0 for real a. This convention
sets B_ij,de=0 at zero joint probability. With positive atom weights, zero
joint probability also implies I_id I_je=0 at every atom, so this agrees with
omitting impossible joint observations. This is distinct from requiring all
joint probabilities to be positive.

For a Bool matrix h on Fin N and two finite sets A,B⊆Fin N:

* The **printed** no-edge predicate is absence of i,j with h_ij=true and
  [(i∈A and j∉B) or (j∈A and i∉B) or
  (i∉A and j∈B) or (j∉A and i∈B)]. These complements are literal.
* The **corrected** no-edge predicate is absence of an edge with one endpoint
  in A and the other in B in either direction. Its four source disjuncts repeat
  the two directions; repetition does not change the proposition.
* Vector independence means, for **every** two full label functions
  a,b:Fin N→Fin K,
  Pr(∀i∈A,D_i=a_i and ∀j∈B,D_j=b_j)
  =Pr(∀i∈A,D_i=a_i)Pr(∀j∈B,D_j=b_j).
* Printed/genuine dependency means: for every A and B, if A,B are disjoint
  and satisfy the printed/corrected no-edge predicate respectively, their
  exposure vectors are independent as just defined. Disjoint means no common
  element. Symmetry and absence of self-loops are not part of these predicates.
* A row bound m means ∀i, Σ_j 1{h_ij=true}≤m, with a natural-number sum.
* Pair independence of i,j means ∀d,e, p_ij,de=p_id p_je.

Independent product designs have weights w(z)v(t); the R-replicate design on
functions zs:Fin R→Ω has weight Π_{r∈Fin R}w(zs(r)). These are full product
laws, hence independent draws, including independence from the observed draw
when the two constructions are combined. For a simulated total let
C_id(zs)=Σ_r I_id(zs(r)), ptilde_id=(C_id+1)/(R+1), and
Htilde_d(z,zs)=Σ_i I_id(z)Yobs_i(z)/ptilde_id(zs).
All counts C_id are real sums of zero-one indicators. The natural R+1 is cast
to ℝ before division. The minimum predicate for p0 says an i attains p0 and
every p_id≥p0. The cancellation factor is κ=(Σ_i|y_id|)/|T_d|.

Convergence in probability to a means: for every real ε>0, the real sequence
Pr_n(ε<|X_n−a|) tends to 0 along the natural atTop filter. Normal convergence
with mean m and variance v:ℝ≥0 means convergence of Pr_n(X_n≤x), for every
real x, to the CDF of Mathlib's Gaussian real measure of mean m and variance v.
Only strictly positive v=1 or 8 occurs in these five statements. Let Φ be the
CDF of the Gaussian with mean 0 and variance 1, and
q_α=inf{x∈ℝ:1−α/2≤Φ(x)}, implemented by real `sInf`.

The sequence framework used below has the following complete content.
For every n∈ℕ there is a support size M_n, label size K_n, positive normalized
weights on Fin M_n, and a population on Fin(n+1) with K_n labels. There are
selected labels d_n,e_n∈Fin K_n which are distinct, and both have all marginal
probabilities strictly between 0 and 1. These are fields of the sequence,
not later theorem hypotheses. Write τhat_n,τ_n,V_n,Vhat_n for the contrast,
population contrast, its variance, and variance estimator defined above at
d_n,e_n. The other sequence predicates expand as follows:

* All-label positivity: ∀n,a,i, 0<p_ia<1.
* Comparison boundedness: ∃c1,c2∈ℝ, c1≥0,c2>0, such that ∀n,i the absolute
  outcomes at d_n and e_n are ≤c1, and |1/p_id_n|,|1/p_ie_n|≤c2.
* Condition 3: the same constants and bounds for **all** labels a at every n.
* Condition 4: ∃Bool matrices g_n such that ∀n,i,j,
  g_nij=false implies pair independence, and
  [Σ_iΣ_j 1{g_nij=true}]/(n+1)²→0.
* Printed Condition 5: ∃m∈ℕ and matrices h_n such that ∀n the printed
  dependency predicate holds and every row has at most m true entries.
* Genuine Condition 5: additionally each h_n is symmetric, and the genuine
  dependency predicate replaces the printed predicate; m is uniform in n.
* Condition 6: ∃c∈ℝ, c>0, with (n+1)V_n→c.
* The lower-tail condition: ∀δ>0,
  Pr_n((n+1)Vhat_n<(n+1)V_n−δ)→0.
* Centered concentration: for every ε>0,
  Pr_n(ε<|(n+1)(Vhat_n−E_n Vhat_n)|)→0.
* Vanishing scaled-estimate variance: Var_n((n+1)Vhat_n)→0.
* Coverage at α is Pr_n(Vhat_n≥0 and
  |τhat_n−τ_n|≤q_α sqrt(Vhat_n)).
* A constant positive-joint lower bound b means ∀n,i≠j, each of
  p_ij,d_nd_n, p_ij,e_ne_n, p_ij,d_ne_n is either 0 or ≥b.
* The positive-joint domain at n means that at least one of these three
  probabilities for some i≠j is positive.
* Being its minimum b means b>0, one such off-diagonal probability equals b,
  and every positive probability among these three families is ≥b.
* Nested stable outcomes means existence of injections labels_n:Fin K_n↪ℕ,
  two different integers d,e∈ℕ, and y∞:ℕ→ℕ→ℝ, such that labels_n(d_n)=d,
  labels_n(e_n)=e, and y_ia at n equals y∞(i.val,labels_n(a)) for all n,i,a.

The last predicate requires a common outcome table, whereas the sequence
structure by itself permits different tables at different sizes.

## SAP.P013a.T1

Location: `SAP/P013a/Challenge/Part1.lean:7`; principal expansions:
`Defs/Part5.lean:14,42` and `Defs/WholeW1.lean:14`.

This is a closed conjunction, not an implication from arbitrary experiments.
For every natural r and proof 2≤r, set N=2r, ε=N^−2 and t=1−2ε.
There are r **independent** pairs, each with exposure outcomes 00,01,10,11
and probabilities ε,1/2−ε,1/2−ε,ε. The sample space is Fin r→Fin 4
with the product of these weights. Unit i belongs to pair floor(i/2); its
exposure is the first bit for even i and second bit for odd i. Both label
outcomes are +1 for even i and −1 for odd i. The score s(a) is four times
the first bit minus the second bit, in the signed integers and then ℝ;
it takes values (0,−4,4,0). The pair variance score u_N(a) is 2/ε if the
bits agree and 16−4/t otherwise. Let A_r be the event every pair splits.

The following are asserted for **every** r≥2:

1. For all i,d, p_id=1/2 and |y_id|=1. For all i≠j,d,e, the joint probability
   is ε (same pair, equal labels), 1/2−ε (same pair, unequal labels), or 1/4
   (different pairs). The Bool matrix h_ij=1{floor(i/2)=floor(j/2)} satisfies
   both dependency predicates and has row bound 2.
2. τ_10=0. For every atom z,
   τhat_10(z)=Σ_a s(z_a)/N,
   N²Vhat_10(z)=Σ_a u_N(z_a), and Vhat_10(z)>0.
3. Var(τhat_10)=8t/N and E Vhat_10=Var(τhat_10).
4. Pr(A_r)=t^r; Pr(not A_r)≤1/N; and for every z∈A_r,
   NVhat_10(z)=8−2/t.
5. Var(NVhat_10)=4(N−2)^4(N+2)^4/[N^5(N²−2)].
6. The one-pair expectation of u_N is 16t.
7. For each i the **exact** natural row sum of h is 2 (including its diagonal).

The conditions in item 1 and the dependency and row-bound facts are also
repeated explicitly in the conjunction. Then use r=n+2 for n=0,1,…,
N_n=2(n+2), V_n=Var(τhat_10), W_n=N_nVhat_10. The assertions are:

* N_n V_n→8; W_n converges in probability to 6; Vhat_10/V_n converges in
  probability to 3/4;
* Var(W_n)/(4N_n)→1, and Var(W_n) tends to +∞;
* sqrt(N_n)τhat_10 converges to a centered Gaussian of variance 8;
* **for every** real α with 0<α<1, the interval coverage probability tends to
  2Φ(q_α sqrt(3/4))−1, and this number is strictly less than 1−α;
* there does not exist C≥0 such that eventually Var(W_n)≤C/N_n;
* 0.91037489444 < 2Φ(q_(1/20) sqrt(3/4))−1 < 0.91037489445.

The theorem docstring describes a counterexample to printed asymptotic
conservativeness, including a strictly positive unbiased estimator and exact
95 percent coverage bounds. It calls the row bound “degree-two.”

Junk-value audit: N≥4, ε>0, t>0, N²−2>0, p_id=1/2, and V_n=8t/N>0;
all the ratios actually asserted therefore have nonzero denominators.
The general estimator convention B=0 at a zero joint probability is harmless
for impossible exposure pairs; same-unit unequal labels necessarily have zero
joint probability and are handled by C's missing-joint correction. All square
roots used here have positive arguments. The infimum defining q_α is finite
and attained at the usual normal quantile for α∈(0,1); outside this range its
totalized value is never used. All finite index sets here are nonempty.
`pairEpsilon 0` would equal 0, but cannot occur. floor(i/2), parity and
finite-index constructors are total with proven bounds. The pair score uses
**integer** subtraction, not truncated natural subtraction. Every remaining
subtraction is real or integer subtraction. Expectations are finite sums,
not Bochner integrals. The Gaussian CDF is a probability-measure CDF; it has
no infinite-to-real issue. No liminf/limsup, rpow, empty extremum, or partial
function default affects this statement.

## SAP.P013a.T2

Location: `SAP/P013a/Challenge/Part1.lean:14`; principal expansion:
`Defs/WholeW1.lean:33–73`. The sequence definitions, estimates and conditions
have all been expanded in the common reading above.

This is the conjunction of six independently quantified assertions:

1. **For every** sequence S (with the structural fields described above),
   if comparison boundedness, genuine Condition 5, Condition 6, and the
   lower-tail condition hold, then **for every** α∈ℝ, 0<α<1 implies
   1−α≤liminf_n Pr_n(Vhat_n≥0 and |τhat_n−τ_n|≤q_α sqrt(Vhat_n)).
   No stable outcome table or all-label positivity is required here.
2. **For every** S, centered concentration implies the lower-tail condition.
3. **For every** S, vanishing scaled-estimate variance implies **both** centered
   concentration and the lower-tail condition. No boundedness, graph or
   positive variance assumption is attached to assertions 2 and 3 beyond
   the sequence fields.
4. **For every** S satisfying comparison boundedness and genuine Condition 5,
   and **every** real b>0 satisfying the uniform lower bound on nonzero
   off-diagonal joints, there exists C≥0 such that eventually
   Var_n((n+1)Vhat_n)≤C/(n+1). Both centered concentration and the lower-tail
   condition also follow. C may depend on S and b; it does not depend on n.
5. **For every** S satisfying comparison boundedness and genuine Condition 5,
   and **every** function b:ℕ→ℝ such that for every n in the positive-joint
   domain b_n is its attained positive minimum, three conclusions hold:
   the domain holds eventually; there exists C≥0 with eventually
   Var_n((n+1)Vhat_n)≤C/[(n+1)b_n]; and, if (n+1)b_n→+∞, centered
   concentration and the lower-tail condition follow. No condition is
   imposed on b_n when its domain is empty.
6. **There exists** S with a nested stable outcome table, all-label positivity,
   Condition 3, genuine Condition 5 and Condition 6, but
   liminf_n coverage_n(α=1/2)<1/2. This witness is not required to satisfy
   the lower-tail condition.

The docstring calls this corrected coverage of the population contrast,
describes the additional lower-tail condition and both joint-probability
rates, and says outcome stability across sizes is unnecessary for the
positive assertions. It says the three original conditions permit failure.

Junk-value audit: n+1>0; the treated/control marginals are strictly positive
by the sequence fields, so neither their HT denominators nor their inverse
probability bounds are made trivial by division by zero. Other unused labels
can have zero marginals in assertions 1–5, but the estimator uses only the
comparison labels. Zero off-diagonal joints use the harmless impossible-event
convention described above. In assertion 5 b_n may be arbitrary outside its
domain, but the conclusion explicitly makes the domain eventual, so eventual
rate bounds do not depend on arbitrary zero denominators. In assertion 4 b>0.
Variances V_n can be zero at initial sizes; no variance ratio or true-variance
studentization occurs. Vhat_n can be negative: Mathlib sqrt then returns 0,
but coverage explicitly requires Vhat_n≥0. For α∈(0,1) the normal quantile
is the genuine finite quantile. Coverage is in [0,1], so real liminf is used
on a bounded sequence and cannot take an unbounded/empty-order fallback.
The structural labels force K_n≥2; normalized positive weights force M_n≥1.
An individual positive-joint domain can be empty (in particular at n=0),
which is expressly handled by the antecedent in assertion 5. The stable-table
existentials use injections into ℕ, without any partial inverse/default.
All sums are finite and all measures implicit in them can be taken discrete;
there are no integrability, log, rpow or infinite `toReal` conventions here.

## SAP.P013a.T3

Location: `SAP/P013a/Challenge/Part1.lean:22`; principal expansion:
`Defs/Part5.lean:97–118`.

This is a closed numerical counterexample conjunction. The actual assignment
space is Fin 4 with exposure vectors (00,01,10,11) having weights
(2/9,4/9,1/9,2/9). There are two units and two labels. The potential outcomes
at label 0 are both 0; at label 1 they are (a,−1). There is **one independent
simulated assignment from the same law**, independent also of the actual
assignment: the joint weight of (z,t)∈Fin 4×Fin 4 is w(z)w(t).
The random estimate is

H_a(z,t)=Σ_{i=0,1} I_i1(z)y_i,D_i(z) / [(I_i1(t)+1)/2].

This is the add-one simulated HT total with R=1. The theorem asserts:

* With a=2, **for every** unit i and label d, 0<p_id<1;
  p_01=1/3, p_11=2/3; T_1=1; E H_2=2/9;
  |(E H_2−1)/1|=7/9; 4/9<7/9 and 1/2<7/9;
  (1−1/3)^(1+1)≤1/2<(1−1/3)^1.
* 1≥log(1/2)/log(1−1/3)−1, yet
  1/2<|(E H_2−T_1)/T_1|.
* With a=1, T_1=0, E H_1=−1/3, and
  |E H_1−T_1|>|T_1|(1−1/3)^(1+1).

There are no universally quantified input experiments or additional
hypotheses. The docstring says the a=2 example refutes the printed relative
bias and replicate rule and the a=1 example refutes the absolute inequality.

Junk-value audit: both designs have positive normalized weights. Every
smoothed denominator is 1/2 or 1. Relative bias occurs only in the a=2
case with total 1. The zero-total case asserts an **absolute** inequality;
no relative ratio at zero is used. log(1/2) and log(2/3) have positive
arguments and log(2/3)≠0. Every exponent is a natural exponent and every
subtraction in the numerical inequalities is real subtraction. Finite sets
are nonempty; no limit, infimum, square root, nonintegrable expectation,
extended real conversion, or partial default occurs.

## SAP.P013a.T4

Location: `SAP/P013a/Challenge/Part1.lean:26`; principal expansion:
`Defs/Part5.lean:120–138`.

The first conjunct quantifies, in order, over an arbitrary type Ω with a
Fintype instance, natural N,K, design w, population (D,y), a proof N>0,
label d∈Fin K with ∀i,0<p_id<1, natural R with R≥1, and real p0 such that
some p_id equals p0 and every p_id≥p0. Let T=Σ_i y_id,
κ=(Σ_i|y_id|)/|T|, and E be the expectation of Htilde_d under the product
weight w(z)Π_r w(zs_r). It asserts all of:

1. E=Σ_i y_id[1−(1−p_id)^(R+1)].
2. E=T−Σ_i y_id(1−p_id)^(R+1).
3. |E−T|≤(1−p0)^(R+1)Σ_i|y_id|.
4. **If T≠0**, then κ≥1, |(E−T)/T|≤κ(1−p0)^(R+1), and both:
   * if all y_id≥0 or all y_id≤0, κ=1 and
     |(E−T)/T|≤(1−p0)^(R+1), and **for every** real b>0,
     R≥log(b)/log(1−p0)−1 implies |(E−T)/T|≤b;
   * **for every** real b>0, without a sign condition,
     R≥log(b/κ)/log(1−p0)−1 implies |(E−T)/T|≤b.

An independent second conjunct asserts the **rational** inequalities
(1999/2000)^(10593+1)≤1/200<(1999/2000)^(10592+1).

The docstring says these are corrected exact expectation, signed absolute
and relative bounds, sign-qualified replication guidance, and a numerical
threshold, using independent simulated assignments.

Junk-value audit: N>0 and attainment of p0 with strict marginal positivity
give 0<p0<1. Thus log(1−p0)<0 and its denominator is nonzero; b>0 and
κ≥1 on the relative-bias branch give b/κ>0. Smoothed probabilities are
strictly positive since counts are nonnegative and R+1>0. κ is totalized
to 0 if T=0, but **every use of κ or relative bias in a conclusion is
guarded by T≠0**. The absolute identities and bound remain meaningful at
T=0. Empty Ω is ruled out by a design, empty unit sets by N>0, empty
labels by the quantified d. The replicate construction permits R=0 in
general (one empty function, product weight 1), but this statement requires
R≥1. Rational division has nonzero denominators 2000 and 200. All powers
are natural powers, all probability expressions are finite real sums,
and no square root, order extremum, limit or partial-function fallback occurs.

## SAP.P013a.T5

Location: `SAP/P013a/Challenge/Part1.lean:30`; principal expansion:
`Defs/Part5.lean:140–165`.

This is a conjunction of six assertions:

1. **For every** N∈ℕ and A,B⊆Fin N with A∩B=∅, the printed no-edge
   predicate for h_ij=1{i=j} holds **iff A=B=∅**.
2. **For every** finite Ω, natural N,K, positive normalized design w and
   map D:Ω→Fin N→Fin K, that same identity matrix satisfies the printed
   dependency condition, its row bound is 1, and **for every** i the exact
   natural row sum is 1. Thus the independence implication puts no
   constraint on the law of D beyond the empty-set case.
3. **For every** q∈ℕ, on Fin(3q) let h_ij=1{i≠j and floor(i/3)=floor(j/3)}.
   This is symmetric, its diagonal is false, for **every** disjoint A,B its
   printed no-edge predicate holds iff A=B=∅, and **every** row sum is
   exactly 2. **For every** finite Ω, label size K, design w and exposure
   map on these units, the printed dependency condition holds for h.
4. **For every** N∈ℕ take Ω=Fin 2 with weights (1/2,1/2) and D_i(z)=z for
   all units, and y_id=0 for all i,d. The identity matrix satisfies printed
   dependency and the row bound 1; every row sum is exactly 1. For all
   i,d, p_id=1/2. For all i,j, p_ij,11=1/2 and pair independence fails,
   including for i=j.
5. **For every** N and Bool matrix g on Fin N, if all false entries imply
   pair independence for this shared law, the total natural number of
   true entries is N².
6. **There exists** a sequence S (as fully expanded above) with all-label
   positivity, uniformly bounded outcomes and inverse marginals
   (Condition 3), and printed Condition 5, but **not** Condition 4.

There are no extra hypotheses relating the exposure law to the supplied
matrices beyond those explicitly stated. The docstring describes vacuity
of the printed dependency definition for the identity and triangle
matrices and a fully shared Bernoulli counterexample to the purported
implication from Condition 5 to Condition 4.

Junk-value audit: N=0 or q=0 gives empty unit types and vacuous individual
row claims, but the universal results include all positive sizes, and the
existential sequence uses n+1 units at every n. It cannot be witnessed by
empty populations. If K=0, a map D on nonempty units and a nonempty sample
space cannot exist; the quantification remains substantive for K=2.
All pair-independence assertions are polynomial identities of finite
probabilities and involve no division. The sequence fields and shared
marginals are nondegenerate. In Condition 3, reciprocal zero would in
isolation be misleading, but all-label positivity is explicitly required
of the witness. Condition 4 divides only by (n+1)²>0; its limit sequence
is a ratio of a finite number of true entries to a positive square.
The graph indices floor(i/3) use natural division by 3; natural subtraction
does not occur. No log, sqrt, rpow, empty/unbounded order extremum,
integrability fallback, extended real conversion or partial default affects
the statement. The “vacuous” graph antecedent is an asserted mathematical
phenomenon here, not vacuity of the entire theorem's assumptions.
