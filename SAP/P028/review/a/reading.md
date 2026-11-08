# Blind mathematical reading

This file was written from `SAP/P028/Defs*.lean`, `SAP/P028/Defs/*.lean`,
`SAP/P028/Challenge*.lean`, `SAP/P028/Challenge/*.lean`, and the Mathlib
definitions below, before opening either `claims.json` or `record.json`.
There are nine stubs: T1, T2, T4, T5, T6, T7, T8, T9, T10. No T3 stub exists.
This is a reading of the propositions, not a reliance on their `sorry` proofs.

## Mathlib semantics and common notation

Booleans are identified with 0 and 1 only when passed through `realBit` (real
values) or `bit` (rational values). `Fin 3` consists of 0,1,2 and `Fin 17` of
0,...,16. Both these finite spaces and Bool have the discrete sigma algebra;
products have the product sigma algebra. All unmarked algebra below is real,
except the explicitly rational finite-law calculations.

Mathlib `Measure` is a countably additive nonnegative extended-real measure.
`IsProbabilityMeasure μ` means μ(Ω)=1. `μ.real E` is `(μ E).toReal`;
infinite extended-real mass would convert to 0, but probability measures here
have no infinite-mass events. `Measurable f` means measurable inverse images.
`Integrable f μ` means almost-everywhere strong measurability and finite integral
of the norm (for real functions, absolute integrability). A set integral is a
Bochner integral against the restricted measure. Mathlib returns 0 for a
nonintegrable Bochner integrand. Its real and rational division is total:
a/0=0. Thus a conditional mean defined below is a genuine conditional mean
only when its event has positive mass. Measurability and global integrability
of both potential outcomes make all their observed selections and restrictions
integrable. Null-event means are totalized values, not asserted ordinary
conditional expectations unless positivity is separately stated.

`IndepFun X Z μ` is independence of the sigma algebras pulled back by X and Z:
for every pair of measurable inverse-image events A,B, μ(A∩B)=μ(A)μ(B).
The definition passes through the constant probability kernel on Unit; it does
not assume any unidentified conditional expectations.

Sources followed: Mathlib `MeasureTheory/MeasurableSpace/Defs.lean` (Measurable),
`MeasurableSpace/Instances.lean` (Bool and Fin),
`Measure/MeasureSpaceDef.lean` and `Measure/Real.lean` (real-valued measure),
`Measure/Typeclasses/Probability.lean` (probability measure),
`Function/L1Space/Integrable.lean` (Integrable),
`Integral/Bochner/Basic.lean` (integral and restricted-integral notation), and
`Probability/Independence/{Basic,Kernel/Indep,Kernel/IndepFun}.lean`
(independence).

### The general causal model

For any type Ω with any measurable-space structure, a model M consists of:

* a probability measure P on Ω;
* measurable S:Ω→{0,1,2}, measurable real Y₀,Y₁:Ω→ℝ, and measurable Z:Ω→{0,1};
* ∫|Y₀|dP<∞ and ∫|Y₁|dP<∞;
* (S,Y₀,Y₁) independent of Z;
* P(Z=z)>0 for **each** z∈{0,1};
* E[D₁−D₀]≠0, where D_z=1 when S=0, D_z=0 when S=1, and D_z=z when S=2.

Write A={S=0}, N={S=1}, C={S=2}, U=Cᶜ=A∪N, G_z={Z=z}.
Observed D=D_Z and Y=Y_D. Thus exclusion and no defiers are built into the
model rather than added as theorem hypotheses. The first stage is E[1_C]≠0.

For any event E put m(f;E)=(∫_E f dP)/P(E), with the totalized convention
above. Put p=P(C), e_z=m(Y;G_z), c_d=m(Y_d;C), n=m(Y;U),
τ=m(Y₁−Y₀;C). Set H_dz={D=d,Z=z}, w_dz=P(H_dz)/P(G_z),
b_dz=m(Y;H_dz), j_dz=m(1_{D=d}Y;G_z), and
k=∫_A Y₁dP+∫_N Y₀dP. `boundedOutcomes` means
**for every** d∈{0,1} and **every** ω∈Ω, 0≤Y_d(ω)≤1 (pointwise, not only a.e.).

A response T is any measurable R:Ω→{0,1}. Put B={R=1},
eᵣ_z=m(Y;G_z∩B), bᵣ_dz=m(Y;H_dz∩B),
v_dz=m(R·1_{D=d}Y;G_z), and
h_dz=P(R=0,D=d,Z=z)/P(G_z). Let P_z=P|G_z/P(G_z),
where scaling and inversion are initially extended-real measure operations.
The model's arm positivity makes P_z the ordinary conditional probability law.
Finally t_dz=w_dz bᵣ_dz if w_dz>0, and t_dz=0 otherwise.

### Scalar systems and intervals

For real p,e₀,e₁ put δ=(e₁−e₀)/p and

* L₀=max(0,−δ,1−(1−e₀)/p), U₀=min(1,1−δ,e₀/p);
* L₁=max(0,δ,1−(1−e₁)/p), U₁=min(1,1+δ,e₁/p).

The mixture system Q(p,e₀,e₁,x₀,x₁) is
∃n∈ℝ: px₀+(1−p)n=e₀, px₁+(1−p)n=e₁,
0≤x₀≤1, 0≤x₁≤1, 0≤n≤1.
The corrected system K is px₀+e₁−px₁=e₀, 0≤x₀,x₁≤1,
0≤e₁−px₁≤1−p. The printed system J has the same conditions except that
its final upper bound is 1. All subtraction in these definitions is ordinary
real subtraction.

## SAP.P028.T1

This theorem has no parameters or hypotheses: it asserts the following
conjunction about two fixed rational laws L and U. A rational law is any list
of 17 atoms (d₀,d₁,y₀,y₁,r₀,r₁) of Boolean potential values with 17 rational
weights. Repeated atoms are allowed. The actual lists are transcribed below.
Define α₀=99/200, α₁=101/200, and give (i,z) weight m_i α_z.
For a subset E of the 17 indices let P_f(E)=Σ_{i∈E}m_i, E_f f=Σ_i m_i f(i),
and m_f(f;E)=Σ_{i∈E}m_i f(i)/P_f(E). At assignment z set D=d_z,
Y=y_{d_z}, R=r_z. C means d₀=0,d₁=1.

`finiteValid` means every one of the 17 masses is strictly positive, their
sum is 1, d₀≤d₁ for every atom, E_f(d₁−d₀)=P_f(C), and P_f(C)>0.
The theorem asserts:

1. Both L and U are finiteValid and have p=2047/9999; α₀,α₁ have the
   stated values and are strictly positive. For each law, all 34 joint
   weights m_iα_z are positive and sum to 1.
2. For **each** M in the two-element list [L,U], every respondent arm
   P_f(r_z=1), every treatment cell P_f(d_z=d), and every respondent
   treatment cell P_f(d_z=d,r_z=1) has positive mass, for all relevant d,z.
3. For **each** M∈[L,U], **every** subset E of the 17 indices and
   **every** z, Σ_{i∈E}m_iα_z=P_f(E)α_z. This explicitly records randomized
   assignment independent of the latent atom.
4. For **every** z,d,v, P_f(D=d,R=1,Y=v | assignment z), computed in either
   law, is the corresponding recorded count divided by arm count; for
   **every** z,d the same holds for P_f(D=d,R=0 | assignment z):

   |z|d|recorded Y=0|recorded Y=1|missing|arm count|
   |--|--|--|--|--|--|
   |0|0|212|167|36|495|
   |0|1|39|40|1|495|
   |1|0|164|130|26|505|
   |1|1|67|110|8|505|

5. The two entire observed joint laws on (Z,D,R,RY) agree as functions
   {0,1}⁴→ℚ. Explicitly each value is α_z times
   P_f(d_z=d,r_z=r,r_z·y_{d_z}=v). Their complier means are
   (c₀,c₁)_L=(1423/10235,6749/10235),
   (c₀,c₁)_U=(7633/10235,7642/10235), and the means differ in both coordinates.
6. For **each** M∈[L,U], w₁₀=16/99, w₀₁=64/101,
   eᵣ₀=207/458, eᵣ₁=240/471, bᵣ₁₀=40/79, bᵣ₀₁=130/294.
   The full arm means are (208/495,266/505) in L and (27/55,248/505) in U.
7. Define G(p,q,r,e₀,e₁,a,n)=((e₀−qa−rn)/p,
   (e₀−qa−rn)/p+(e₁−e₀)/p). Substituting the full p,w₁₀,w₀₁,e₀,e₁,b₁₀,b₀₁
   yields the actual two complier means in each law. Substituting respondent
   eᵣ₀,eᵣ₁,bᵣ₁₀,bᵣ₀₁, while retaining full p,w₁₀,w₀₁, instead yields
   (1594452863/3629163146,896530960/1244058109) in both laws, different from
   the actual complier pair in either law.
8. For **each** d∈{0,1}, there does **not** exist a function
   F:({0,1}⁴→ℚ)→ℚ such that **for every** 17-index rational law M,
   finiteValid(M) implies F(observedLaw(M))=c_d(M). The order is
   ∀d ¬∃F ∀M; F may depend on d, but cannot depend on M except through
   its observed law. This is a nonexistence result already on this finite class.

The fixed lowerLaw table (bits in order d₀,d₁,y₀,y₁,r₀,r₁):

|i|atom|mass|
|--|--|--|
|0|(1,1,0,0,1,0)|104/12375|
|1|(1,1,0,0,1,1)|871/12375|
|2|(0,0,0,0,0,1)|738/15655|
|3|(0,0,0,0,1,1)|4346/15655|
|4|(1,1,0,1,0,1)|1/495|
|5|(1,1,0,1,1,1)|8/99|
|6|(0,0,1,0,1,0)|26/505|
|7|(0,0,1,0,1,1)|26/101|
|8|(0,1,0,0,0,0)|40958176/44062954375|
|9|(0,1,0,0,0,1)|343024724/44062954375|
|10|(0,1,0,0,1,0)|2170783328/396566589375|
|11|(0,1,0,0,1,1)|18180310372/396566589375|
|12|(0,1,0,1,0,1)|29736094/1762518175|
|13|(0,1,0,1,1,1)|1576012982/15862663575|
|14|(0,1,1,0,1,0)|13228208/12792470625|
|15|(0,1,1,0,1,1)|110786242/12792470625|
|16|(0,1,1,1,1,1)|9603827/511698825|

The fixed upperLaw table (bits in order d₀,d₁,y₀,y₁,r₀,r₁):

|i|atom|mass|
|--|--|--|
|0|(1,1,0,0,0,1)|1/495|
|1|(1,1,0,0,1,1)|13/165|
|2|(0,0,0,0,1,0)|26/505|
|3|(0,0,0,0,1,1)|164/505|
|4|(1,1,0,1,1,0)|32/5841|
|5|(1,1,0,1,1,1)|40/531|
|6|(0,0,1,0,0,1)|936/20503|
|7|(0,0,1,0,1,1)|4342/20503|
|8|(0,1,0,0,1,1)|6746986/511698825|
|9|(0,1,0,1,1,0)|79537936/30190230675|
|10|(0,1,0,1,1,1)|19884484/548913285|
|11|(0,1,1,0,0,1)|79169476/11541651275|
|12|(0,1,1,0,1,1)|3305325623/103874861475|
|13|(0,1,1,1,0,0)|933302176/680957425225|
|14|(0,1,1,1,0,1)|233325544/12381044095|
|15|(0,1,1,1,1,0)|38965365848/6128616827025|
|16|(0,1,1,1,1,1)|9741341462/111429396855|


## SAP.P028.T2

For **every** type Ω, **every** measurable-space structure on Ω,
**every** causal model M on Ω, and **every** measurable response R, assume
pointwise 0≤Y₀,Y₁≤1. The theorem asserts all of the following:

1. p>0 and p=1−w₁₀−w₀₁.
2. pc₀=j₀₀−j₀₁ and pc₁=j₁₁−j₁₀.
3. If w₁₀>0, w₀₁>0, both P(G_z∩B)>0, P(H₁₀∩B)>0,
   P(H₀₁∩B)>0, both eᵣ_z=e_z, and bᵣ₁₀=b₁₀, bᵣ₀₁=b₀₁, then
   c₀=(eᵣ₀−w₁₀bᵣ₁₀−w₀₁bᵣ₀₁)/p and
   c₁=c₀+(eᵣ₁−eᵣ₀)/p.
4. If P(G_z∩B)>0 for **every** z and R is independent of (Y,D) under
   P_z for **every** z, then eᵣ_z=e_z for **every** z. Furthermore,
   if w₁₀>0 and w₀₁>0, then all the mean equalities and response-positivity
   statements in item 3 hold, and both displayed identification formulas hold.
5. If for **every** d,z with w_dz>0 one has P(H_dz∩B)>0 and
   bᵣ_dz=b_dz, then e_z=Σ_{d∈{0,1}}t_dz for **every** z,
   c₀=(t₀₀−t₀₁)/p, and c₁=(t₁₁−t₁₀)/p.
6. Without further response hypotheses,
   (v₀₀−v₀₁−h₀₁)/p ≤ c₀ ≤ (v₀₀+h₀₀−v₀₁)/p and
   (v₁₁−v₁₀−h₁₀)/p ≤ c₁ ≤ (v₁₁+h₁₁−v₁₀)/p.

Outside that universal implication, the theorem also asserts these eight
real arithmetic identities, independently of Ω or the existence of any M:

* (167/495−130/505−26/505)/(2047/9999)=1423/10235;
* (167/495+36/495−130/505)/(2047/9999)=7633/10235;
* (110/505−40/495−1/495)/(2047/9999)=6749/10235;
* (110/505+8/505−40/495)/(2047/9999)=7642/10235;
* (207/458−(16/99)(40/79)−(64/101)(130/294))/(2047/9999)
  =1594452863/3629163146;
* the preceding left side plus (240/471−207/458)/(2047/9999)
  =896530960/1244058109;
* ((415/495)(167/379)−(320/505)(130/294))/(2047/9999)=16568969/38014837;
* ((185/505)(110/177)−(80/495)(40/79))/(2047/9999)=295510/414829.

## SAP.P028.T4

For **every** real p,e₀,e₁,x₀,x₁, assume 0<p and p<1 (no bounds on e₀,e₁
or x₀,x₁ are assumed). All the following hold jointly:

1. Q↔K.
2. For **every** real n, px₁+(1−p)n=e₁ implies n=(e₁−px₁)/(1−p).
3. px₀+e₁−px₁=e₀ iff x₀=x₁−δ.
4. If x₀=x₁−δ, then 0≤x₀≤1 iff δ≤x₁≤1+δ.
5. 0≤e₁−px₁≤1−p iff (e₁+p−1)/p≤x₁≤e₁/p.
6. (e₁+p−1)/p=1−(1−e₁)/p.
7. Q iff x₀=x₁−δ and L₁≤x₁≤U₁.
8. L₁−δ=L₀ and U₁−δ=U₀.
9. 0≤e₁−px₁≤1 iff (e₁−1)/p≤x₁≤e₁/p.
10. If e₁≤1 and x₁≥0, then (e₁−1)/p≤x₁, and
    (0≤e₁−px₁≤1 iff x₁≤e₁/p).
11. Q implies J.

In a separate unconditional conjunct, J(1/2,3/4,3/4,0,0) holds whereas
Q(1/2,3/4,3/4,0,0) does not. Thus the universal implication in item 11
is strict somewhere, not asserted strict for every choice of input moments.

## SAP.P028.T5

There are no hypotheses. At p=1/2,e₀=e₁=3/4,x₀=x₁=0, J holds, Q fails,
K fails, (e₁−px₁)/(1−p)=3/2, (e₁−1)/p=−1/2,
(e₁+p−1)/p=1/2, L₀=L₁=1/2, U₀=U₁=1.
Additionally, **there exists** a causal model M on Bool×Bool, with its
discrete product measurable space, with pointwise outcomes in [0,1],
p=1/2, e₀=e₁=3/4, and c₀=c₁=1. The existential model is not required
to have any specified composition of A versus N, assignment probability,
or off-complier potential values beyond the causal-model conditions.

## SAP.P028.T6

For **every** type Ω, **every** measurable-space structure, and **every** causal
model M on it, assume pointwise bounded outcomes. Then:

1. 0<p≤1; 0≤k≤1−p; for **every** z, e_z=pc_z+k;
   and k=j₁₀+j₀₁.
2. If p<1, P(U)=1−p>0, k=(1−p)n and 0≤n≤1.
3. If p=1, k=0, c₀=e₀ and c₁=e₁.
4. For **every** z, c_z=(e_z−k)/p.
5. For **every** d, 0≤c_d≤1.
6. For **every** z, 0≤e_z−pc_z≤1−p and
   1−(1−e_z)/p≤c_z≤e_z/p.
7. L₀(p,e₀,e₁)≤c₀≤U₀(p,e₀,e₁),
   L₁(p,e₀,e₁)≤c₁≤U₁(p,e₀,e₁), and c₁=c₀+δ(p,e₀,e₁).

Separately, for **every** real e₀,e₁ satisfying 0≤e₀≤1 and 0≤e₁≤1,
L₀(1,e₀,e₁)=U₀(1,e₀,e₁)=e₀ and
L₁(1,e₀,e₁)=U₁(1,e₀,e₁)=e₁. These arithmetic endpoint identities do
not depend on existence of M on the universally quantified Ω.

## SAP.P028.T7

This has no parameters or hypotheses. It uses a fixed atom with
(d₀,d₁,y₀,y₁,r₀,r₁)=(0,1,0,1,1,1), and a two-point rational sample
space indexed by z=0,1, each of weight 1/2. All probabilities and means
in the next sentences are finite sums and normalized sums on this space.

It asserts total probability 1, both arm probabilities 1/2, d₀≤d₁,
0≤y₀,y₁≤1, E(d₁−d₀)=1, P(C)=1, arm means (0,1), complier means
(0,1), P(d₁=d₀)=0, 1−P(C)=0, 1−P(C)·1=0,
P(D=1,Z=0)=P(D=0,Z=1)=0. It asserts for **every** real n that
1·0+(1−1)n=0 and 1·1+(1−1)n=1, and for **every** real a,n that
0a+0n=0.

Additionally, for **every** predicate E on all six-bit atoms and **every**
z, P(E(fixed atom)∧Z=z)=P(E(fixed atom))P(Z=z), explicitly giving
randomization; for **every** z, D_z=z and Y_{D_z}=z. Define
q=P(D=1,Z=0)/P(Z=0) and r=P(D=0,Z=1)/P(Z=1).
It asserts q=r=q+r=0 and, for **every** rational a,n, qa+rn=0.
Finally L₀(1,0,1)=U₀(1,0,1)=0 and L₁(1,0,1)=U₁(1,0,1)=1.
The theorem does not form a conditional mean of a null noncomplier event;
the arbitrary-n equations express that the mixture equations do not determine it.

## SAP.P028.T8

For **every** type Ω and measurable-space structure the theorem asserts two
conjuncts. First, for **every** causal model M on Ω, pointwise bounded
outcomes imply p>0, L₀≤c₀≤U₀, L₁≤c₁≤U₁ and c₁=c₀+δ.

Second, independently of Ω, for **every** real p,e₀,e₁, assuming
0<p≤1, 0≤e₀≤1, 0≤e₁≤1 and |e₁−e₀|≤p, one has L₀≤U₀ and L₁≤U₁,
and both of these attainment assertions:

* For **every** real x₁ with L₁≤x₁≤U₁, **there exists** a causal model
  on Bool×Bool with pointwise bounded outcomes, p(M)=p, e₀(M)=e₀,
  e₁(M)=e₁, c₁(M)=x₁ and c₀(M)=x₁−δ.
* For **every** real x₀ with L₀≤x₀≤U₀, **there exists** a causal model
  on Bool×Bool with pointwise bounded outcomes, the same three specified
  input moments, c₀(M)=x₀ and c₁(M)=x₀+δ.

The two existential witnesses may depend on all preceding scalar parameters
and the chosen coordinate; no single M must attain all coordinate choices.
No observable treatment-cell probabilities or other data are fixed in these
attainment statements. Full compliance p=1 is included.

## SAP.P028.T9

For **every** type Ω, **every** measurable-space structure, and **every** causal
model M on it (global absolute integrability of both potentials remains part
of M, but no [0,1] outcome bound is assumed), suppose **every** one of the
four H_dz has positive probability. Then p>0, P(A)>0, P(N)>0, P(U)>0,
w₁₀+w₀₁>0, and, for **every** z, e_z=Σ_d w_dz b_dz. Moreover:

* w₁₀=P(A), w₀₁=P(N), p=1−w₁₀−w₀₁;
* b₁₀=m(Y₁;A), b₀₁=m(Y₀;N);
* n=(w₁₀b₁₀+w₀₁b₀₁)/(w₁₀+w₀₁);
* c₀=(e₀−w₁₀b₁₀−w₀₁b₀₁)/p;
* c₁=c₀+(e₁−e₀)/p;
* c₁=(e₁−w₁₀b₁₀−w₀₁b₀₁)/p.

All conditional-mean and displayed ratio events here have positive mass under
the model and positive-cell premise.

## SAP.P028.T10

For **every** type Ω and **every** measurable-space structure, first for
**every** causal model M on Ω (integrable real potential outcomes, without
requiring boundedness), all these identities hold:

* m(D;G₁)−m(D;G₀)=p and p>0;
* e₁−e₀=pτ;
* τ=(e₁−e₀)/p;
* τ=(e₁−e₀)/(m(D;G₁)−m(D;G₀)).

The model's nonzero unconditioned potential-treatment first stage and
randomization ensure all denominators here are nonzero.

Second, independently of Ω, **there exist** two causal models M₀,M₁ on
Bool×Bool, both with pointwise [0,1] outcomes, both with p=1/2,
e₀=e₁=3/4 and τ=0, but c₀=c₁=1/2 in M₀ and c₀=c₁=1 in M₁.
This nonidentification assertion holds the three scalar figures p,e₀,e₁
fixed; it does not require equality of the full observed laws of (Z,D,Y).
