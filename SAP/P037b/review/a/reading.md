# Blind reading

Saved before opening `claims.json` or `record.json`. This is a reading of the actual theorem types, not of their summaries or restriction declarations. Each Challenge theorem is the corresponding `TxxStatement` below. All displayed conjuncts belong to the assertion. Universally quantified parameters in separate conjuncts are independent.

## Underlying definitions and conventions

`Fin n` is the set of integers 0 through n−1. Matrices and vectors are functions on the indicated finite index sets; equality is entrywise. `dotProduct v w` is Σᵢvᵢwᵢ; `Matrix.mulVec M v` has entries ΣⱼMᵢⱼvⱼ. Matrix multiplication, transpose, diagonal, identity, scalar multiplication and subtraction have their ordinary real meanings. These definitions were followed into Mathlib's `Data/Matrix/Mul.lean` (dot product and matrix-vector product), `LinearAlgebra/Matrix/Defs.lean` (transpose), and `Data/Matrix/Diagonal.lean` (diagonal).

For an n×k real X, put A(X)=(XᵀX)⁻¹Xᵀ, H(X)=XA(X), b(X,y)=A(X)y, e(X,y)=y−Xb(X,y), and C(X,y)=A(X)diag(e(X,y)²)A(X)ᵀ. The inverse is Mathlib's determinant/adjugate inverse, **zero for a singular matrix**, not a pseudoinverse (`LinearAlgebra/Matrix/NonsingularInverse.lean`, lines 164–176). Where specified, injectivity of the map v↦Xv means full column rank and makes XᵀX nonsingular. A quadratic form Q(V,l) is lᵀVl.

For a real random vector v on (Ω,μ), M(v)ⱼ=∫vⱼdμ and Cov(v)ⱼₗ=∫(vⱼ−M(v)ⱼ)(vₗ−M(v)ₗ)dμ. These are coordinatewise Bochner integrals. Mathlib sets a nonintegrable Bochner integral to zero (`MeasureTheory/Integral/Bochner/Basic.lean`, lines 148–163 and 204). The explicit first- and second-product-integrability assumptions below are therefore substantive. `IsProbabilityMeasure μ` means μ(Ω)=1 (`MeasureTheory/Measure/Typeclasses/Probability.lean`, lines 63–66).

A `ProbabilityDesign Ω` is a finite type Ω with a real mass p(z)>0 for **every** z, with Σzp(z)=1. Thus Ω cannot be empty and contains only positive-mass states. Write P(E)=Σzp(z)1_E(z) and E_P f=Σzp(z)f(z). No measurability or analytic integrability issue arises in these sums. A product sample z:Fin J→Ω is given mass ∏ⱼp(zⱼ), encoding independent draws. Arbitrary specified draws in deterministic clauses need not be random, but are states of this full-support Ω.

Finite sets have their ordinary membership, cardinality, intersection, difference, disjointness, and image. `univ.powersetCard m` contains exactly the m-element subsets, and its cardinality is the binomial coefficient (`Data/Finset/Powerset.lean`, lines 198–214). `Nat.choose n m` is zero for m>n and positive for m≤n (`Data/Nat/Choose/Basic.lean`, lines 85 and 117). Natural-number subtraction is truncated; subtraction after a real cast is real subtraction. Real division is total, with x/0=0. Empty sums and products are 0 and 1.

The fixed six-group regression data are, in group order 0,…,5:

| quantity | entries |
|---|---|
| multiplicities N | (14,14,7,7,7,7) |
| treatment T | (0,0,1,1,1,1) |
| composition R | (0,0,0,0,1/5,1/5) |
| outcome Y | (0,1/5,1/10,3/10,2/5,3/5) |

Rows xᵢ=(1,Tᵢ,TᵢRᵢ); b=(1/10,1/10,3/2). G=ΣᵢNᵢxᵢxᵢᵀ, rhs=ΣᵢNᵢxᵢYᵢ, meat=ΣᵢNᵢ(Yᵢ−xᵢᵀb)²xᵢxᵢᵀ. The named matrices are

Ginv=[[1/28,−1/28,0],[−1/28,3/28,−5/14],[0,−5/14,25/7]],

V=[[1/2800,−1/2800,0],[−1/2800,3/2800,−1/280],[0,−1/280,1/28]].

Centered rows are xcᵢ=(1,Tᵢ,Tᵢ(Rᵢ−1/10)); bc=(1/10,1/4,3/2); Gcinv=[[1/28,−1/28,0],[−1/28,1/14,0],[0,0,25/7]]. Gc and meatc use these centered rows and bc in the same formulas.

For four schools i=0,…,3, potential outcomes are Yᵢ(t)=3i/100+3·1_t/100. The six assignments z=0,…,5 treat pairs {0,1},{0,2},{0,3},{1,2},{1,3},{2,3}, respectively. Observed Y uses this treatment. A school is kept iff observed Y>1/50. KT and KC are the kept treated and kept controls. Δ(z)=Σ_KT Y/|KT|−Σ_KC Y/|KC|, w(z)=|KT||KC|/(|KT|+|KC|). R_B(z)=Σ_bw(z_b)Δ(z_b)/Σ_bw(z_b), also defined at B=0 by real division's convention.

For local seed examples, L(self,peers,refs,s)∈{0,1,2,3,4} is: 4 if s intersects self; otherwise 1 if s misses peers; otherwise 2 if s misses refs; otherwise 3. It never returns 0. The five-label probability function is π₀=1/2 and, for k≠0, π_k=number of m-subsets s with L(s)=k divided by 2·choose(n,m). In the stated examples the seed count is feasible. The four-label screens below use labels 0,1,2,3, excluding 4.

For π:I→{0,1,2,3}→ℝ, positive population F(π)={i:∀k,0<πᵢₖ<1}; cutoff F_c(π)={i:∀k,c<πᵢₖ}. Given assignment z and four arbitrary predicate masks seed, outcome, baseline, screen, analysis set S(z)={i∈F_.01(estimated):¬seed(z,i) and outcome(z,i) and baseline(z,i) and screen(z,i)}.

Blocked avoidance B(n,t,m)=(1/2)∏ₕ choose(nₕ−mₕ,tₕ)/choose(nₕ,tₕ). Here the subtraction inside choose is natural subtraction. In the general probability identity mₕ is the cardinality of a subset of Fin(nₕ), so mₕ≤nₕ; tₕ≤nₕ is explicitly assumed.

The rare design has Ωrare=Bool×∏ₕ₌₀³{s⊆{0,…,9}:|s|=5}, mass 1/(2·252⁴) per state. Label is 0 if the Boolean is false; if true, 1 when both s₀ and s₁ avoid {0,…,4}; otherwise 3 if 0∈s₀, and 2 otherwise. πrare(k) is the finite weighted label probability.

Blocked school support A_B consists of subsets of {0,…,B−1}×{0,1,2,3} with exactly two selections per block. Its mass is 6^(−B) on support and zero elsewhere (the exponent is an integer). Uniform school support U(n,m) is all m-subsets of Fin n, and its event probability is the event count divided by choose(n,m).

For a Boolean directed graph B, U(B)ᵢⱼ=Bᵢⱼ∨Bⱼᵢ; indegree dⱼ counts incoming true entries. Sort d increasingly. The quantile is the linear interpolation at h/10, h=9(n−1): (10−h mod 10)/10 times sorted[floor(h/10)] plus (h mod 10)/10 times the next entry; out-of-range list values default to 0. Referents Γ(B)={j:dⱼ>quantile}, using a strict inequality. For seeds s, total seed peers t counts j∈s with Bᵢⱼ; referent seed peers r additionally require j∈Γ. Nonseed label l(t,r) is 0 if t=0, 1 if t>0 and r=0, and 2 otherwise. Network labels apply that rule to these two counts.

B10 has edges 1→0, 2→1, 3→1 only. B20 has edges 1→0, 0→2, 0→4, a→1 for a=8,…,13, and a→2 for a=14,…,19 only. Eligible seeds E=(1,2,4,5,6,7). For either input graph B on 20 vertices, graph probability at 0 is 1/2 for control label 0, and for k=1,2,3 is the count of three-element subsets of these six eligible vertices whose network label at vertex 0 equals k−1, divided by 40. The referent set stays Γ(B20) even when B=U(B20).

## SAP.P037b.T18

The assertion is a conjunction of four universally quantified statements.

1. For every measurable Ω, probability measure μ, n,k∈ℕ, real n×k matrix X, response y∈ℝⁿ, injectivity of X.mulVec, and v:Ω→ℝⁿ, assume every vᵢ and every vᵢvⱼ is integrable, M(v)=0, and ∫vᵢvⱼ=1 if i=j and 0 otherwise. Set b=Ay and b*(ω)=A(Xb+(eᵢvᵢ(ω))ᵢ). Then for every ω, b*=b+A(eᵢvᵢ)ᵢ; M(b*)=b; Cov(b*)=C(X,y). Independence of the vᵢ is not assumed.
2. For every n,k,X of full column rank with n>0, Hᵀ=H, H²=H, every diagonal Hᵢᵢ belongs to [0,1], ΣᵢHᵢᵢ=k, and ΣᵢHᵢᵢ/n=k/n.
3. For every measurable Ω, probability μ, n,k,X of full column rank, β∈ℝᵏ, σ²∈ℝ with σ²≥0, and u:Ω→ℝⁿ, assume every uᵢ and uᵢuⱼ is integrable, M(u)=0 and ∫uᵢuⱼ=σ² if i=j, 0 otherwise. Put y(ω)=Xβ+u(ω), V=Cov(Ay), EVⱼₗ=∫C(X,y(ω))ⱼₗdμ. For every ω, e(X,y(ω))=(I−H)u(ω); for every i, ∫eᵢ²=σ²(1−Hᵢᵢ); V=σ²AAᵀ=σ²(XᵀX)⁻¹; EV=σ²A diag(1−Hᵢᵢ)Aᵀ; V−EV=σ²A diag(Hᵢᵢ)Aᵀ; and for every t∈ℝᵏ, tᵀ(V−EV)t≥0.
4. For every n and real vectors a,h, assuming 0≤hᵢ≤1 for every i and S=Σᵢaᵢ²>0, Σaᵢ²(1−hᵢ)/S=1−Σaᵢ²hᵢ/S≤1. This ratio equals 1 iff for every i, aᵢ≠0 implies hᵢ=0.

## SAP.P037b.T19

For the fixed four-school construction: every individual treatment effect is 3/100; for every z,i, i is kept iff i≠0 or 0 is treated. For every z, |KT|=2 and |KC| has table (2,2,2,1,1,1); Δ has table (−3/100,0,3/100,−3/200,3/100,3/40); w has table (1,1,1,2/3,2/3,2/3). Under uniform averaging of the six states, EΔ=3/200≠3/100, Ew=5/6, E(wΔ)=1/100, and E(wΔ)/Ew=3/250≠3/100.

For every ε>0, as B→∞ through naturals, Σ_{z∈{0,…,5}^B}6^(−B)1{|R_B(z)−3/250|>ε}→0. This is an ordinary real limit (`Filter.Tendsto` at `atTop` to the neighborhoods of 0), i.e. convergence in probability under the product uniform assignment laws. The B=0 term is allowed, but the conclusion concerns the tail.

For all real nT,nC,yT,yC with nT>0,nC>0, nT(1−nT/(nT+nC))²+nC(nT/(nT+nC))²=nTnC/(nT+nC), and (1−nT/(nT+nC))yT−(nT/(nT+nC))yC=[nTnC/(nT+nC)](yT/nT−yC/nC). Finally, every nonempty subset of the four schools has average potential treatment effect 3/100.

## SAP.P037b.T20

For every finite Ω,I, every type K with decidable equality (not necessarily finite), full-support probability design P on Ω, exposure map D:Ω×I→K, Boolean variable inclusion A:Ω×I→Bool, outcomes y:I×K→ℝ and Boolean fixed inclusion a:I→Bool, all three following conclusions hold:

* For every d∈K and i∈I with πᵢ(d)=P(Dᵢ=d)>0, E[aᵢ1{Dᵢ=d}yᵢ(d)/πᵢ(d)]=yᵢ(d) when aᵢ is true, and 0 otherwise.
* For every d, if all included i have πᵢ(d)>0 and the fixed included set F={i:aᵢ=true} is nonempty, E[(Σᵢaᵢ1{Dᵢ=d}yᵢ(d)/πᵢ(d))/|F|]=(Σ_{i∈F}yᵢ(d))/|F|. Positivity is not required for excluded units, whose numerator is zero.
* For every d,i with πᵢ(d)>0, E[Aᵢ1{Dᵢ=d}yᵢ(d)/πᵢ(d)]=yᵢ(d)P(Aᵢ=true,Dᵢ=d)/πᵢ(d).

Separately, for arbitrary types Ω,I and Y:Ω×I→ℝ, assume for every i either Y(z,i)>1/50 for all z, or Y(z,i)≤1/50 for all z. Then for every z,z′,i, Y(z,i)>1/50 iff Y(z′,i)>1/50.

## SAP.P037b.T21

All assertions concern explicitly fixed seed examples; there are no external hypotheses. There are choose(12,6)=924 seed sets. For self=∅, peers={0,…,5}, refs={0}, the five probabilities are (1/2,1/1848,461/1848,1/4,0). The first four lie strictly between 0 and 1, and 0<1/1848<1/100. For self={2}, peers={0,1}, refs={0}, probabilities are (1/2,1/22,3/44,3/22,1/4), and each of the first four exceeds 1/100. Both s={2,3,4,5,6,7} and s′={3,4,5,6,7,8} are supported six-seed sets; their second-example treated labels are 4 and 1, respectively.

There exists a sequence of 10000 pairs (Boolean,seed set), every set having six elements, such that the first example's unconditional four label frequencies (Boolean false means label 0; true means L) are (1/2,1/2000,499/2000,1/4). No independence or probability distribution on this existential sequence is asserted.

The treated-only five-label counts over all 924 subsets are respectively (0,1,461,462,0) and (0,84,126,252,462). The first example's first-four probability sum is 1; the second example's five-probability sum is 1. All four exhibited sequence frequencies are positive, and 1/2000<1/100.

## SAP.P037b.T22

1. For every finite full-support design P on Ω, arbitrary type I, D:Ω×I→Fin 5, integer J>0, arbitrary draws:Fin J→Ω, four arbitrary predicate masks, and z∈Ω, set πᵢₖ=P(Dᵢ=k), and phatᵢₖ=number of draws with Dᵢ=k divided by J, for k=0,1,2,3 (`castSucc` preserves k's value). Then F(π)=F₀(π); F_.01(π)⊆F(π); F_.01(phat)⊆F₀(phat); F₀(phat)⊆F(π); S(z)⊆F(π); and S(z)⊆{i:¬seed(z,i)}.
2. For every finite full-support design and event E with 0<P(E)<1, the product-law probability that at least 101 of 10000 independent draws hit E lies strictly between 0 and 1.
3. For every finite full-support design, arbitrary I, arbitrary real estimated array and predicate masks, and i∈I, P(seed(z,i))≤P(i∉S(z)).
4. For every natural r≤10000, r/10000>1/100 iff r≥101; if r≥101, then 1/(r/10000)≤10000/101<100.

## SAP.P037b.T23

This is an unconditional finite numerical certificate for the fixed six groups. ΣN=56 and ΣNT=28; Ginv·G=I; Gb=rhs; every |Yᵢ−xᵢᵀb|=1/10; Ginv·meat·Ginvᵀ=V.

Writing l0=(1,0,0), l1=(1,1,1/10), d=(0,1,1/10), it asserts l0ᵀb=1/10; l1ᵀb=7/20; Q(V,l0)=Q(V,l1)=1/2800; Q(V,d)=1/1400; l0ᵀVd=−1/2800. It also asserts the scalar identities ((28/100)/27)/56=1/5400, 1/1400>1/2800, 1/5400<1/2800, (1/5400)/(1/2800)=14/27, and ((28/100)/27)/28≠1/2800.

For centered quantities, Gcinv·Gc=I, Gc bc is the centered normal RHS, every fitted value xcᵢᵀbc equals xᵢᵀb, and entry (1,1) of Gcinv·meatc·Gcinvᵀ is 1/1400. The displayed 1/5400 is a scalar arithmetic expression; no residual sample mean or sample variance is defined in the theorem.

## SAP.P037b.T24

1. For every p∈ℕ, real covariate row zbar indexed by Fin p, coefficient vector b indexed by Fin 3 disjoint-union Fin p, and c∈ℝ, rows l0=(1,0,0,zbar) and l1=(1,1,c,zbar) satisfy l0ᵀb=b0+Σzbarⱼbⱼ, l1ᵀb=b0+b1+cb2+Σzbarⱼbⱼ, and (l1−l0)ᵀb=b1+cb2.
2. For every k∈ℕ, symmetric real k×k matrix V and vectors l0,d∈ℝᵏ, Q(V,l0+d)=Q(V,l0)+Q(V,d)+2l0ᵀVd, and Q(V,l0+d)=Q(V,d) iff Q(V,l0)+2l0ᵀVd=0. Positive semidefiniteness is not required.
3. For every n,p∈ℕ, real data T,C,y indexed by Fin n, n×p covariate matrix z, and c∈ℝ, let X have columns (1,T,TC,z), Xc columns (1,T,T(C−c),z), and b=A(X)y, bc=A(Xc)y, V=C(X,y). If X.mulVec is injective, then Xc bc=Xb, e(Xc,y)=e(X,y), bc1=b1+cb2, and C(Xc,y)11=V11+2cV12+c²V22. T need not be binary; n and p have no positivity premise beyond what injectivity forces.

## SAP.P037b.T25

For the fixed graphs and seed laws: B10 has quantile 11/10 and referents {1}; vertex 0 with seeds {1} has directed network label 0 and union-graph network label 2, with referents held fixed. B20 has quantile 3/2 and referents {1,2}; its four probabilities are (1/2,1/10,3/20,1/4), versus (1/2,1/40,3/40,2/5) for its union graph. Every probability in each vector lies in (0,1).

The indegree vectors are (1,2,0,0,0,0,0,0,0,0) and (1,6,7,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0). Both graphs have no loops; no indegree equals the relevant quantile. At B10's vertex 0, total and referent seed counts for {1} are (0,0) directed and (1,1) under union. At B20's vertex 0 the directed peers are {2,4}, union peers {1,2,4}. There are 20 three-subsets of the six eligible vertices. Their four shifted-label histograms (including an unused index 0) are (0,4,6,10) and (0,1,3,16). For each noncontrol k=1,2,3, the two probabilities differ and their reciprocals differ. These are unconditional finite assertions.

## SAP.P037b.T26

1. For every n∈ℕ and Boolean B on Fin n with no diagonal true entries, U(B) is symmetric, has no diagonal true entries, contains every directed true entry, and for every i,j, [U(B)ᵢⱼ=true and Bᵢⱼ=false] iff [Bⱼᵢ=true and Bᵢⱼ=false].
2. For every n, Boolean B and Boolean masks z,γ on Fin n and i∈Fin n, the union seed count is the outgoing count plus the incoming-only count. The same equality holds with γ additionally required in all three counts. These are sums of natural 0/1 indicators; no no-loop premise is present here.
3. For every c,b,r,q∈ℕ with r≤c and q≤b, l(c,r)=l(c+b,r+q) iff (c>0 or b=0) and (r>0 or q=0). Further, l(c+b,r+q)=0 implies l(c,r)=0, and l(c,r)=2 implies l(c+b,r+q)=2.
4. For every finite Ω, positive real weights p summing to 1, natural-valued functions c,b,r,q on Ω satisfying r(z)≤c(z), q(z)≤b(z) everywhere, P(l(c+b,r+q)=0)≤P(l(c,r)=0) and P(l(c,r)=2)≤P(l(c+b,r+q)=2). The first inequality is strict if some state changes from label 0 to a different label; the second is strict if some state changes from a label other than 2 to label 2. These probabilities are finite indicator sums, and every state has positive weight.

## SAP.P037b.T29

For Ωrare the total mass is 1; the four probabilities are (1/2,1/127008,31751/127008,1/4), all in (0,1). For every natural r (no upper bound), |r/10000−πrare(1)|≥πrare(1)>πrare(1)/2 in the sense that both the nonstrict first bound and the strict half bound are asserted.

For product-law 10000 draws, H counts label-1 hits: EH=625/7938; P(H=0)=(127007/127008)^10000; E[(H/10000−1/127008)²]=127007/161310320640000. Also 9/10<(127007/127008)^10000<19/20.

The final conjunct repeats the all-natural-r error bounds with the numerical probabilities; asserts 10000/127008=625/7938; p(1−p)/10000=127007/161310320640000 at p=1/127008; this value divided by p² equals 127007/10000; and (1/2)(1−1/2)/10000=1/40000=(1/200)². There are no external hypotheses or empirical-data premises.

## SAP.P037b.T30

1. For every finite full-support P on Ω, event E and J∈ℕ with J>0, let p=P(E), H(z)=number of hits in z:Fin J→Ω, q(z)=∏ⱼP.mass(zⱼ), phat=H/J. For every natural r≤J, P_q(H=r)=choose(J,r)p^r(1−p)^(J−r). Also E_q phat=p; E_q(phat−p)²=p(1−p)/J; P_q(H=0)=(1−p)^J. For every ε>0, P_q(|phat−p|≥ε)≤p(1−p)/(Jε²)≤1/(4Jε²). For every ε,δ>0 with J≥1/(4δε²), that probability is ≤δ. If p=0, every draw sequence has H=0. If 0<p<1, both (1−p)^J and p(1−p)/J are positive.
2. For every such design, m,J∈ℕ with J>0, family Eₖ indexed by Fin m and ε>0, the product-law probability that at least one |phatₖ−P(Eₖ)|≥ε is ≤m/(4Jε²). No independence between events Eₖ is assumed.
3. For every b∈ℕ, n,t:Fin b→ℕ, peer subsets peersₕ⊆Fin(nₕ), and hypotheses tₕ≤nₕ for every h, one-half times the uniform independent tₕ-subset probability of avoiding peersₕ in every block equals B(n,t,(|peersₕ|)ₕ). This includes the empty-block case b=0.
4. For four blocks of size 10 selecting 5 each, B at peer counts (2,2,2,2), (5,3,0,0), (6,2,0,0), (5,5,0,0) equals respectively 8/6561, 1/6048, 0, 1/127008.
5. For every finite full-support P, event E, J>0 and arbitrary specified draws, the observed frequency equals r/J for some natural r≤J; if 0<p<1/(2J), its distance to p is at least p; if p=0 its frequency is 0. For every arbitrary I and D:Ω×I→Fin 5, positivity of all four empirical frequencies implies all four true probabilities belong to (0,1). All four πrare values belong to (0,1), and there exists a sequence of 10000 Ωrare states for which at least one of those four empirical frequencies is not positive.

## SAP.P037b.T31

Unconditionally, |A14|=78364164096, |U(56,28)|=7648690600760440, |U(8,4)|=70, |A2|=36. The eight-school set {0,1,2,3} belongs to U(8,4), while the corresponding four schools of block 0 are not in A2. Under uniform 28-of-56 selection, P(0 and 1 selected)=27/110; under uniform 2-of-4 selection it is 1/6.

Define vU(y)=average over U(8,4) of [(Σᵢsᵢyᵢ)/4]² and vB(y)=average over A2 of the analogous square, with sᵢ=1 on the selected set and −1 off it. Then vU(1,1,1,1,0,0,0,0)=1/7; vB(1 on block 0,0 on block 1)=0; vU(2,0,1,1,1,1,1,1)=1/7; vB(2 at (0,0),0 at (0,1),1 elsewhere)=1/6. These definitions are uncentered second moments, not explicitly covariance definitions.

Separately, for every finite Ω, n∈ℕ, weights p(z)≥0 summing to 1, Boolean assignments S:Ω×Fin n→Bool with P(Sᵢ=true)=1/2 for every i, y∈ℝⁿ, and m∈ℕ with m>0, put T(z)=Σᵢ(2·1{Sᵢ=true}−1)yᵢ/m. Then ET=0 and ET²=m^(−2)ΣᵢΣⱼyᵢyⱼ times the entry 1 when i=j and 4P(Sᵢ=true,Sⱼ=true)−1 otherwise. No fixed treated count, block structure, or relation between n and m is assumed in this general identity.

## SAP.P037b.T32

For every B,n,m∈ℕ with n≥2 and m≤n: |A_B|=6^B; Σ_{s∈A_B}6^(−B)=1; |U(n,m)|=choose(n,m); for every h∈Fin n, P_U(h selected)=m/n; for every h,j∈Fin n with h≠j, P_U(h and j selected)=m(m−1)/(n(n−1)). The subtraction in this last real expression is real subtraction. B need not be positive, and m may be zero.

Separately, for every finite Ω,U, type K with decidable equality, weights p on Ω and q on U, Boolean S on Ω satisfying Σzp(z)1{S(z)}=1/2 and Σzp(z)=1, f:Bool×U→K, k∈K, and hypotheses p≥0,q≥0,Σuq(u)=1, the product-law probability of f(S(z),u)=k equals (1/2)Σuq(u)1{f(false,u)=k}+(1/2)Σuq(u)1{f(true,u)=k}. The displayed product p(z)q(u) encodes independence; f depends on the school state only through S(z).
