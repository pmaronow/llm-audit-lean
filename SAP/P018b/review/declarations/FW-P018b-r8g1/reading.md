# Blind statement reading

Saved at stage 1, before opening either claims.json or record.json. This document reads the elaborated targets and all their unit-local dependencies in closure.json. Sources: Challenge/Part1.lean, Defs/Part1--Part4.lean, and Defs/WholeW1.lean through line 407. All 82 distinct line-0 auxiliary declarations in the closures were printed by scratch/BlindCheck.lean (scratch/blind-check.log). These are numeral/typeclass proofs, decidability instances, proofs that the six listed sets really are dyads, the proof of nonemptiness used by min/max, and the exhaustive sum-type matcher for the twenty-unit point. They add no statistical assumptions or mathematical quantities.

## Mathematical notation used in the five readings

This notation is an explicit unfolding, not a reference to additional SAP definitions.

Vectors of dimension k are functions {0,...,k-1} → ℝ; matrices are functions on two such indices. The outer product xy' has entry x_a y_b; x·y = Σ_a x_a y_a. Multiplication, determinant, trace, transpose and characteristic polynomial are the Mathlib matrix operations. PSD means symmetric with x'Mx ≥ 0 for every real x; PD replaces ≥ with > for x ≠ 0. Define C_P(M)=PMP, with no transpose inserted.

For finite sets of units V and observations E, let s_d ⊆ V be a two-element set and suppose d ↦ s_d is injective. Write A_df=1 if s_d∩s_f is nonempty, otherwise 0. For vector scores b_d let

- M(b)=Σ_d Σ_f A_df b_d b_f';
- U_i(b)=Σ_{d:i∈s_d} b_d;
- D(b)=Σ_d b_d b_d'.

For counts T_d∈ℕ and record scores q_dt, t∈{0,...,T_d-1}, put b_d=Σ_t q_dt,
J=Σ_dt q_dt q_dt', E_i=Σ_{d:i∉s_d}Σ_t q_dt q_dt',
C_i=U_i(b)U_i(b)'+E_i, E_i^o=Σ_{r∈{0,1}}E_i=2E_i, and C_i^o=U_i(b)U_i(b)'+E_i^o.
Also K_i=Σ_{d≠f:i∈s_d∩s_f} b_d b_f' (an ordered pair sum), and L_i=Σ_{d:i∈s_d}b_d b_d'.

For rows X_d and responses Y_d define G=Σ_d X_d X_d', βhat=G⁻¹Σ_d X_d Y_d, ehat_d=Y_d-X_d·βhat, and Vhat=G⁻¹ M((X_d ehat_d)_d)G⁻¹. The inverse is Mathlib's nonsingular inverse, equal to zero on a singular real matrix.

The actual dyads at sample size N are all two-element subsets of {0,...,N-1}, not ordered endpoint pairs. A dyad's first/second endpoints are its minimum/maximum. D_N=N(N-1)/2 with subtraction in ℝ. Its neighbours are the other dyads with nonempty intersection.

For a law μ and symmetric pair functions X(u,v)∈ℝ^k, Y(u,v)∈ℝ, write E for componentwise Bochner integration, Q=E_{μ×μ}[XX'], β=Q⁻¹E[XY], ε=Y-X·β, h=Xε, g(u)=E_v h(u,v), Γ=E_u[g(u)g(u)'], and V=4Q⁻¹ΓQ⁻¹. A sample has product law μ^N; dyad data are obtained by evaluating the functions at the minimum and maximum endpoints. Its coefficient error is βhat-β. The finite linear-approximation covariance target is
V_N=(N/D_N²)Q⁻¹ Cov_{μ^N}(Σ_d h_d)Q⁻¹.
Cov(F)_ab=∫(F_a-∫F_a)(F_b-∫F_b).

For possibly changing sample spaces and laws μ_N, “f_N →p 0” here means: for every real η>0, (μ_N{ω:η≤‖f_N(ω)‖}).toReal → 0 as N→∞. Finite-dimensional function norms are supremum norms (and matrix norms use the elementwise scoped instance). “f_N ⇒ ν” means all f_N are almost everywhere measurable, ν is a probability measure, and E[g(f_N)]→∫g dν for every bounded continuous real g. “ν is centered normal with covariance V” means V is PSD, ν is a probability measure, and every linear functional c·x has law gaussianReal(0,(c'Vc).toNNReal). Mathlib gaussianReal with zero variance is Dirac at zero.

## SAP.P018b.T15

Location: Challenge/Part1.lean:9--13; expanded proposition at Defs/Part4.lean:21--44.

There are no outer hypotheses. The first conjunct universally quantifies, in order, finite types V,E with decidable equality; a function s:E→finite subsets of V; a proof |s_d|=2 for every d; a proof s is injective; a natural dimension k; counts T:E→ℕ; vectors q_dt∈ℝ^k; and an arbitrary matrix P∈ℝ^{k×k}. Neither positive counts, fitted scores, complete coverage of all dyads, invertible P, nor symmetric P is assumed. Put n=|V| and use the explicitly expanded sums above. All of the following hold:

1. For each i, E_i^o=2E_i.
2. Σ_i E_i^o=2(n-2)J, with n cast to ℝ before subtraction.
3. Σ_i C_i^o-D(b)-(n-2)J=M(b)+(n-2)J.
4. Σ_i C_P(C_i^o)-C_P(D(b))-(n-2)C_P(J)=C_P(M(b))+(n-2)C_P(J).
5. If n≥3 and C_P(J)≠0, the left side of (4) is unequal to C_P(M(b)).

Independently, there are unconditional exact scalar calculations. Take units 0,1,2,3, observations in the order 01,02,03,12,13,23, one record per dyad, k=1, and q=(1,2,3,4,5,6). Then D(b)=[91], M(b)=[385], Σ_i U_i(b)²=[476], Σ_i E_i=[182], J=[91], and Σ_i E_i^o=[364]. The statement also asserts the real equalities 476+2·182-91-2·91=567, 567≠385, 476+182-91-2·91=385, 476+364-91-2·91=567, 567=385+182, and 6²+10²+12²+14²=476. The docstring calls this an ordered-nonincident reading and a six-dyad mismatch; it does not call the printed claim false.

Junk conventions: all quantities are finite sums and polynomial operations; there is no division, inverse, integration, log, root, real power, infimum or supremum. T_d=0 makes its record sum zero; k=0 gives the unique empty vector/matrix; E may be empty. If V has fewer than two elements, the hypotheses force E empty. The coefficient n-2 is real subtraction and may then be negative, but multiplies zero. Natural cardinality casts and the indices in the explicit vectors are exact. The strict-inequality conclusion is guarded by n≥3 and C_P(J)≠0, so the empty cases do not manufacture a mismatch. No partial-function default occurs.

## SAP.P018b.T16

Location: Challenge/Part1.lean:15--18; expanded proposition at Defs/Part4.lean:47--62.

Universally quantify finite decidable types V,E, an injective assignment of two-element subsets s_d, dimension k∈ℕ, arbitrary natural record counts T_d, arbitrary real vectors q_dt, and an arbitrary real k×k matrix P, in that order. There are no probabilistic or regression hypotheses. With b_d=Σ_tq_dt and n=|V|, the conclusion is the conjunction of both corrected identities

M(b)=Σ_i C_i-D(b)-(n-2)J,

C_P(M(b))=Σ_i C_P(C_i)-C_P(D(b))-(n-2)C_P(J),

and five intermediate identities:

1. M(b)-D(b)=Σ_i K_i.
2. For every i, C_i=K_i+L_i+E_i.
3. Σ_i L_i=2D(b).
4. Σ_i E_i=(n-2)J.
5. M(b)=D(b)+Σ_i K_i.

Thus incident dyads are clustered together and each nonincident record contributes its own outer product once. The bread can later be specialized to a sample Gram inverse; no such inverse is present in this statement. The docstring asserts both identities and all five intermediate steps.

Junk conventions: identical finite/empty-index and cast considerations to T15, independently checked here. T_d=0 and k=0 are permitted and produce honest zero sums; n-2 is real subtraction. Injectivity excludes two distinct dyads with the same endpoint set, which would otherwise make an off-diagonal pair share two units. No division, inverse, root, integration, infimum/supremum, or default value enters. The hypotheses admit the six distinct dyads on four units with positive counts and nonzero scores.

## SAP.P018b.T17

Location: Challenge/Part1.lean:20--29; expanded proposition at Defs/WholeW1.lean:57--102, including negativeSampleFacts and negativePopulationFacts (Defs/Part4.lean:64--83).

This is an unconditional conjunction, not an implication with an assumed witness. Its five groups and additional limit clauses are as follows.

1. On the six dyads 01,02,03,12,13,23 let A_df indicate endpoint overlap and c=(1,-1,0,0,-1,1). Then det(tI-A)=(t-5)(t-1)^3(t+1)^2; Ac=-c; Σ_dc_d=0; Σ_dc_d²=4.
2. With one intercept-only observation per dyad, X_d=(1) and Y=c: det G=6, βhat=0, all fitted residuals equal c_d, and Vhat_00=-1/9<0. For every natural N>4, put X_d=(1) on every actual dyad and set Y_01=Y_23=1, Y_02=Y_13=-1, all other Y_d=0. Then det G=D_N>0, βhat=0, ehat=Y, Vhat_00=-4/D_N²<0.
3. On the six dyads put x=(1,2,3,1,2,1), X_d=(1,x_d), Y=(4,3,5,3,3,4), and r=(3/5,-4/5,4/5,-2/5,-4/5,3/5). Then G=[[6,10],[10,20]], det G=20, βhat=(3,2/5), ehat_d=r_d, Σ_d X_dr_d=0,
M(Xr)=[[-34/25,-2],[-2,-98/25]],
Vhat=[[-17/50,21/125],[21/125,-58/625]].
Both diagonals are negative, det Vhat=52/15625>0, tr Vhat<0, -Vhat is PD, and neither diagonal equals r² for any real r.
4. An iid unit has law uniform on the eight points (C,S)∈{0,1,2,3}×{false,true}; z(false)=-1,z(true)=1. Set
X(u,v)=(1,|C_u-C_v|),
Y(u,v)=|C_u-C_v|+a(C_u,C_v)+z(S_u)+z(S_v),
where the four rows of a are (0,1,-1,0),(1,0,0,-1),(-1,0,0,1),(0,-1,1,0).
The asserted standing properties are: this is a probability law; X,Y are measurable and symmetric; they are almost everywhere bounded by one finite common nonnegative constant; one fixed coordinate of X is identically one; and det Q≠0. In addition 0≤X_1≤3 and -2≤Y≤5 pointwise.
The proposition specifies
Q=[[1,5/4],[5/4,5/2]], det Q=15/16;
β=(1/3,11/15);
Γ=[[226/225,284/225],[284/225,5971/3600]];
V=[[1004/225,-48/125],[-48/125,1856/5625]],
V PD and det V=67072/50625.
The event ω_i=(i,true) for all four units has real probability 1/4096. Every sample in this event has det G=20 and the preceding negative Vhat. Under the map taking each of the six listed sets to an actual dyad, all its X,Y rows equal those in group 3.
5. At N=20, take mutually independent N(0,1) variables x_i,ν_i,ε_dt, one observation per actual dyad. X_d=(1,|x_i-x_j|), Y_d=|x_i-x_j|+ν_i+ν_j+ε_d. At the fixed point x_0=1,x_1=2,x_2=3,x_3=4, all remaining x_i=5/2, all ν_i=0, and ε_d equal the zero-padded cycle in group 2, the proposition asserts
G=[[190,74],[74,100]], det G=13524,
βhat=(37/3381,3286/3381),
Vhat_11=-31032915283/43557147269307<0.
The product Gaussian law gives strictly positive probability to {det G≠0 and Vhat_11<0}; it does not assert that the fixed point itself has positive probability.

Finally V_N→V for the bounded model in group 4, and there exists a probability law ν on ℝ² whose every linear functional is centered normal with variance c'Vc and for which √N(βhat-β)⇒ν under the iid unit product laws.

Junk conventions: G⁻¹ and Q⁻¹ are zero at singular matrices. All explicitly evaluated fits are nonsingular, and the positive-probability Gaussian event requires rank. The bounded iid model has singular samples with positive probability; its βhat is totalized there for the weak limit, and finite-sample coefficient moments are explicitly not asserted. Small N=0,1 produce empty dyad sets, D_N=0 and division/inversion values zero in V_N; they do not affect an atTop limit. √N is always on the nonnegative domain, including zero. Covariances and means use Bochner integrals, which return zero if not integrable; bounded scores ensure the population and finite target moments exist. No unbounded inverse moments are used in V_N. Product laws are probabilities, so every event .toReal is finite rather than .toReal(∞)=0. V PSD in the normal-law predicate ensures .toNNReal does not clip a negative variance. Min/max endpoints require the proved two-element cardinality, so have no empty-set default. All explicit vector indices are valid; no Nat subtraction pads data. No logarithm, real power, limsup, sInf, or sSup appears.

## SAP.P018b.T18

Location: Challenge/Part1.lean:31--39; Defs/WholeW1.lean:117--144, including Defs/Part4.lean:88--121.

The proposition is an unconditional conjunction of universal assertions and concrete witnesses. First universally quantify finite decidable V,E, an injective two-element assignment s, k∈ℕ, arbitrary scores q_d∈ℝ^k, and P with P'=P. Let B_id=1_{i∈s_d} and S_da=(q_d)_a. Then

- (B'B-I)_df=1_{s_d∩s_f≠∅}, M(q)=S'(B'B-I)S=(BS)'(BS)-S'S.
- PMP is symmetric and equals P[Σ_i U_i(q)U_i(q)']P-PD(q)P.
- Each of the last two terms is PSD.

For every real v define the optional standard error as Some(√v) when v≥0 and None otherwise. The following are asserted:

1. For every v, an r with standardError(v)=Some(r) exists iff v≥0.
2. For every real a,b, |max(a,0)-max(b,0)|≤|a-b|.
3. For every real n≥0 and v,V with V≥0, |n max(v,0)-V|≤|nv-V|.
4. For every n≥0,V>0,v<0, V≤|nv-V|.
5. For every measurable space Ω, probability law μ, real n≥0, function v:Ω→ℝ and V>0, μ{v<0}.toReal≤μ{V≤|nv-V|}.toReal. No measurability hypothesis on v is explicitly included in this universal inequality.
6. For every sequence of measurable spaces, probability measures μ_N, functions v_N:Ω_N→ℝ and real sequence V_N≥0, N v_N-V_N→p0 implies N max(v_N,0)-V_N→p0.
7. Under the same quantifiers with a fixed V>0, Nv_N-V→p0 implies μ_N{v_N<0}.toReal→0.

Next, for all natural N,k with N≥2, all rows X on all actual dyads, and arbitrary real residual arrays e, let P=(Σ_dX_dX_d')⁻¹. Then the diagonal-plus-neighbour sum
Σ_d[e_d² X_dX_d'+Σ_{f≠d:s_f∩s_d≠∅}e_de_f X_dX_f']
equals M((X_de_d)_d), P'=P, and its sandwich by P is symmetric.

The six-row two-coefficient fitted example X,Y from the T17 reading has det G≠0 and its Vhat is not PSD.

For every sequence of measurable spaces and probability laws, real functions v_N and real targets V_N, if there exists c>0 with eventually c≤V_N and Nv_N-V_N→p0, then μ_N{v_N<0}.toReal→0. Quantifiers are ∀ spaces/laws/v/V, then the existence premise, then the convergence premise.

For every real v, v≥0 implies the optional error is Some(√v); v<0 implies it is None, no real square equals v, and √max(v,0)=0. For every finite m and v:{0,...,m-1}→ℝ, the number of None errors equals the number of negative inputs.

Finally, using the eight-point bounded iid population specified in the T17 reading, for every real c the four-unit probability of
|βhat_0-β_0|>|c|√max(Vhat_00,0)
is at least 1/4096. This is a finite-sample lower bound on noncoverage for that explicit family of intervals; no confidence-level parameter or universal nominal-coverage assertion appears.

Junk conventions: the optional standard error deliberately hides Real.sqrt's totalization to zero on negative reals; its nonnegative branch is meaningful and its negative branch is None. The truncated convention deliberately returns zero on negative v. Empty lists (m=0), k=0 and empty E give empty counts/matrices and true algebraic identities, but the non-PSD witness is nonempty and full rank. Arbitrary sample matrices may be singular; their zero inverse is symmetric, so the structural assertion remains algebraically correct there. The positive-probability noncoverage bound uses a full-rank event of the concrete model. Bochner means entering its population coefficient exist. Probability .toReal values cannot involve ∞. Although the general v_N statements do not require measurability, Mathlib measures of sets are defined on all sets as outer measures; under the stated usual measurable setting they are genuine event probabilities. No rates or independence are assumed in these abstract convergence implications. n in the deterministic inequalities is a nonnegative real, whereas the sequences use the exact real cast of the natural sample index N. No real power, log, infimum/supremum, limsup or partial index is used.

## SAP.P018b.T19

Location: Challenge/Part1.lean:41--52; Defs/WholeW1.lean:148--218,223--225,229--237,242--251,263--407; repeated-data operations at Defs/Part3.lean:11--56.

There are no outer hypotheses. The theorem existentially quantifies, in order, a type U, a measurable-space structure on U, and a measure μ on U with functions level:U→ℕ, label:U→ℕ and A,B:U→Bool. All the following are conjunctive conclusions for that single model.

Write M(u)=level(u)+1≥1, C(u)=label(u)+1, a(u)=1 if A(u)=true and -1 otherwise, and b(u) analogously. The law conclusion says μ is a probability measure, all four coordinates are measurable, label(u)<level(u)+1 pointwise, and, for every m∈ℕ, c∈{0,...,m}, and choices of the two signs,
μ{level=m,label=c,A=a,B=b}=ofReal[2^{-(m+1)}/(4(m+1))].
Equivalently P(M=M0)=2^{-M0}, C is uniform on {1,...,M0} conditional on M, and both signs are independent fair signs independent of these coordinates. Unused coordinates of U are permitted.

Define δ_M=1/(M²2^{M²+2}). A pair is small when its levels agree and labels differ. Set s_uv=δ_{M(u)} and z_uv=a(u)+a(v) on small pairs, and s_uv=1,z_uv=0 on other pairs. For each actual dyad there are two records, t=0,1, with σ_0=1,σ_1=-1,
X_dt=(1,1+σ_t s_d), Y_dt=b_i+b_j+σ_t z_d.
Units are sampled independently with product law μ^N. All records use the same endpoint functions, evaluated at the minimum/maximum endpoints.

For this repeated data define G=Σ_dt X_dtX_dt', L=Σ_dT_d=2D_N, β_N=(E G)⁻¹EΣ_dtX_dtY_dt, βhat=G⁻¹Σ_dtX_dtY_dt, fitted block scores b_d^fit=Σ_t X_dt(Y_dt-X_dt·βhat), Vhat=G⁻¹[Σ_{d,f:overlap}b_d^fit(b_f^fit)']G⁻¹, and H_N=(1/L)E G. In this paragraph b_d^fit is a score, distinct from the unit sign b_i.

The “repeated standing” conclusion is: μ is a probability law; T_d>0 at N≥2; every record kernel is measurable on U×U; there is one finite C0≥0 bounding all row norms and absolute responses almost everywhere, uniformly in N,d,t; and there is one coordinate j which equals one in every row pointwise. There is no extra sample-rank premise. More precisely all coordinates of every X_dt lie in [0,2] and |Y_dt|≤4. Conditional on the entire sample design array, E[Y_dt | design]=0 almost surely for all N,d,t.

Put Qs=E_{μ×μ}s_uv², S=Σ_ds_d², R=Σ_ds_dz_d, abar=N⁻¹Σ_i a_i, bbar=N⁻¹Σ_i b_i, and r_d=z_d-βhat_1s_d. The population conclusions are β_N=0 for every N, 2/3≤Qs≤1, and for every N≥2,
H_N=[[1,1],[1,1+Qs]], det H_N=Qs.
For every N≥2 and every sample ω, S>0, det G=4D_NS>0,
βhat=(2bbar-R/S,R/S),
ehat_dt=b_i+b_j-2bbar+σ_t(z_d-βhat_1s_d), |ehat_dt|≤8,
and Vhat_11=[Σ_{d,f:overlap}(s_dr_d)(s_fr_f)]/S².

For N and level index m, define E_{N,m}={all N levels equal m and all N labels are distinct}. For all N≥3 and N≤m+1, it has strictly positive probability
p_{N,m}=2^{-(m+1)N}(m+1)_{\underline N}/(m+1)^N,
where the falling factorial is Mathlib Nat.descFactorial, and on it βhat_1=2abar/δ_{m+1}. The squared slope is integrable under the restricted measure μ^N|E_{N,m}, and its conditional second moment (restricted integral divided by p_{N,m}) is exactly 4/(Nδ_{m+1}²).

For all N≥3 and N(N-1)≤m+1, three further inequalities hold:

- (m+1)_{\underline N}/(m+1)^N≥1/2;
- the restricted extended second-moment integral on E_{N,m} is at least (32/N)(m+1)^4 2^{2(m+1)^2-(m+1)N};
- that lower bound is at least 2^{(m+1)^2}.

For every N≥3, both ∫|βhat_1| and ∫βhat_1² are infinite, formulated as nonnegative extended integrals of ofReal. For every N≥4, ∫max(Vhat_11,0)=∞ and ∫max(-Vhat_11,0)<∞ in the same extended sense.

Let Disp=Σ_i(a_i-abar)². For every N≥2 and every m, on E_{N,m}
Vhat_11=(N-2)(N-3)Disp/(D_N²δ_{m+1}²).
Also E Disp=N-1; for all m with N≤m+1 its conditional mean on E_{N,m} is N-1; outside the union of all E_{N,m}, |Vhat_11|≤16D_N².

Let
hterm_m=2^{-3(m+1)}(1-1/(m+1))²δ_{m+1}²,
H=Σ_{m≥0}hterm_m,
v=4H/Qs²,
W=[[4+v,-v],[-v,v]].
The series is summable and H>0. It is asserted that v>0, W is PD, det W=4v, N Vhat-W→p0, and there exists a centered normal law ν with covariance W for which √N(βhat-β_N)⇒ν. The per-level function wholeRareh, which is not in this target's closure, is not needed for these assertions.

Finally attach an independent r_i with law Lebesgue measure restricted to [0,1] to each unit. The directed record array still has two records per dyad, but takes the plus/minus undirected rows in original order if r_i<r_j and reverse order if r_i>r_j; on ties it uses the plus record twice. It has iid product law (μ×Unif[0,1])^N. For weights w_dt=1, define weighted G_w=Σ_dt w_dtX_dtX_dt', XY_w=Σ_dt w_dtX_dtY_dt, βhat_w=G_w⁻¹XY_w, fitted blocks Σ_t w_dtX_dt(Y_dt-X_dt·βhat_w), and Vhat_w by the same overlap sandwich with G_w. For every N, almost surely all r_i are distinct and (βhat_w,Vhat_w) equals the undirected (βhat,Vhat) on the projected unit sample. For every N≥3 its absolute and squared slope moments are infinite; for every N≥4 its sandwich slope positive-part mean is infinite and negative-part mean finite. Moreover N Vhat_w-W→p0 and √N βhat_w⇒ a centered normal law of covariance W. The target does not separately assert the directed standing or common-kernel/positive-limit-design predicates.

Junk conventions: δ_0=0 in the standalone total definition because 1/0=0, but every use here is δ_{level+1} or δ_{m+1}, whose denominator is strictly positive. Means abar,bbar divide by N: at N=0 they are zero, but every fit/event formula using them is guarded by N≥2 or N≥3. For N=0,1 dyads are empty and G, its inverse and β_N are zero; the all-N β_N=0 clause includes that harmless convention. All substantive fit formulas prove positive determinants rather than assuming inverses exist. Event ratios only occur when N≤m+1 and the event has positive probability; the later conditional-dispersion ratio has the same positive-event condition. Real powers with integer exponents have base 2>0; the other powers are natural. N(N-1) in the growth hypothesis uses natural truncated subtraction, but N≥3 makes it ordinary subtraction. Falling factorials become zero outside their combinatorial range, which is excluded by the premises. Arithmetic such as N-2 and N-3 in real-valued formulas is real subtraction.

All finite expectations are of measurable bounded quantities or are explicitly integrable under the restricted event law; condExp is with respect to the sigma algebra generated by the measurable full design, on a probability space. Thus its zero fallback for a non-subalgebra, nonintegrability, or lack of sigma finiteness does not account for the conditional-mean claim. Infinite moments use ∫⁻ and are not silently converted to Bochner zero or toReal(∞)=0. Probability .toReal is only applied to finite event measures. The sum defining H has Mathlib's zero convention for a nonsummable family, but summability and H>0 are asserted explicitly. The directed tie branch can change data on ties, which have measure zero under the independent continuous auxiliary law; every equivalence there is almost sure. √N and the normal-law variances are nonnegative. There are no logs, real noninteger powers, sInf/sSup, or limsup/liminf; endpoints use nonempty finite min/max. The existential U need not itself be standard Borel syntactically, but can be chosen countable discrete; the theorem is not universally quantifying conditional-law constructions over arbitrary U.
