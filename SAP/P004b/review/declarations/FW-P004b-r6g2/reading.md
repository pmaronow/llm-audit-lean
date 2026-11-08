# Blind reading

Saved before opening `claims.json` or `record.json`. Sources: the five Challenge
docstrings and every declaration listed in their `closure.json` entries. The
line-zero auxiliaries were also printed in `scratch/BlindProofs.lean`: they are
only `NeZero` and `Nat.AtLeastTwo` instances for numerical literals, not extra
mathematical assumptions. No Solution or external audit was read.

Notation used below is explicitly expanded here, so subsequent formulas contain
no opaque SAP predicates. For a natural number N, the nodes are `Fin N`, and an
assignment is a function z : Fin N → Bool. Write x_i(z)=1 when z_i=true and 0
otherwise; q_i(true)=p_i and q_i(false)=1-p_i. The real-valued functional
E_p f = Σ_{z : Fin N → Bool} (Π_i q_i(z_i)) f(z) is a finite sum. Whenever
0<p_i<1 it is expectation under independent Bernoulli coordinates. A table R
is any function Fin N → (Fin N → Bool) → ℝ. Set

- m_ia = E_p[1_{z_i=a} R_i(z)]/q_i(a), τ_i=m_i,true-m_i,false;
- bar m_a=(Σ_i m_ia)/N and τ=(Σ_i τ_i)/N;
- C_i(z;g)=x_i(R_i(z)-g_i,true)/p_i
  -(1-x_i)(R_i(z)-g_i,false)/(1-p_i);
- d_i(g)=τ_i-(g_i,true-g_i,false);
- A_g(z)=Σ_i[g_i,true-g_i,false+C_i(z;g)]/N;
- H(z)=Σ_i[x_i R_i(z)/p_i-(1-x_i)R_i(z)/(1-p_i)]/N;
- L(z)=A_g(z) with g_i,a=bar m_a;
- Cov_p(f,h)=E_p(fh)-E_p(f)E_p(h), Var_p(f)=Cov_p(f,f).

These expand Assignment, bit, coin, designWeight, expect, marginal, nodeEffect,
barMu, ame, residualContrast, residualEffect, augmented, ht, linearHajek, cov,
and variance wherever they occur below. For i≠j,
M_ij,ab(f)=E_p[1_{z_i=a,z_j=b}f(z)]/[q_i(a)q_j(b)]
expands pairMarginal. Its definition is the same ratio at i=j, although no
pair-moment assertion below uses that diagonal.

Write I(i,l) iff i=l OR there exist assignments z,z' agreeing at every
coordinate k≠l with R_i(z)≠R_i(z'). Write S(i,j) iff there exists l with both
I(i,l) and I(j,l). These are interferes and sharesSource, including their
forced diagonal. A ball for an arbitrary real array D is the finite set
{j : Fin N | D(i,j)≤r}; it is not assumed to be a metric unless stated.

## SAP.P004b.T21

The statement is the conjunction of the following five groups, with separate
universal quantifiers in each group (Defs/WholeW2.lean:302–329):

1. For every N, real p, table R, and finite sets B_i of nodes, assume N>0,
   0<p<1, i∈B_i for all i, j∈B_i iff i∈B_j, and j∉B_i implies ¬S(i,j).
   In this group p_i=p and g_i,a=bar m_a. For every i,
   Var_p(C_i)=E_p[(R_i-bar m_true)² | z_i=true]/p
   +E_p[(R_i-bar m_false)² | z_i=false]/(1-p)-d_i(g)².
   Also Var_p(L)≤N⁻² Σ_i |B_i| [the same two positive second-moment terms].
   Conditional expectations here are precisely the m-style finite ratios
   above, applied to the squared table. This is the full T21Statement,
   including the definition sahLimit (Defs/Part6.lean:29–40,
   Defs/Part3.lean:73–76).
2. Independently, for every N>0, 0<p<1, table R, and node i, let
   f_ia=E_p[R_i-bar m_a | z_i=a] and
   s_ia=E_p[(R_i-bar m_a)² | z_i=a]. Then
   Var_p(C_i)=s_i1/p-f_i1²+s_i0/(1-p)-f_i0²+2f_i1 f_i0
   =s_i1/p+s_i0/(1-p)-(f_i1-f_i0)². This unfolds residualFirst,
   residualSecond, and cltRaw at its `true` argument.
3. Independently, for every N, metric space X with a measurable space,
   population P, and reals p,d,h, assume N>0, 0<p<1, d,h≥0,
   well-defined averages at d, and h<D_ij implies ¬S(i,j).
   A population consists of nonempty sets A_i⊆X (no disjointness, compactness,
   or measurability assumption on A_i is built into the structure), a measure
   ζ, outcomes y:X→Assignment N→ℝ, and arbitrary bands b:ℝ→Set ℝ.
   Let δ_i(x)=Metric.infDist x A_i,
   D_ij=inf{dist(x,y):x∈A_i,y∈A_j}, G_i(d)={x:δ_i(x)∈b(d)}, and
   R_i(z)=(∫_{G_i(d)} y(x,z) dζ)/(ζ(G_i(d))).toReal.
   Well-defined means every G_i(d) is measurable, 0<ζ(G_i(d))<∞, and
   y(·,z) is integrable on G_i(d) for every assignment z. The conclusion is
   Var_p(L)≤N⁻² Σ_i |{j:D_ij≤h}|(s_i1/p+s_i0/(1-p)). This unfolds
   SpatialPopulation and all its relevant fields, nodeDistance,
   nodeSeparation, region, circleAverage, WellDefined, LocalAt, and ball.
   This quantifier uses `X : Type*`, not an array of populations.
4. For the fixed two-node table R_i(z)=ε_i(1-x_i), ε_0=1, ε_1=-1,
   p=1/4: both bar m values are zero; I(i,j) iff i=j;
   Var_p(L)=1/6; the quantity
   N⁻² Σ_i |B_i|[s_i1/p+
   (E_p[(R_i-bar m_false)² | z_i=true])²/(1-p)] is zero for B_i={i};
   and the corrected bound N⁻² Σ_i |B_i|(s_i1/p+s_i0/(1-p)) is 2/3.
   This expands sahBoundWitness and printedSAH, including the conditioning
   arm and the outer square in the latter.
5. For the fixed two-node table R_i(z)=ε_i x_i/2, p=1/4: both bar m
   values are zero; replacing coordinate 0 by true or false gives R_0=1/2
   or 0, respectively, for every assignment; Var_p(C_0)=3/4; and
   s_01/p-s_01²+s_00/(1-p)-s_00²+2f_01 f_00=15/16.
   This expands sahNodeWitness and printedNodeVariance.

The Challenge docstring describes corrected finite bounds and two numerical
defects, explicitly excluding a feasible-estimator consistency claim. There is
no asymptotic assertion in this theorem.

Junk-value audit: real division is total with a/0=0, but N>0 and 0<p<1
exclude it in all these statistical ratios. The fixed witnesses satisfy these
conditions. Spatial average integrals would return zero for non-integrable
functions, and ENNReal.toReal sends ∞ to zero, but WellDefined excludes both
branches and zero mass. Metric.infDist to ∅ is zero, but node_nonempty excludes
this; the distance set defining D_ij is nonempty and bounded below by zero, so
its real sInf is an ordinary infimum, even for noncompact/unbounded sets. No
triangle inequality or strictly positive separation is required for D. N=0 is
excluded from every quantified assertion with averages. Fin N and Bool are
finite, all expectations exist, and Nat-to-real casts of N and |B_i| are exact
nonnegative casts. No truncated subtraction, log, sqrt, rpow, liminf/limsup,
unbounded supremum, or partial-function default occurs. Function.update in the
last witness is total. The auxiliary proofs only validate numerical literals.

## SAP.P004b.T22

This is a conjunction of a general formula, its projection specialization,
and a fixed three-node computation (Defs/WholeW1.lean:115–125).

For each N and all p:Fin N→ℝ, R, B_i, and deterministic fits g_i,a, in that
order, assume N>0, 0<p_i<1 for every i, i∈B_i, and j∉B_i implies ¬S(i,j).
No symmetry of B is imposed. Put σ_true=1 and σ_false=-1, and define

- T_a=N⁻² Σ_i E_p[(R_i-g_ia)² | z_i=a]/q_i(a);
- D=N⁻² Σ_i d_i(g)²;
- P=N⁻² Σ_i Σ_{j∈B_i,j≠i} Σ_ab σ_a σ_b
  M_ij,ab((R_i-g_ia)(R_j-g_jb));
- F=N⁻² Σ_i Σ_{j∈B_i,j≠i} Σ_ab σ_a σ_b
  (m_ia-g_ia)(m_jb-g_jb);
- Q=N⁻¹ Σ_i Σ_{j∈B_i} d_i(g)d_j(g).

The conclusion is Var_p(A_g)=T_true+T_false-D+P-F,
-D-F=-N⁻²Σ_iΣ_{j∈B_i}d_i(g)d_j(g), and
Q≥0 implies Var_p(A_g)≤T_true+T_false+P. These expand armSign,
armSecondMoment, diagonalEffectSquare, signedPairSecondMoment,
signedPairMeanProduct, fiveTermVariance, homophilyQ, and varianceExpansion.

Independently quantify N,k,p,R,B,O in that order, where O_i is a real vector
indexed by Fin k. Require N>0, all propensities interior, det(J) a unit in ℝ
(equivalently nonzero), and the same two neighborhood conditions. Define
J_ab=N⁻¹Σ_i p_i(1-p_i)O_ia O_ib,
β_a=J⁻¹ v_a, (v_a)_j=N⁻¹Σ_i m_ia p_i(1-p_i)O_ij,
g_ia=Σ_j O_ij β_a,j. The estimator
[Σ_i(g_i1-g_i0)+Σ_i C_i(z;g)]/N equals A_g as a function of z, and all
three variance conclusions above hold for this g. These explicitly expand
projectionInformation, projectionBeta, covariateFits, projectionFits, and
projectionLinearIPW.

For the last conjunct take N=3, p_i=1/2, R_2=0 and
R_0(z)=R_1(z)=x_2-1/2, k=1, O_i0=1, B_i=all nodes, and g the projection
fit. The assertion is: det(J) is a unit; both β vectors and all fits are zero;
the projection estimator is (2/3)[(2x_0-1)+(2x_1-1)](x_2-1/2);
its variance and T_true+T_false are 2/9; D=P=F=0;
P_lit=2/9, F_lit=0, V_lit=4/9, and the corrected five-term sum is 2/9.
Here P_lit is P with σ_aσ_b removed and the second fit g_jb replaced by
g_ib; F_lit is F with only that second-fit replacement; V_lit is
T_true+T_false-D+P_lit-F_lit. These are exactly the definitions of
threeNodeVarianceTable/Witness, literalPairSecondMoment,
literalPairMeanProduct, and literalVariance. They do not assert a limit.

Junk-value audit: N>0 and all 0<p_i<1 protect every denominator, including
pair denominators. Off-diagonal erasure ensures pairMarginal is used only for
distinct nodes. Matrix inversion is Mathlib's total nonsingular inverse,
which is zero on singular real matrices; the unit-determinant hypothesis and
the explicit witness's unit determinant exclude this default. k=0 is allowed:
empty sums give zero fits and the empty matrix determinant is 1. This is a
legitimate no-covariate case, not a source of vacuity because k=1 also occurs.
No spatial integral, quantile, sqrt, rpow, truncated subtraction, liminf,
limsup, or partial-function default enters. Empty B_i are excluded by i∈B_i;
an empty off-diagonal sum is correctly zero. The numerical auxiliaries merely
certify literals and indices.

## SAP.P004b.T23

Three independently quantified blocks (Defs/WholeW1.lean:153–192):

First, for every N, phat:Fin N→ℝ, R, B_i, g, and assignment z, assume N>0,
both n_1=Σ_i 1_{z_i=true} and n_0=Σ_i 1_{z_i=false} are positive, and
0<phat_i<1. Define the N×2 real matrix X by X_i0=1,X_i1=x_i; set
A=(XᵀX)⁻¹, λ_i=x_i/n_1-(1-x_i)/n_0,
e_i=(n_1/N)x_i(R_i-g_i1)/phat_i
+(n_0/N)(1-x_i)(R_i-g_i0)/(1-phat_i),
Ω_ij=1 if j∈B_i and zero otherwise, and
S=A[Xᵀ (e_i e_j Ω_ij)_ij X]A.
Then (AXᵀ)_1i=λ_i; λ_i e_i=C_i(z;g)/N with p=phat;
(0,1)S(0,1)ᵀ=S_11=Σ_iΣ_{j∈B_i}λ_iλ_j e_i e_j
=N⁻²Σ_iΣ_{j∈B_i}C_i(z;g)C_j(z;g). No neighborhood, covariance,
symmetry, or stochastic hypothesis on B is imposed. This expands ValidArms,
armCount, designMatrix, lambda, weightedEpsilon, neighborhoodMatrix,
sandwich, treatmentSelector, treatmentQuadratic, and oracleHAC.

Second, for every N,k,p,R,B,O,θ,β,z, assume N>0 and all 0<p_i<1.
O_i and θ are Fin k real vectors and β assigns one such vector to each arm.
Set g_ia=Σ_j O_ijβ_a,j and phat_i=exp(Σ_j O_ijθ_j)/
(1+exp(Σ_j O_ijθ_j)). Then all 0<phat_i<1;
Q=N⁻¹Σ_i d_i(g)Σ_{j∈B_i}d_j(g) with each neighbor using its own O_j;
the e_i formula above holds with these phat and g; and
H_phat(z)=N⁻¹Σ_i[x_i R_i(z)/phat_i-(1-x_i)R_i(z)/(1-phat_i)].
The last two are explicit definitional equalities, not a statement that θ or β
solve an optimization problem or are consistent. This expands
logisticPropensity and covariateFits as well as homophilyQ and ht.

Third, for every real α with 0<α<1 define
Φ(t)=(gaussianReal 0 1 ((-∞,t])).toReal and
q(a)=inf{t∈ℝ:a≤Φ(t)}. Assert that each of the two sets at a=α/2 and
a=1-α/2 is nonempty and bounded below, q(α/2)=-q(1-α/2),
q(α/2)<0<q(1-α/2), and, for every real t,
[q(α/2)≤|t|≤q(1-α/2)] iff [|t|≤q(1-α/2)] iff
[q(α/2)≤t≤q(1-α/2)]. Further, for every N,p,phat,R,z and reals V_sah,
V_hac, assuming N>0, all p and phat interior, and both V values positive,
the same pair of equivalences holds at
t=(H_phat(z)-τ_p)/sqrt(V_sah), and separately at V_hac. The symbols V_sah
and V_hac are arbitrary positive real numbers; the statement does not define
them as particular estimators and asserts no coverage or probability limit.
This expands normalCDF, normalQuantile, FiniteQuantile, correctedIPWEvents,
and all remaining statistical definitions via the initial notation.

Junk-value audit: both counts positive imply N≥2 and an invertible Gram
matrix, so λ and inverse-Gram expressions use no zero/default branch.
Interior phat and N>0 protect IPW and e denominators. Logistic denominators
are strictly positive because real exp is positive everywhere. Empty Fin k is
allowed and gives phat=1/2 and zero fits. Quantile sets are explicitly proved
nonempty and bounded below, so no empty/unbounded real sInf is used; the
Gaussian measure is a probability, so its toReal is finite. V>0 excludes
sqrt's nonpositive branch and zero division. All finite expectations exist.
There are no Bochner-integral, truncated-subtraction, rpow, limit or partial
function conventions affecting these conclusions. Numeric auxiliaries only
validate index literals.

## SAP.P004b.T24

For every N and assignment z with both counts n_1,n_0 positive, and then
every vector e:Fin N→ℝ and matrix Q:Fin N×Fin N→ℝ, define X,A,λ as in
T23, M=I-XAXᵀ, K_ij=Q_ijλ_iλ_j,
T=(n_1 n_0/N) M K M, μ=tr(T), ν=2tr(TT), and
df=tr(T)²/tr(TT). Matrix products and trace here are finite real sums;
`I` is the Kronecker-delta matrix. Then

- Mᵀ=M, MM=M, MX=0;
- (AXᵀ)_1i=λ_i for every i;
- (0,1)A(0,1)ᵀ=N/(n_1 n_0)=Σ_i λ_i²;
- n_1 n_0/N=1/[(0,1)A(0,1)ᵀ];
- (0,1)A[Xᵀ(e_i e_j Q_ij)_ij X]A(0,1)ᵀ
  =Σ_iΣ_j λ_iλ_j e_i e_j Q_ij;
- ν≠0 implies df=2μ²/ν.

Under the same outer N,z and positive-count hypotheses, independently
quantify e,D,h; assume every D_ij≥0 and h>0. The entrywise matrix
U_ij=1 if 0≤D_ij/h≤1, otherwise 0, equals
Ω_ij=1 if D_ij≤h, otherwise 0; the sandwich treatment quadratic equals
eᵀ K e for K_ij=Ω_ijλ_iλ_j. D need not satisfy metric axioms.

Finally, independently for every natural N, compatibility of the shapes
(1,2) and (N,2) is equivalent to N=2, as is compatibility of (2,N) and
(2,2). Shape compatibility means only that the first pair's second natural
number equals the second pair's first natural number. There is no assertion
about values of ill-typed products.

These formulas fully expand T24WholeStatement (WholeW1.lean:220–239),
ShapeCompatible, leverageKernel, traceAdjustment, traceMu, traceNu,
effectiveDegreesOfFreedom, residualMaker, kernelVariance, uniformKernel,
distanceKernel, ball, neighborhoodMatrix, and the shared matrix/count
definitions unfolded in the preceding paragraph.

Junk-value audit: positive counts force N≥2, invertibility of XᵀX, and a
positive treatment quadratic, protecting all count, matrix and reciprocal
normalizations. df is globally total and would be zero at tr(TT)=0, but the
only df assertion is guarded by ν≠0. The theorem allows nonsymmetric Q and
does not assert df positive. Bandwidth h>0 protects D/h; D≥0 makes the
one-sided uniform kernel equal the closed ball indicator. Shape equalities
are ordinary natural equality and handle N=0 without any matrix values.
There is no log, sqrt, rpow, integral, conditional expectation, sInf/sSup,
truncated subtraction, limit, or partial-function default in this target.

## SAP.P004b.T25

Three conjoined blocks (WholeW1.lean:266–287). First quantify N, real p,
table R and real constants μ_1,μ_0. Assume N>0 and 0<p<1. Let
a_i(z)=x_i/(Np)-(1-x_i)/(N(1-p)),
b_i(z)=(μ_1-μ_0)/N-[x_iμ_1/(Np)-(1-x_i)μ_0/(N(1-p))],
c_i(z)=a_i(z)R_i(z)+b_i(z)-τ_i/N,
c_i^print(z)=a_i(z)R_i(z)+b_i(z)-τ_i.
The assertion is that for every i, as functions of z,
c_i=[μ_1-μ_0+C_i(z;g)-τ_i]/N with g_i,a=μ_a; E_p c_i=0;
for every z, Σ_i c_i=A_g(z)-τ; with μ_1=μ_0=0 the sum is H(z)-τ;
and E_p c_i^print=(1/N-1)τ_i.

Still under those hypotheses, for every real array D with D_ii=0, then
every node i, real s≥0 and assignment z, set J={j:D_ij≤s} and define
E_p[U | z_J](z)=
Σ_{z'}(Π_j q(z'_j))1_{∀j∈J,z'_j=z_j} U(z') /
Π_{j∈J} q(z_j).
Then E_p[c_i | z_J](z)=a_i(z)E_p[R_i | z_J](z)+b_i(z)-τ_i/N.
Thus only the table value is averaged; the own coin remains fixed because
i∈J. This expands conditionOn, ball, expandedCenteredSummand,
expandedPrintedSummand, and centeredSummand. All τ_i and expectations use
the constant propensity p.

Second, for the fixed eight-node table R_i(z)=x_i with p=1/2, every i has
τ_i=1, E_p c_i^print=-7/8, and E_p c_i=0 when μ_1=μ_0=0.

Third, quantify p,μ_1,μ_0, arrays D_N and tables R_N for every N including
N=0. Assume 0<p<1, every D_N,ii=0, and the following uniform property:
there exist ψ:ℝ→ℝ, positive numbers g_Ni, and real G such that ψ≥0 on
[0,∞), ψ is antitone there, ψ(s)→0 as s→+∞, and there exist exponent
e>4 and real C,S with S>0 such that ψ(s)≤C s^(-e) for every s≥S;
also 0<g_Ni≤G for all N,i; and for every N,i,s≥0,
sqrt(E_p[(R_Ni-E_p[R_Ni | z_{J_Ni(s)}])²])≤g_Ni ψ(s).
The conclusion is that there exist (possibly different) ψ,g,G,C,S,e with
all these same properties for the array c_Ni in place of R_Ni. The constants
μ_1,μ_0 do not depend on N. No boundedness of R or metric/spatial growth
condition on D is required. This is the complete definition of TableNED,
including the strict exponent e>4 and exact finite-cylinder conditional
expectation. Limits use the usual real atTop and neighborhood filters.

Junk-value audit: the first group has N>0, 0<p<1; every cylinder denominator
is a product of positive numbers, with empty product 1, so the conditional
ratio is genuine even for an empty ball. D_ii=0 and s≥0 ensure own-coin
measurability. In the array group N=0 creates no node i at all, so no
summand division by zero is evaluated in any quantified node condition;
N>0 follows automatically whenever i:Fin N exists. The L2 radicand is
nonnegative under positive product weights; sqrt never replaces a negative
moment by zero. Real rpow is used only at s≥S>0 in the polynomial bound,
so no nonpositive-base convention is used. The uniform ψ is only controlled
on nonnegative radii, as are the NED inequalities. Finite spaces ensure all
expectations and conditional expectations exist; there are no
nonintegrable-function, toReal(∞), sInf/sSup, liminf/limsup, truncated
subtraction, or partial-function conventions. Natural casts are exact. The
eight-node witness has genuine nonzero effect, so it is not explained by a
zero or undefined expectation. Auxiliary proofs only certify numerals.
