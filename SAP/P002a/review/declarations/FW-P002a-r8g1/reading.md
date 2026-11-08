# Blind reading

Saved before opening claims.json, record.json, earlier.json, or architect-report.md.
The sources read are Challenge/Part1.lean and all the declarations in closure.json,
including generated constructors, projections and auxiliary proofs. The four auxiliary
proofs in these closures were also printed by scratch/BlindCheck.lean: each merely
provides `(1 + 1).AtLeastTwo` for a real-number numeral. They impose no model assumption.
Only statements and definitions, not the admitted Challenge proofs, are being audited.

## SAP.P002a.T2

### Objects and fully expanded notation

A population consists of a natural number n, two real potential outcomes y_i(0),
y_i(1) for each i in Fin n, two Boolean receipt indicators d_i(0), d_i(1), and a
natural treatment-arm size m. A covariate population additionally has x_i in R^k
(implemented as Fin k -> R). An assignment is a subset S of Fin n with cardinality
m. Let D be the finite set of all such subsets. For any real function f of subsets,
E_D f = (sum over S in D of f(S)) / |D|,
Var_D f = E_D[(f-E_D f)^2], and P_D(E) = |{S in D : E(S)}|/|D|.
All of these are finite sums and real division, not abstract integrals.

The real encoding of a Boolean is 0 or 1. The complier set C is
{i : d_i(0)=0 and d_i(1)=1}. Monotone receipt means d_i(0)=1 implies d_i(1)=1,
for every i. Write M(q)=(sum_i q_i)/n and M_H(q)=(sum_{i in H}q_i)/|H|.
The parameter beta is (sum_{i in C}(y_i(1)-y_i(0)))/|C|.
For a in {0,1}, set w_ai=y_i(d_i(a))-beta*d_i(a), v_ai=w_ai-M(w_a),
V(q)=sum_i(q_i-M(q))^2/(n-1),
Cov(q,t)=sum_i(q_i-M(q))(t_i-M(t))/(n-1).
For a subset H with at least two elements, V_H and Cov_H use its own mean and
denominator |H|-1; both are defined to be zero if |H|<2.
Put pi=m/n, n0=n-m, c=pi^2(1-pi)^2,
S_a^2=c V(w_a), and S_diff^2=c sum_i(v_1i-v_0i)^2/(n-1).
The centered fourth norm is F(q)=sqrt(sqrt(M(q^4))).

The raw admissibility predicate means ALL of the following:
n>=2, 0<m<n, monotone receipt, C nonempty, rn<=m<=(1-r)n,
Cov_C(w_1,w_0)>=-delta sqrt(V_C(w_1))sqrt(V_C(w_0)), and
F(v_a)<=A sqrt(V(w_a)) for each a. This is exactly the conjunction named Theta.

For the adjusted predicate, put h_i=(1,x_i), indexed by Option(Fin k).
For any H, G_H has entries M_H(h_is*h_it), and the score vector has entries
M_H(h_is*q_i). Define L_H(q) as G_H^{-1}score when det G_H is nonzero;
otherwise choose a coefficient c minimizing sum_{i in H}(q_i-h_i dot c)^2 over all
real coefficient vectors, if a minimizer exists, and return the zero vector if no
minimizer exists. The inverse here is Mathlib's nonsingular matrix inverse.
All dot products are finite coordinate sums. Let p_a=L_all(w_a) and
u_ai=w_ai-h_i dot p_a.

The adjusted admissibility predicate means n>=2, 0<m<n, monotone receipt, C nonempty,
rn<=m<=(1-r)n,
Cov(u_1,u_0)>=-delta sqrt(V(u_1))sqrt(V(u_0)),
F(u_a)<=B sqrt(V(u_a)) for each a,
sum_i x_is=0 and M(x_s^4)<=A for each covariate coordinate s, and
e sum_s b_s^2 <= M((sum_s x_is*b_s)^2) for every b in R^k.
This is exactly the conjunction named Xi. In particular the covariance condition
in Xi is over the entire population of residuals, whereas Theta's is over compliers.

For S, the observed response is q_i(S)=y_i(d_i(1_{i in S}))-beta*d_i(1_{i in S}).
The raw statistic is t(S)=sum_i q_i(S)(1_{i in S}-pi)/n.
The oracle adjusted statistic is
t_o(S)=M_S(q(S)-sum_s x_s p_1,s)-M_{S^c}(q(S)-sum_s x_s p_0,s).
Its coefficients are the two population potential-response coefficients p_1,p_0,
not fits on S and not a common pooled observed-response coefficient.

### Complete statement and quantifiers

This theorem is a conjunction of the following propositions. Each universal claim
chooses its data independently of the other conjuncts.

1. For every n, population, delta<1, 0<r<=1/2 and A>0 satisfying the raw admissibility
   predicate above, with d=max(delta,0),
   (1-d)[n0/(n*m) S_1^2 + m/(n*n0) S_0^2] <= Var_D t.
2. For every n,k, covariate population, k>0, delta<1, e,A,B>0 and 0<r<=1/2 satisfying
   adjusted admissibility,
   (1-d)[n0/(n*m) V(u_1) + m/(n*n0) V(u_0)] <= Var_D t_o.
3. For every raw-admissible population and constants as in (1), IF |C|>=2, define
   V1=V_C(w_1), V0=V_C(w_0), K=Cov_C(w_1,w_0),
   Q=sum_{i in C}(v_1i-v_0i)^2/(|C|-1), b1=1+d*n0/m and b0=1+d*m/n0. Then
   Q=V1+V0-2K,
   Q<=V1+V0+2d sqrt(V1)sqrt(V0)
   <=b1 V1+b0 V0
   <=[b1 sum_{i in C}v_1i^2+b0 sum_{i in C}v_0i^2]/(|C|-1).
4. For every raw-admissible population and constants as in (1), including singleton C,
   S_diff^2 <= c/(n-1)[b1 sum_i v_1i^2+b0 sum_i v_0i^2].
5. For every adjusted-admissible population and constants as in (2),
   sum_i(u_1i-u_0i)^2 <= b1 sum_i u_1i^2+b0 sum_i u_0i^2.
6. For every raw population and real delta,r,A, if delta<0 and raw admissibility
   holds at delta, it also holds at 0 with r,A unchanged. Independently, for every
   covariate population and real delta,e,A,B,r, if delta<0 and adjusted admissibility
   holds at delta, it also holds at 0 with all other constants unchanged. These two
   inclusion clauses add no outer sign restrictions on the other constants.
7. Both (1) and (2) also hold with the factor 1-delta when 0<=delta<1, under the same
   respective dimension and constant hypotheses.

The docstring calls this the entire corrected group chain (C.3)-(C.6), the full
population bound (C.8), the residual-square bound preceding (E.10), two variance
bounds, the negative-delta inclusions, and recovery of the nonnegative-delta formulas.
There is no explicit subsequence quantifier; a pointwise universal result applies to
each admissible member of any sequence. There is no variance positivity hypothesis.

### Totalizations and possible junk values

Real division by zero returns zero. M and M_H therefore return zero on an empty
population or empty H; V and Cov divide by zero at n=1; assignment averages become
zero if D is empty. The admissibility predicates exclude n<2, empty arms, empty D,
and empty C, so none of these conventions affects their advertised quantities.
The group covariance/variance is explicitly zero on a singleton (and on an empty
set); the group chain separately assumes |C|>=2. The singleton convention is relevant
to admissibility and is not itself the ordinary sample covariance with denominator
zero. The scaled and variance inequalities include singleton compliers.

All subtractions n-1, n-m, |C|-1 appearing as denominators here are in R, not
truncated natural subtraction. Natural cardinalities and sizes are cast exactly
into R. Complements are relative to Fin n. Numerator sums and index types are finite.
Positive k is required only for the adjusted inequalities, not for the inclusion.
Zero residual or outcome variance is allowed; its square root is genuinely zero.
Fourth powers average to a nonnegative number; variance sums of squares have positive
denominator under admissibility; Real.sqrt's zero value at negative inputs is unused.

On singular designs OLS uses Classical.choose of an actual minimizer, without a
minimum-norm tie rule. Finite least squares always has a minimizer, including empty
samples, so the final zero fallback is unreachable for real finite data. The inverse
branch is only used for a nonzero determinant. Xi's centering and positive quadratic
lower bound make the population augmented Gram nonsingular for the adjusted bounds.
There are no logs, real powers, infinite integrals, toReal, extrema, limits, or
partial-function defaults in T2 beyond the explicitly described OLS completion.

## SAP.P002a.T7

### Objects, definitions, and hypotheses

The quantifier order is: any type Omega with a measurable space; any measure mu
with total mass one; any strictly increasing sizes: N -> N; any natural dimension
k; any deterministic family P_j of covariate populations on Fin(sizes j); any
family Z_j:Omega -> Finset(Fin(sizes j)); any real delta,e,A,B,r; proofs of k>0,
delta<1, e,A,B>0, 0<r<=1/2; admissibility of EVERY P_j; strict positivity of EACH
population arm residual variance at EVERY j; exact measurable assignment marginals;
then any deterministic strictly increasing sub:N->N. Only after all these universal
choices does the almost-everywhere path quantifier occur.

Here a covariate population consists of real y_i(0),y_i(1), Boolean d_i(0),d_i(1),
natural m and vectors x_i in R^k. Write n=sizes j, C={i:d_i(0)=0,d_i(1)=1},
beta=sum_C(y_i(1)-y_i(0))/|C| and w_ai=y_i(d_i(a))-beta*d_i(a), encoding Booleans
as 0/1. The mean is M(q)=sum_i q_i/n and a subset mean is M_H(q)=sum_H q_i/|H|.
Variance and covariance are the centered sums divided by n-1. The fourth norm is
sqrt(sqrt(M(q^4))). Define h_i=(1,x_i),
G_H=M_H(h_i h_i^T), score_H(q)=M_H(h_i q_i), and
L_H(q)=G_H^{-1}score_H(q) when det(G_H) is nonzero, otherwise a classically chosen
minimizer of sum_H(q_i-h_i dot c)^2, otherwise zero if there is no such minimizer.
Let u_ai=w_ai-h_i dot L_all(w_a).

Admissibility (Xi) means n>=2, 0<m<n, d_i(0)=1 implies d_i(1)=1 for every i,
C nonempty, rn<=m<=(1-r)n,
Cov(u_1,u_0)>=-delta sqrt(V(u_1))sqrt(V(u_0)),
sqrt(sqrt(M(u_a^4)))<=B sqrt(V(u_a)) for both a,
sum_i x_is=0 and M(x_s^4)<=A for every s, and
e sum_s b_s^2<=M((sum_s x_is b_s)^2) for every b in R^k.
The additional positivity assumption is V(u_a)>0 for both a and every j. It does
not give a common lower bound in j. Notice that the fourth norm is of the residual
itself, with no extra centering operation (population OLS has an intercept).

For each j let D_j consist of all m-element subsets of Fin n. Finite conditional
probability is the number of subsets satisfying the event divided by |D_j|;
expectation is the uniform sum over D_j, and design variance is the uniform mean of
the squared deviation from that expectation.
The assignment assumption says, for EVERY j and EVERY predicate E on subsets,
{omega:E(Z_j omega)} is measurable and
mu{omega:E(Z_j omega)}=ofReal(P_Dj(E)). Thus every coordinate has the exact uniform
complete-randomization distribution, is supported on D_j almost surely, and is
measurable. No independence across j is imposed.

### Conclusion with all quantities expanded

On one mu-conull set, simultaneously for all positive real thresholds, four real
sequences tend to zero as j tends to infinity. For a given j put N=sub(j),
S0=Z_N(omega), q_i=y_i(d_i(1_{i in S0}))-beta*d_i(1_{i in S0}), and hold q fixed
while varying the reassignment S over D_N. Define c_H=L_H(q), c=L_all(q),
t_f(S)=M_S(q_i-sum_s x_is c_S,s)-M_{S^c}(q_i-sum_s x_is c_Sc,s),
t_o(S)=M_S(q_i-sum_s x_is c_s)-M_{S^c}(q_i-sum_s x_is c_s),
v_o=Var_DN(t_o), and
vhat(S)=sum_{i in S}(q_i-h_i dot c_S)^2/m^2
        +sum_{i in S^c}(q_i-h_i dot c_Sc)^2/(n-m)^2.
Here slope coordinates are used in t_f,t_o, while the residual sums include the
intercept. This oracle uses one pooled observed-response population fit.
Let H(x) be (gaussianReal 0 1)({z in R:x<=|z|}), converted from ENNReal to R.
The Gaussian has mean zero and variance one. The four sequences are:

1. For every kappa>0: P_DN(|t_f-t_o|>=kappa sqrt(v_o)).
2. For every x>0: |P_DN(|t_o|>=x sqrt(v_o))-H(x)|.
3. For every x>0: |P_DN(|t_f|>=x sqrt(v_o))-H(x)|.
4. For every kappa>0: P_DN(|vhat/v_o-1|>=kappa).

All use non-strict event inequalities. The same conull set works for the four
clauses and every positive threshold. The conull set may depend on the fixed
deterministic sequence and subsequence. Nothing quantifies a random subsequence or
one common event over all subsequences. Tendsto means the usual real limit via
the atTop filter on N and the neighborhood filter at zero on R.

The docstring explicitly claims exactly these four limits, usual measure-theoretic
conditions, arbitrary coupling across sizes, fixed least-squares completion on
singular arms, pointwise residual positivity, and no finite-size oracle-variance
positivity assumption.

### Totalizations and possible junk values

Every size is at least two and every assignment has nonempty arms almost surely.
The countable union over sizes of the marginal exceptional sets is null. Thus n,
n-1,m,n-m,|C| and |D_j| are positive whenever used on those paths. Subtractions in
these formulas are real subtraction; casts of natural sizes/cardinalities are exact.
The singleton-complier convention in group covariance is not used in Xi's covariance
condition, which is over the full population. Boolean encodings and finite subset
complements have their ordinary meanings. Dimension k>0 excludes an empty covariate
index; the augmented index also always contains the intercept.

Finite sums ensure all design moments exist. Every design variance and residual
fourth moment is nonnegative, so square roots do not use their negative-input
totalization. v_o CAN be zero at a finite size; then sqrt(v_o)=0 and the non-strict
events in (1)-(3) are automatically true. In (4) Lean's real vhat/0 is zero,
so the absolute error is one. None of these finite zero cases is excluded by an
explicit assumption. Their effect on the asserted limits must be justified, not
silently removed. The docstring correctly identifies this convention.

Singular arm fits use a selected least-squares minimizer, not an inverse of a
singular matrix. A finite least-squares minimizer exists; the final fallback zero
branch is unreachable. Population fits have full rank under Xi with e>0 and
centered covariates. normalTail's toReal cannot see infinity because its measure
is a probability measure. ENNReal.ofReal in the marginal law sees an ordinary
finite nonnegative probability. There are no log/rpow values, conditional-law
defaults, empty infima/suprema, or limsup/liminf conventions in this statement.
The conditional probabilities are explicit finite reassignment averages.

## SAP.P002a.T9

### Finite component

For every positive natural n, positive natural k, array x_i in R^k, real e>0,
with sum_i x_is=0 for every s, and with e<=lambda, the following hold.
Here M(q)=sum_i q_i/n,
C_st=M(x_is*x_it), h_i=(1,x_i),
G_st=M(h_is*h_it), normSq(b)=sum_s b_s^2,
lambda=inf {M((sum_s x_is b_s)^2): b in R^k, sum_s b_s^2=1}, and
lambda_aug=inf {M((h_i dot b)^2): b in R^(k+1), sum_s b_s^2=1}.
The infima are Mathlib's real sInf. The conclusions, all conjoined, are:
G_none,none=1; G_none,s=G_s,none=0 for all covariate indices s;
G_s,t=C_s,t for all s,t; lambda_aug=min(1,lambda);
min(1,e)<=lambda_aug; and
min(1,e) sum_s b_s^2 <= b dot (G b) for every augmented coefficient vector b.
Thus the block diagonal identity is stated entry by entry, with the exact least
Rayleigh value as well as its lower bound. No fourth-moment condition is imposed
on this finite component.

### Sequence component: objects and hypotheses

Independently of the finite component, for every type Omega, measurable space,
probability measure mu, strictly increasing deterministic natural sizes, natural
dimension k, deterministic family of covariate populations P_j, family of observed
assignments Z_j, and real constants delta,e,A,B,r, assume
k>0, delta<1, e,A,B>0, 0<r<=1/2, Xi at EVERY j, and exact measurable uniform
complete-randomization marginals. Next universally choose any deterministic
strictly increasing sub:N->N. There is no residual-variance positivity hypothesis.

For completeness, these predicates unfold as follows. The population has real
y_i(0),y_i(1), Boolean d_i(0),d_i(1), natural m, and real covariate coordinates x_is.
C={i:d_i(0)=0,d_i(1)=1}, beta=sum_C(y_i(1)-y_i(0))/|C|,
w_ai=y_i(d_i(a))-beta*d_i(a), using the real indicators 0/1.
For any H, M_H(q)=sum_H q_i/|H|,
G_H=M_H((1,x_i)(1,x_i)^T), score_H(q)=M_H((1,x_i)q_i).
L_H(q) is G_H^{-1}score_H(q) if det G_H is nonzero; otherwise it is a chosen
minimizer of sum_H(q_i-(1,x_i) dot c)^2 if one exists, and otherwise zero.
Let u_ai=w_ai-(1,x_i) dot L_all(w_a). Write
V(q)=sum_i(q_i-M(q))^2/(n-1),
Cov(q,t)=sum_i(q_i-M(q))(t_i-M(t))/(n-1).
Xi is the conjunction of n>=2, 0<m<n, monotonicity d_i(0)=1 implies d_i(1)=1,
C nonempty, rn<=m<=(1-r)n,
Cov(u_1,u_0)>=-delta sqrt(V(u_1))sqrt(V(u_0)),
sqrt(sqrt(M(u_a^4)))<=B sqrt(V(u_a)) for both a,
sum_i x_is=0 and M(x_s^4)<=A for every s,
and e sum_s b_s^2<=M((sum_s x_is b_s)^2) for every b in R^k.

D_j is the finite set of all m-element subsets of Fin(sizes j).
P_Dj(E)=|{S in D_j:E(S)}|/|D_j|. Exact measurable marginals mean, for every j
and every predicate E on subsets, the inverse image under Z_j is measurable and
its mu-measure is ENNReal.ofReal(P_Dj(E)). There is no independence assumption.

### Sequence conclusion and quantifier order

For mu-almost every omega THERE EXISTS a real sequence err_j tending to zero
SUCH THAT for all sufficiently large j and BOTH Boolean arms a, simultaneously,
the following inequality holds. Put N=sub(j), S=Z_N(omega),
q_i=y_i(d_i(1_{i in S}))-beta*d_i(1_{i in S}),
H_a=S for a=1 and H_a=S^c for a=0,
b=L_Ha(q)-L_all(q). Then
(min(1,e)+err_j) sum_s b_s^2 <= b dot (G_Ha b).
The error is allowed to depend on omega and on every previously chosen object,
including the subsequence, and one error and one eventual cutoff work for both
arms. It is not required to be nonnegative or measurable as a function of omega.
The statement gives the bound only for this coefficient-error vector b, rather
than for every vector at each random arm design. Tendsto uses atTop on N and
the usual neighborhoods of zero in R. The finite and sequence conclusions are
conjoined, without dependencies between their separately quantified data.

The docstring describes the same finite identity, least eigenvalue and quadratic
bound, followed by the corrected coefficient-error bound under every measurable
coupling, with the independent coupling as a special case.

### Totalizations and possible junk values

Positive n ensures all finite population means are genuine. Positive k ensures the
covariate unit sphere is nonempty, and the augmented unit sphere is also nonempty.
Both sets of Rayleigh values are nonempty, bounded below by zero, and bounded above
(finite-dimensional compact spheres and continuous quadratic functions). Thus their
real sInf values are actual finite infima and do not use sInf(empty)=0 or an
unbounded-set totalization. The minimum min(1,e) is strictly positive.

For sequences, n>=2, 0<m<n and nonempty C avoid all population, LATE, and arm mean
zero denominators on the conull set of valid assignments. Casts are exact and the
denominators n-1,n-m are real subtraction, not natural truncated subtraction.
Finite fourth moments and variances under Xi are nonnegative, so square roots
are ordinary nonnegative square roots. Zero residual variance is permitted and
does not enter a quotient. There is no variance denominator in the conclusion.
Singular sample arms use a selected genuine least-squares minimizer; the no-minimizer
fallback is unreachable for finite real data. The population augmented Gram is
positive definite under the centering and e>0 condition, so its inverse branch is
genuine. The real error may initially be sufficiently negative to make a bound
weak, but err->0 and min(1,e)>0 require a substantive eventual positive bound.

All probability cardinality denominators are positive under valid design; the
marginal law's ENNReal.ofReal acts on probabilities in [0,1]. Empty index types,
partial-function defaults, logs, real powers, toReal(infinity), undefined integrals,
and limsup/liminf totalizations do not enter T9.
