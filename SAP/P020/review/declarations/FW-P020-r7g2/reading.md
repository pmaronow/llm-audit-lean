# Blind reading

This file was written before opening `claims.json` or `record.json`. I read the
five Challenge docstrings and statements, all source definitions in their
closures, and printed every line-0 auxiliary proof in `scratch/ClosureProofs.lean`.
The auxiliary declarations prove finite-numeral bounds, positive sizes and arm
counts, or normalization/nonnegativity of uniform finite weights; they add no
unstated mathematical conditions.

## Finite-sum notation used below

These are expanded mathematical abbreviations, not additional assumptions.
`Fin M` is the set of natural numbers strictly less than the natural number M;
all sums below are Mathlib finite sums with real summands. For a real vector v
on `Fin M`, write

- m(v) = (sum over j < M of v_j) / (M : real);
- V(v) = (sum over j < M of (v_j - m(v))^2) / M;
- C(v,w) = (sum over j < M of
  (v_j - m(v))(w_j - m(w))) / M;
- d(v,x,k)_j = v_j - k(x_j - m(x)).

Thus the covariance/variance use divisor M, not M-1. A finite law consists of a
finite set S, a real function p on its ambient type, nonnegative p on S, and
sum over S of p = 1. Its expectation is exactly sum over S of p(t)f(t);
its variance is sum over S of p(t)(f(t) - sum over S of p(u)f(u))^2;
its covariance is the corresponding sum of centered products. Values outside
S are ignored. A normalized finite law cannot have empty support.

Whenever a population is used, its full data are natural M and t with 0 < t < M,
positive natural cluster sizes n_j for j < M, and two arbitrary real vectors
y0_j,y1_j of cluster potential totals. Put c = M - t in natural numbers,
N = sum over j < M of n_j, x_j = (n_j : real), and
A = {s contained in {0,...,M-1} : cardinality(s) = t}. A is nonempty.
The randomization is the uniform law on A; write
E_A f = (sum over s in A of f(s)) / cardinality(A),
Var_A f = E_A[(f - E_A f)^2], and
Cov_A(f,g) = E_A[(f - E_A f)(g - E_A g)].
For a set s let s-complement be {0,...,M-1} minus s. Treatment arm sums use s;
control arm sums use this complement. An observed cluster total is y1_j when
j is in s and y0_j otherwise. The individual-average effect is
Delta = (sum y1_j - sum y0_j) / N.

For a real coefficient k set a1_j(k) = d(y1,x,k)_j and
a0_j(k) = d(y0,x,k)_j. The adjusted arm-total estimates are
(M/t) sum over j in s of a1_j(k) and
(M/c) sum over j outside s of a0_j(k).
Their difference divided by N is
D_P(k,s) = (M/N)[(sum over s of a1_j(k))/t
                    - (sum over s-complement of a0_j(k))/c].
All natural denominators in real arithmetic are cast to real numbers.

## SAP.P020.T6

Source: `SAP/P020/Challenge/Part1.lean:40-42` and
`SAP/P020/Defs/Part3.lean:173-203`.

There are no quantified inputs or hypotheses: this is a conjunction of exact
computations for the fixed population M=3, t=1, n=(1,2,3), y0=(0,0,0),
y1=(0,0,3). Its support A consists of the three singleton sets s0={0}, s1={1},
s2={2}, each of probability 1/3. N=6 and Delta=1/2.

For every set s define the fitted slope
q(s) = C(x, o(s))/V(x), where o_j(s) = y1_j if j is in s and y0_j otherwise.
This is the usual slope with an intercept from the three observed cluster
totals regressed on the three cluster sizes. The theorem states all of:

- q(s0)=0, q(s1)=0, q(s2)=3/2;
- D_P(q(s0),s0)=0, D_P(q(s1),s1)=0,
  D_P(q(s2),s2)=3/8;
- E_A[D_P(q(s),s)]=1/8, this expectation is unequal to Delta, and
  E_A[D_P(q(s),s)]-Delta=-3/8;
- Cov_A(q, u)=1/2 and Cov_A(q, v)=-1/4, where
  u(s)=(sum over j in s of n_j)/t and
  v(s)=(sum over j outside s of n_j)/c;
- N=6, V(x)=2/3;
- (u(s0),u(s1),u(s2))=(1,2,3) and
  (v(s0),v(s1),v(s2))=(5/2,2,3/2);
- E_A[D_P(q(s),s)]-Delta
  = (M/N)[Cov_A(q,v)-Cov_A(q,u)].

The docstring calls this an explicit nondegenerate OLS witness and describes its
mean, bias, assignment values, and the two covariances.

Junk-value audit: real division is totalized with division by zero equal to
zero. Here t=1, c=2, M=3, N=6, cardinality(A)=3 and V(x)=2/3, so every
denominator is nonzero. The natural subtraction M-t=2 is exact, with no
truncation. All finite indices are in bounds (the printed numeral-bound proofs
certify this), all individual sizes are positive, and the law has nonempty
support. No empty sums, undefined moments, partial functions, logarithms,
square roots, real powers, Bochner integrals, infinity conversions, extrema,
or limits are used. No junk value affects this statement.

## SAP.P020.T7

Source: `SAP/P020/Challenge/Part1.lean:44-46` and
`SAP/P020/Defs/Part3.lean:205-230`.

There are four independently universally quantified conjuncts, in this order:

1. For every natural n, every Y:Fin n -> real, and every real b0,b1,
   sum over i<n of (b0+b1 Y_i) = n b0 + b1 sum over i<n of Y_i.
2. For every population P as specified above, every arm a in Bool, every real
   b0,b1,k, and every j:Fin M: replace each y^a_j by
   y'^a_j = n_j b0 + b1 y^a_j, preserving M,t,n and their certificates.
   With k'=b0+b1 k, the centered adjusted total satisfies
   d(y'^a,x,k')_j = b0(N/M) + b1 d(y^a,x,k)_j.
   The arm Bool chooses y1 for true and y0 for false.
3. For every P, then real b0,b1,k, then set s of finite cluster indices,
   then a proof that s has exactly t elements, the conjunction holds:
   D_P'(k',s) = (M/N)[
     (sum over j in s of (b0 N/M + b1 a1_j(k)))/t
     - (sum over j outside s of (b0 N/M + b1 a0_j(k)))/c],
   and D_P'(k',s)=b1 D_P(k,s).
4. With the same quantifier order and assignment hypothesis as in (3),
   D_P'(k',s) = (M/N)[b1 (sum over s of a1_j(k))/t
                            - b1 (sum over s-complement of a0_j(k))/c],
   and that displayed right-hand side equals b1 D_P(k,s).

Here every D is exactly the finite sum defined in the preceding notation;
no stochastic or asymptotic assumption is involved. The docstring describes
individual affine transformation, coefficient transformation, potential-total
identities and the corrected estimator equality chain.

Junk-value audit: (1) permits n=0, so its domain is empty and both sums are
zero, and n b0=0. This is a legitimate empty-sum extension, without division.
For (2)-(4), 0<t<M implies M>=2 and c>0; positive sizes imply N>0.
Thus M,t,c,N are all nonzero in real arithmetic, natural subtraction M-t
does not truncate, and neither arm is empty for admissible s. Arbitrary
b0,b1,k, including zero, require no inverses and cause no degeneracy.
All casts preserve the finite natural sizes exactly. No nonintegrable mean,
infinite value, partial function, log/sqrt/rpow, supremum/infimum, or limit is
involved. No junk value affects this statement.

## SAP.P020.T8

Source: `SAP/P020/Challenge/Part1.lean:48-50` and
`SAP/P020/Defs/Part3.lean:232-255`.

The statement is a conjunction of three independent universal assertions:

1. For every implicit natural M, a proof 0<M, vectors v,x:Fin M -> real,
   and real k, m(d(v,x,k))=m(v).
2. For every implicit natural M, a proof 0<M, v,x:Fin M -> real,
   and real k,
   V(d(v,x,k)) = V(v)+k^2 V(x)-2k C(v,x).
3. For every implicit natural M, a proof 0<M, v,w,x:Fin M -> real,
   and real k, let delta_j=x_j-m(x) and Q=C(d(v,x,k),d(w,x,k)).
   All seven equalities below hold:

   Q = m(d(v,x,k) d(w,x,k)) - m(d(v,x,k)) m(d(w,x,k));

   Q = m((v-k delta)(w-k delta)) - m(v)m(w);

   Q = m(vw-vk delta-wk delta+k^2 delta^2) - m(v)m(w);

   Q = m(vw)-m(v)m(w)-m(vk delta)-m(wk delta)+m(k^2 delta^2);

   Q = C(v,w)-k(C(v,x)+m(v)m(delta))
               -k(C(w,x)+m(w)m(delta))+k^2 V(x);

   Q = C(v,w)-k(C(v,x)+m(v)0)-k(C(w,x)+m(w)0)+k^2 V(x);

   Q = C(v,w)-k C(v,x)-k C(w,x)+k^2 V(x).

Vector products and squares inside m are pointwise; m,V,C,d are precisely the
real finite-sum expressions at the beginning of this reading. There is no
population, randomization, positivity requirement on x, or nonzero-variance
hypothesis. The single generic variance identity applies to either arm vector.
The docstring describes preserved means, both arm variance expansions, and
the corrected covariance expansion.

Junk-value audit: M is the only denominator, and the explicit 0<M guards it.
Constant vectors, zero variance and k=0 are legitimate algebraic cases, with
no division by a variance. The index type is nonempty; all quantities are
finite real sums. No subtraction of natural sizes, partial functions,
integrals, log/sqrt/rpow, infinite conversions, extrema, or limits occur.
No junk value affects the result.

## SAP.P020.T9

Source: `SAP/P020/Challenge/Part1.lean:52-54` and
`SAP/P020/Defs/Part4.lean:11-41`.

There are no quantified inputs or hypotheses. Four concrete conjuncts are
asserted, using two populations:

- P has M=2,t=1,n=(1,2),y0=(0,0),y1=(1,2).
- B has the same M,t,n but y0=y1=(0,2).

For P put s={0}, b0=0,b1=1,k=0. Then s is an admissible assignment,
D_P'(0,s)=2/3, whereas
W=(M/N)[(sum over s of d(y1,x,0))/t
               -(sum over s-complement of d(y1,x,0))/c]=-2/3,
and D_P'(0,s) is unequal to W. The transformed population P' is P itself.
The second arm in W deliberately uses the treatment potential y1.

For B, s={0} is admissible, C(y0,y1)=1, while
m(y0)y1_0-m(y0)m(y1)=-1, and the covariance is unequal to this last
expression. A third conjunct repeats the bracket calculation for the bare
real vectors v=w=(0,2): C(v,w)=1, m(v)w_0-m(v)m(w)=-1,
m(v)w_1-m(v)m(w)=1, and the covariance differs from the expression at
index 0. The fourth conjunct explicitly states D_P(0,{0})=2/3.

The docstring describes two admissible witnesses against a control-subscript
expression and an expectation-bracket expression, evaluating the latter at
both clusters. The statement itself supplies numerical inequalities, without
quantifying over a printed claim or proving a general corrected formula.

Junk-value audit: both populations have M=2,t=c=1,N=3, both sizes are
positive, and the chosen set is a singleton in the correct two-element
universe. Every denominator M,t,c,N is nonzero. Natural M-t is exact.
The covariance is a finite uniform-cluster sum, not a conditional or design
expectation. No random replicate dependence, empty types, undefined moments,
integrals, logs, square roots, real powers, infinity conversions, extrema,
limits or partial functions are used. The mismatches are ordinary arithmetic,
not junk-value artifacts.

## SAP.P020.T10

Source: `SAP/P020/Challenge/Part1.lean:56-58` and
`SAP/P020/Defs/Part4.lean:43-58`.

The statement is a conjunction of two independently universally quantified
assertions. Each quantifies, in order, a population P, individual potential
data I, a sharp-null proof, a finite set s, and a proof s is admissible.
The population data and randomization are exactly as expanded above.
I consists of Y0_j,Y1_j:Fin(n_j) -> real with certificates
sum over i<n_j of Y0_ji=y0_j and
sum over i<n_j of Y1_ji=y1_j. The sharp-null hypothesis is
for every j and i, Y0_ji=Y1_ji. The observed individual O_ji(s) is Y1_ji
when j is in s and Y0_ji otherwise.

The first universal assertion concludes both:

- for every j then i, Y0_ji=O_ji(s) and Y1_ji=O_ji(s);
- for every j, y0_j=y1_j.

The second universal assertion concludes the full conjunction:

- for every j, y0_j=o_j(s) and y1_j=o_j(s), where o is the observed total;
- V(y0)=V(y1);
- V(y1)=V(o(s));
- C(y0,y1)=V(o(s));
- Var_A H=F(P);
- F(P)=G(P,s).

Here all three new quantities are expanded as follows:

H(s) = [(M/t) sum over j in s of y1_j
        -(M/c) sum over j outside s of y0_j]/N;

F(P) = (M^2/N^2)[
 (M/(M-1))(V(y0)/c+V(y1)/t)
 +(1/(M-1))(2C(y0,y1)-V(y0)-V(y1))];

G(P,s) = M^4 V(o(s))/[N^2(M-1)ct].

Var_A is the actual finite randomization variance expanded earlier; thus the
assertion identifies actual HT variance, its general potential-total formula,
and a formula in the observed cluster-total variance under the individual
sharp null. This matches the subjects named in the blind docstring.

Junk-value audit: 0<t<M implies M>=2 and c>0; all n_j>0 imply N>0,
so t,c,M,M-1,N and the squared/product denominators are nonzero. M-t is
natural subtraction without truncation; M-1 in the formulas is real
subtraction. The assignment law is nonempty uniform finite support, every
individual index type has positive cardinality, all observations are explicit
if-then-else expressions, and every moment is a finite real sum. The sharp
null permits zero variance, but variance is never a divisor. There are no
nonintegrable integrals, log/sqrt/rpow, infinity conversions, extrema, limits,
or default values of partial functions. No junk value affects the result.
