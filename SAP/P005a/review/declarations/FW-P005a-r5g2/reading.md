# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: all entries of
`closure.json`, the five Challenge declarations and docstrings, and their source
definitions in Defs Part1, Part2, Part3, Part4, Part6, Part7, and WholeW2.
`scratch/BlindClosure.lean` also printed every line-zero/generated dependency,
the Population constructor/projections, and the Arm constructors/recursors.
Those auxiliary proofs certify numeral instances, the index 0 in Fin 1, and
ordinary equality case analysis; they add no statistical hypotheses.

## Mathematical notation used to unfold the definitions

This dictionary is part of each section below. All its operations are finite
sums, real field operations, finite matrices, real supremum, and Mathlib limits.
It leaves no SAP statistical notion uninterpreted.

For natural numbers n,d, the units are U={0,...,n-1} and coordinates are
{0,...,d-1}. A population is exactly three arbitrary real arrays
x:U→R^d, yT:U→R, yC:U→R, with no properties built into its type.
The generated constructor constructs those arrays and the projections return
them. Put x_i·v=Σ_{k<d}x_ik v_k and h_i=Σ_{k<d}x_ik².
For A⊆U, write

* ā_A=(Σ_{i∈A}a_i)/|A|; ā=ā_U; a_i°=a_i-ā.
* x̄_A,k=(Σ_{i∈A}x_ik)/|A|.
* C_A(a,b)=overline{ab}_A-ā_A b̄_A; C(a,b)=C_U(a,b).
* G_kl=(1/n)Σ_i x_ik x_il.
* L_A,kl=overline{x_k x_l}_A-x̄_A,k x̄_A,l;
  N_A(y)_k=overline{y x_k}_A-ȳ_A x̄_A,k.
* β(y)_k=(1/n)Σ_i y_i x_ik, and β̂_A(y)=L_A^{-1}N_A(y).
* ν2_A(y)=(L_A^{-1}-I)N_A(y),
  ν3_A(y)_k=-x̄_A,k overline{y°}_A.
* e_i(y)=y_i-ȳ-x_i·β(y).
* D={S⊆U:|S|=m}; Sᶜ=U\S. E_m f=(Σ_{S∈D}f(S))/|D|,
  and P_m(B)=|{S∈D:B(S)}|/|D|. There is one uniform draw of a
  labelled subset, not a sequence of replicated draws.
* τ=ȳT-ȳC,
  τ̂(S)=ȳT_S-ȳC_{Sᶜ}-x̄_S·β̂_S(yT)+x̄_{Sᶜ}·β̂_{Sᶜ}(yC),
  and leading(S)=overline{e(yT)}_S-overline{e(yC)}_{Sᶜ}.
* κ=sup_{i∈U}(h_i/n). Standardization means x̄_U=0 and G=I.
  Regularity means det L_S≠0 and det L_{Sᶜ}≠0 for every S∈D.
* p=m/n and
  A(n,s)=(n-s)(n-2s)/[(n-1)(n-2)s²]; the control coefficient is
  A(n,n-m), with n-m computed in the natural numbers before this call.
* For a varying natural allocation m(n), real functions R_n on subsets of
  U_n, and real scale r_n, the asserted order R=O_p(r) means exactly
  ∀ε∈R, ε>0 ⇒ ∃M∈R, M>0 ∧ ∃N∈N, ∀n≥N,
  |{S∈D_n:|R_n(S)|>M r_n}|/|D_n|<ε.
* The sequence assumptions from size b mean: for every n≥b,
  1≤d(n)≤n and 0<m(n)<n; there is one K≥0 bounding
  (1/n)Σ_i yT_ni², (1/n)Σ_i yC_ni², and every
  (1/n)Σ_i x_nik² for all those n; x̄_n=0 and G_n=I eventually;
  and there are real 0<lo<hi<1 with lo<m(n)/n<hi for every n≥b.
  `standingAssumptions` uses b=3. `wholeStandingAssumptions` uses the
  quantified starting size b. Neither definition includes a leverage rate or
  invertibility.
* The inverse-free corrected arm value for s=|A| is
  H_A(y)=ȳ_A-x̄_A·N_A(y)+(n-s)/[(n-2)s] C_A(h,y).
  Arm is an ordinary two-element type: treated chooses A=S,y=yT;
  control chooses A=Sᶜ,y=yC. Its decidable equality is ordinary equality.

All n,s,m in displayed real arithmetic are their real casts unless explicitly
described as natural subtraction/division. Limits at infinity mean the Mathlib
filter `atTop` on N, and real limits use ordinary real neighborhoods. Eventual
assertions mean they hold for all n beyond some natural threshold.

## SAP.P005a.T6

The docstring promises the two third-moment identities, the negative signs in
the ν3 components, and the corrected control-minus-treatment identity for
centered covariates. The proposition universally quantifies n,d,m∈N, then an
arbitrary population, then hypotheses n≥3, m>0, m<n, x̄_U=0. There is no
standardized-Gram, positive-dimension, moment-growth, or invertibility premise.
For every such choice it asserts all five equalities:

1. E_m[||x̄_S||² overline{yT°}_S]=A(n,m) C(h,yT).
2. E_m[||x̄_{Sᶜ}||² overline{yC°}_{Sᶜ}]=A(n,n-m) C(h,yC).
3. E_m[x̄_S·ν3_S(yT)]=-A(n,m) C(h,yT).
4. E_m[x̄_{Sᶜ}·ν3_{Sᶜ}(yC)]=-A(n,n-m) C(h,yC).
5. The expectation in 4 minus the expectation in 3 equals
   -A(n,n-m) C(h,yC)+A(n,m) C(h,yT).

Here ||x̄_A||² is explicitly Σ_{k<d}x̄_A,k², and the ν3
expressions are explicitly -Σ_k x̄_A,k² overline{y°}_A.

Junk conventions: real division by zero is zero, but n≥3 and 0<m<n make
both arms, the design, and every denominator in these identities nonzero.
The natural subtraction n-m is untruncated under m<n. Arithmetic inside
A is real subtraction, so n-2m may be negative and its sign is retained.
The empty coordinate type d=0 is allowed: all dots and leverages are zero,
so the identities then hold as zero equalities. This does not make the
universal statement vacuous. No inverse, square root, logarithm, integral,
extended-real conversion, supremum, infimum, or limsup is used here.

## SAP.P005a.T7

This is a conjunction about one specified sequence; it has no external
hypotheses. Its docstring calls that sequence a refutation of a printed
stochastic order, and advertises exact finite calculations as well.
For each natural n set d=1, m=floor(n/2). For i<n define

* v_0=0 and v_i=-1+2(i-1)/(n-2) for i≠0;
* a_0=1 and a_i=v_i/n² for i≠0; z_i=a_i-1/n;
* q=(1/n)Σ_i z_i²; x_i=z_i/sqrt(q); yT_i=yC_i=v_i;
* B=(Σ_i z_i v_i)/(Σ_i z_i²), E_i=v_i-Bz_i;
* F_n(A)=v̄_A+(1/n-ā_A) C_A(a,v)/C_A(a,a);
* R_n(S)=τ̂(S)-τ-leading(S) and r_n=sqrt(κ_n/n).

It asserts, conjunctively:

* The sequence assumptions above from b=3 hold. For every n≥6 it is
  standardized, both outcome second moments are ≤1, its covariate second
  moment is exactly 1, 1/4<m/n<3/4, and every assignment is regular.
* κ_n→1, κ_n log(1)→0, τ_n=0 for all n≥6, and for all even n≥6 and
  every S∈D_n, n-6≤|R_n(S)|. The sequence R is **not** O_p(r).
* For every n≥6, q>0 and κ_n log(1)=0.
* For every n≥6, Σ_i v_i=0,
  Σ_i v_i²=n(n-1)/[3(n-2)], ā=1/n, and
  q=(n-1)/n² [1+1/(3(n-2)n²)]. Outcomes agree in absolute value
  and have absolute value ≤1. For every S∈D_n both arm sizes are at
  least 3 and both scalar variances C_A(x,x) are strictly positive.
* For every n≥6,
  κ_n=(1-1/n)²/(nq)=3n(n-1)(n-2)/[3n²(n-2)+1],
  and for all i,j<n with j=0, x_i²≤x_j².
* For every n≥6 and every A⊆U containing 0 with |A|≥2,
  |C_A(a,v)/C_A(a,a)|≤2. If n is even and |A|=floor(n/2),
  also |F_n(A)|≤25/18.
* For every n≥6, B=n²/[3n²(n-2)+1], 0≤B≤1/12,
  both population slopes equal sqrt(q)B, both residual arrays equal E,
  and |E_i|≤13/12 for every i. For every assignment,
  leading(S)=Ē_S-Ē_{Sᶜ}, |leading(S)|≤13/6, and 13/6<3.
* For every n≥6 and every A with |A|≥2,
  v̄_A-x̄_A β̂_A(v)=F_n(A). If A excludes 0 then v_i=n²a_i
  throughout A and F_n(A)=n.
* For every even n≥6 and every assignment, n-3≤|τ̂(S)|.
* For every n≥6, 0<r_n≤1/sqrt(n). For every even such n and every
  assignment, (n-6)sqrt(n)≤|R_n(S)|/r_n.
  The real sequence (2j-6)sqrt(2j) tends to +infinity as j→infinity.
  For every real M there is N≥6 such that for every even n≥N,
  P_{floor(n/2)}(|R_n|>M r_n)=1.
* At n=6 there are 20 assignments, κ=360/433, B=36/433, and the
  minimum over assignments of |R| equals 4357386/779833, within 1/200
  of 559/100. At n=12 the corresponding count is 924, κ=3960/4321,
  B=144/4321, and minimum 8690712840/752921287, within 1/200 of
  1154/100. Each minimum is expressed as a lower bound for **every**
  assignment plus existence of an assignment attaining it, not as an infimum.

Junk conventions: floor(n/2) is natural division. The subtraction i-1 in
v_i is natural truncated subtraction, but it is used only on the i≠0 branch,
where i≥1. All other displayed n-2, n-6, 2j-6 terms are real
subtractions, including the tail-limit term. Divisions at n=0,2 and sqrt
of q=0 are totalized; the important finite assertions start at n≥6, where
q>0, and the sequence assumptions at n≥3 use positive finite values.
Real.sqrt(t)=0 for t≤0; here the asserted q and r are positive on the tail.
The scalar slope and matrix inverse have zero defaults for singular
covariances/matrices. Distinct raw covariates and |A|≥2 exclude these
defaults in all fitted-line claims, and regularity/positive variances exclude
them for all assignments at n≥6. The supremum defining κ is over a finite
nonempty set when n≥1, hence is a genuine maximum; at n=0 it is the
default empty real supremum, which cannot change any tail assertion.
log(1)=0 is the ordinary logarithm at a positive argument, not log's
out-of-domain convention. Early n may yield empty designs, zero means,
undefined-in-ordinary-mathematics ratios assigned zero, or empty unit types;
all are ignored by the eventual order and limits. Finite minima explicitly
assert attainment. No integrals, toReal, rpow, limsup, or liminf occur.

## SAP.P005a.T9

The docstring promises a repaired interacted expansion under a stronger
logarithmic condition and describes its relation to other logarithms.
The proposition is a conjunction of the following independent universals.

First, for every natural d≥1,
log(max(d,2))≤log(2d)≤2log(max(d,2)). Next, for all sequences
d:N→N and k:N→R such that eventually d_n≥1 and k_n≥0:

* k_n log(2d_n)→0 iff k_n log(max(d_n,2))→0;
* k_n log(2d_n)→0 implies both k_n→0 and k_n log(d_n)→0;
* if eventually d_n≥2, k_n log(d_n)→0 iff k_n log(2d_n)→0.

Second, universally choose a starting size b≥2, then d,m:N→N, then a
population sequence of types Population n (d_n). Assuming the sequence
conditions from b, eventual regularity at every assignment at each size, and
κ_n log(2d_n)→0, conclude

  τ̂_n(S)-τ_n-leading_n(S)=O_p(sqrt(κ_n d_n/n)).

The remainder has no term left implicit: it is the finite arm-slope
expression τ̂ in the dictionary minus the population mean difference and
the two sample means of the population residuals. The conclusion expands
to the ε,M,N tail-probability quantifiers in the dictionary. Invertibility
is required eventually, not at every n before the tail.

Third, universally for eventually positive integer d_n and eventually
nonnegative real k_n,

  k_n log(2d_n)→0 iff
  [k_n log(d_n)→0 and (if d_n=1 then k_n else 0)→0].

Thus the dimension-one clause refers to the possibly intermittent
dimension-one indices, using zero elsewhere.

Junk conventions: all eventual hypotheses can ignore early d=0, n=0,
empty designs, empty supremum, singular inverses, and Real.log(0)=0.
On the relevant tail d≥1, log arguments 2d and max(d,2) are ≥2;
log(d) is valid also at d=1, where its true value is zero. There is no
negative logarithm argument. Real.log outside its positive domain would use
log(abs(t)) for t<0 and zero at t=0, but this cannot affect the limits here.
Natural products 2*d are unbounded integer products followed by exact real
casts; no machine overflow is present. κ is a finite maximum on nonempty
unit types. Standardization and positive dimension eventually make κ>0;
the square-root scale is nonnegative and eventually positive. Every
randomization space on the tail is nonempty, with both arms nonempty, and
the required inverses are genuine. No integrals, toReal, sInf, limsup,
liminf, or rpow occur.

## SAP.P005a.T10

This is another unconditional conjunction specifying a counterexample.
Here n=6,d=1,m=2, a=(-3,-2,-1,0,1,5), t=sqrt(3/20),
x_i=t a_i, yT_i=y_i=a_i², yC_i=0. For every subset A of six units
define W_c(A)=ȳ_A-x̄_A N_A(y)+c C_A(h,y). This defines W even
for the empty subset. The docstring calls the c=1/8 expression printed,
and says c=1/2 gives an unbiased correction.

The statement asserts every one of the following:

* x̄=0, G=1; regularity of all size-two assignments;
  (1/6)Σ_i y_i²≤121; 1/4<2/6<3/4.
* E_2 W_{1/8}=4913/1200, E_2 W_{1/2}=20/3,
  ȳ=20/3, and E_2 W_{1/8}≠ȳ.
* There are 15 assignments; a is injective. For each assignment both
  scalar variances are positive, and for A=S and A=Sᶜ,
  C_A(x,x)=(3/20)C_A(a,a).
* For every i, h_i=(3/20)a_i²;
  overline{a²}=40/6; h̄=1; C(h,y)=343/30.
* 2/[(6-2)4]=1/8 and 4/[(6-2)2]=1/2.
* For **every** A⊆U, including empty A,
  W_{1/8}(A)-W_{1/2}(A)=-(3/8)C_A(h,y),
  x̄_A N_A(y)=(3/20)ā_A[overline{ay}_A-ā_A ȳ_A],
  and C_A(h,y)=(3/20)[overline{a²y}_A-overline{a²}_A ȳ_A].
* E_2 C_S(h,y)=(3/5)(343/30), and
  E_2 W_{1/8}-E_2 W_{1/2}=-1029/400.

Junk conventions: sqrt(3/20) is strictly positive, and every design arm
has size 2 or 4, so no mean, expectation, or randomization denominator
vanishes. All relevant covariances/matrices are positive and invertible;
the matrix-inverse default is not used. The generic identities over all
subsets also include empty A, whose means and covariances are zero because
0/0=0. Those polynomial identities extend to this default without making
the actual counterexample empty or undefined. No supremum, logarithm,
asymptotic order, integral, toReal, rpow, or extremum convention is involved.

## SAP.P005a.T11

The docstring promises inverse cancellation, generic arm expectations,
correct weights and their uniqueness as cancelling coefficients, a singleton
case, leverage bounds, and both asymptotic arm orders without an added rate.
The proposition conjoins several universal statements; none is an existential
choice of a favorable coefficient in place of the stated coefficient.

1. For all n,d, populations, subsets A, real arrays y, and real c, if
   n≥3, A is nonempty, and det L_A≠0, then

       ȳ_A-x̄_A·β̂_A(y)-[-x̄_A·ν2_A(y)-c C_A(h,y)]
       =ȳ_A-x̄_A·N_A(y)+c C_A(h,y)
       =ȳ_A-x̄_A·β(y)-x̄_A·[N_A(y)-β(y)]+c C_A(h,y).

   The quantifiers are population, A, y, c, then the hypotheses; there
   is no centering or standardization assumption in these algebraic identities.

2. For all populations with n≥3, 2≤m<n, x̄=0, and every real c,

       E_m[ȳ_S-x̄_S·N_S(yT)+c C_S(h,yT)]
       =ȳT+[-(n-m)/(m(n-1))+A(n,m)
              +c(m-1)n/(m(n-1))] C(h,yT).

   The bracket is zero iff c=(n-m)/[(n-2)m]. The expectation of
   H_S(yT) equals ȳT. With c=m/[(n-2)(n-m)] instead, the expectation
   is ȳT plus

       [m²-(n-m)²]/[(n-2)m(n-m)] · [(m-1)n/(m(n-1))] C(h,yT).

3. For all populations with n≥3, 0<m<n, n-m≥2, x̄=0, and every
   c, the corresponding control expectation is

       E_m[ȳC_{Sᶜ}-x̄_{Sᶜ}·N_{Sᶜ}(yC)+c C_{Sᶜ}(h,yC)]
       =ȳC+[-m/((n-m)(n-1))+A(n,n-m)
              +c(n-m-1)n/((n-m)(n-1))] C(h,yC).

   The bracket vanishes iff c=m/[(n-2)(n-m)];
   E_m H_{Sᶜ}(yC)=ȳC.

4. For every sequence satisfying the assumptions from b=3 and each
   of the two arms, putting A=S or Sᶜ and y=yT or yC, respectively,

       H_A(y)-[ȳ_A-x̄_A·β(y)]=O_p(sqrt(κ_n/n)).

   There is no invertibility or additional rate premise for this inverse-free
   statement. It has the full ε,M,N quantifiers specified above.

5. For all natural n,s with n≥3 and 2≤s<n,

       (n-s)/[n(s-1)]-A(n,s)·[s(n-1)]/[(s-1)n]
       =(n-s)/[(n-2)s].

6. For all populations with n≥3, 0<s<n, x̄=0, then for all real
   arrays y and real c, let
   b(n,s,c)=-(n-s)/[s(n-1)]+A(n,s)+c(s-1)n/[s(n-1)].
   The expectation over uniform size-s A of
   ȳ_A-x̄_A·N_A(y)+c C_A(h,y) is ȳ+b(n,s,c)C(h,y),
   and E_s H_A(y)=ȳ. If s≥2, b=0 iff c=(n-s)/[(n-2)s].
   If s=1 then b=0 for every c. These are coefficient uniqueness
   assertions, not uniqueness of an unbiased estimator when C(h,y)=0.

7. For all populations with n≥3, 0<m<n, x̄=0, and real c, the
   same control expectation equals ȳC+b(n,n-m,c)C(h,yC), and
   E_m H_{Sᶜ}(yC)=ȳC. This includes control singletons.

8. For all populations with n>0 and G=I, d/n≤κ≤1 and h_i≤n for
   all i. Mean-zero covariates are not required for this bound.

9. For every starting size b≥2, all population sequences satisfying
   the sequence assumptions from b, and each of the two arms, the same
   O_p(sqrt(κ_n/n)) assertion as in item 4 holds.

Junk conventions: the determinant hypothesis excludes singular inverse
defaults in item 1. All finite expectations require n≥3 and 0<s<n, so
no sample or design mean is over an empty set and n-2,s,n-1 are nonzero.
The unsimplified weight divides by s-1 only where s≥2. In singleton
claims this division is absent: s-1 appears only as a multiplier, the
coefficient b vanishes, and sample covariances are genuinely zero.
Natural subtraction n-m equals ordinary subtraction under m<n.
The generic arm value H for empty A would use division by zero, but the
finite conclusions never use an empty arm. In asymptotic conclusions,
early invalid sizes, empty suprema, and zero/negative-domain square roots
cannot affect an eventual assertion: eventually the design and both arms
are nonempty, n≥3, standardization holds, and κ>0. For the leverage
inequality n>0 makes the finite supremum a real maximum, including d=0
where κ=0 and the inequalities remain meaningful. Empty coordinate
types are allowed in the finite universals and simply make vectors/dots
zero; the sequence assumptions force positive dimension on the tail.
No Bochner integral, nonintegrability convention, toReal of infinity,
rpow, sInf, limsup, liminf, or partial-function default is used.
