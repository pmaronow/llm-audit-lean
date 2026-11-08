# Blind reading

Written before opening `claims.json` or `record.json`. The sources read were the two
Challenge declarations and every declaration named in their `closure.json`
entries. Generated declarations with line 0 were additionally printed by Lean;
their types and bodies are in `scratch/closure-proofs.log`.

## SAP.P037c.T34

The theorem at `SAP/P037c/Challenge/Part1.lean:60` has no parameters or
hypotheses outside its defined proposition. It asserts the conjunction described
below. Its docstring describes constant-effect imputation with fixed controls,
reduced controls, a concrete loss-of-control example, and aliased designs.

### Expanded notation and operations

All vectors have real entries. `Fin n` means the integers 0 through n-1.
Matrices are functions of a row and column index; multiplication, matrix-vector
multiplication, and dot products are finite sums. For a category assignment
D : Fin n -> Fin 4 and a control matrix C with p columns, write

    H(D,C)[i,j] = 1{D(i)=j}             if 0 <= j < 4,
                 C[i,j-4]             if 4 <= j < 4+p.

Thus the first four columns are category indicators, with no separate intercept,
and all remaining columns are fixed covariates. This expands `pooledExposureRow`.
For a real weight vector w and real design H, write

    L(w,H) = (H^T diag(w) H)^(-1) H^T diag(w).

This is exactly `regressionMap`, using Mathlib's total nonsingular matrix inverse.
Write `Min(w,H,y,b)` for the assertion that, for every coefficient vector c,

    sum_i w_i (y_i - sum_j H_ij b_j)^2
       <= sum_i w_i (y_i - sum_j H_ij c_j)^2.

This expands `regressionMinimum`; it does not assert uniqueness. Write
`Col(H) = {H v : v is a real coefficient vector}`. This is the range of
Mathlib's linear map `H.mulVecLin`, as a real submodule, not an informal rank
surrogate. Write `Est(H,ell)` for

    for every v, H v = 0 implies ell(v) = 0,

where ell is a real linear map from the coefficient space to R. This expands
`wholeEstimable`. Finally, for any finite index set Omega, real functions prob,f,

    V_prob(f) = sum_z prob(z) f(z)^2 - (sum_z prob(z) f(z))^2.

This expands `wholeVariance`. Normalization and nonnegativity are separate
hypotheses at its uses, rather than part of this function's type.

### 1. Fixed-control identities (`SameControlCertificate`, `SameControlExtra`)

For every finite type Omega (with its `Fintype` instance), independently for each
of the two conjuncts, quantify in the following order:

1. Natural numbers n,p, and a proof n>0;
2. D0 : Fin n -> Fin 4, D : Omega -> Fin n -> Fin 4;
3. C : Matrix (Fin n) (Fin p) R;
4. w0 : Fin n -> R and w : Omega -> Fin n -> R;
5. proofs all w0_i>0 and all w(z)_i>0;
6. proofs the maps v -> H(D0,C)v and, for every z, v -> H(D(z),C)v
   are injective (full column rank);
7. y : Fin n -> R, prob : Omega -> R, and proofs prob(z)>=0 for all z
   and sum_z prob(z)=1.

With these inputs define

    b0 = L(w0,H(D0,C)) y,
    cbar_j = (sum_i C_ij)/n,
    row(k) = (four category indicators for k, cbar_0,...,cbar_(p-1)),
    m_k = row(k) dot b0,
    r = y - H(D0,C)b0,
    ystar(z)_i = y_i + m_(D(z)_i) - m_(D0_i),
    Lz = L(w(z),H(D(z),C)).

The conclusions of `SameControlCertificate` are all of the following:

- For every k,l in Fin 4, m_k-m_l=b0_k-b0_l (indices k,l refer to
  the first four coefficients).
- For every z, Lz H(D(z),C) is the (4+p)-dimensional identity, and
  Lz ystar(z)=Lz r+b0.
- For every z and k, row(k) dot Lz ystar(z)=row(k) dot Lz r+m_k.
- For every k,l, the variances, under prob, of
  (row(k)-row(l)) dot Lz ystar(z) and (row(k)-row(l)) dot Lz r are equal.

The conclusions of `SameControlExtra`, under the same independently quantified
inputs, are:

- For every z,i, ystar(z)_i=y_i-b0_(D0_i)+b0_(D(z)_i).
- For every z, ystar(z)=r+H(D(z),C)b0.
- For every k, the variances of row(k) dot Lz ystar(z) and row(k) dot Lz r
  are equal.

Every variance here is the finite second-moment-minus-squared-first-moment
formula above. Thus no fitted coefficient equality is assumed as a hypothesis.

### 2. Reduced-control identity (`Whole34Reduced`)

For every natural n,p,q, assignment D : Fin n -> Fin 4, full control matrix
C : Matrix (Fin n) (Fin p) R, reduced control matrix
Cc : Matrix (Fin n) (Fin q) R, and weight vector w, assume all w_i>0 and
injectivity of v -> H(D,Cc)v. For every tau : Fin 4 -> R,
gamma : Fin p -> R, and r : Fin n -> R, let

    Hc=H(D,Cc), Lc=L(w,Hc),
    theta=(tau_0,tau_1,tau_2,tau_3,0,...,0), u=C gamma.

Then

    Lc (r + (i -> tau_(D_i)) + u) = Lc r + theta + Lc u,
    Hc (Lc u)=u if and only if u belongs to Col(Hc).

There is no assumption that Cc is a subset or a collapse of C; the assertion is
valid for any such matrices. It neither asserts every omission changes a
variance nor assumes u lies outside the reduced space.

### 3. Concrete loss of control (`Whole34LostControl`)

Here all data are fixed definitions, not existentially quantified placeholders.
The units are I=Fin 4 x Fin 2. A state is z=(A,s), encoded as
Fin 6 x (Fin 4 -> Bool). `controlPair` lists the subsets
{0,1},{0,2},{0,3},{1,2},{1,3},{2,3} in that order; A is the selected subset.
Put alpha=(1/10,1/5,3/10,2/5). For i=(j,h), define match to mean
s(j) equals the Boolean truth value of h=0. The category D_z(i) is 3 on selected
j with match, 2 on selected j without match, 0 on unselected j with match,
and 1 on unselected j without match. These are `pairReferentRate` and
`controlExposure` unfolded.

The state mass and unit category probabilities used by the definitions are

    P(A,s) = (1/6) product_j [alpha_j if s(j)=true, else 1-alpha_j]
                            for j in A,
                       and [1/2] for j outside A;
    u_(j,0) = alpha_j/2, u_(j,1) = (1-alpha_j)/2;
    pi_i(0)=pi_i(1)=1/4, pi_i(2)=1/2-u_i, pi_i(3)=u_i.

These expand `controlMass`, `controlPiI`, and `controlPi`. In particular
pi_i(2)+pi_i(3)=1/2. For any assignment D use weights w_D(i)=1/pi_i(D_i).
The observed D0 assigns categories (3,2) to the two units of each j<2 and
(0,1) to those of each j>=2. Observed outcomes by j are
(0,2),(1,0),(3,1),(2,4). Define

    Hfull(D) = H(D, one control column u),
    b0 = L(w_D0,Hfull(D0)) y,
    m_k = b0_k + b0_4/4,
    r = y-Hfull(D0)b0,
    ystar(z)_i = y_i + m_(D_z(i)) - m_(D0_i).

These expand `controlFullRow`, `controlWeight`, `controlObserved`, `controlY`,
`controlPoint`, `controlPointMean`, `controlResidual`, and `whole33Imputed`.
The full contrast at z on an input vector f is b_3-b_2 with
b=L(w_Dz,Hfull(D_z))f. The collapsed contrast uses only the four indicator
columns in place of Hfull(D_z). This expands both branches of `controlContrast`.
`controlVariance` is V_P with the mass P above.

Let C2 have columns (u,pi(2)), C1 the single column u+pi(2), and J(D)
the four indicator columns. These are `whole34TwoControls`,
`whole34SumControl`, and `whole34Indicators`. The five asserted facts are:

1. Col(C1) is a strict submodule of Col(C2).
2. For every D : I -> Fin 4, Col(H(D,C1))=Col(J(D)).
3. For every such D, Col(H(D,C2))=Col(Hfull(D)).
4. The vector i -> u_i b0_4 does not belong to Col(J(D0)).
5. V_P(collapsed contrast of r) differs from
   V_P(full contrast of ystar(z)).

The column-space equalities are statements about possibly aliased matrices;
these matrices are not themselves passed to `regressionMap` in these equalities.

### 4. Bases and unique fits (`Whole34Basis`)

For every n,p, H : Matrix (Fin n) (Fin p) R, and w : Fin n -> R with
every w_i>0, both of the following hold:

- There exist q : N and B : Matrix (Fin n) (Fin q) R such that B's
  coefficient-to-fit map is injective and Col(B)=Col(H).
- For every q,B with those two properties, and then every y : Fin n -> R,
  Min(w,B,y,L(w,B)y), some coefficient a satisfies Min(w,H,y,a), and
  for every a,

      Min(w,H,y,a) iff H a = B L(w,B)y.

In particular the fitted vector is unique even if coefficients in H are not.

### 5. Aliased shifts and variance (`Whole34Aliased`)

The first clause quantifies n,p,H,w, assumes all weights positive, and then
quantifies y,theta,a,b : Fin p -> R, except y : Fin n -> R. If
Min(w,H,y,a) and Min(w,H,y+H theta,b), conclude

    H b = H a + H theta,
    for every real linear functional ell, Est(H,ell) implies
       ell(b)=ell(a)+ell(theta).

The second clause independently quantifies a finite type Omega, n,p,
H : Omega -> Matrix (Fin n) (Fin p) R,
w,r : Omega -> Fin n -> R, a fixed theta : Fin p -> R,
a,b : Omega -> Fin p -> R, a single fixed real linear functional ell, and
prob : Omega -> R. Assume all weights positive, Est(H(z),ell) for every z,
Min(w(z),H(z),r(z),a(z)) for every z,
Min(w(z),H(z),r(z)+H(z)theta,b(z)) for every z,
prob(z)>=0 and sum prob=1. Conclude ell(b(z))=ell(a(z))+ell(theta)
for every z and equality of the two V_prob variances. The functional must
be estimable at every state, not only the observed state.

### Junk-value and boundary audit

- `regressionMap` uses an inverse which is zero for a singular real square
  matrix. In the universal full-rank identities, positive weights and the explicit
  injectivity hypotheses ensure invertibility. In the basis clause the inverse
  is used on the injective basis B, rather than the potentially aliased H.
  The aliased clauses use the minimizing predicate, not a singular inverse.
  The concrete example uses the one-control full design and indicator-only
  design; whether these remain full rank at every state is a concrete check to
  make, rather than an assumption supplied by this theorem.
- The only population-mean division by n in the general identity is protected
  by n>0. The concrete mean uses 4, a nonzero real number. Category probabilities
  in the concrete example are strictly between 0 and 1/2, so inverse-probability
  weights do not divide by zero. All fixed rational denominators are nonzero.
- The column selector uses natural subtraction j-4 only in the branch j>=4;
  its generated proof establishes j-4<p. There is no truncation error.
- Fin index numerals, casts, `castAdd`, and `castSucc` address actual in-bounds
  indices. The finite tuple definitions have no out-of-range default branch.
- Omega may syntactically be empty, but then sum prob=1 is impossible. This
  only eliminates empty laws, not nonempty instances. The full-rank four-category
  map cannot be injective when n<4+p. Empty control sets p=0 are allowed. The
  basis and aliased claims allow zero rows or columns, whose zero-dimensional
  linear algebra and empty sums have their ordinary meanings.
- `wholeVariance` alone accepts signed or unnormalized weights, but its general
  uses in this theorem impose a probability law. The concrete state masses are
  products of positive rational factors, with the six-pair mixture form stated
  above. The definition has no infinite expectations.
- No `Real.log`, square root, real power, Bochner integral, extended-real
  `toReal`, infimum/supremum, limsup/liminf, partial-function default, or
  infinite sum occurs in this statement's closure.
- The line-0 declarations in this closure are nonzero-numeral certificates,
  the bound for the selector j-4, and the standard surjectivity instance for
  the identity ring homomorphism. Their printed bodies add no statistical
  assumptions or hidden choices.

## SAP.P037c.T43

The theorem at `SAP/P037c/Challenge/Part1.lean:71` has no outer hypotheses.
Its proposition conjoins two universally quantified regression assertions,
a universally quantified orthogonality assertion, and a fixed finite certificate.
The docstring describes the expected-normal-equation bias formula, its
common-intercept corollary, and this certificate.

### Expanded notation and objects

For a finite type Omega, a `FiniteDesign Omega` consists of a real function
d(w), proofs d(w)>=0 for every state, and sum_w d(w)=1. The constructor and
weight projection in the closure are exactly the constructor and field of this
structure. No uniformity or independence is built into it. Put

    E[f] = sum_w d(w) f(w),
    <x,y> = sum_i x_i y_i,
    Q(x,y) = sum_w d(w) sum_i x(w)_i y(w)_i.

These finite sums expand `designMean`, `inner`, and `cross`.
For B : N the observation set is I=Fin B x Fin 4. For x : I -> R put

    Mx_(h,j) = x_(h,j) - (1/4) sum_(k in Fin 4) x_(h,k).

This expands `blockDemean`: exactly four observations per block, each equally
weighted when demeaning. Given T,C : Omega -> I -> R and fixed covariates
X : K -> I -> R, let

    t(w)=M(T(w)), z(w)=M(i -> T(w)_i C(w)_i), V_k=M(X_k),
    alpha=Q(z,t)/Q(t,t),
    r(w)_i=z(w)_i-alpha t(w)_i-p sum_k lam_k V_ki.

This expands `treatmentProjection`, `residual`, and `blockResidual` completely.
Here alpha is a ratio of expected sums, not a state-by-state OLS coefficient.
For Ytilde : Omega -> I -> R and coefficients tau,b : R, g : K -> R,
`NormalEquations d t z V Ytilde tau g b` means that, with

    e(w)_i=Ytilde(w)_i-[tau t(w)_i+sum_k g_k V_ki+b z(w)_i],

Q(t,e)=0, Q(V_k,e)=0 for every k (V_k treated as constant over w), and
Q(z,e)=0. It is a condition on expected normal equations, not an assertion
that a random fitted coefficient is unbiased.

### 1. Bias assertion (`BlockModelBiasStatement`)

For every pair of finite types Omega,K (and their finite enumerations),
universally quantify in this order:

1. B : N;
2. normalized finite design d;
3. T,C,Y : Omega -> (Fin B x Fin 4) -> R;
4. X : K -> (Fin B x Fin 4) -> R;
5. a,eta,mu : (Fin B x Fin 4) -> R, all fixed over assignment;
6. lam : K -> R, then real p,tau0,beta,tau,b, then g : K -> R;
7. the following hypotheses.

The hypotheses are:

- For every unit i, E[T_i]=p.
- For every i, E[T_i C_i]=p mu_i.
- For every i, Mmu_i=sum_k lam_k M(X_k)_i.
- For every state w and unit i,
  Y(w)_i=a_i+T(w)_i[tau0+eta_i+beta C(w)_i].
- Q(t,t) != 0.
- Q(r,r)>0, with r expanded as above.
- The actual coefficients tau,g,b satisfy the expected normal equations
  for response M(Y(w)) and regressors t,z,V, as expanded above.

The conclusion is

    b-beta = [sum_w d(w) sum_i r(w)_i T(w)_i eta_i] / Q(r,r).

In particular, the type does not require binary T, positive p, any range bound
on C, a particular randomization mechanism, or independence. It uses raw first
moments rather than division by p or a conditional expectation.

### 2. Common-intercept assertion (`CommonInterceptStatement`)

Independently repeat the same quantification except that eta is absent and
the outcome hypothesis is

    Y(w)_i=a_i+T(w)_i[tau0+beta C(w)_i].

All other moment, span, nonzero-Q(t,t), positive-Q(r,r), and normal-equation
hypotheses are the same. The conclusion is b=beta. The untreated levels a_i
remain arbitrary fixed real numbers; equality or constancy of a_i is not assumed.

### 3. Orthogonality assertion (`Whole43Orthogonality`)

Independently, for every finite Omega,K, B : N, normalized finite design d,
T,C : Omega -> I -> R, X : K -> I -> R, mu : I -> R, lam : K -> R,
and p : R, assume, in order,

    E[T_i]=p for all i,
    E[T_i C_i]=p mu_i for all i,
    Mmu_i=sum_k lam_k M(X_k)_i for all i,
    Q(t,t) != 0.

For r as above, conclude all four assertions:

    E[r_i]=0 for every i,
    Q(r,t)=0,
    Q(r,V_k)=0 for every k,
    Q(r,z)=Q(r,r).

Positive Q(r,r), outcomes, and normal-equation solutions are not hypotheses
of this particular conjunct.

### 4. Explicit certificate (`Whole43Certificate`)

There is one block, four units i=(0,j) with j in Fin 4, four states w in Fin 4,
each of mass 1/4, and no covariate columns (K=Fin 0). Define

    T(w)=(1,1,0,0) when w=0 or 1, and (0,0,1,1) when w=2 or 3;
    C(w)_i=1/4 when w=0 or 2, and 3/4 when w=1 or 3;
    a_(0,j)=j/10;
    Y(w)_i=a_i+T(w)_i[3/10+(2/5)C(w)_i].

These expand `whole43Design`, `whole43Treatment`, `whole43Composition`, and
`whole43Outcome`. The certificate explicitly asserts:

1. E[T_i]=1/2 for every i.
2. E[T_i C_i]=(1/2)(1/2) for every i.
3. The demeaned constant mu_i=1/2 is the empty linear combination of
   demeaned covariates (lam and X are the unique functions from Fin 0).
4. Q(t,t)=1.
5. Q(r,r)=1/16 for p=1/2 and no covariates.
6. The expected normal equations for these demeaned outcomes hold with
   tau=3/10, g the empty vector, and b=2/5.
7. T(w)_i=0 or 1 for every state and unit.
8. sum_i T(w)_i=2 at every state.
9. For every unit i, T(0)_i+T(2)_i=1 and T(1)_i+T(3)_i=1.
10. C(w)_i=1/4 or 3/4 for every state and unit.
11. Some two units have different fixed levels j/10.

The certificate contains no asserted relation between C and an underlying
network, seed population, or within-school referent indicators. It certifies
the specified algebraic four-state design.

### Junk-value and boundary audit

- The denominator Q(t,t) in alpha is explicitly required nonzero in both
  regression assertions and the orthogonality assertion. The denominator
  Q(r,r) in the bias formula is explicitly positive. The certificate supplies
  the exact nonzero values 1 and 1/16. Thus real division's value at zero
  cannot make the claimed bias formula or orthogonality assertion trivial.
- The symbol p is never divided by. It is allowed to be zero or outside the
  probability range when T is real-valued. This is an algebraic extension,
  not a conditional-expectation definition making use of 0/0.
- All demeaning uses the nonzero real denominator 4. The fixed outcome levels
  use the nonzero denominator 10. All other rationals have nonzero denominators.
- Omega cannot be empty for an actual `FiniteDesign`: its total field would
  assert 0=1. B=0 is permitted syntactically, but Q(t,t)!=0 cannot then hold.
  K may be empty; this legitimately represents no covariates, as in the
  certificate, and its empty sums are zero.
- Finite sums of real functions are integrable on these finite probability
  spaces with their discrete sigma algebras. There is no undefined expectation,
  unbounded sum, or infinite probability converted to a real number.
- The casts of j to R in the certificate are ordinary nonnegative integer
  casts. Numeric Fin indices are in range. No natural subtraction occurs.
- No logarithm, square root, real power, infimum/supremum, limsup/liminf,
  partial-function default, or Bochner-integral default occurs in this closure.
- Generated line-0 proofs concern nonzero numeral denominators or prove
  the uniform design's nonnegativity and normalization. In particular the
  strangely named `T35WholeStatement._proof_1`, `whole27Mass._proof_1`, and
  `whole34TwoControls._proof_1` reused in this closure certify ordinary
  numeral facts; they do not import additional statistical assertions.
