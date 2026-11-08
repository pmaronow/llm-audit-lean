# Blind reading

This file was written after reading `closure.json`, the target statements and
docstrings, and all their unit-local dependencies, but before opening
`claims.json` or `record.json`. The auxiliary declarations without source lines
were inspected using `scratch/ClosureCheck.lean`, importing only the definitions.

## SAP.P016a.T8

Sources: `Challenge/Part1.lean:34-36`, `Defs/Part5.lean:68-83`, and the Part1
dependencies listed in the closure.

An outcome on n units is a function y : Fin n → ℝ; an assignment is a function
z : Fin n → Bool. Write b(true)=1, b(false)=0. For g ∈ {false,true}, let
N_g(z)=Σ_{i∈Fin n} 1_{z(i)=g}, A_g(y,z)=Σ_i 1_{z(i)=g} y(i), and
m_g(y,z)=A_g(y,z)/(N_g(z):ℝ). Write D(y,z)=m_true(y,z)-m_false(y,z).
Generation is the function i ↦ y(i)+b(z(i))t, and adjustment of Y is
i ↦ Y(i)-b(z(i))t. These are all ordinary finite sums and real arithmetic.

The statement is the conjunction of the following three separately quantified
assertions, in this order.

1. For every natural n, every y : Fin n → ℝ, every z : Fin n → Bool, and every
   pair t,t₀ : ℝ, the function i ↦ y(i)+b(z(i))t-b(z(i))t₀ equals
   i ↦ y(i)+b(z(i))(t-t₀), and i ↦ y(i)+b(z(i))t-b(z(i))t equals y.
   No positivity or nonempty-group hypothesis occurs here.
2. For every natural n, finite type Ω, real weights p : Ω → ℝ with
   p(ω)≥0 for every ω and Σ_ω p(ω)=1, assignment map a : Ω → (Fin n → Bool),
   baseline y₀ : Fin n → ℝ, t : ℝ, arbitrary statistic
   T : (Fin n → ℝ) → Ω → ℝ, and α : ℝ with 0≤α≤1, let
   v_ω(i)=y₀(i)+b(a(ω)(i))t-b(a(ω)(i))t. Then:
   - for every predicate E : ℝ → Prop,
     Σ_ω 1_{E(T(v_ω,ω))}p(ω) = Σ_ω 1_{E(T(y₀,ω))}p(ω);
   - Σ_ω 1_{Σ_w 1_{T(v_ω,ω)≤T(v_ω,w)}p(w) ≤ α}p(ω) ≤ α.
   The inner tail includes ties and uses the same law as the outer draw. T may
   depend on the entire design index ω, not just its assignment. There is no
   injectivity, uniformity, or full-support requirement on a or p. `FiniteLaw.mk`
   packages exactly the weights, nonnegativity and normalization; `.weight`
   projects the weights. `mass` and `upperP` are exactly the sums above.
3. For every natural n, Y : Fin n → ℝ, z : Fin n → Bool, proofs
   0<N_false(z) and 0<N_true(z), then every t : ℝ,
   D(Y,z)=D((i↦Y(i)-b(z(i))t),z)+t, and equality of those two unshifted mean
   differences is equivalent to t=0. Both positive-size hypotheses precede t.

The docstring describes recovery of the true baseline, equality of the adjusted
observed/reference law, calibration of inclusive upper tails, and exactly the
raw mean shift.

Junk values and edge cases: real division by zero is totalized to zero, so a
group mean would be zero for an empty group. Both groups are explicitly
nonempty wherever a mean occurs in this statement, so this convention is
irrelevant there. n=0 is permitted in the first two conjuncts, where the outcome
function is empty and the algebraic recovery remains meaningful. An empty Ω
cannot carry `FiniteLaw`, since its total mass would be 0=1. Zero individual
weights and repeated assignments are allowed and cause no undefined operation.
All sums are finite; no integrals, logarithms, square roots, powers with domain
extensions, infinities, extremal-set defaults, limits, partial functions or
truncated natural subtraction occur. Natural group sizes are cast exactly to ℝ.

## SAP.P016a.T9

Sources: `Challenge/Part1.lean:38-40`, `Defs/Part6.lean:11-34`, and all its
listed Part1 dependencies, including the generated proof declarations.

Outcomes and assignments are the same finite real vectors and Boolean functions
as above. For this section, explicitly define N_g(z)=Σ_i 1_{z(i)=g},
m_g(u,z)=(Σ_i 1_{z(i)=g}u(i))/(N_g(z):ℝ), and
F_g(u,z;t)=(Σ_i 1_{z(i)=g ∧ u(i)≤t})/(N_g(z):ℝ).
`rss` is R(u,z)=Σ_i (u(i)-m_{z(i)}(u,z))². The pooled mean is
ū=(Σ_i u(i))/(n:ℝ); `tss` is Q(u)=Σ_i(u(i)-ū)².
`ks` is max({0}∪{|F_true(u,z;u(i))-F_false(u,z;u(i))|:i∈Fin n});
`signedKS` takes that same maximum without the absolute values. These maxima
are implemented by a finite list, `List.ofFn`, folded with `max` and seed 0.

Let u=(0,1,2,3), and enumerate six assignments in exactly this order:
z₀=TTFF, z₁=TFTF, z₂=TFFT, z₃=FTTF, z₄=FTFT, z₅=FFTT.
The statement is the conjunction of:

1. For every i : Fin 4, F_true(u,z₅;u(i))-F_false(u,z₅;u(i)) is entry i of
   (-1/2,-1,-1/2,0). The signed maximum for z₅ is 0 and the absolute maximum
   is 1; both maxima for z₀ are 1.
2. Q(u)=5. Under the six equally weighted indices k∈Fin 6, the inclusive
   lower and upper tails of the constant statistic k↦Q(u), observed at k=0,
   are both 1. The inclusive lower tail of k↦R(u,z_k), observed at k=0, is
   1/3. An inclusive lower tail at z means Σ_w 1_{s(w)≤s(z)}p(w), and an
   inclusive upper tail means Σ_w 1_{s(z)≤s(w)}p(w). The uniform law here
   has p(k)=1/6, with its nonnegativity and normalization proved in the
   `uniformLaw` constructor.
3. Fix six units, S₀₁=S₁₀=1 and all other S_ij=0, assignment z=TFTFTF,
   and outcome u(i)=1. For each i put C_i=Σ_j b(z(j))S_ji and
   d_i=Σ_j S_ji; b maps true to 1 and false to 0. The four-column matrix
   X has rows (1,b(z(i)),C_i,d_i), explicitly
   (1,1,0,1), (1,0,1,1), (1,1,0,0), (1,0,0,0), (1,1,0,0), (1,0,0,0).
   W has rows (b(z(i)),C_i,d_i), with no intercept. For any finite real
   matrix M and coefficient vector β : Fin k → ℝ, define
   L(u,M,β)=Σ_i(u(i)-Σ_j M_ij β_j)² and
   I(u,M)=sInf{L(u,M,β):β∈(Fin k→ℝ)}. Then
   L(u,X,(1,0,0,0))=I(u,X)=0 and
   L(u,W,(1,1,0))=I(u,W)=2.
4. For every k : Fin 6, R((0,1,2,3),z_k) is entry k of (1,4,5,5,4,1).
5. For every natural n with 0<n, every finite type Ω, every nonnegative
   normalized real weight function p on Ω, every u : Fin n → ℝ, every
   a : Ω → (Fin n → Bool), and every observed index z : Ω, the function
   on assignments that ignores its argument and returns Q(u) has value Q(u)
   at every a(ω). The event of this equality has mass 1, and its constant
   statistic has inclusive lower and upper tails 1 at z. The order is
   n, positivity, Ω, its finite-type structure, its probability law, u, a, z.

The docstring identifies discrepancies from signed-KS, pooled-mean and
missing-intercept readings, and mentions the general constant-statistic law,
inclusive tails and complete SSR table.

Junk values and edge cases: all concrete group means and empirical CDFs use
group size 2. The general pooled mean has n>0, and contains no group mean or
CDF; assignments there may have an empty group without affecting Q(u).
`uniformLaw` requires a nonempty type, and Fin 6 has cardinality 6, so 1/card
never uses division by zero. More generally `FiniteLaw` rules out an empty Ω;
the explicit z : Ω also does so. The least-squares set is nonempty (zero
coefficients exist) and bounded below by zero (sum of real squares), so its
`sInf` is an ordinary infimum, with no empty/unbounded-set default. In the two
examples the displayed coefficients also attain it. Fin numerals used here
denote valid indices; the generated auxiliaries are `NeZero 6`,
`Nonempty (Fin 6)`, and numeral `AtLeastTwo` instances (2,3,4,5). The
`u4._proof_1` and `doubledP._proof_1` auxiliaries are only the corresponding
numeral instance for 3 and 2; the doubled-tail definition itself is not in the
statement closure. No additional mathematical assumption is hidden in these
proof constants. Empty-list max defaults in the general definitions do not
occur in these four- and six-unit statistics. Natural sizes/cardinalities are
cast into ℝ, with no truncation or overflow. No log, square root, noninteger
power, infinity conversion, integration, limit or partial-function default
occurs.

## SAP.P016a.T10

Sources: `Challenge/Part1.lean:42-44`, `Defs/Part6.lean:36-62`, and every
listed Part1 dependency.

Here outcomes u are functions Fin n→ℝ, assignments z are functions Fin n→Bool,
b(true)=1, b(false)=0, N_g=Σ_i1_{z(i)=g}, and
m_g=(Σ_i1_{z(i)=g}u(i))/(N_g:ℝ). Put
D=m_true-m_false and R=Σ_i(u(i)-m_{z(i)})². The basic design matrix B has
row i equal to (1,b(z(i))). For any X : Fin n → Fin k → ℝ and coefficient
vector β : Fin k → ℝ, let f_X(β)(i)=Σ_j X_ijβ_j,
L(u,X,β)=Σ_i(u(i)-f_X(β)(i))², and I(u,X)=sInf(range(L(u,X,·))).

The statement is the conjunction of these four assertions, with independent
quantification in each:

1. For every natural n, proof 2≤n, outcome u, assignment z, and proofs
   N_false>0 and N_true>0, I(u,B)=R. For every a,b : ℝ,
   L(u,B,(a,b))=R iff a=m_false and b=D. Also
   R=Σ_i u(i)²-(N_false:ℝ)m_false²-(N_true:ℝ)m_true².
   Thus the coefficient minimizer for this particular two-column design is
   unique as well as attaining the residual sum of squares.
2. For every n,k : ℕ, u, z, proofs N_false>0 and N_true>0, then every
   X : Fin n → Fin k → ℝ, there exists β with L(u,X,β)=I(u,X). For every
   β,γ, if both attain I(u,X), f_X(β)=f_X(γ) as functions on Fin n.
   It asserts uniqueness of fitted values, without requiring X to have
   independent columns or asserting uniqueness of β. The z and group-size
   hypotheses restrict this general regression assertion even though X need
   not contain z and they are not needed for finite least squares.
3. For every n,u,z with both group sizes positive, define
   F_g(t)=(Σ_i1_{z(i)=g ∧ u(i)≤t})/(N_g:ℝ), and
   K=max({0}∪{|F_true(u(i))-F_false(u(i))|:i∈Fin n}). Then
   K=sSup{ |F_true(t)-F_false(t)| : t∈ℝ },
   K(u,z)=K(u,(i↦¬z(i))), and 0≤K≤1. K is the list fold of the displayed
   finite maximum, not an assumed continuous supremum.
4. For every n, S : Fin n → Fin n → ℝ, symmetry proof
   ∀i,j,S_ij=S_ji, binary-entry proof ∀i,j,S_ij=0 or S_ij=1,
   assignment z, positive sizes of both groups, and i : Fin n,
   Σ_j b(z(j))S_ji=Σ_j S_ij b(z(j)), and Σ_j S_ji=Σ_j S_ij.
   The left sides are exactly `treatedNeighbors` and `degree`, respectively.
   There is no zero-diagonal hypothesis, and no nonnegativity condition beyond
   that implied by the binary entries. Group-size and binary hypotheses are
   stronger than needed for these identities, but are explicit.

The docstring describes corrected SSR minima, unique fitted values, the KS
threshold supremum, label invariance and range, and the symmetric-network
columns.

Junk values and edge cases: the positive group sizes rule out n=0 and division
by zero in every m_g and F_g used in this theorem. The n≥2 hypothesis in the
first clause is also implied by those sizes. Each least-squares range is
nonempty (zero coefficient vector) and bounded below by zero, so `sInf` never
uses a default. k=0 is allowed in the second clause: the unique empty
coefficient vector gives the zero fitted vector, a genuine finite regression
case. The CDF-difference range is nonempty (all real thresholds are allowed)
and lies in [0,1], so `sSup` also has its ordinary bounded meaning. The finite
KS list is nonempty under the group hypotheses; even its seed 0 is an actual
attainable tail difference at thresholds below all outcomes. Casting natural
group sizes into ℝ does not change their positivity. Subtraction is real
subtraction, with no truncation. No logs, roots, fractional powers, infinities,
integrals, limits, partial-function defaults or empty assignment types enter.

## SAP.P016a.T11

Sources: `Challenge/Part1.lean:46-48`, `Defs/Part6.lean:64-80`,
`Defs/Part2.lean:83-84`, and all listed Part1 and generated dependencies.

Every concrete vector is indexed by Fin 4. Let z=TTFF and u=(0,1,2,3).
For any y : Fin 4→ℝ and assignment w : Fin 4→Bool, define
N_g=Σ_i1_{w(i)=g}, m_g=(Σ_i1_{w(i)=g}y(i))/(N_g:ℝ),
F_g(t)=(Σ_i1_{w(i)=g ∧ y(i)≤t})/(N_g:ℝ),
R(y,w)=Σ_i(y(i)-m_{w(i)})²,
K(y,w)=max({0}∪{|F_true(y(i))-F_false(y(i))|:i∈Fin 4}), and
K⁺(y,w)=max({0}∪{F_true(y(i))-F_false(y(i)):i∈Fin 4}).
These are precisely `rss`, `ks`, and `signedKS`.

For a statistic H : (Fin 4→ℝ) → (Fin 4→Bool) → ℝ,
`EffectIncreasing H` means: for every assignment w, then every pair y,y' of
outcome vectors, if for every i one has y(i)≤y'(i) when w(i)=true and
y'(i)≤y(i) when w(i)=false, then H(y,w)≤H(y',w). There is no nonempty-group
hypothesis in this definition; the condition is weak coordinate monotonicity.

The theorem asserts the conjunction of:

1. For every i, u(i)≤v(i) on treated units and v(i)≤u(i) on controls, where
   v=(2,3,2,3). K(u,z)=1, K(v,z)=0, K⁺(u,z)=1, K⁺(v,z)=0.
   Furthermore, putting w=(0,1,4,5), for every i one has w(i)<v(i) on
   treated units and v(i)<w(i) on controls, and K(w,z)=1. Together with the
   already asserted K(v,z)=0 this is a strict coordinate-change witness.
2. R((0,2,0,2),z)=4, R((1,2,0,2),z)=5/2, and
   R((0,3,0,2),z)=13/2. For every i, (0,2,0,2)(i) is at most each of the
   corresponding coordinates of (1,2,0,2) and (0,3,0,2). The fixed controls
   are in fact unchanged in both changes, so both qualify for the preceding
   treated-up/control-down weak condition.
3. For every i, F_true(u,z;u(i))-F_false(u,z;u(i)) is entry i of
   (1/2,1,1/2,0).
4. ¬EffectIncreasing K, ¬EffectIncreasing K⁺, ¬EffectIncreasing R, and
   ¬EffectIncreasing ((y,w)↦-R(y,w)), each at n=4. Unfolding any negation
   says that some assignment and pair of outcome vectors satisfying the
   weak coordinate condition violate the asserted nondecrease. All four
   negations are explicit, not merely left as inferences from the tables.

The docstring says the weak/strict KS witnesses and opposite SSR changes
refute effect-increasing monotonicity of both KS versions and both SSR
orientations.

Junk values and edge cases: the fixed witnesses always have two treated and
two control units, so their means and CDFs have denominator 2. The universal
definition `EffectIncreasing` also covers assignments with empty groups;
those would use the Lean convention division by zero = 0 in m_g and F_g.
However, the explicit failures already occur with both groups nonempty, so
the negations do not depend on that convention. The fixed length-four KS
list is nonempty; its max seed 0 is the proper nonnegative reference level.
There are no infima, suprema, integrals, infinite values, logarithms, roots,
domain-extended powers, limits, natural truncated subtraction or partial
functions in this closure. Natural counts are exactly cast into ℝ, and Fin
literals and vector indices used here are valid. The generated proof
declarations imported from T9, u4 and doubledP concern only positive numerals
and finite indices; T11's own auxiliary is the numeral `AtLeastTwo` instance
for 13. They add no statistical hypothesis.
