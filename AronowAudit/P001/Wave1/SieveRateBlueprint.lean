import AronowAudit.P001.Wave1.PolynomialBlpBlueprint
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Blueprint: refutation of `AronowAudit.P001.printed_sieve_insufficient_degree_rate` (P001-T119)

Record 18 of group P001a: P001-T119 / `AronowAudit.P001.printed_sieve_insufficient_degree_rate`;
resolution `refute`. Frozen contract (P001_Foundations.lean:5109): for every IID stream of
pairs with integrable `Y`, a covariate PDF positive exactly on `[a,b]` (`a < b`), a globally
smooth CEF `m`, degrees with `J_n → ∞`, `J_n/n → 0`, and every pointwise least-squares
polynomial fit (`IsSieveLS`, squared residuals), the population L² error
`∫ (fit_n - m)² d(law of X)` tends to `0` in probability (`CP`).

`Target` is the negation of exactly that contract with `Ω : Type`; the `example` checks by
`Iff.rfl` that it is the negation of the frozen type at universe 0.

Witness (paper proof, record 18; validated derivation
`runs/P001/validate/P001-C04-E001/v2/artifact/derivation.md`): `Ω = ℕ → ℝ × ℝ` with the
infinite product of `Uniform[0,1] ⊗ N(0,1)`, `X_i, Y_i` the coordinates, `a = 0`, `b = 1`,
`f = 1_{[0,1]}`, `m = 0`, `J_n = ⌊n^{3/4}⌋`, and *any* least-squares fit (one exists for every
sample by projection, `N4`). Along `n = t⁴` (`J_n = t³`), for `t ≥ 25`, the bad event
`{risk ≥ 1}` has probability at least `1/72`, so `CP` fails at `ε = 1`.

Proof skeleton (all constants explicit, no asymptotic theorem):
* on the design event `D_n = {all X_i ∈ [1/n, 1], X injective}` (probability `≥ 1/6`, `N16`),
  the design has full column rank (`N5`) and *every* minimizer equals the OLS polynomial
  (`N6`), so no measurable selection of `fit` is needed (outer-measure monotonicity);
* `r_t = T_{t³}((2x-1-a)/(1-a))`, `a = t⁻⁴`, satisfies `|r_t| ≤ 1` on `[a,1]` and
  `∫_0^{1/2} r_t² ≥ 9t⁸/1638400` (`N10`, `N11`, `N12`);
* for each fixed design in `D_n`, `L(y) = ⟨b̂(y), w⟩` with `w_k = ∫_0^{1/2} x^k r_t` is exactly
  `N(0, σ²)`, `σ² = wᵀ(PᵀP)⁻¹w` (`N13`); with prob. `≥ 1/12`, `L² > σ²/2` (`N14`); on that
  event `∫_0^{1/2} p̂² ≥ L²/N > σ²/(2N) ≥ N/(2 Σ r_t(x_i)²) ≥ N/(2t⁴) ≥ 9t⁴/3276800 > 1`
  (`N7`, `N8`, `N9`), giving `N15` (fixed-design statement, as referee 1 required);
* the first `n` pairs have law `Uniform^n ⊗ N(0,1)^n` (`N18`), the bad set is measurable
  (`N17`), and nonnegative Fubini gives probability `≥ (1/6)(1/12)` (`N19`);
* the full risk under `Uniform[0,1]` dominates the `[0,1/2]` risk (`N20`).

Referee-1 fixes applied: the design event carries `X_i ≤ 1` and injectivity (fix 1); the
Gaussian step is a deterministic-design statement about the finite Gaussian product, with no
global conditional expectation of inverse-Gram quantities (fix 2); the finite-sample law,
measurability of the bad set and the Fubini step are separate nodes (fix 3). Constants
differ from the mapper's (`/720` Chebyshev bound, `1/6` design probability, threshold
`t ≥ 25`, final `1/72`); any positive constant suffices.

The sorry-bearing `sieve_degree_counterexample` (:1096) and the unproved sieve asymptotics
must not be used. Usable proved inputs: `gram_quadratic_form` (:7610),
`gram_unit_of_lower_bound` (:7616), `olsCoef` (:450), `PolynomialBlp.N3` (blueprint node).
Writers prove `theorem nk_proof : Nk` in `AronowAudit/P001/Wave1/SieveRate/Nk.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_sieve_insufficient_degree_rate` (universe 0). -/
def Target : Prop :=
  ¬ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ), IID μ (fun i ω => (X i ω, Y i ω)) → Integrable (Y 0) μ →
    ∀ (a b : ℝ), a < b → ∀ (f : ℝ → ℝ), HasPDF (μ.map (X 0)) f →
    (∀ x, 0 < f x ↔ x ∈ Set.Icc a b) → ∀ (m : ℝ → ℝ), ContDiff ℝ ⊤ m →
    IsCEF μ (X 0) (Y 0) m → ∀ (J : ℕ → ℕ), Tendsto J atTop atTop →
    Tendsto (fun (n : ℕ) => (J n : ℝ) / (n : ℝ)) atTop (nhds 0) →
    ∀ (fit : ℕ → Ω → Polynomial ℝ), IsSieveLS X Y J fit →
    CP μ (fun n ω => ∫ x, ((fit n ω).eval x - m x) ^ 2 ∂(μ.map (X 0))) 0

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration, universe 0).
Only the frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔
    ¬ (type_of% @AronowAudit.P001.printed_sieve_insufficient_degree_rate.{0}) := Iff.rfl

/-! ## Witness data -/

/-- `Uniform[0,1]` (the project's `uniformLaw 0 1`) is a probability measure. Needed to form
the infinite product; proved here because the witness cannot be stated without it. -/
instance uniformLaw01_isProbabilityMeasure : IsProbabilityMeasure (uniformLaw 0 1) := by
  constructor
  rw [uniformLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h : (fun x : ℝ => ENNReal.ofReal (if x ∈ Set.Icc (0 : ℝ) 1 then (1 - 0)⁻¹ else 0)) =
      (Set.Icc (0 : ℝ) 1).indicator 1 := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
  rw [h, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
  simp

/-- One observation: `X ~ Uniform[0,1]` independent of `Y ~ N(0,1)`. -/
def sieveNu : Measure (ℝ × ℝ) := (uniformLaw 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure sieveNu := by unfold sieveNu; infer_instance

/-- The IID stream law on `ℕ → ℝ × ℝ`. -/
def sieveMu : Measure (ℕ → ℝ × ℝ) := Measure.infinitePi (fun _ : ℕ => sieveNu)

/-- Covariates `X_i(ω) = (ω i).1`. -/
def sieveX : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i ω => (ω i).1

/-- Outcomes `Y_i(ω) = (ω i).2`. -/
def sieveY : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i ω => (ω i).2

open Classical in
/-- The covariate PDF `f = 1_{[0,1]}` (positive exactly on the closed interval). -/
def sieveF : ℝ → ℝ := fun x => if x ∈ Set.Icc (0 : ℝ) 1 then 1 else 0

/-- The (globally smooth) CEF `m = 0`. -/
def sieveM : ℝ → ℝ := fun _ => 0

/-- The printed-rate degrees `J_n = ⌊n^{3/4}⌋`. -/
def sieveJ : ℕ → ℕ := fun n => Nat.floor ((n : ℝ) ^ (3/4 : ℝ))

theorem sieveF_pos (x : ℝ) : 0 < sieveF x ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold sieveF
  split_ifs with h <;> simp [h]

/-! ## Deterministic design objects -/

/-- Vandermonde matrix of a design `x` at degree `d`: `P i k = x_i ^ k`. -/
def vand (d : ℕ) {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin (d + 1)) ℝ :=
  fun i k => x i ^ (k : ℕ)

/-- The polynomial with coefficient vector `b`: `∑_k b_k X^k`. -/
def coeffPoly {d : ℕ} (b : Fin (d + 1) → ℝ) : Polynomial ℝ :=
  ∑ k : Fin (d + 1), C (b k) * X ^ (k : ℕ)

/-- The OLS polynomial `∑_k ((PᵀP)⁻¹Pᵀy)_k X^k` (the project's `olsCoef`, :450). -/
def olsPoly (d : ℕ) {n : ℕ} (x y : Fin n → ℝ) : Polynomial ℝ :=
  coeffPoly (olsCoef (vand d x) y)

/-- `∫_{[0,1/2]} p q` (Lebesgue). -/
def regionInt (p q : Polynomial ℝ) : ℝ := ∫ z in Set.Icc (0 : ℝ) (1/2), p.eval z * q.eval z

/-- `w_k = ∫_{[0,1/2]} x^k r(x) dx`, `k ≤ d`. -/
def regionMoments (d : ℕ) (r : Polynomial ℝ) : Fin (d + 1) → ℝ :=
  fun k => regionInt (X ^ (k : ℕ)) r

/-- The design event: all points in `[1/n, 1]` and pairwise distinct (referee-1 fix 1). -/
def designSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 1 / (n : ℝ) ≤ x i ∧ x i ≤ 1) ∧ Function.Injective x}

/-- The boundary Chebyshev polynomial `r_t(x) = T_{t³}((2x - 1 - a)/(1 - a))`, `a = t⁻⁴`. -/
def chebR (t : ℕ) : Polynomial ℝ :=
  (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).comp
    (C (2 / (1 - 1 / ((t : ℝ) ^ 4))) * X - C ((1 + 1 / ((t : ℝ) ^ 4)) / (1 - 1 / ((t : ℝ) ^ 4))))

/-- The `n`-fold standard Gaussian product (fixed-design response law). -/
def gaussVec (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- The `n`-fold uniform product (design law). -/
def unifVec (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => uniformLaw 0 1)

/-- The first `n` covariates and outcomes of a stream. -/
def firstN (n : ℕ) (ω : ℕ → ℝ × ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => sieveX i ω, fun i => sieveY i ω)

/-- The bad set at `n = t⁴`: design event and OLS `[0,1/2]`-risk above `1`. -/
def badSet (t : ℕ) : Set ((Fin (t ^ 4) → ℝ) × (Fin (t ^ 4) → ℝ)) :=
  {z | z.1 ∈ designSet (t ^ 4) ∧
    1 < regionInt (olsPoly (t ^ 3) z.1 z.2) (olsPoly (t ^ 3) z.1 z.2)}

/-! ## Nodes: model and rates -/

/-- **Node N1** (paper proof, record 18, step 1: "Let ν=Uniform[0,1]⊗N(0,1), let μ be its
infinite IID product ... Product construction gives measurable IID pairs and the indicated
one-observation law"). The stream is a probability measure, the coordinate pairs are IID,
and the one-observation law and covariate marginal are as stated.
Suggested route: the pattern of `lift_stream_iid` (P001_PrintedRefutations.lean:27):
`iIndepFun_infinitePi`, `Measure.infinitePi_map_eval`, `measurable_pi_apply`; the pair
`(sieveX i ω, sieveY i ω)` is `ω i` (`Prod.mk.eta`); `Measure.map_fst_prod` for the
marginal. -/
def N1 : Prop :=
  IsProbabilityMeasure sieveMu ∧ IID sieveMu (fun i ω => (sieveX i ω, sieveY i ω)) ∧
    sieveMu.map (fun ω => (sieveX 0 ω, sieveY 0 ω)) = sieveNu ∧
    sieveMu.map (sieveX 0) = uniformLaw 0 1

/-- **Node N2** (paper proof, record 18, step 1: "The first marginal has density f=1_{[0,1]}
... The second marginal is an independent standard Gaussian, hence E|Y_i|<∞, E[Y_i]=0 ...
Independence verifies IsCEF μ X_0 Y_0 0 by integrating over every X_0-event"). Under `N1`:
the covariate PDF, integrability of `Y_0`, and the zero CEF.
Suggested route: `HasPDF`: `uniformLaw` unfolds to `withDensity` of
`ofReal (if x ∈ Icc 0 1 then (1-0)⁻¹ else 0)`, equal to `ofReal (sieveF x)`; integrable
`sieveF` (`integrable_indicator_iff`, finite volume of `Icc`); `Y_0`: `integrable_map_measure`
with `memLp_id_gaussianReal`/`integrable_id_gaussianReal`-type lemmas; CEF: transport the
set integral to `sieveNu` (`setIntegral_map`), then `setIntegral_prod`/`integral_prod` on
`A ×ˢ univ` and `integral_id_gaussianReal` (mean `0`). -/
def N2 : Prop :=
  N1 → HasPDF (sieveMu.map (sieveX 0)) sieveF ∧ Integrable (sieveY 0) sieveMu ∧
    IsCEF sieveMu (sieveX 0) (sieveY 0) sieveM

/-- **Node N3** (paper proof, record 18, steps 1 and 3: "For J_n=⌊n^{3/4}⌋, n^{3/4}-1<J_n≤n^{3/4};
hence J_n→∞ and 0≤J_n/n≤n^{-1/4}→0 ... Then d=J_n=t³, since (t⁴)^{3/4}=t³").
Suggested route: `Nat.floor_le`, `Nat.lt_floor_add_one`, `Real.rpow_natCast`,
`Real.rpow_mul` (`((t:ℝ)^4)^(3/4) = t^3`), `Nat.floor_natCast`;
`tendsto_rpow_atTop`, `tendsto_natCast_atTop_atTop`, `Nat.tendsto_floor_atTop`-type facts;
squeeze with `n^{-1/4}` (`tendsto_rpow_neg_atTop`). -/
def N3 : Prop :=
  Tendsto sieveJ atTop atTop ∧
    Tendsto (fun n : ℕ => (sieveJ n : ℝ) / (n : ℝ)) atTop (nhds 0) ∧
    ∀ t : ℕ, sieveJ (t ^ 4) = t ^ 3

/-- **Node N4** (paper proof, record 18, step 1: "For every n and every ω, send the J_n+1
polynomial coefficients linearly into ℝ^n by evaluation at the n design points. Its image
is finite dimensional and closed. Project ... The resulting polynomial has natDegree≤J_n and
minimizes the exact squared residual sum ... At n=0 choose the zero polynomial. Choice over
(n,ω)"). A least-squares fit exists for every stream and every degree sequence, given the
abstract finite-dimensional least-squares node `PolynomialBlp.N3`.
Suggested route: apply `PolynomialBlp.N3` in `EuclideanSpace ℝ (Fin n)` with
`v k = (fun i => X i ω ^ k)`, `y = (fun i => Y i ω)` (`EuclideanSpace.norm_eq`,
`Real.sqrt_le_sqrt`/`sq_le_sq'`), polynomial `∑ C (b k) X^k`; coefficients of any `q` with
`natDegree ≤ J n` (`Polynomial.as_sum_range'`); `Classical.choose` over `(n, ω)`. -/
def N4 : Prop :=
  PolynomialBlp.N3.{0} →
  ∀ {Ω : Type} (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ), ∃ fit : ℕ → Ω → Polynomial ℝ,
    IsSieveLS X Y J fit

/-! ## Nodes: least squares on full-rank designs -/

/-- **Node N5** (paper proof, record 18, step 4: "A polynomial of degree≤d with n≥d+1
distinct zeroes is the zero polynomial, so P has full column rank and A is positive
definite"). An injective design with at least `d+1` points gives an invertible Gram matrix.
Suggested route: `P.mulVec c i = (coeffPoly c).eval (x i)`; if `P c = 0` then `coeffPoly c`
has `n > d` roots, so it is `0` (`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`),
hence `c = 0` (coefficients of `coeffPoly`); then the proved `gram_unit_of_lower_bound`
(:7616) or `Matrix.PosDef.det_pos` with `Matrix.posDef_conjTranspose_mul_self`-type facts. -/
def N5 : Prop :=
  ∀ (n d : ℕ) (x : Fin n → ℝ), d + 1 ≤ n → Function.Injective x →
    IsUnit ((vand d x).transpose * vand d x).det

/-- **Node N6** (paper proof, record 18, step 4: "On this full-rank set the pointwise
least-squares minimizer is unique and its coefficient vector is b̂=A^{-1}P^TY"; mapper step 1:
"The rest of the argument applies to every pointwise minimizing fit"). Every degree-`≤ d`
minimizer of the residual sum (in the `IsSieveLS` form) on an injective design with
`d + 1 ≤ n` is the OLS polynomial. Stated under `N5`.
Suggested route: write `p = coeffPoly b` (`natDegree ≤ d`); residual sum `= ‖y - P b‖²`
(`Finset.sum_range` vs `Fin` sums: `Fin.sum_univ_eq_sum_range`); Pythagoras
`‖y - Pb‖² = ‖y - Pb̂‖² + ‖P(b - b̂)‖²` from the normal equations `Pᵀ(y - Pb̂) = 0`
(`Matrix.mul_nonsing_inv`, `gram_quadratic_form` :7610); minimality against `olsPoly` forces
`P(b - b̂) = 0`, so `b = b̂` by `N5`'s injectivity. -/
def N6 : Prop :=
  N5 →
  ∀ (n d : ℕ) (x y : ℕ → ℝ) (p : Polynomial ℝ), d + 1 ≤ n →
    Function.Injective (fun i : Fin n => x i) → p.natDegree ≤ d →
    (∀ q : Polynomial ℝ, q.natDegree ≤ d →
      ∑ i ∈ Finset.range n, (y i - p.eval (x i)) ^ 2 ≤
        ∑ i ∈ Finset.range n, (y i - q.eval (x i)) ^ 2) →
    p = olsPoly d (fun i : Fin n => x i) (fun i : Fin n => y i)

/-! ## Nodes: deterministic inequalities -/

/-- **Node N7** (paper proof, record 18, step 4: "Integral Cauchy–Schwarz gives
Z²≤R_{n,1/2}"). Cauchy–Schwarz on `[0,1/2]` for polynomials.
Suggested route: polynomials are integrable on the bounded interval
(`Continuous.integrableOn_Icc`); `0 ≤ regionInt (p - λ r) (p - λ r)` with
`λ = regionInt p r / regionInt r r` (`setIntegral_nonneg`, `integral_sub`,
`integral_mul_left`), or `integral_mul_le_Lp_mul_Lq_of_nonneg`. -/
def N7 : Prop :=
  ∀ p r : Polynomial ℝ, 0 < regionInt r r → regionInt p r ^ 2 / regionInt r r ≤ regionInt p p

/-- **Node N8** (paper proof, record 18, step 4: "Write r_n(x)=c^Tp(x) ... The scalar
Z=(∫_0^{1/2}m̂_n(x)r_n(x)dx)/√N equals w^Tb̂/√N ... c^TAc ... =∑_i r_n(X_i)²"). Linearity of
`regionInt` in coefficient vectors, and the Vandermonde evaluation identity.
Suggested route: `coeffPoly`, `Polynomial.eval_finset_sum`, `integral_finset_sum`,
`integral_mul_left`; `Matrix.mulVec`, `dotProduct`, `Polynomial.eval_C`, `eval_X`,
`eval_pow`. -/
def N8 : Prop :=
  (∀ (d : ℕ) (b : Fin (d + 1) → ℝ) (r : Polynomial ℝ),
      regionInt (coeffPoly b) r = b ⬝ᵥ regionMoments d r) ∧
    ∀ (d n : ℕ) (x : Fin n → ℝ) (c : Fin (d + 1) → ℝ) (i : Fin n),
      (vand d x).mulVec c i = (coeffPoly c).eval (x i)

/-- **Node N9** (paper proof, record 18, step 4: "Cauchy–Schwarz in the positive-definite
inner product ⟨v,z⟩_A=v^TAz, applied to c and A^{-1}w, gives N²=(c^Tw)²≤(c^TAc)(w^TA^{-1}w)").
Suggested route: `A = PᵀP` is symmetric and invertible; set `u = A⁻¹ w`, then
`c ⬝ w = (P c) ⬝ (P u)` and `w ⬝ A⁻¹ w = ‖P u‖²` (`Matrix.mulVec_mulVec`,
`Matrix.mul_nonsing_inv`, `Matrix.dotProduct_mulVec`, `gram_quadratic_form` :7610); then the
Euclidean Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` (or `abs_real_inner_le_norm`
in `EuclideanSpace`). -/
def N9 : Prop :=
  ∀ (n K : ℕ) (P : Matrix (Fin n) (Fin K) ℝ), IsUnit (P.transpose * P).det →
    ∀ c w : Fin K → ℝ,
      (c ⬝ᵥ w) ^ 2 ≤ (∑ i, (P.mulVec c i) ^ 2) * (w ⬝ᵥ ((P.transpose * P)⁻¹).mulVec w)

/-- **Node N10** (paper proof, record 18, step 2: "The cosine addition identity proves
T_d(cos θ)=cos(dθ) by induction. Therefore |T_d(z)|≤1 on [-1,1]").
Suggested route: `Polynomial.Chebyshev.T_real_cos` with `z = cos (arccos z)`
(`Real.cos_arccos`), `Real.abs_cos_le_one`. -/
def N10 : Prop :=
  ∀ (d : ℕ) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → |(Chebyshev.T ℝ (d : ℤ)).eval z| ≤ 1

/-- **Node N11** (paper proof, record 18, step 2: "Write T_d(1+s)=∑_{j=0}^d a_j s^j ...
(j+1)(2j+1)a_{j+1}=(d²-j²)a_j ... All a_j are nonnegative ... T_d(1+s)≥a_3s³,
a_3=d²(d²-1)(d²-4)/90≥d⁶/360"). Cubic growth of `T_d` just above `1`; the stated constant
`1/720` is weaker than the paper's `1/360`, and only `0 ≤ s ≤ 1` is needed.
Suggested routes: (i) the paper's coefficient recurrence (expand `T_d (1 + s)` via the
Chebyshev ODE as a polynomial identity); or (ii) `Polynomial.Chebyshev.T_real_cosh`:
`1 + s = cosh θ` with `θ ≥ 0` (`Real.cosh` continuous and surjective onto `[1,∞)` on
`[0,∞)`), `cosh θ - 1 ≤ (θ²/2) cosh θ` gives `θ² ≥ 2s/(1+s) ≥ s`, and
`cosh y ≥ y⁶/720` for `y ≥ 0` (`Real.cosh_eq`, power series or repeated
`Real.add_one_le_exp`-type bounds); then `T_d(1+s) = cosh(dθ) ≥ d⁶θ⁶/720 ≥ d⁶ s³/720`. -/
def N11 : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    (d : ℝ) ^ 6 * s ^ 3 / 720 ≤ (Chebyshev.T ℝ (d : ℤ)).eval (1 + s)

/-- **Node N12** (paper proof, record 18, step 3: "Define r_n(x)=T_d((2x-1-a)/(1-a)), a
degree-d polynomial. On B_n each sample point lies in [a,1], so |r_n(X_i)|≤1 ... For
0≤x≤a/4 the affine argument is at most -(1+3/(2(n-1))) ... |r_n(x)|≥T_d(u_n) ... N_n ≥
T_d(u_n)²/(4n)"; step 5: "T_d(u_n)≥(d⁶/360)(3/(2n))³"). The boundary polynomial at
`n = t⁴`, `d = t³`, under `N10`, `N11`: degree, sup bound on `[1/n, 1]`, and the explicit
lower bound `∫_0^{1/2} r_t² ≥ 9t⁸/1638400` (from `T ≥ 3t⁶/640` with the `/720` constant).
Suggested route: `Polynomial.natDegree_comp_le`, `Polynomial.Chebyshev.natDegree_T`,
`natDegree_sub_le`/`natDegree_C_mul_X_le`; `eval_comp`; for `x ∈ [0, a/4]` the argument `w`
satisfies `-(1+a)/(1-a) ≤ w ≤ -(1+a/2)/(1-a)`, use `Polynomial.Chebyshev.T_eval_neg`
(`Int.negOnePow`, `|·| = 1`) and `N11` at `s = |w| - 1 ∈ [3/(2(n-1)), 2/(n-1)] ⊆ [0,1]`;
`setIntegral_mono_set` to `Icc 0 (a/4)`, `setIntegral_ge_of_const_le`-type bound. -/
def N12 : Prop :=
  N10 → N11 → ∀ t : ℕ, 2 ≤ t →
    (chebR t).natDegree ≤ t ^ 3 ∧
    (∀ z ∈ Set.Icc (1 / ((t : ℝ) ^ 4)) 1, |(chebR t).eval z| ≤ 1) ∧
    9 * (t : ℝ) ^ 8 / 1638400 ≤ regionInt (chebR t) (chebR t)

/-! ## Nodes: fixed-design Gaussian computations (referee-1 fix 2) -/

/-- **Node N13** (paper proof, record 18, step 4: "For each fixed such design, the
independent Gaussian response law gives E[b̂|X]=0 and Cov(b̂|X)=A^{-1} ... For each fixed
full-rank design, Z is centered Gaussian and its variance is v(X)=w^TA^{-1}w/N"). For a
deterministic full-rank design matrix, every linear functional of the OLS coefficients
under the standard Gaussian response product is exactly `N(0, wᵀ(PᵀP)⁻¹w)`.
Suggested route: `olsCoef P y ⬝ w = y ⬝ α` with `α = P (PᵀP)⁻¹ w` (symmetry of the inverse:
`Matrix.transpose_nonsing_inv`, `Matrix.dotProduct_mulVec`); `‖α‖² = wᵀ(PᵀP)⁻¹w`
(`Matrix.nonsing_inv_mul`); the coordinates are independent standard Gaussians
(`iIndepFun_pi`, `Measure.pi_map_eval`/`measurePreserving_eval`), hence jointly Gaussian
(`ProbabilityTheory.iIndepFun.hasGaussianLaw`), a continuous linear image is Gaussian
(`HasGaussianLaw.map_fun`, `HasGaussianLaw.map_eq_gaussianReal`) with mean `0` and variance
`∑ α_i²` (`IndepFun.variance_sum`/`variance_smul`, `variance_id_gaussianReal`). -/
def N13 : Prop :=
  ∀ (n K : ℕ) (P : Matrix (Fin n) (Fin K) ℝ), IsUnit (P.transpose * P).det →
    ∀ w : Fin K → ℝ,
      (gaussVec n).map (fun y => olsCoef P y ⬝ᵥ w) =
        gaussianReal 0 (w ⬝ᵥ ((P.transpose * P)⁻¹).mulVec w).toNNReal

/-- **Node N14** (paper proof, record 18, step 6: "For each fixed full-rank design,
Gaussianity gives E[Z²|X]=v and E[Z⁴|X]=3v² ... Subtract v/2 and square to get
P(Z²>v/2|X)≥1/12"). A one-dimensional Gaussian tail fact.
Suggested routes: Paley–Zygmund with `∫ z² = v`, `∫ z⁴ = 3v²` under `gaussianReal 0 v`
(central moments, e.g. via `gaussianReal_map_const_mul` from `N(0,1)` and its even moments),
splitting `v = ∫ z² ≤ v/2 + √(∫ z⁴ · P(z² > v/2))`; or directly from the density
(`gaussianReal_apply`, `gaussianPDFReal`, lower bound of the density on `[√(v/2), 2√v]`). -/
def N14 : Prop :=
  ∀ v : ℝ≥0, 0 < v → (1 : ℝ) / 12 ≤ ((gaussianReal 0 v) {z | (v : ℝ) / 2 < z ^ 2}).toReal

/-- Conclusion of the fixed-design step: for `t ≥ 25` and every design in `D_{t⁴}`, the OLS
`[0,1/2]`-risk exceeds `1` with Gaussian probability at least `1/12`. -/
def FixedDesignBound : Prop :=
  ∀ t : ℕ, 25 ≤ t → ∀ x ∈ designSet (t ^ 4),
    (1 : ℝ) / 12 ≤
      ((gaussVec (t ^ 4)) {y | 1 < regionInt (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)}).toReal

/-- **Node N15** (paper proof, record 18, steps 4-6: "v(X)≥N/(c^TAc)=N/(∑_i r_n(X_i)²). On B_n,
v(X)≥T_d(u_n)²/(4n²) ... On B_n and t≥18, v>2, so that event implies R_{n,1/2}≥Z²>1").
The fixed-design bound, from the deterministic and Gaussian nodes. With `r = chebR t`,
`c` its coefficients (`natDegree ≤ t³`, so `r = coeffPoly c`), `w = regionMoments (t³) r`,
`N = regionInt r r = c ⬝ w > 0`, `σ² = wᵀ(PᵀP)⁻¹w`: on `{σ²/2 < L²}` (probability `≥ 1/12`
by `N13`, `N14`; `σ² > 0` by `N9`), `regionInt p̂ p̂ ≥ L²/N > σ²/(2N) ≥ N/(2∑ r(x_i)²) ≥
N/(2t⁴) ≥ 9t⁴/3276800 > 1` for `t ≥ 25` (`25⁴ · 9 = 3515625 > 3276800`).
Suggested route: `measure_mono` from `{σ²/2 < L²}` into the target set; `Measure.map_apply`
(measurable `y ↦ olsCoef P y ⬝ w`: linear, `Continuous.measurable`). -/
def N15 : Prop :=
  N5 → N7 → N8 → N9 → N10 → N11 → N12 → N13 → N14 → FixedDesignBound

/-! ## Nodes: design law, measurability and Fubini (referee-1 fix 3) -/

/-- **Node N16** (paper proof, record 18, step 3: "By independence P(B_n)=(1-1/n)^n ... The
almost-sure upper bound X_i≤1 is understood"; step 4: "Uniform sample points are distinct
with probability one"). The design event has probability at least `1/6` (the paper's
`1/4` also holds; `1/6` suffices and follows from `(1-1/n)^n ≥ 1/(2e) > 1/6`).
Suggested route: `Measure.pi_pi` on the box `Set.pi univ (fun _ => Icc (1/n) 1)` (mass
`(1 - 1/n)^n` under `uniformLaw 0 1`); `(1 + 1/(n-1))^(n-1) ≤ e` (`Real.add_one_le_exp`,
`Real.exp_one_lt_d9`); each diagonal `{x | x i = x j}`, `i ≠ j`, is null (two-coordinate
marginal `uniform ⊗ uniform`, `Measure.prod_apply`, `measure_singleton` for the atomless
uniform law: `NoAtoms` via `withDensity` of Lebesgue); `measure_biUnion_null_iff`. -/
def N16 : Prop :=
  ∀ n : ℕ, 2 ≤ n → (1 : ℝ) / 6 ≤ ((unifVec n) (designSet n)).toReal

/-- **Node N17** (referee-1 fix 3: "verify measurable risk/bad events"). The bad set is
measurable in `(design, responses)`.
Suggested route: `designSet` is a box intersected with `⋂_{i ≠ j} {x_i ≠ x_j}`
(`measurableSet_eq_fun`, `MeasurableSet.iInter`); `(x, y) ↦ olsCoef (vand d x) y` is
measurable (entries of `(PᵀP)⁻¹ = Ring.inverse (det) • adjugate` are measurable:
`Matrix.inv_def`, `Continuous.matrix_det`/`Continuous.matrix_adjugate`-type facts,
`Measurable.inv`); `regionInt (coeffPoly b) (coeffPoly b)` is a quadratic polynomial in `b`
(`N8`-style linearity), hence continuous; `measurableSet_lt`. -/
def N17 : Prop := ∀ t : ℕ, MeasurableSet (badSet t)

/-- **Node N18** (referee-1 fix 3: "verify ... the finite product law of the first n
pairs"). Under `N1`, the first `n` covariates and outcomes have law
`Uniform^n ⊗ N(0,1)^n`.
Suggested route: `Measure.infinitePi_map_restrict` (law of the first `n` coordinates is
`Measure.pi (fun _ => sieveNu)`), then `measurePreserving_arrowProdEquivProdArrow` to split
`Fin n → ℝ × ℝ` into `(Fin n → ℝ) × (Fin n → ℝ)`; `Measure.map_map`. -/
def N18 : Prop :=
  N1 → ∀ n : ℕ, sieveMu.map (firstN n) = (unifVec n).prod (gaussVec n)

/-- Conclusion of the Fubini step: the stream bad event has probability at least `1/72`. -/
def BadProbBound : Prop :=
  ∀ t : ℕ, 25 ≤ t → (1 : ℝ) / 72 ≤ (sieveMu (firstN (t ^ 4) ⁻¹' badSet t)).toReal

/-- **Node N19** (paper proof, record 18, step 6: "Integration over the covariate design gives
P(R_{t⁴,1/2}>1)≥P(B_{t⁴})/12 ... These conditional computations may be performed as
fixed-design Gaussian integrals and then integrated by the nonnegative Fubini theorem").
Suggested route: `Measure.map_apply` (measurable `firstN`, `N17`), `N18`,
`Measure.prod_apply` (sections `Prod.mk x ⁻¹' badSet t`), `setLIntegral_mono`/
`lintegral_mono` with the indicator of `designSet` times `1/12` (`N15`'s conclusion
`FixedDesignBound`), `lintegral_indicator_const`, `N16`; `ENNReal.toReal` conversions. -/
def N19 : Prop :=
  N1 → N18 → N16 → N17 → FixedDesignBound → BadProbBound

/-- **Node N20** (paper proof, record 18, step 6: "The full risk in the recorded conclusion
is R_n=∫_0^1 m̂_n(x)²dx, because the covariate marginal is exactly Uniform[0,1] and m=0.
Nonnegativity gives R_n≥R_{n,1/2}"). Full uniform risk dominates the `[0,1/2]` risk.
Suggested route: `uniformLaw` is `withDensity` of `1_{[0,1]}`
(`integral_withDensity_eq_integral_toReal_smul`/`setIntegral` of the indicator density),
`setIntegral_mono_set` from `Icc 0 (1/2)` to `Icc 0 1` (nonnegative integrand, polynomial
integrable on `Icc 0 1`). -/
def N20 : Prop :=
  ∀ p : Polynomial ℝ,
    regionInt p p ≤ ∫ z, (p.eval z - sieveM z) ^ 2 ∂(uniformLaw 0 1)

/-! ## Assembly -/

/-- On the bad event the stream risk is at least `1`: the fit is the OLS polynomial
(`N6`, through `N3` for the degree and `N5`), and the full risk dominates the region risk
(`N20`). -/
theorem badSet_subset (hN1 : N1) (hN3 : N3) (hN5 : N5) (hN6 : N6) (hN20 : N20)
    (fit : ℕ → (ℕ → ℝ × ℝ) → Polynomial ℝ) (hfit : IsSieveLS sieveX sieveY sieveJ fit)
    (t : ℕ) (ht : 2 ≤ t) :
    firstN (t ^ 4) ⁻¹' badSet t ⊆
      {ω | 1 ≤ dist (∫ x, ((fit (t ^ 4) ω).eval x - sieveM x) ^ 2
        ∂(sieveMu.map (sieveX 0))) 0} := by
  intro ω hω
  obtain ⟨hdes, hrisk⟩ := hω
  have hJt : sieveJ (t ^ 4) = t ^ 3 := hN3.2.2 t
  have hd : t ^ 3 + 1 ≤ t ^ 4 := by
    have h2t : 2 ≤ t := ht
    have : t ^ 3 * 2 ≤ t ^ 3 * t := Nat.mul_le_mul_left _ h2t
    have hpos : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
    calc t ^ 3 + 1 ≤ t ^ 3 * 2 := by omega
      _ ≤ t ^ 3 * t := this
      _ = t ^ 4 := by ring
  have hfeq : fit (t ^ 4) ω =
      olsPoly (t ^ 3) (fun i : Fin (t ^ 4) => sieveX i ω) (fun i : Fin (t ^ 4) => sieveY i ω) :=
    hN6 hN5 (t ^ 4) (t ^ 3) (fun i => sieveX i ω) (fun i => sieveY i ω) (fit (t ^ 4) ω) hd
      hdes.2 (hJt ▸ (hfit (t ^ 4) ω).1)
      (fun q hq => (hfit (t ^ 4) ω).2 q (hJt ▸ hq))
  show 1 ≤ dist (∫ x, ((fit (t ^ 4) ω).eval x - sieveM x) ^ 2 ∂(sieveMu.map (sieveX 0))) 0
  rw [hN1.2.2.2, hfeq, Real.dist_eq, sub_zero]
  exact hrisk.le.trans ((hN20 _).trans (le_abs_self _))

/-- The nodes suffice: specialize the frozen contract to the witness with any least-squares
fit; along `n = t⁴` the `ε = 1` bad-event probabilities stay `≥ 1/72` for `t ≥ 25`, so they
cannot tend to `0`. -/
theorem assemble (hBlp : PolynomialBlp.N3.{0}) (hN1 : N1) (hN2 : N2) (hN3 : N3) (hN4 : N4)
    (hN5 : N5) (hN6 : N6) (hN7 : N7) (hN8 : N8) (hN9 : N9) (hN10 : N10) (hN11 : N11)
    (hN12 : N12) (hN13 : N13) (hN14 : N14) (hN15 : N15) (hN16 : N16) (hN17 : N17) (hN19 : N19)
    (hN18 : N18) (hN20 : N20) : Target := by
  intro H
  have hprob : IsProbabilityMeasure sieveMu := hN1.1
  obtain ⟨hpdf, hYi, hcef⟩ := hN2 hN1
  obtain ⟨fit, hfit⟩ := hN4 hBlp sieveX sieveY sieveJ
  have hCP := @H (ℕ → ℝ × ℝ) _ sieveMu hprob sieveX sieveY hN1.2.1 hYi 0 1 one_pos sieveF hpdf
    sieveF_pos sieveM contDiff_const hcef sieveJ hN3.1 hN3.2.1 fit hfit
  have hT := (hCP 1 one_pos).comp (tendsto_pow_atTop (n := 4) (by norm_num))
  have hev := hT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 72))
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hev
  have hlt := ht₀ (max t₀ 25) (le_max_left _ _)
  have hbad := hN19 hN1 hN18 hN16 hN17 (hN15 hN5 hN7 hN8 hN9 hN10 hN11 hN12 hN13 hN14) (max t₀ 25)
    (le_max_right _ _)
  have hsub := badSet_subset hN1 hN3 hN5 hN6 hN20 fit hfit (max t₀ 25)
    (le_trans (by norm_num) (le_max_right _ _))
  have hmono := ENNReal.toReal_mono (measure_ne_top sieveMu _) (measure_mono hsub)
  simp only [Function.comp, prob] at hlt
  linarith

end

end AronowAudit.P001.Wave1.SieveRate
