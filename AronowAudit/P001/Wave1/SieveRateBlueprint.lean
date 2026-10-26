import AronowAudit.P001.Wave1.PolynomialBlpBlueprint
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Counterexample to the printed sieve degree-rate assertion (P001-T119)

The printed assertion states that for every IID stream of
pairs with integrable `Y`, a covariate PDF positive exactly on `[a,b]` (`a < b`), a globally
real-analytic CEF `m` (`ContDiff ℝ ⊤ m` in this library), degrees with `J_n → ∞`,
`J_n/n → 0`, and every pointwise least-squares polynomial fit (`IsSieveLS`, squared
residuals), the population L² error
`∫ (fit_n - m)² d(law of X)` tends to `0` in probability (`CP`).

`Target` negates this universal assertion for `Ω : Type` (universe 0).

The witness has `Ω = ℕ → ℝ × ℝ` with the
infinite product of `Uniform[0,1] ⊗ N(0,1)`, `X_i, Y_i` the coordinates, `a = 0`, `b = 1`,
`f = 1_{[0,1]}`, `m = 0`, `J_n = ⌊n^{3/4}⌋`, and *any* least-squares fit (one exists for every
sample by projection, `N4`). Along `n = t⁴` (`J_n = t³`), for `t ≥ 25`, the bad event
`{risk ≥ 1}` has probability at least `1/72`, so `CP` fails at `ε = 1`.

The probability bound follows from these explicit inequalities:
* on the design event `D_n = {all X_i ∈ [1/n, 1], X injective}` (probability `≥ 1/6`, `N16`),
  the design has full column rank (`N5`) and *every* minimizer equals the OLS polynomial
  (`N6`), so no measurable selection of `fit` is needed (outer-measure monotonicity);
* `r_t = T_{t³}((2x-1-a)/(1-a))`, `a = t⁻⁴`, satisfies `|r_t| ≤ 1` on `[a,1]` and
  `∫_0^{1/2} r_t² ≥ 9t⁸/1638400` (`N10`, `N11`, `N12`).
  Write `N = ∫_0^{1/2} r_t(x)² dx` for this regional squared norm;
* for each fixed design in `D_n`, `L(y) = ⟨b̂(y), w⟩` with `w_k = ∫_0^{1/2} x^k r_t` is exactly
  `N(0, σ²)`, `σ² = wᵀ(PᵀP)⁻¹w` (`N13`); with prob. `≥ 1/12`, `L² > σ²/2` (`N14`); on that
  event `∫_0^{1/2} p̂² ≥ L²/N > σ²/(2N) ≥ N/(2 Σ r_t(x_i)²) ≥ N/(2t⁴) ≥ 9t⁴/3276800 > 1`
  (`N7`, `N8`, `N9`), giving the fixed-design statement `N15`;
* the first `n` pairs have law `Uniform^n ⊗ N(0,1)^n` (`N18`), the bad set is measurable
  (`N17`), and nonnegative Fubini gives probability `≥ (1/6)(1/12)` (`N19`);
* the full risk under `Uniform[0,1]` dominates the `[0,1/2]` risk (`N20`).

The Gaussian computations are for deterministic designs under the finite Gaussian
response product. Nonnegative Fubini avoids any integrability assumption on a random
inverse Gram matrix.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- Negation of the universal assertion (universe 0). -/
def Target : Prop :=
  ¬ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ), IID μ (fun i ω => (X i ω, Y i ω)) → Integrable (Y 0) μ →
    ∀ (a b : ℝ), a < b → ∀ (f : ℝ → ℝ), HasPDF (μ.map (X 0)) f →
    (∀ x, 0 < f x ↔ x ∈ Set.Icc a b) → ∀ (m : ℝ → ℝ), ContDiff ℝ ⊤ m →
    IsCEF μ (X 0) (Y 0) m → ∀ (J : ℕ → ℕ), Tendsto J atTop atTop →
    Tendsto (fun (n : ℕ) => (J n : ℝ) / (n : ℝ)) atTop (nhds 0) →
    ∀ (fit : ℕ → Ω → Polynomial ℝ), IsSieveLS X Y J fit →
    CP μ (fun n ω => ∫ x, ((fit n ω).eval x - m x) ^ 2 ∂(μ.map (X 0))) 0

/-! ## Witness data -/

/-- `Uniform[0,1]` (`uniformLaw 0 1`) is a probability measure. Needed to form
the infinite product; this supplies the probability-measure instance for the witness. -/
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

/-- The globally real-analytic CEF `m = 0`. -/
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

/-- The OLS polynomial `∑_k ((PᵀP)⁻¹Pᵀy)_k X^k` (`olsCoef`). -/
def olsPoly (d : ℕ) {n : ℕ} (x y : Fin n → ℝ) : Polynomial ℝ :=
  coeffPoly (olsCoef (vand d x) y)

/-- `∫_{[0,1/2]} p q` (Lebesgue). -/
def regionInt (p q : Polynomial ℝ) : ℝ := ∫ z in Set.Icc (0 : ℝ) (1/2), p.eval z * q.eval z

/-- `w_k = ∫_{[0,1/2]} x^k r(x) dx`, `k ≤ d`. -/
def regionMoments (d : ℕ) (r : Polynomial ℝ) : Fin (d + 1) → ℝ :=
  fun k => regionInt (X ^ (k : ℕ)) r

/-- The design event: all points in `[1/n, 1]` and pairwise distinct. -/
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

/-! ## model and rates -/

/-- The stream law is a probability measure with IID coordinate pairs,
one-observation law `sieveNu`, and covariate marginal `uniformLaw 0 1`. -/
def N1 : Prop :=
  IsProbabilityMeasure sieveMu ∧ IID sieveMu (fun i ω => (sieveX i ω, sieveY i ω)) ∧
    sieveMu.map (fun ω => (sieveX 0 ω, sieveY 0 ω)) = sieveNu ∧
    sieveMu.map (sieveX 0) = uniformLaw 0 1

/-- Under `N1`, the covariate has PDF `sieveF`, the outcome is integrable,
and `sieveM` is a CEF. -/
def N2 : Prop :=
  N1 → HasPDF (sieveMu.map (sieveX 0)) sieveF ∧ Integrable (sieveY 0) sieveMu ∧
    IsCEF sieveMu (sieveX 0) (sieveY 0) sieveM

/-- The degrees `sieveJ` diverge, their ratio to sample size tends to zero,
and `sieveJ (t⁴) = t³`. -/
def N3 : Prop :=
  Tendsto sieveJ atTop atTop ∧
    Tendsto (fun n : ℕ => (sieveJ n : ℝ) / (n : ℝ)) atTop (nhds 0) ∧
    ∀ t : ℕ, sieveJ (t ^ 4) = t ^ 3

/-- Under `PolynomialBlp.N3`, a pointwise least-squares fit exists for every
stream and degree sequence. -/
def N4 : Prop :=
  PolynomialBlp.N3.{0} →
  ∀ {Ω : Type} (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ), ∃ fit : ℕ → Ω → Polynomial ℝ,
    IsSieveLS X Y J fit

/-! ## least squares on full-rank designs -/

/-- An injective design with at least `d+1` points has an invertible Vandermonde
Gram matrix at degree `d`. -/
def N5 : Prop :=
  ∀ (n d : ℕ) (x : Fin n → ℝ), d + 1 ≤ n → Function.Injective x →
    IsUnit ((vand d x).transpose * vand d x).det

/-- Under `N5`, every degree-bounded residual-sum minimizer on an injective design
with `d+1 ≤ n` equals the OLS polynomial. -/
def N6 : Prop :=
  N5 →
  ∀ (n d : ℕ) (x y : ℕ → ℝ) (p : Polynomial ℝ), d + 1 ≤ n →
    Function.Injective (fun i : Fin n => x i) → p.natDegree ≤ d →
    (∀ q : Polynomial ℝ, q.natDegree ≤ d →
      ∑ i ∈ Finset.range n, (y i - p.eval (x i)) ^ 2 ≤
        ∑ i ∈ Finset.range n, (y i - q.eval (x i)) ^ 2) →
    p = olsPoly d (fun i : Fin n => x i) (fun i : Fin n => y i)

/-! ## deterministic inequalities -/

/-- Integral Cauchy–Schwarz on `[0,1/2]` for polynomials with positive squared norm. -/
def N7 : Prop :=
  ∀ p r : Polynomial ℝ, 0 < regionInt r r → regionInt p r ^ 2 / regionInt r r ≤ regionInt p p

/-- Coefficient vectors represent the regional integral through `regionMoments`
and polynomial evaluation through the Vandermonde matrix. -/
def N8 : Prop :=
  (∀ (d : ℕ) (b : Fin (d + 1) → ℝ) (r : Polynomial ℝ),
      regionInt (coeffPoly b) r = b ⬝ᵥ regionMoments d r) ∧
    ∀ (d n : ℕ) (x : Fin n → ℝ) (c : Fin (d + 1) → ℝ) (i : Fin n),
      (vand d x).mulVec c i = (coeffPoly c).eval (x i)

/-- For an invertible Gram matrix, Cauchy–Schwarz bounds `(c ⬝ᵥ w)²` by the product
of the design quadratic form and the inverse-Gram quadratic form. -/
def N9 : Prop :=
  ∀ (n K : ℕ) (P : Matrix (Fin n) (Fin K) ℝ), IsUnit (P.transpose * P).det →
    ∀ c w : Fin K → ℝ,
      (c ⬝ᵥ w) ^ 2 ≤ (∑ i, (P.mulVec c i) ^ 2) * (w ⬝ᵥ ((P.transpose * P)⁻¹).mulVec w)

/-- Chebyshev polynomials have absolute value at most `1` on `[-1,1]`. -/
def N10 : Prop :=
  ∀ (d : ℕ) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → |(Chebyshev.T ℝ (d : ℤ)).eval z| ≤ 1

/-- For `d ≥ 3` and `0 ≤ s ≤ 1`, `T_d(1+s) ≥ d⁶ s³ / 720`. -/
def N11 : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    (d : ℝ) ^ 6 * s ^ 3 / 720 ≤ (Chebyshev.T ℝ (d : ℤ)).eval (1 + s)

/-- Under `N10` and `N11`, the boundary polynomial has degree at most `t³`,
is bounded by `1` on `[t⁻⁴,1]`, and has regional squared norm at least `9t⁸/1638400`
for `t ≥ 2`. -/
def N12 : Prop :=
  N10 → N11 → ∀ t : ℕ, 2 ≤ t →
    (chebR t).natDegree ≤ t ^ 3 ∧
    (∀ z ∈ Set.Icc (1 / ((t : ℝ) ^ 4)) 1, |(chebR t).eval z| ≤ 1) ∧
    9 * (t : ℝ) ^ 8 / 1638400 ≤ regionInt (chebR t) (chebR t)

/-! ## fixed-design Gaussian computations -/

/-- On a deterministic full-rank design, every linear functional of the OLS
coefficients under standard Gaussian responses is centered Gaussian with the stated variance. -/
def N13 : Prop :=
  ∀ (n K : ℕ) (P : Matrix (Fin n) (Fin K) ℝ), IsUnit (P.transpose * P).det →
    ∀ w : Fin K → ℝ,
      (gaussVec n).map (fun y => olsCoef P y ⬝ᵥ w) =
        gaussianReal 0 (w ⬝ᵥ ((P.transpose * P)⁻¹).mulVec w).toNNReal

/-- For a centered Gaussian with positive variance `v`,
the probability of `z² > v/2` is at least `1/12`. -/
def N14 : Prop :=
  ∀ v : ℝ≥0, 0 < v → (1 : ℝ) / 12 ≤ ((gaussianReal 0 v) {z | (v : ℝ) / 2 < z ^ 2}).toReal

/-- For `t ≥ 25` and every design in `D_{t⁴}`, the OLS
`[0,1/2]`-risk exceeds `1` with Gaussian probability at least `1/12`. -/
def FixedDesignBound : Prop :=
  ∀ t : ℕ, 25 ≤ t → ∀ x ∈ designSet (t ^ 4),
    (1 : ℝ) / 12 ≤
      ((gaussVec (t ^ 4)) {y | 1 < regionInt (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)}).toReal

/-- The deterministic inequalities and Gaussian bounds in `N5`, `N7`–`N14`
imply `FixedDesignBound`. -/
def N15 : Prop :=
  N5 → N7 → N8 → N9 → N10 → N11 → N12 → N13 → N14 → FixedDesignBound

/-! ## design law, measurability and Fubini -/

/-- For `n ≥ 2`, the uniform-design event has probability at least `1/6`. -/
def N16 : Prop :=
  ∀ n : ℕ, 2 ≤ n → (1 : ℝ) / 6 ≤ ((unifVec n) (designSet n)).toReal

/-- The joint bad set is measurable in the design and responses. -/
def N17 : Prop := ∀ t : ℕ, MeasurableSet (badSet t)

/-- Under `N1`, the first `n` covariates and outcomes have product law
`(unifVec n).prod (gaussVec n)`. -/
def N18 : Prop :=
  N1 → ∀ n : ℕ, sieveMu.map (firstN n) = (unifVec n).prod (gaussVec n)

/-- For `t ≥ 25`, the stream bad event has probability at least `1/72`. -/
def BadProbBound : Prop :=
  ∀ t : ℕ, 25 ≤ t → (1 : ℝ) / 72 ≤ (sieveMu (firstN (t ^ 4) ⁻¹' badSet t)).toReal

/-- The stream law, finite-sample law, design probability, measurability, and
fixed-design bound imply `BadProbBound`. -/
def N19 : Prop :=
  N1 → N18 → N16 → N17 → FixedDesignBound → BadProbBound

/-- The full squared risk under `uniformLaw 0 1` dominates the `[0,1/2]` squared risk. -/
def N20 : Prop :=
  ∀ p : Polynomial ℝ,
    regionInt p p ≤ ∫ z, (p.eval z - sieveM z) ^ 2 ∂(uniformLaw 0 1)

/-! ## Failure of convergence in probability -/

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

/-- Along `n = t⁴`, every least-squares fit has bad-event probabilities at least
`1/72` for `t ≥ 25`, contradicting convergence in probability. -/
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
