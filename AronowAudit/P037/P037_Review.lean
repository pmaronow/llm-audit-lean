import AronowAudit.P037.P037_FiniteDesign

/-!
An expected-projection argument.
The residual below uses design-expected projection coefficients. It is not
the seed innovation D(C-μ), nor an assignment-specific fitted residual.
The result allows arbitrary fixed untreated levels. It establishes expected
normal-equation identification; finite-sample unbiasedness and empirical
adequacy are separate questions.
-/

namespace AronowAudit.P037.ExpectedProjection
open scoped BigOperators
set_option autoImplicit false

noncomputable def inner {I : Type*} [Fintype I] (x y : I → ℝ) : ℝ :=
  ∑ i, x i * y i

noncomputable def cross {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y : Ω → I → ℝ) : ℝ :=
  designMean d (fun w => inner (x w) (y w))

theorem cross_comm {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y : Ω → I → ℝ) : cross d x y = cross d y x := by
  simp only [cross, inner, mul_comm]

theorem cross_left_sub {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y z : Ω → I → ℝ) :
    cross d (fun w i => x w i - y w i) z = cross d x z - cross d y z := by
  simp only [cross, inner, sub_mul, Finset.sum_sub_distrib, designMean_sub]

theorem cross_right_sub {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y z : Ω → I → ℝ) :
    cross d x (fun w i => y w i - z w i) = cross d x y - cross d x z := by
  simp only [cross, inner, mul_sub, Finset.sum_sub_distrib, designMean_sub]

theorem cross_left_mul {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y : Ω → I → ℝ) (c : ℝ) :
    cross d (fun w i => c * x w i) y = c * cross d x y := by
  simp only [cross, inner, mul_assoc, ← Finset.mul_sum, designMean_mul]

theorem cross_right_mul {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y : Ω → I → ℝ) (c : ℝ) :
    cross d x (fun w i => c * y w i) = c * cross d x y := by
  rw [cross_comm, cross_left_mul, cross_comm d y x]

theorem cross_right_add {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y z : Ω → I → ℝ) :
    cross d x (fun w i => y w i + z w i) = cross d x y + cross d x z := by
  simp only [cross, inner, mul_add, Finset.sum_add_distrib, designMean_add]

theorem cross_right_sum {Ω I K : Type*} [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (x : Ω → I → ℝ) (y : K → Ω → I → ℝ) :
    cross d x (fun w i => ∑ k, y k w i) = ∑ k, cross d x (y k) := by
  simp only [cross, inner, Finset.mul_sum]
  have hs : (fun w => ∑ i, ∑ k, x w i * y k w i) =
      (fun w => ∑ k, ∑ i, x w i * y k w i) := by
    funext w; exact Finset.sum_comm
  rw [hs, designMean_sum]

theorem cross_fixed_right {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x : Ω → I → ℝ) (a : I → ℝ) :
    cross d x (fun _ => a) = ∑ i, designMean d (fun w => x w i) * a i := by
  simp only [cross, inner, designMean_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_comm] using designMean_mul d (a i) (fun w => x w i)

theorem cross_fixed_right_zero {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x : Ω → I → ℝ)
    (hx : ∀ i, designMean d (fun w => x w i) = 0) (a : I → ℝ) :
    cross d x (fun _ => a) = 0 := by
  rw [cross_fixed_right]
  simp only [hx, zero_mul, Finset.sum_const_zero]

/-- Coefficient on demeaned treatment in the expected projection. -/
noncomputable def treatmentProjection {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) : ℝ := cross d z t / cross d t t

/-- The mean-spanning fixed-control coefficient is plam. -/
noncomputable def residual {Ω I K : Type*} [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) (V : K → I → ℝ)
    (lam : K → ℝ) (p : ℝ) : Ω → I → ℝ := fun w i =>
  z w i - treatmentProjection d t z * t w i - p * ∑ k, lam k * V k i

/-- Mean-spanning and equal marginal treatment probabilities force the
expected-projection residual to have coordinatewise mean zero. -/
theorem residual_mean_zero {Ω I K : Type*} [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) (V : K → I → ℝ)
    (lam : K → ℝ) (p : ℝ)
    (ht : ∀ i, designMean d (fun w => t w i) = 0)
    (hz : ∀ i, designMean d (fun w => z w i) = p * ∑ k, lam k * V k i) :
    ∀ i, designMean d (fun w => residual d t z V lam p w i) = 0 := by
  intro i
  simp only [residual, designMean_sub, designMean_mul, designMean_const, ht, hz]
  ring

/-- These are the actual expected nuisance normal equations. No rank
condition on redundant fixed columns is needed for this residual. -/
theorem residual_nuisance_orthogonal {Ω I K : Type*}
    [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) (V : K → I → ℝ)
    (lam : K → ℝ) (p : ℝ)
    (ht : ∀ i, designMean d (fun w => t w i) = 0)
    (hz : ∀ i, designMean d (fun w => z w i) = p * ∑ k, lam k * V k i)
    (htt : cross d t t ≠ 0) :
    cross d (residual d t z V lam p) t = 0 ∧
      ∀ k, cross d (residual d t z V lam p) (fun _ => V k) = 0 := by
  have hmean := residual_mean_zero d t z V lam p ht hz
  constructor
  · unfold residual
    rw [cross_left_sub, cross_left_sub, cross_left_mul]
    have hfixed : cross d (fun _ i => p * ∑ k, lam k * V k i) t = 0 := by
      rw [cross_comm]
      exact cross_fixed_right_zero d t ht _
    rw [hfixed]
    simp only [treatmentProjection]
    field_simp
    ring
  · intro k
    exact cross_fixed_right_zero d _ hmean (V k)

/-- Expected residual-on-raw-composition moment equals its residual
sum of squares, as in Frisch-Waugh-Lovell. -/
theorem residual_composition_moment {Ω I K : Type*}
    [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) (V : K → I → ℝ)
    (lam : K → ℝ) (p : ℝ)
    (ht : ∀ i, designMean d (fun w => t w i) = 0)
    (hz : ∀ i, designMean d (fun w => z w i) = p * ∑ k, lam k * V k i)
    (htt : cross d t t ≠ 0) :
    cross d (residual d t z V lam p) z =
      cross d (residual d t z V lam p) (residual d t z V lam p) := by
  have horth := residual_nuisance_orthogonal d t z V lam p ht hz htt
  have hmean := residual_mean_zero d t z V lam p ht hz
  have hfixed := cross_fixed_right_zero d (residual d t z V lam p) hmean
    (fun i => p * ∑ k, lam k * V k i)
  change cross d (residual d t z V lam p) z =
    cross d (residual d t z V lam p) (fun w i =>
      z w i - treatmentProjection d t z * t w i - p * ∑ k, lam k * V k i)
  rw [cross_right_sub, cross_right_sub, cross_right_mul, horth.1, hfixed]
  ring

/-- Expected normal equations written as orthogonality of the fitted
residual to treatment, fixed controls, and raw composition. -/
def NormalEquations {Ω I K : Type*} [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) (V : K → I → ℝ)
    (Y : Ω → I → ℝ) (τ : ℝ) (g : K → ℝ) (b : ℝ) : Prop :=
  let e := fun w i => Y w i - (τ * t w i + (∑ k, g k * V k i) + b * z w i)
  cross d t e = 0 ∧ (∀ k, cross d (fun _ => V k) e = 0) ∧ cross d z e = 0

/-- Common-slope response model: arbitrary fixed untreated
levels a, a common treatment intercept τ₀, and schoolwise moderation η.
The hY equality is on demeaned variables, with H = M(D⊙η). -/
theorem expected_projection_bias_identity {Ω I K : Type*}
    [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z H Y : Ω → I → ℝ) (V : K → I → ℝ)
    (lam : K → ℝ) (p τ₀ β τ b : ℝ) (g : K → ℝ) (a : I → ℝ)
    (ht : ∀ i, designMean d (fun w => t w i) = 0)
    (hz : ∀ i, designMean d (fun w => z w i) = p * ∑ k, lam k * V k i)
    (htt : cross d t t ≠ 0)
    (hK : 0 < cross d (residual d t z V lam p) (residual d t z V lam p))
    (hY : ∀ w i, Y w i = a i + τ₀ * t w i + H w i + β * z w i)
    (hN : NormalEquations d t z V Y τ g b) :
    b - β = cross d (residual d t z V lam p) H /
      cross d (residual d t z V lam p) (residual d t z V lam p) := by
  let r := residual d t z V lam p
  let e := fun w i => Y w i - (τ * t w i + (∑ k, g k * V k i) + b * z w i)
  have horth := residual_nuisance_orthogonal d t z V lam p ht hz htt
  have hmean := residual_mean_zero d t z V lam p ht hz
  have hrz := residual_composition_moment d t z V lam p ht hz htt
  change cross d t e = 0 ∧ (∀ k, cross d (fun _ => V k) e = 0) ∧
    cross d z e = 0 at hN
  have hre : cross d (residual d t z V lam p) e = 0 := by
    change cross d (fun w i => z w i - treatmentProjection d t z * t w i -
      p * ∑ k, lam k * V k i) e = 0
    rw [cross_left_sub, cross_left_sub, cross_left_mul, hN.1, hN.2.2]
    have hv : cross d (fun _ i => p * ∑ k, lam k * V k i) e = 0 := by
      rw [cross_comm, cross_right_mul, cross_right_sum]
      simp_rw [cross_right_mul, cross_comm d e, hN.2.1, mul_zero]
      simp
    rw [hv]
    ring
  have hrt : cross d r t = 0 := horth.1
  have hrv : ∀ k, cross d r (fun _ => V k) = 0 := horth.2
  have hrz2 : cross d r z = cross d r r := hrz
  have hfit : cross d r Y = b * cross d r r := by
    have hf : cross d r (fun w i => τ * t w i + (∑ k, g k * V k i) + b * z w i) =
        b * cross d r r := by
      rw [cross_right_add, cross_right_add, cross_right_mul, cross_right_sum,
        cross_right_mul]
      simp only [cross_right_mul, hrv, hrt, mul_zero, Finset.sum_const_zero, zero_add, hrz2]
    dsimp only [e] at hre
    rw [cross_right_sub, hf] at hre
    linarith
  have htrue : cross d r Y = cross d r H + β * cross d r r := by
    have hyfun : Y = fun w i => a i + τ₀ * t w i + H w i + β * z w i := by
      funext w i; exact hY w i
    rw [hyfun, cross_right_add, cross_right_add, cross_right_add,
      cross_right_mul, cross_right_mul, cross_fixed_right_zero d _ hmean,
      hrt, hrz2]
    ring
  have hne : cross d r r ≠ 0 := ne_of_gt hK
  apply (eq_div_iff hne).2
  nlinarith [hfit, htrue]

/-- The actual deterministic four-school block demeaning operation.
Keeping analysis membership fixed is what makes this operator fixed. -/
noncomputable def blockDemean {B : ℕ} (x : (Fin B × Fin 4) → ℝ) :
    (Fin B × Fin 4) → ℝ := fun i => x i - (1/4:ℝ) * ∑ j, x (i.1,j)


theorem blockDemean_sub {B : ℕ} (x y : (Fin B × Fin 4) → ℝ) :
    blockDemean (fun i => x i - y i) = fun i => blockDemean x i - blockDemean y i := by
  funext i
  simp only [blockDemean, Finset.sum_sub_distrib]
  ring

theorem blockDemean_mul {B : ℕ} (x : (Fin B × Fin 4) → ℝ) (c : ℝ) :
    blockDemean (fun i => c * x i) = fun i => c * blockDemean x i := by
  funext i
  simp only [blockDemean, ← Finset.mul_sum]
  ring

theorem blockDemean_sum {B : ℕ} {K : Type*} [Fintype K]
    (x : K → (Fin B × Fin 4) → ℝ) :
    blockDemean (fun i => ∑ k, x k i) = fun i => ∑ k, blockDemean (x k) i := by
  funext i
  simp only [blockDemean, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem blockDemean_idempotent {B : ℕ} (x : (Fin B × Fin 4) → ℝ) :
    blockDemean (blockDemean x) = blockDemean x := by
  funext i
  simp only [blockDemean, Fin.sum_univ_four]
  ring

theorem blockDemean_inner {B : ℕ} (x y : (Fin B × Fin 4) → ℝ) :
    inner (blockDemean x) y = inner x (blockDemean y) := by
  simp only [inner, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  simp only [blockDemean, Fin.sum_univ_four]
  ring

/-- Equal marginal treatment probabilities are enough here; assignments
within a block need not be independent. -/
theorem demeaned_treatment_mean {Ω : Type*} [Fintype Ω] {B : ℕ}
    (d : FiniteDesign Ω) (T : Ω → (Fin B × Fin 4) → ℝ) (p : ℝ)
    (hT : ∀ i, designMean d (fun w => T w i) = p) :
    ∀ i, designMean d (fun w => blockDemean (T w) i) = 0 := by
  intro i
  simp only [blockDemean, Fin.sum_univ_four, designMean_sub, designMean_mul,
    designMean_add, hT]
  ring

/-- The fixed controls must span the design mean after demeaning.
The relevant first moment is E[D_i C_i]=p μ_i, not C_i=q_i. -/
theorem demeaned_composition_mean {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (T C : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (μ : (Fin B × Fin 4) → ℝ)
    (lam : K → ℝ) (p : ℝ)
    (hTC : ∀ i, designMean d (fun w => T w i * C w i) = p * μ i)
    (hspan : ∀ i, blockDemean μ i = ∑ k, lam k * blockDemean (X k) i) :
    ∀ i, designMean d (fun w => blockDemean (fun j => T w j * C w j) i) =
      p * ∑ k, lam k * blockDemean (X k) i := by
  intro i
  simp only [blockDemean, designMean_sub, designMean_mul, designMean_sum, hTC]
  calc
    _ = p * blockDemean μ i := by
      simp only [blockDemean, ← Finset.mul_sum]
      ring
    _ = _ := by rw [hspan]; rfl

/-- The expected-projection residual is itself block centered. -/
theorem raw_residual_centered {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (T C : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (lam : K → ℝ) (p : ℝ) (w : Ω) :
    blockDemean (residual d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) lam p w) =
    residual d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) lam p w := by
  let ρ := treatmentProjection d (fun w => blockDemean (T w))
    (fun w => blockDemean (fun i => T w i * C w i))
  change blockDemean (fun i => blockDemean (fun i => T w i * C w i) i -
      ρ * blockDemean (T w) i - p * ∑ k, lam k * blockDemean (X k) i) = _
  rw [blockDemean_sub, blockDemean_sub, blockDemean_mul, blockDemean_mul,
    blockDemean_sum]
  simp only [blockDemean_mul, blockDemean_idempotent]
  rfl

/-- Full finite fixed-analysis-model result. T is the 0/1 school-treatment
indicator (the proof in fact only needs its stated first moments).
Untreated levels a_i and treatment moderation η_i are arbitrary fixed vectors.
The normal equations are for the actual raw DC regressor and original fixed
controls after block effects are profiled. All projection orthogonality is
derived, not assumed.

This is an expected-equations statement. It makes no finite-sample OLS
unbiasedness claim and does not validate the response model empirically. -/
theorem block_model_bias_identity {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (T C Y : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (a η μ : (Fin B × Fin 4) → ℝ)
    (lam : K → ℝ) (p τ₀ β τ b : ℝ) (g : K → ℝ)
    (hT : ∀ i, designMean d (fun w => T w i) = p)
    (hTC : ∀ i, designMean d (fun w => T w i * C w i) = p * μ i)
    (hspan : ∀ i, blockDemean μ i = ∑ k, lam k * blockDemean (X k) i)
    (hY : ∀ w i, Y w i = a i + T w i * (τ₀ + η i + β * C w i))
    (htt : cross d (fun w => blockDemean (T w)) (fun w => blockDemean (T w)) ≠ 0)
    (hK : 0 < cross d
      (residual d (fun w => blockDemean (T w))
        (fun w => blockDemean (fun i => T w i * C w i))
        (fun k => blockDemean (X k)) lam p)
      (residual d (fun w => blockDemean (T w))
        (fun w => blockDemean (fun i => T w i * C w i))
        (fun k => blockDemean (X k)) lam p))
    (hN : NormalEquations d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) (fun w => blockDemean (Y w)) τ g b) :
    let r := residual d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) lam p
    b - β = cross d r (fun w i => T w i * η i) / cross d r r := by
  let t := fun w => blockDemean (T w)
  let z := fun w => blockDemean (fun i => T w i * C w i)
  let V := fun k => blockDemean (X k)
  let r := residual d t z V lam p
  have ht := demeaned_treatment_mean d T p hT
  have hz := demeaned_composition_mean d T C X μ lam p hTC hspan
  have hy : ∀ w i, blockDemean (Y w) i =
      blockDemean a i + τ₀ * t w i + blockDemean (fun j => T w j * η j) i + β * z w i := by
    intro w i
    simp only [blockDemean, hY, t, z, Fin.sum_univ_four]
    ring
  have hi := expected_projection_bias_identity d t z
    (fun w => blockDemean (fun i => T w i * η i)) (fun w => blockDemean (Y w))
    V lam p τ₀ β τ b g (blockDemean a) ht hz htt hK hy hN
  have hcross : cross d r (fun w => blockDemean (fun i => T w i * η i)) =
      cross d r (fun w i => T w i * η i) := by
    unfold cross
    congr 1
    funext w
    rw [← blockDemean_inner, raw_residual_centered]
  change b - β = cross d r (fun w i => T w i * η i) / cross d r r
  rw [← hcross]
  exact hi

/-- A short name for the expected-projection residual of the actual
block-demeaned raw composition regressor. -/
noncomputable def blockResidual {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (T C : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (lam : K → ℝ) (p : ℝ) :=
  residual d (fun w => blockDemean (T w))
    (fun w => blockDemean (fun i => T w i * C w i))
    (fun k => blockDemean (X k)) lam p

/-- Common treatment intercepts suffice for expected-equation
identification even with arbitrary fixed untreated school outcomes.
Zero moderation numerator is the weaker sufficient condition in the bias
identity; this corollary takes η=0. -/
theorem common_intercept_identifies_slope {Ω K : Type*}
    [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (T C Y : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (a μ : (Fin B × Fin 4) → ℝ)
    (lam : K → ℝ) (p τ₀ β τ b : ℝ) (g : K → ℝ)
    (hT : ∀ i, designMean d (fun w => T w i) = p)
    (hTC : ∀ i, designMean d (fun w => T w i * C w i) = p * μ i)
    (hspan : ∀ i, blockDemean μ i = ∑ k, lam k * blockDemean (X k) i)
    (hY : ∀ w i, Y w i = a i + T w i * (τ₀ + β * C w i))
    (htt : cross d (fun w => blockDemean (T w)) (fun w => blockDemean (T w)) ≠ 0)
    (hK : 0 < cross d (blockResidual d T C X lam p) (blockResidual d T C X lam p))
    (hN : NormalEquations d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) (fun w => blockDemean (Y w)) τ g b) :
    b = β := by
  have hy : ∀ w i, Y w i = a i + T w i * (τ₀ + (0:ℝ) + β * C w i) := by
    simpa using hY
  have hi := block_model_bias_identity d T C Y X a (fun _ => 0) μ lam p τ₀ β τ b g
    hT hTC hspan hy htt hK hN
  have hz : cross d (blockResidual d T C X lam p) (fun _ _ => (0:ℝ)) = 0 := by
    simp only [cross, inner, mul_zero, Finset.sum_const_zero, designMean_const]
  change b - β = cross d (blockResidual d T C X lam p)
    (fun w i => T w i * 0) / cross d (blockResidual d T C X lam p)
      (blockResidual d T C X lam p) at hi
  simp only [mul_zero, hz, zero_div] at hi
  linarith


end AronowAudit.P037.ExpectedProjection

