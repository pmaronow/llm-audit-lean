import SAP.P001a.WH.W1.Leaves
import AronowAudit.P015.P015_ConvergenceCompletion
import AronowAudit.P001.Wave1.Gap.DecideB

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L8

lemma wholeHC0_scaling {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hn : 0 < n) :
    (n : ℝ) • wholeHC0 Z D n ω =
      (wholeEmpiricalQ Z n ω)⁻¹ * wholeFittedMeat Z D n ω *
        (wholeEmpiricalQ Z n ω)⁻¹ := by
  let A := wholeRows Z n ω
  let r : Fin n → ℝ := fun i => D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω
  have hc : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hgram : A.transpose * A = (n : ℝ) • wholeEmpiricalQ Z n ω := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, A, wholeRows,
      Matrix.smul_apply, smul_eq_mul, wholeEmpiricalQ]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => Z i ω j * Z i ω k) n]
    field_simp
  have hmeat : A.transpose * Matrix.diagonal (fun i => (r i)^2) * A =
      (n : ℝ) • wholeFittedMeat Z D n ω := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      A, wholeRows, r, Matrix.smul_apply, smul_eq_mul,
      wholeFittedMeat, wholeMeat]
    have hinner (l : Fin n) :
        (∑ i : Fin n, Z i ω j * (if i = l then
          (D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω)^2 else 0)) =
          (D l ω - Z l ω ⬝ᵥ wholeBetaHat Z D n ω)^2 * Z l ω j := by
      classical
      rw [Finset.sum_eq_single l]
      · simp
        ring
      · intro i hi hne
        simp [hne]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    simp_rw [hinner]
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω)^2 *
        Z i ω j * Z i ω k) n]
    field_simp
  have hinv : ((n : ℝ) • wholeEmpiricalQ Z n ω)⁻¹ =
      (n : ℝ)⁻¹ • (wholeEmpiricalQ Z n ω)⁻¹ :=
    AronowAudit.P015.ConvergenceCompletion.inverse_smul_real
      (wholeEmpiricalQ Z n ω) (n : ℝ) hc
  rw [wholeHC0, show wholeRows Z n ω = A by rfl]
  dsimp [A, r]
  rw [hgram, hmeat, hinv]
  simp [smul_smul, hc]

/-- The fitted-meat/inverse-Gram limits pass through the sandwich product. -/
lemma sandwich_product_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (hgram : WholeGramLimits μ Z D b)
    (hmeat : CP μ (wholeFittedMeat Z D) (wholeOmega μ (Z 0) (D 0) b)) :
    CP μ (fun n ω => (wholeEmpiricalQ Z n ω)⁻¹ * wholeFittedMeat Z D n ω *
      (wholeEmpiricalQ Z n ω)⁻¹)
      (wholeSandwich μ (Z 0) (D 0) b) := by
  let Q := (wholeQ μ (Z 0))⁻¹
  let M := wholeOmega μ (Z 0) (D 0) b
  let I := Bool × Fin p × Fin p
  let X : ℕ → Ω → I → ℝ := fun n ω i =>
    if i.1 then wholeFittedMeat Z D n ω i.2.1 i.2.2
    else (wholeEmpiricalQ Z n ω)⁻¹ i.2.1 i.2.2
  let x₀ : I → ℝ := fun i => if i.1 then M i.2.1 i.2.2 else Q i.2.1 i.2.2
  have hcoord : ∀ i, TendstoInMeasure μ (fun n ω => X n ω i) atTop (fun _ => x₀ i) := by
    rintro ⟨t, j, k⟩
    cases t
    · have hc : CP μ (fun n ω => (wholeEmpiricalQ Z n ω)⁻¹ j k) (Q j k) := by
        exact AronowAudit.P001.probability_convergence_continuous_at μ
          (fun n ω => (wholeEmpiricalQ Z n ω)⁻¹) (wholeQ μ (Z 0))⁻¹
          (fun A : Matrix (Fin p) (Fin p) ℝ => A j k) hgram.inverse
          (((continuous_apply k).comp (continuous_apply j)).continuousAt)
      exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure
        μ _ _).mp hc
    · have hc : CP μ (fun n ω => wholeFittedMeat Z D n ω j k) (M j k) := by
        exact AronowAudit.P001.probability_convergence_continuous_at μ
          (wholeFittedMeat Z D) M (fun A : Matrix (Fin p) (Fin p) ℝ => A j k)
          hmeat (((continuous_apply k).comp (continuous_apply j)).continuousAt)
      exact (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure
        μ _ _).mp hc
  let G : (I → ℝ) → Matrix (Fin p) (Fin p) ℝ := fun x j k =>
    ∑ l : Fin p, (∑ m : Fin p,
      x (false, j, m) * x (true, m, l)) * x (false, l, k)
  have hG : ContinuousAt G x₀ := by
    apply continuousAt_pi.2
    intro j
    apply continuousAt_pi.2
    intro k
    dsimp [G]
    fun_prop
  have hlim := AronowAudit.P015.ConvergenceCompletion.finite_cmt μ X x₀ G hcoord hG
  have hcp : CP μ (fun n ω => G (X n ω)) (G x₀) :=
    (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure
      μ _ _).mpr hlim
  have hseq (n : ℕ) (ω : Ω) :
      G (X n ω) = (wholeEmpiricalQ Z n ω)⁻¹ * wholeFittedMeat Z D n ω *
        (wholeEmpiricalQ Z n ω)⁻¹ := by
    ext j k
    simp [G, X, Matrix.mul_apply]
  have hQsym : (wholeQ μ (Z 0)).transpose = wholeQ μ (Z 0) := by
    ext j k
    simp [wholeQ, mul_comm]
  have hInvSym : Q.transpose = Q := by
    dsimp [Q]
    rw [Matrix.transpose_nonsing_inv, hQsym]
  have htarget : G x₀ = wholeSandwich μ (Z 0) (D 0) b := by
    ext j k
    simp [G, x₀, wholeSandwich, Q, M, Matrix.mul_apply, hInvSym]
  simpa only [hseq, htarget] using hcp

end SAP.P001a.WH.W1.P.T18_L8

theorem SAP.P001a.WH.W1.T18_L8_proof : SAP.P001a.WH.W1.T18_L8 := by
  intro Ω hΩ μ hμ p Z D hiid b h hgram hmeat
  have hprod := SAP.P001a.WH.W1.P.T18_L8.sandwich_product_limit μ Z D b hgram hmeat
  intro ε hε
  have hscale (n : ℕ) (ω : Ω) (hn : 0 < n) :=
    SAP.P001a.WH.W1.P.T18_L8.wholeHC0_scaling Z D n ω hn
  have heq : ∀ᶠ n : ℕ in atTop,
      (fun ω => (n : ℝ) • wholeHC0 Z D n ω) =ᵐ[μ]
        (fun ω => (wholeEmpiricalQ Z n ω)⁻¹ * wholeFittedMeat Z D n ω *
          (wholeEmpiricalQ Z n ω)⁻¹) := by
    have hnat : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.2 ⟨1, fun n hn => by omega⟩
    filter_upwards [hnat] with n hn
    exact Filter.Eventually.of_forall (fun ω => hscale n ω (by omega))
  have heq' : ∀ᶠ n : ℕ in atTop,
      (fun ω => (wholeEmpiricalQ Z n ω)⁻¹ * wholeFittedMeat Z D n ω *
        (wholeEmpiricalQ Z n ω)⁻¹) =ᵐ[μ]
      (fun ω => (n : ℝ) • wholeHC0 Z D n ω) := by
    filter_upwards [heq] with n hn
    exact hn.symm
  have hlim := (AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure
    μ _ _).mp hprod
  have hfinal : TendstoInMeasure μ (fun n : ℕ => fun ω => (n : ℝ) • wholeHC0 Z D n ω)
      atTop (fun _ => wholeSandwich μ (Z 0) (D 0) b) := by
    exact TendstoInMeasure.congr' heq' Filter.EventuallyEq.rfl hlim
  exact ((AronowAudit.P001.Wave1.DecideB_cp_iff_tendstoInMeasure
    μ _ _).mpr hfinal) ε hε
