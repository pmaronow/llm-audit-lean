import SAP.P011b.WH.W2.Leaves
import AronowAudit.P011.Wave1.Gap.GLP011B5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

theorem SAP.P011b.WH.W2.T16_L1_proof : SAP.P011b.WH.W2.T16_L1 := by
  intro F c1 c2 c3 c4 hscale p D b hp hpn hrank hmean hreg
  obtain ⟨_, _, _, _, _, hdep, _, hdegree, _, _⟩ := hscale
  obtain ⟨Bx, By, lam, hBx, hBy, hlam, hx, hy, hG⟩ := hreg
  let F' : AronowAudit.P011.Family := SAP.P011b.Bridge.toFamily F
  let S : ∀ k, (Fin (F.size k) → ℝ) → ℝ := fun k y =>
    AronowAudit.P011.l2
      (AronowAudit.P011.Wave1.olsr_score (D k) (b k) y) /
        Real.sqrt (F'.size k : ℝ)
  let T : ∀ k, (Fin (F.size k) → ℝ) → ℝ := fun k y =>
    Real.sqrt (F'.size k : ℝ) *
      AronowAudit.P011.l2
        (AronowAudit.P011.ols (D k) y - b k)
  have hm (k : ℕ) :
      Integrable (fun y => (S k y)^2) (F'.model k).law ∧
        (∫ y, (S k y)^2 ∂(F'.model k).law) ≤
          (p : ℝ) * (c2 + 1) * (2 * Bx * By)^2 := by
    have hmean' : AronowAudit.P011.MeanModel (F'.model k) (D k) (b k) := by
      change (∀ i, Integrable (fun y => y i) (F'.model k).law) ∧
        ∀ i, AronowAudit.P011.expectation (F'.model k) (fun y => y i) = (D k *ᵥ b k) i
      exact hmean k
    have hdep' : AronowAudit.P011.Dependency (F'.model k) := by
      change AronowAudit.P011.VariableDependency (F'.model k).law
        (F'.model k).G (fun i y => y i)
      exact hdep k
    have hx' : ∀ i, AronowAudit.P011.l2 (D k i) ≤ Bx := by
      intro i
      exact hx k i
    have hy' : ∀ᵐ y ∂(F'.model k).law, ∀ i, |y i| ≤ By := hy k
    have hd' : ∀ i, (AronowAudit.P011.degree (F'.model k).G i : ℝ) + 1 ≤ c2 + 1 := by
      intro i
      have hi := hdegree k i
      change (SAP.P011b.degree (F.model k).G i : ℝ) + 1 ≤ c2 + 1
      linarith
    have hscore := AronowAudit.P011.Wave1.olsr_score_norm_moment
      (F.positive k) (F'.model k) (D k) (b k) hmean' hdep'
      Bx By (c2 + 1) hBx hBy hx' hy' hd'
    change Integrable (fun y : Fin (F.size k) → ℝ =>
        (AronowAudit.P011.l2
          (AronowAudit.P011.Wave1.olsr_score (D k) (b k) y) /
          Real.sqrt (F.size k : ℝ))^2) ((SAP.P011b.Bridge.toFamily F).model k).law ∧
      (∫ y : Fin (F.size k) → ℝ,
        (AronowAudit.P011.l2
          (AronowAudit.P011.Wave1.olsr_score (D k) (b k) y) /
          Real.sqrt (F.size k : ℝ))^2 ∂((SAP.P011b.Bridge.toFamily F).model k).law) ≤
        (p : ℝ) * (c2 + 1) * (2 * Bx * By)^2
    exact hscore
  have hS : AronowAudit.P011.Tight F' S :=
    AronowAudit.P011.Wave1.olsr_tight_of_moment F' S
      ((p : ℝ) * (c2 + 1) * (2 * Bx * By)^2) (by positivity)
      (fun k => (hm k).1) (fun k => (hm k).2)
  have hdom : ∀ k, ∀ᵐ y ∂(F'.model k).law,
      |T k y| ≤ (1 / lam) * |S k y| := by
    intro k
    filter_upwards [] with y
    have hnR : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
    have hsqrt : 0 < Real.sqrt (F.size k : ℝ) := Real.sqrt_pos.mpr hnR
    dsimp [T, S]
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (AronowAudit.P011.DenseCompletion.l2_nonneg _)),
      abs_of_nonneg (div_nonneg (AronowAudit.P011.DenseCompletion.l2_nonneg _) (Real.sqrt_nonneg _))]
    calc
      _ ≤ Real.sqrt (F'.size k : ℝ) *
          (AronowAudit.P011.l2
            (AronowAudit.P011.Wave1.olsr_score (D k) (b k) y) /
            ((F.size k : ℝ) * lam)) :=
        mul_le_mul_of_nonneg_left
          (AronowAudit.P011.Wave1.olsr_error_bound (F.positive k) (D k) (hrank k)
            (b k) lam hlam (hG k) y)
          (Real.sqrt_nonneg _)
      _ = (1 / lam) * S k y := by
        dsimp [S, F', SAP.P011b.Bridge.toFamily]
        field_simp
        rw [Real.sq_sqrt hnR.le]
        ring
  have hT : AronowAudit.P011.Tight F' T :=
    AronowAudit.P011.Wave1.rrn_tight_dominated F' S T (1 / lam) (by positivity) hS hdom
  change AronowAudit.P011.Tight F' T
  exact hT
