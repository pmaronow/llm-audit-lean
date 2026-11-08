import SAP.P025b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P025b.WH.W1.P.T14_L1

private theorem selected_denominator (h : ℕ)
    (ω : ℕ → Fin 2 × Fin 2 × Fin 2)
    (w : Fin h × (Fin 3 × Fin 2) → ℝ) :
    (∑ rj : Fin h × Fin 3,
      w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2))) =
      pairClassWeightSum h ω w 0 + pairClassWeightSum h ω w 1 +
        pairClassWeightSum h ω w 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, Finset.sum_add_distrib, pairClassWeightSum]

private theorem selected_numerator (h : ℕ)
    (ω : ℕ → Fin 2 × Fin 2 × Fin 2)
    (w : Fin h × (Fin 3 × Fin 2) → ℝ) :
    (∑ rj : Fin h × Fin 3,
      w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2)) *
        threeOutcomes rj.2) =
      2 * pairClassWeightSum h ω w 1 +
        3 * pairClassWeightSum h ω w 2 := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_three, threeOutcomes, Finset.sum_add_distrib,
    Finset.mul_sum, mul_comm, pairClassWeightSum]

end SAP.P025b.WH.W1.P.T14_L1

theorem SAP.P025b.WH.W1.T14_L1_proof : SAP.P025b.WH.W1.T14_L1 := by
  intro h hh ω w hw
  let A := SAP.P025b.pairClassWeightSum h ω w
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hwBounds (r : Fin h) (j : Fin 3) :
      2 ≤ w (r, (j, pairChoice (ω r.val) j)) ∧
      w (r, (j, pairChoice (ω r.val) j)) ≤ 4 := by
    have hwr := hw (r, (j, pairChoice (ω r.val) j))
    norm_num at hwr ⊢
    exact hwr
  have hA : ∀ j : Fin 3, 2 * (h : ℝ) ≤ A j ∧ A j ≤ 4 * (h : ℝ) := by
    intro j
    constructor
    · calc
        2 * (h : ℝ) = ∑ _r : Fin h, (2 : ℝ) := by simp [mul_comm]
        _ ≤ ∑ r : Fin h, w (r, (j, pairChoice (ω r.val) j)) :=
          Finset.sum_le_sum fun r _ => (hwBounds r j).1
    · calc
        A j = ∑ r : Fin h, w (r, (j, pairChoice (ω r.val) j)) := rfl
        _ ≤ ∑ _r : Fin h, (4 : ℝ) :=
          Finset.sum_le_sum fun r _ => (hwBounds r j).2
        _ = 4 * (h : ℝ) := by simp [mul_comm]
  have hpos : 0 < A 0 + A 1 + A 2 := by
    have h0 := (hA 0).1
    have h1 := (hA 1).1
    have h2 := (hA 2).1
    linarith
  have hden : (∑ rj : Fin h × Fin 3,
      w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2))) =
      A 0 + A 1 + A 2 := by
    simpa [A] using
      SAP.P025b.WH.W1.P.T14_L1.selected_denominator h ω w
  have hnum : (∑ rj : Fin h × Fin 3,
      w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2)) *
        threeOutcomes rj.2) = 2 * A 1 + 3 * A 2 := by
    simpa [A] using
      SAP.P025b.WH.W1.P.T14_L1.selected_numerator h ω w
  have hclass : ratio threeOutcomes (fun _ => 1) A =
      (2 * A 1 + 3 * A 2) / (A 0 + A 1 + A 2) := by
    norm_num [ratio, threeOutcomes, Fin.sum_univ_three]
    ring
  have hratio : ratio (fun ri => threeOutcomes ri.2.1)
      (pooledIndicator pairDesign h ω) w =
      (2 * A 1 + 3 * A 2) / (A 0 + A 1 + A 2) := by
    have hp := AronowAudit.P025.pair_pooled_ratio h ω w
    rw [← SAP.P025b.Bridge.ratio_eq, ← SAP.P025b.Bridge.threeOutcomes_eq,
      ← SAP.P025b.Bridge.pairChoice_eq, ← SAP.P025b.Bridge.pairDesign_eq,
      ← SAP.P025b.Bridge.pooledIndicator_eq] at hp
    rw [hp]
    change (∑ rj : Fin h × Fin 3,
      (1 : ℝ) * w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2)) *
        threeOutcomes rj.2) /
        (∑ rj : Fin h × Fin 3,
          (1 : ℝ) * w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2))) = _
    have hnum' : (∑ rj : Fin h × Fin 3,
        (1 : ℝ) * w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2)) *
          threeOutcomes rj.2) = 2 * A 1 + 3 * A 2 := by
      simpa [mul_assoc] using hnum
    have hden' : (∑ rj : Fin h × Fin 3,
        (1 : ℝ) * w (rj.1, (rj.2, pairChoice (ω rj.1.val) rj.2))) =
          A 0 + A 1 + A 2 := by simpa using hden
    rw [hnum', hden']
  have hscale : ratio threeOutcomes (fun _ => 1) A =
      ratio threeOutcomes (fun _ => 1) (fun j => A j / (h : ℝ)) := by
    have hc : (1 / (h : ℝ)) ≠ 0 := one_div_ne_zero hhR.ne'
    have hscale' := (AronowAudit.P025.ratio_scale_weights
      threeOutcomes (fun _ => 1) A (1 / (h : ℝ)) hc).symm
    have hweights : (fun j => (1 / (h : ℝ)) * A j) = fun j => A j / (h : ℝ) := by
      funext j
      simp [div_eq_mul_inv, mul_comm]
    simpa only [← SAP.P025b.Bridge.ratio_eq, hweights] using hscale'
  change (∀ j : Fin 3, 2 * (h : ℝ) ≤ A j ∧ A j ≤ 4 * (h : ℝ)) ∧
      0 < A 0 + A 1 + A 2 ∧
      ratio (fun ri => threeOutcomes ri.2.1) (pooledIndicator pairDesign h ω) w =
        (2 * A 1 + 3 * A 2) / (A 0 + A 1 + A 2) ∧
      ((2 * A 1 + 3 * A 2) / (A 0 + A 1 + A 2) =
        ratio threeOutcomes (fun _ => 1) (fun j => A j / (h : ℝ)) ∧
        weightBox (1/4) (1/2) (fun j => A j / (h : ℝ)))
  refine ⟨hA, hpos, hratio, ?_, ?_⟩
  · calc
      (2 * A 1 + 3 * A 2) / (A 0 + A 1 + A 2) =
          ratio threeOutcomes (fun _ => 1) A := hclass.symm
      _ = ratio threeOutcomes (fun _ => 1) (fun j => A j / (h : ℝ)) := hscale
  · intro j
    constructor
    · norm_num
      apply (le_div_iff₀ hhR).2
      exact (hA j).1
    · norm_num
      apply (div_le_iff₀ hhR).2
      exact (hA j).2
