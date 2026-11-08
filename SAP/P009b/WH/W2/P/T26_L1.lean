import SAP.P009b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P009b.WH.W2.P.T26_L1

private theorem incoming_event_eq_own {n : ℕ} (E : SAP.P009b.Experiment n)
    (hNo : SAP.P009b.NoInterference E) (i : Fin n) (z : SAP.P009b.Assignment n) :
    (fun w : SAP.P009b.Assignment n =>
      ∀ j, AronowAudit.P009.Interferes (SAP.P009b.Bridge.toExperiment E) j i →
        w j = z j) = (fun w => w i = z i) := by
  funext w
  apply propext
  constructor
  · intro h
    exact h i (Or.inl rfl)
  · intro h j hj
    have hji : j = i :=
      (AronowAudit.P009.SparseCompletion.noI_interferes
        (SAP.P009b.Bridge.toExperiment E) hNo j i).mp hj
    subst j
    exact h

end SAP.P009b.WH.W2.P.T26_L1

theorem SAP.P009b.WH.W2.T26_L1_proof : SAP.P009b.WH.W2.T26_L1 := by
  intro n hn E k q s hReg hNo
  have hReg' : AronowAudit.P009.Regular (SAP.P009b.Bridge.toExperiment E) k q s := hReg
  have hk : 0 < k := hReg'.1
  have hq : 2 ≤ q := hReg'.2.1
  have hk2 : 2 ≤ k := AronowAudit.P009.BernoulliCompletion.regular_k_ge_two
    hn (SAP.P009b.Bridge.toExperiment E) k q s hReg'
  constructor
  · intro i z
    let E' := SAP.P009b.Bridge.toExperiment E
    have hprob : k⁻¹ ≤ AronowAudit.P009.marginal E' i (z i) :=
      (AronowAudit.P009.BernoulliCompletion.regular_marginal_bounds E' k q s
        hReg' i (z i)).1
    have hevent := SAP.P009b.WH.W2.P.T26_L1.incoming_event_eq_own E hNo i z
    have heventProb : AronowAudit.P009.prob E'.design
        (fun w => ∀ j, AronowAudit.P009.Interferes E' j i → w j = z j) =
        AronowAudit.P009.marginal E' i (z i) := by
      change AronowAudit.P009.prob E'.design
          (fun w => ∀ j, AronowAudit.P009.Interferes E' j i → w j = z j) =
        AronowAudit.P009.prob E'.design (fun w => w i = z i)
      rw [hevent]
    have hprob' : k⁻¹ ≤ AronowAudit.P009.prob E'.design
        (fun w => ∀ j, AronowAudit.P009.Interferes E' j i → w j = z j) := by
      calc
        k⁻¹ ≤ AronowAudit.P009.marginal E' i (z i) := hprob
        _ = AronowAudit.P009.prob E'.design
            (fun w => ∀ j, AronowAudit.P009.Interferes E' j i → w j = z j) := heventProb.symm
    have hmean : AronowAudit.P009.mean E'.design
        (fun w => Real.rpow |E'.outcome i w| q) ≤ Real.rpow k q := hReg'.2.2.2.2.1 i
    have hAtom := AronowAudit.P009.OutcomeCompletion.moment_atom_lower E' i z q
    have hAtom' : AronowAudit.P009.prob E'.design
        (fun w => ∀ j, AronowAudit.P009.Interferes E' j i → w j = z j) *
          Real.rpow |E'.outcome i z| q ≤ AronowAudit.P009.mean E'.design
            (fun w => Real.rpow |E'.outcome i w| q) := by
      simpa only [Real.rpow_eq_pow] using hAtom
    have hval : 0 ≤ Real.rpow |E'.outcome i z| q := Real.rpow_nonneg (abs_nonneg _) _
    have hLower : k⁻¹ * Real.rpow |E'.outcome i z| q ≤ Real.rpow k q := by
      calc
        k⁻¹ * Real.rpow |E'.outcome i z| q ≤
            AronowAudit.P009.prob E'.design
              (fun w => ∀ j, AronowAudit.P009.Interferes E' j i → w j = z j) *
                Real.rpow |E'.outcome i z| q :=
          mul_le_mul_of_nonneg_right hprob' hval
        _ ≤ AronowAudit.P009.mean E'.design
            (fun w => Real.rpow |E'.outcome i w| q) := hAtom'
        _ ≤ Real.rpow k q := hmean
    have hPow : Real.rpow |E'.outcome i z| q ≤ Real.rpow k (q + 1) := by
      have hmul : k⁻¹ * Real.rpow |E'.outcome i z| q ≤ Real.rpow k q := hLower
      calc
        Real.rpow |E'.outcome i z| q = k * (k⁻¹ * Real.rpow |E'.outcome i z| q) := by
          rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
        _ ≤ k * Real.rpow k q := mul_le_mul_of_nonneg_left hmul hk.le
        _ = Real.rpow k (q + 1) := by
          calc
            k * Real.rpow k q = Real.rpow k 1 * Real.rpow k q := by
              congr 1
              exact (Real.rpow_one k).symm
            _ = Real.rpow k (1 + q) := (Real.rpow_add hk 1 q).symm
            _ = Real.rpow k (q + 1) := by congr 1; ring
    have hbound : |E'.outcome i z| ≤ Real.rpow k (1 + 1 / q) := by
      have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
      apply (Real.rpow_le_rpow_iff (abs_nonneg _) (Real.rpow_nonneg hk.le _) hqpos).mp
      rw [← Real.rpow_mul hk.le]
      have hex : (1 + 1 / q) * q = q + 1 := by field_simp [hqpos.ne']
      rw [hex]
      exact hPow
    change |E.outcome i z| ≤ Real.rpow k (1 + 1 / q) at hbound
    exact hbound
  · have hexp : 1 + 1 / q ≤ (3 : ℝ) / 2 := by
      have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
      have hrecip : 1 / q ≤ (1 : ℝ) / 2 :=
        (div_le_div_iff₀ hqpos (by norm_num)).2 (by norm_num; linarith)
      linarith
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hexp

