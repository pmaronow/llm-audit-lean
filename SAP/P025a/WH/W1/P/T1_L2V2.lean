import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

theorem SAP.P025a.WH.W1.T1_L2V2_proof : SAP.P025a.WH.W1.T1_L2V2 := by
  intro n hn y hy γ hγ
  have hmean :
      SAP.P025a.populationMean y - y ⟨0, hn⟩ =
        (∑ i : Fin n, (y i - y ⟨0, hn⟩)) / n := by
    simp [SAP.P025a.populationMean, Finset.sum_sub_distrib]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  have hsign : 0 ≤ (∑ i : Fin n, (y i - y ⟨0, hn⟩)) / n := by
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      exact sub_nonneg.mpr (hy (Nat.zero_le i.val))
    · exact_mod_cast hn.le
  have hγpos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hzero :
      AronowAudit.P025.ratio y (fun _ => 1)
          (AronowAudit.P025.threshold γ 1 0) =
        AronowAudit.P025.populationMean y := by
    simp [AronowAudit.P025.ratio, AronowAudit.P025.threshold,
      AronowAudit.P025.populationMean]
  have hden :
      (∑ i : Fin n, (1 : ℝ) * AronowAudit.P025.threshold γ 1 1 i) =
        (n : ℝ) + (γ - 1) := by
    have hu := AronowAudit.P025.threshold_den_update
      (fun _ : Fin n => (1 : ℝ)) γ 1 ⟨0, hn⟩
    have hu' :
        (∑ i : Fin n, (1 : ℝ) * AronowAudit.P025.threshold γ 1 1 i) =
          (∑ i : Fin n, (1 : ℝ) * AronowAudit.P025.threshold γ 1 0 i) +
            (γ - 1) := by
      simpa using hu
    have hbase :
        (∑ i : Fin n, (1 : ℝ) * AronowAudit.P025.threshold γ 1 0 i) =
          (n : ℝ) := by
      simp [AronowAudit.P025.threshold]
    rw [hbase] at hu'
    exact hu'
  have hinc := AronowAudit.P025.threshold_increment hn
    (fun _ : Fin n => (1 : ℝ)) y (by intro i; norm_num)
    γ 1 hγpos zero_lt_one ⟨0, hn⟩
  refine ⟨hmean, hsign, ?_⟩
  calc
    SAP.P025a.lowerValue y (fun _ => 1) γ 1 - SAP.P025a.populationMean y =
        AronowAudit.P025.ratio y (fun _ => 1)
            (AronowAudit.P025.threshold γ 1 1) -
          AronowAudit.P025.ratio y (fun _ => 1)
            (AronowAudit.P025.threshold γ 1 0) := by
      change SAP.P025a.ratio y (fun _ => 1)
          (SAP.P025a.lowerWeights γ 1) - SAP.P025a.populationMean y = _
      rw [SAP.P025a.Bridge.ratio_eq, SAP.P025a.Bridge.populationMean_eq,
        ← SAP.P025a.Bridge.threshold_lower]
      rw [← hzero]
    _ = (γ - 1) * 1 *
          (y ⟨0, hn⟩ - AronowAudit.P025.ratio y (fun _ => 1)
            (AronowAudit.P025.threshold γ 1 0)) /
          (∑ i : Fin n, (1 : ℝ) * AronowAudit.P025.threshold γ 1 1 i) := hinc
    _ = (γ - 1) * (y ⟨0, hn⟩ - SAP.P025a.populationMean y) /
          ((n : ℝ) + (γ - 1)) := by
      rw [hzero, hden]
      rw [← SAP.P025a.Bridge.populationMean_eq]
      ring
