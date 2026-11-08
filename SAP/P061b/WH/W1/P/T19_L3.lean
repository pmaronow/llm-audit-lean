import SAP.P061b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P061b.Bridge

namespace SAP.P061b.WH.W1.P.T19_L3

open Bridge
open scoped BigOperators Classical

noncomputable def cellSchedule {Ω : Type} {N : ℕ} (g : Schedule Ω N) (d : ℝ)
    (i j : Fin N) (a b : ℝ) : Schedule Ω N :=
  fun k z => if g k z = d then if k = i then a else if k = j then b else 0 else 0

noncomputable def statisticAt {Ω : Type} {N : ℕ}
    (T : Ω × (Fin N → ℝ) → ℝ) (g : Schedule Ω N) (d : ℝ)
    (i j : Fin N) (z : Ω) (a b : ℝ) : ℝ :=
  T (z, fun k => cellSchedule g d i j a b k z)

lemma cellSchedule_supportStable {Ω : Type} {N : ℕ}
    (D : AtomicDesign Ω) (g : Schedule Ω N) (d : ℝ) (i j : Fin N)
    (a b : ℝ) : SupportStable D g (cellSchedule g d i j a b) := by
  intro k z w _ _ h
  simp [cellSchedule, h]

lemma observed_eq_when_j_absent {Ω : Type} {N : ℕ}
    (g : Schedule Ω N) (d : ℝ) (i j : Fin N) (z : Ω)
    (a b c : ℝ) (hj : g j z ≠ d) :
    (fun k => cellSchedule g d i j a b k z) =
      (fun k => cellSchedule g d i j a c k z) := by
  funext k
  by_cases hk : g k z = d
  · by_cases hki : k = i
    · subst k
      simp [cellSchedule, hk]
    · by_cases hkj : k = j
      · subst k
        exact (hj hk).elim
      · simp [cellSchedule, hk, hki, hkj]
  · simp [cellSchedule, hk]

lemma observed_eq_when_i_absent {Ω : Type} {N : ℕ}
    (g : Schedule Ω N) (d : ℝ) (i j : Fin N) (z : Ω)
    (a b c : ℝ) (hi : g i z ≠ d) :
    (fun k => cellSchedule g d i j a b k z) =
      (fun k => cellSchedule g d i j c b k z) := by
  funext k
  by_cases hk : g k z = d
  · by_cases hki : k = i
    · subst k
      exact (hi hk).elim
    · by_cases hkj : k = j
      · subst k
        simp [cellSchedule, hk, hki]
      · simp [cellSchedule, hk, hki, hkj]
  · simp [cellSchedule, hk]

lemma statistic_eq_of_observed_eq {Ω : Type} {N : ℕ}
    (T : Ω × (Fin N → ℝ) → ℝ) (g : Schedule Ω N) (d : ℝ)
    (i j : Fin N) (z : Ω) (a b c e : ℝ)
    (h : (fun k => cellSchedule g d i j a b k z) =
      (fun k => cellSchedule g d i j c e k z)) :
    statisticAt T g d i j z a b = statisticAt T g d i j z c e := by
  unfold statisticAt
  rw [h]

lemma exposureMean_cellSchedule_i {Ω : Type} {N : ℕ}
    (D : AtomicDesign Ω) (g : Schedule Ω N) (d : ℝ) (i j : Fin N)
    (a b : ℝ) (hp : 0 < exposureProbability D g i d) :
    exposureMean D g (cellSchedule g d i j a b) i d = a := by
  rw [Bridge.exposure_correspondence]
  have hp' : 0 < AronowAudit.P061.pi (toAudit D) g i d := by
    change 0 < AronowAudit.P061.probability (toAudit D) (fun z => g i z = d)
    rw [← Bridge.probability_correspondence D (fun z => g i z = d)]
    exact hp
  have hc : ∀ z, AronowAudit.P061.Support (toAudit D) z →
      g i z = d → cellSchedule g d i j a b i z = a := by
    intro z hz hgd
    simp [cellSchedule, hgd]
  exact (AronowAudit.P061.constant_cell (toAudit D) g
    (cellSchedule g d i j a b) i d a hp' hc).2.1

lemma exposureMean_cellSchedule_j {Ω : Type} {N : ℕ}
    (D : AtomicDesign Ω) (g : Schedule Ω N) (d : ℝ) (i j : Fin N)
    (a b : ℝ) (hp : 0 < exposureProbability D g j d) (hij : i ≠ j) :
    exposureMean D g (cellSchedule g d i j a b) j d = b := by
  rw [Bridge.exposure_correspondence]
  have hp' : 0 < AronowAudit.P061.pi (toAudit D) g j d := by
    change 0 < AronowAudit.P061.probability (toAudit D) (fun z => g j z = d)
    rw [← Bridge.probability_correspondence D (fun z => g j z = d)]
    exact hp
  have hc : ∀ z, AronowAudit.P061.Support (toAudit D) z →
      g j z = d → cellSchedule g d i j a b j z = b := by
    intro z hz hgd
    simp [cellSchedule, hgd, Ne.symm hij]
  exact (AronowAudit.P061.constant_cell (toAudit D) g
    (cellSchedule g d i j a b) j d b hp' hc).2.1

end SAP.P061b.WH.W1.P.T19_L3

theorem SAP.P061b.WH.W1.T19_L3_proof : SAP.P061b.WH.W1.T19_L3 := by
  intro Ω N D g d i j hpi hpj hijoint
  intro hExists
  rcases hExists with ⟨T, hT⟩
  let v00 := SAP.P061b.WH.W1.P.T19_L3.cellSchedule g d i j 0 0
  let v01 := SAP.P061b.WH.W1.P.T19_L3.cellSchedule g d i j 0 1
  let v10 := SAP.P061b.WH.W1.P.T19_L3.cellSchedule g d i j 1 0
  let v11 := SAP.P061b.WH.W1.P.T19_L3.cellSchedule g d i j 1 1
  let F00 : Ω → ℝ := fun z =>
    SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 0
  let F01 : Ω → ℝ := fun z =>
    SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 1
  let F10 : Ω → ℝ := fun z =>
    SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 0
  let F11 : Ω → ℝ := fun z =>
    SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 1
  have hne : i ≠ j := by
    intro heq
    subst j
    have hzero : exposureProbability D g i d = 0 := by
      simpa [jointExposureProbability, exposureProbability] using hijoint
    exact (ne_of_gt hpi) hzero
  have hji : j ≠ i := Ne.symm hne
  have stable00 : SupportStable D g v00 := by
    simpa [v00] using
      SAP.P061b.WH.W1.P.T19_L3.cellSchedule_supportStable D g d i j 0 0
  have stable01 : SupportStable D g v01 := by
    simpa [v01] using
      SAP.P061b.WH.W1.P.T19_L3.cellSchedule_supportStable D g d i j 0 1
  have stable10 : SupportStable D g v10 := by
    simpa [v10] using
      SAP.P061b.WH.W1.P.T19_L3.cellSchedule_supportStable D g d i j 1 0
  have stable11 : SupportStable D g v11 := by
    simpa [v11] using
      SAP.P061b.WH.W1.P.T19_L3.cellSchedule_supportStable D g d i j 1 1
  have ei00 : exposureMean D g v00 i d = 0 := by
    simpa [v00] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_i D g d i j 0 0 hpi
  have ej00 : exposureMean D g v00 j d = 0 := by
    simpa [v00] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_j D g d i j 0 0 hpj hne
  have ei01 : exposureMean D g v01 i d = 0 := by
    simpa [v01] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_i D g d i j 0 1 hpi
  have ej01 : exposureMean D g v01 j d = 1 := by
    simpa [v01] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_j D g d i j 0 1 hpj hne
  have ei10 : exposureMean D g v10 i d = 1 := by
    simpa [v10] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_i D g d i j 1 0 hpi
  have ej10 : exposureMean D g v10 j d = 0 := by
    simpa [v10] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_j D g d i j 1 0 hpj hne
  have ei11 : exposureMean D g v11 i d = 1 := by
    simpa [v11] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_i D g d i j 1 1 hpi
  have ej11 : exposureMean D g v11 j d = 1 := by
    simpa [v11] using
      SAP.P061b.WH.W1.P.T19_L3.exposureMean_cellSchedule_j D g d i j 1 1 hpj hne
  have h00 := hT v00 stable00
  have h01 := hT v01 stable01
  have h10 := hT v10 stable10
  have h11 := hT v11 stable11
  have hmean00' : designMean D (fun z => T (z, fun k => v00 k z)) = 0 := by
    rw [h00.2, ei00, ej00]
    norm_num
  have hmean01' : designMean D (fun z => T (z, fun k => v01 k z)) = 0 := by
    rw [h01.2, ei01, ej01]
    norm_num
  have hmean10' : designMean D (fun z => T (z, fun k => v10 k z)) = 0 := by
    rw [h10.2, ei10, ej10]
    norm_num
  have hmean11' : designMean D (fun z => T (z, fun k => v11 k z)) = 1 := by
    rw [h11.2, ei11, ej11]
    norm_num
  have hmean00 : designMean D F00 = 0 := by
    simpa [F00, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using hmean00'
  have hmean01 : designMean D F01 = 0 := by
    simpa [F01, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using hmean01'
  have hmean10 : designMean D F10 = 0 := by
    simpa [F10, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using hmean10'
  have hmean11 : designMean D F11 = 1 := by
    simpa [F11, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using hmean11'
  have hF00 : HasFirstMoment D F00 := by
    simpa [F00, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using h00.1
  have hF01 : HasFirstMoment D F01 := by
    simpa [F01, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using h01.1
  have hF10 : HasFirstMoment D F10 := by
    simpa [F10, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using h10.1
  have hF11 : HasFirstMoment D F11 := by
    simpa [F11, SAP.P061b.WH.W1.P.T19_L3.statisticAt] using h11.1
  have hI00 : AronowAudit.P061.Integrable (toAudit D) F00 := by
    exact (Bridge.moment_correspondence D F00).mp hF00
  have hI01 : AronowAudit.P061.Integrable (toAudit D) F01 := by
    exact (Bridge.moment_correspondence D F01).mp hF01
  have hI10 : AronowAudit.P061.Integrable (toAudit D) F10 := by
    exact (Bridge.moment_correspondence D F10).mp hF10
  have hI11 : AronowAudit.P061.Integrable (toAudit D) F11 := by
    exact (Bridge.moment_correspondence D F11).mp hF11
  let G : Ω → ℝ := fun z => F11 z - F10 z
  let H : Ω → ℝ := fun z => F01 z - F00 z
  let M : Ω → ℝ := fun z => G z - H z
  have hIG : AronowAudit.P061.Integrable (toAudit D) G := by
    exact AronowAudit.P061.integrable_sub (toAudit D) hI11 hI10
  have hIH : AronowAudit.P061.Integrable (toAudit D) H := by
    exact AronowAudit.P061.integrable_sub (toAudit D) hI01 hI00
  have hIM : AronowAudit.P061.Integrable (toAudit D) M := by
    exact AronowAudit.P061.integrable_sub (toAudit D) hIG hIH
  have hpoint : ∀ z, InSupport D z → M z = 0 := by
    intro z hz
    have hdisj : ¬ (g i z = d ∧ g j z = d) := by
      intro hex
      have hle : D.p z ≤ jointExposureProbability D g i j d d := by
        change D.p z ≤ AronowAudit.P061.probability (toAudit D)
          (fun w => g i w = d ∧ g j w = d)
        exact AronowAudit.P061.event_atom_le (toAudit D)
          (fun w => g i w = d ∧ g j w = d) z hex
      rw [hijoint] at hle
      exact (not_lt_of_ge hle) hz
    rcases Classical.em (g i z = d) with hi | hi
    · have hj : g j z ≠ d := by
        intro hj
        exact hdisj ⟨hi, hj⟩
      have h1110 :
          SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 1 =
            SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 0 := by
        apply SAP.P061b.WH.W1.P.T19_L3.statistic_eq_of_observed_eq
        exact SAP.P061b.WH.W1.P.T19_L3.observed_eq_when_j_absent
          g d i j z 1 1 0 hj
      have h0100 :
          SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 1 =
            SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 0 := by
        apply SAP.P061b.WH.W1.P.T19_L3.statistic_eq_of_observed_eq
        exact SAP.P061b.WH.W1.P.T19_L3.observed_eq_when_j_absent
          g d i j z 0 1 0 hj
      change (F11 z - F10 z) - (F01 z - F00 z) = 0
      change (SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 1 -
        SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 0) -
        (SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 1 -
        SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 0) = 0
      rw [h1110, h0100]
      ring
    · have h1101 :
          SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 1 =
            SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 1 := by
        apply SAP.P061b.WH.W1.P.T19_L3.statistic_eq_of_observed_eq
        exact SAP.P061b.WH.W1.P.T19_L3.observed_eq_when_i_absent
          g d i j z 1 1 0 hi
      have h1000 :
          SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 0 =
            SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 0 := by
        apply SAP.P061b.WH.W1.P.T19_L3.statistic_eq_of_observed_eq
        exact SAP.P061b.WH.W1.P.T19_L3.observed_eq_when_i_absent
          g d i j z 1 0 0 hi
      change (F11 z - F10 z) - (F01 z - F00 z) = 0
      change (SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 1 -
        SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 1 0) -
        (SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 1 -
        SAP.P061b.WH.W1.P.T19_L3.statisticAt T g d i j z 0 0) = 0
      rw [h1101, h1000]
      ring
  have hmeanM : AronowAudit.P061.expectation (toAudit D) M = 1 := by
    have hE11 : AronowAudit.P061.expectation (toAudit D) F11 = 1 := by
      rw [← Bridge.mean_correspondence D F11]
      exact hmean11
    have hE10 : AronowAudit.P061.expectation (toAudit D) F10 = 0 := by
      rw [← Bridge.mean_correspondence D F10]
      exact hmean10
    have hE01 : AronowAudit.P061.expectation (toAudit D) F01 = 0 := by
      rw [← Bridge.mean_correspondence D F01]
      exact hmean01
    have hE00 : AronowAudit.P061.expectation (toAudit D) F00 = 0 := by
      rw [← Bridge.mean_correspondence D F00]
      exact hmean00
    change AronowAudit.P061.expectation (toAudit D)
      (fun z => (F11 z - F10 z) - (F01 z - F00 z)) = 1
    rw [AronowAudit.P061.expectation_sub (toAudit D) hIG hIH,
      AronowAudit.P061.expectation_sub (toAudit D) hI11 hI10,
      AronowAudit.P061.expectation_sub (toAudit D) hI01 hI00,
      hE11, hE10, hE01, hE00]
    norm_num
  have hsupport := AronowAudit.P061.expectation_support_congr (toAudit D) M
    (fun _ => 0) (by
      intro z hz
      exact hpoint z hz)
  have hzero : AronowAudit.P061.expectation (toAudit D) (fun _ : Ω => 0) = 0 := by
    simp [AronowAudit.P061.expectation]
  have hone : (1 : ℝ) = 0 := by
    calc
      1 = AronowAudit.P061.expectation (toAudit D) M := hmeanM.symm
      _ = AronowAudit.P061.expectation (toAudit D) (fun _ => 0) := hsupport
      _ = 0 := hzero
  exact one_ne_zero hone
