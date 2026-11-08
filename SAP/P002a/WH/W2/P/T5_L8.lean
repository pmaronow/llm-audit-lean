import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T5_L8

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

lemma uniform_margin (h6 : SAP.P002a.WH.W2.T5_L6)
    (h7 : SAP.P002a.WH.W2.T5_L7)
    (k : ℕ) (δ e A B r α : ℝ) (hk : 0 < k) (hδ : δ < -1)
    (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hα : 0 < α ∧ α < 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < α ∧
      ∀ᶠ n in atTop, ∀ P : AronowAudit.P002.CovPopulation n k,
        AronowAudit.P002.Xi P δ e A B r →
          1-α+γ ≤ AronowAudit.P002.adjustedCoverage P
            (AronowAudit.P002.late P.pop) α := by
  obtain ⟨γ, hγ, hγα, h7seq⟩ :=
    h7 k δ e A B r α hk (by linarith [hδ]) he hA hB hr hα
  let x : ℝ := 1-α+γ
  have hxlt : x < 1 := by dsimp [x]; linarith
  have hpositiveSeq : ∀ (sizes : ℕ → ℕ), StrictMono sizes →
      ∀ P : ∀ j, AronowAudit.P002.CovPopulation (sizes j) k,
        (∀ j, AronowAudit.P002.Xi (P j) δ e A B r ∧
          0 < AronowAudit.P002.popVar
            (AronowAudit.P002.residual (P j) true (AronowAudit.P002.late (P j).pop)) +
          AronowAudit.P002.popVar
            (AronowAudit.P002.residual (P j) false (AronowAudit.P002.late (P j).pop))) →
        ∀ᶠ j in atTop, x ≤ AronowAudit.P002.adjustedCoverage (P j)
          (AronowAudit.P002.late (P j).pop) α := by
    intro sizes hsizes P hH
    let R : ∀ j, SAP.P002a.CovPopulation (sizes j) k :=
      fun j => SAP.P002a.Bridge.fromCovPopulation (P j)
    have hXiR (j : ℕ) : SAP.P002a.Xi (R j) δ e A B r := by
      dsimp [R]
      simpa only [SAP.P002a.Bridge.xi_eq,
        SAP.P002a.Bridge.project_covPopulation_roundtrip] using (hH j).1
    have hvarR (j : ℕ) :
        0 < SAP.P002a.popVar
            (SAP.P002a.residual (R j) true (SAP.P002a.late (R j).pop)) +
          SAP.P002a.popVar
            (SAP.P002a.residual (R j) false (SAP.P002a.late (R j).pop)) := by
      dsimp [R]
      simpa only [SAP.P002a.Bridge.popVar_eq, SAP.P002a.Bridge.residual_eq,
        SAP.P002a.Bridge.late_eq, SAP.P002a.Bridge.project_covPopulation_roundtrip,
        SAP.P002a.Bridge.fromCovPopulation, SAP.P002a.Bridge.fromPopulation,
        SAP.P002a.Bridge.toPopulation, SAP.P002a.Bridge.toCovPopulation] using
        (hH j).2
    have hratio (j : ℕ) := (h6 (R j) δ e A B r hδ he hr (hXiR j)).2
    have hseq := h7seq sizes hsizes R hXiR hvarR hratio
    filter_upwards [hseq] with j hj
    simpa only [x, R, SAP.P002a.Bridge.adjustedCoverage_eq, SAP.P002a.Bridge.late_eq,
      SAP.P002a.Bridge.project_covPopulation_roundtrip,
      SAP.P002a.Bridge.fromCovPopulation, SAP.P002a.Bridge.fromPopulation,
      SAP.P002a.Bridge.toPopulation, SAP.P002a.Bridge.toCovPopulation] using hj
  have hp := AronowAudit.P002.Wave1.T2C_U_uniform_eventual
    (fun n (P : AronowAudit.P002.CovPopulation n k) =>
      AronowAudit.P002.Xi P δ e A B r ∧
        0 < AronowAudit.P002.popVar
            (AronowAudit.P002.residual P true (AronowAudit.P002.late P.pop)) +
          AronowAudit.P002.popVar
            (AronowAudit.P002.residual P false (AronowAudit.P002.late P.pop)))
    (fun n (P : AronowAudit.P002.CovPopulation n k) =>
      x ≤ AronowAudit.P002.adjustedCoverage P (AronowAudit.P002.late P.pop) α)
    (by
      intro sizes hsizes P hH
      exact hpositiveSeq sizes hsizes P hH)
  have hzeroSeq : ∀ (sizes : ℕ → ℕ), StrictMono sizes →
      ∀ P : ∀ j, AronowAudit.P002.CovPopulation (sizes j) k,
        (∀ j, AronowAudit.P002.Xi (P j) δ e A B r ∧
          AronowAudit.P002.Wave1.T2C_totalH (P j) = 0) →
        ∀ᶠ j in atTop, x ≤ AronowAudit.P002.adjustedCoverage (P j)
          (AronowAudit.P002.late (P j).pop) α := by
    intro sizes hsizes P hH
    have hP (j : ℕ) := (hH j).1
    have hzero (j : ℕ) := (hH j).2
    have hcov := AronowAudit.P002.Wave1.T2C_zero_coverage_seq sizes hsizes k P
      δ e A B r α he hr.1 hP hzero x hxlt
    exact hcov.mono (fun _ hj => hj.le)
  have hz := AronowAudit.P002.Wave1.T2C_U_uniform_eventual
    (fun n (P : AronowAudit.P002.CovPopulation n k) =>
      AronowAudit.P002.Xi P δ e A B r ∧ AronowAudit.P002.Wave1.T2C_totalH P = 0)
    (fun n (P : AronowAudit.P002.CovPopulation n k) =>
      x ≤ AronowAudit.P002.adjustedCoverage P (AronowAudit.P002.late P.pop) α)
    (by
      intro sizes hsizes P hH
      exact hzeroSeq sizes hsizes P hH)
  refine ⟨γ, hγ, hγα, ?_⟩
  filter_upwards [hp, hz] with n hp hz P hP
  by_cases hH : 0 < AronowAudit.P002.Wave1.T2C_totalH P
  · have hvar : 0 < AronowAudit.P002.popVar
          (AronowAudit.P002.residual P true (AronowAudit.P002.late P.pop)) +
        AronowAudit.P002.popVar
          (AronowAudit.P002.residual P false (AronowAudit.P002.late P.pop)) := by
      have hsecond (a : Bool) :
          AronowAudit.P002.Wave1.T2C_residualH P a ≤
            AronowAudit.P002.popVar (AronowAudit.P002.residual P a
              (AronowAudit.P002.late P.pop)) :=
        AronowAudit.P002.Wave1.T2C_second_le_popVar hP.1.1 _
          (AronowAudit.P002.Wave1.T2C_residual_centered P.x _
            (AronowAudit.P002.Wave1.T2C_Xi_residual_score P δ e A B r he hP a))
      change 0 < AronowAudit.P002.Wave1.T2C_residualH P true +
        AronowAudit.P002.Wave1.T2C_residualH P false at hH
      have hvsum : AronowAudit.P002.Wave1.T2C_residualH P true +
          AronowAudit.P002.Wave1.T2C_residualH P false ≤
          AronowAudit.P002.popVar
              (AronowAudit.P002.residual P true (AronowAudit.P002.late P.pop)) +
            AronowAudit.P002.popVar
              (AronowAudit.P002.residual P false (AronowAudit.P002.late P.pop)) := by
        linarith [hsecond true, hsecond false]
      exact lt_of_lt_of_le hH hvsum
    exact hp P ⟨hP, hvar⟩
  · have hnonneg : 0 ≤ AronowAudit.P002.Wave1.T2C_totalH P :=
      add_nonneg (AronowAudit.P002.Wave1.T2C_residualH_nonneg P true)
        (AronowAudit.P002.Wave1.T2C_residualH_nonneg P false)
    have hzero : AronowAudit.P002.Wave1.T2C_totalH P = 0 :=
      le_antisymm (le_of_not_gt hH) hnonneg
    exact hz P ⟨hP, hzero⟩

end
end SAP.P002a.WH.W2.P.T5_L8

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

theorem SAP.P002a.WH.W2.T5_L8_proof : SAP.P002a.WH.W2.T5_L8 := by
  intro h6 h7 k δ e A B r α hk hδ he hA hB hr hα hlim
  by_contra hδbound
  have hδneg : δ < -1 := by linarith
  obtain ⟨γ, hγ, hγα, hu⟩ :=
    SAP.P002a.WH.W2.P.T5_L8.uniform_margin h6 h7 k δ e A B r α hk hδneg he hA hB hr hα
  let x : ℝ := 1-α+γ
  let f : ℕ → ℝ≥0∞ := fun n => SAP.P002a.infCoverageXi n k δ e A B r α
  let F : Filter ℕ := atTop ⊓ Filter.principal (SAP.P002a.xiSizes k δ e A B r)
  have hFbot : F ≠ ⊥ := by
    intro hbot
    have hlim' : Filter.liminf f F = ENNReal.ofReal (1-α) := hlim
    rw [hbot, Filter.liminf_bot] at hlim'
    exact ENNReal.ofReal_ne_top hlim'.symm
  haveI : F.NeBot := Filter.neBot_iff.mpr hFbot
  have huSAP : ∀ᶠ n in atTop, ∀ P : SAP.P002a.CovPopulation n k,
      SAP.P002a.Xi P δ e A B r →
        x ≤ SAP.P002a.adjustedCoverage P (SAP.P002a.late P.pop) α := by
    filter_upwards [hu] with n hn P hP
    have hcov := hn (SAP.P002a.Bridge.toCovPopulation P)
      ((SAP.P002a.Bridge.xi_eq P δ e A B r).mp hP)
    simpa only [x, SAP.P002a.Bridge.adjustedCoverage_eq,
      SAP.P002a.Bridge.late_eq, SAP.P002a.Bridge.toCovPopulation,
      SAP.P002a.Bridge.toPopulation] using hcov
  have hEventual : ∀ᶠ n in F, ENNReal.ofReal x ≤ f n := by
    apply eventually_inf_principal.mpr
    filter_upwards [huSAP] with n hn hmem
    have hb : ENNReal.ofReal x ≤ SAP.P002a.infCoverageXi n k δ e A B r α := by
      unfold SAP.P002a.infCoverageXi
      refine le_iInf fun β => le_iInf fun P => ?_
      apply ENNReal.ofReal_le_ofReal
      simpa only [P.property.2] using hn P.val P.property.1
    exact hb
  have hlow : ENNReal.ofReal x ≤ Filter.liminf f F := by
    apply (le_liminf_iff).mpr
    intro y hy
    filter_upwards [hEventual] with n hn
    exact lt_of_lt_of_le hy hn
  have hxpos : 0 < x := by dsimp [x]; linarith [hα.2, hγ]
  have hstrict : ENNReal.ofReal (1-α) < ENNReal.ofReal x := by
    exact (ENNReal.ofReal_lt_ofReal_iff hxpos).2 (by dsimp [x]; linarith [hγ])
  rw [hlim] at hlow
  exact (not_lt_of_ge hlow) hstrict

