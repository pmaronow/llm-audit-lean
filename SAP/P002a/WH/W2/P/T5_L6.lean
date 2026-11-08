import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T5_L6
noncomputable section
open scoped BigOperators
open SAP.P002a.Bridge

lemma popVar_nonneg {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    0 ≤ popVar q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold popVar
  apply div_nonneg
  · exact Finset.sum_nonneg fun i hi => sq_nonneg _
  · linarith

lemma popCov_le_sqrt_mul {n : ℕ} (hn : 2 ≤ n) (q t : Fin n → ℝ) :
    popCov q t ≤ Real.sqrt (popVar q) * Real.sqrt (popVar t) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 1 := by linarith
  have hdenNe : (n : ℝ) - 1 ≠ 0 := ne_of_gt hden
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => q i - mean q) (fun i => t i - mean t)
  have hcsVar : popCov q t ^ 2 ≤ popVar q * popVar t := by
    unfold popCov popVar
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hden)).2
    field_simp [hdenNe]
    nlinarith
  have hq : 0 ≤ popVar q := popVar_nonneg hn q
  have ht : 0 ≤ popVar t := popVar_nonneg hn t
  have hp : 0 ≤ Real.sqrt (popVar q) * Real.sqrt (popVar t) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs : |popCov q t| ^ 2 ≤
      (Real.sqrt (popVar q) * Real.sqrt (popVar t)) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt ht]
    exact hcsVar
  have habs : |popCov q t| ≤ Real.sqrt (popVar q) * Real.sqrt (popVar t) :=
    (sq_le_sq₀ (abs_nonneg _) hp).mp hs
  exact (le_abs_self _).trans habs

lemma popVar_sub_identity {n : ℕ} (u v : Fin n → ℝ) :
    popVar (fun i => u i - v i) = popVar u + popVar v - 2 * popCov u v := by
  have hm : mean (fun i => u i-v i) = mean u-mean v := by
    unfold mean
    simp only [Finset.sum_sub_distrib, sub_div]
  have hp (i : Fin n) :
      (u i-v i-(mean u-mean v))^2 =
        (u i-mean u)^2+(v i-mean v)^2-2*((u i-mean u)*(v i-mean v)) := by
    ring
  unfold popVar
  rw [hm]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, popCov]
  ring

lemma designVariance_congr {n : ℕ} (P : Population n)
    {f g : Finset (Fin n) → ℝ}
    (hfg : ∀ S ∈ assignments P, f S = g S) :
    designVariance P f = designVariance P g := by
  have he : expectation P f = expectation P g := by
    unfold expectation
    congr 1
    exact Finset.sum_congr rfl hfg
  unfold designVariance
  rw [he]
  unfold expectation
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  change (f S - expectation P g)^2 = (g S - expectation P g)^2
  rw [hfg S hS]

end

end SAP.P002a.WH.W2.P.T5_L6

open SAP.P002a.Bridge
open SAP.P002a.WH.W2.P.T5_L6

theorem SAP.P002a.WH.W2.T5_L6_proof : SAP.P002a.WH.W2.T5_L6 := by
  intro n k P δ e A B r hδ he hr hXi
  rcases hXi with ⟨hD, hm, hc, hlo, hhi, hcov, hfour, hx, hx4, hRayleigh⟩
  let u : Fin n → ℝ := residual P true (late P.pop)
  let v : Fin n → ℝ := residual P false (late P.pop)
  let V1 : ℝ := popVar u
  let V0 : ℝ := popVar v
  have hn : 2 ≤ n := hD.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ht : (0 : ℝ) < (P.pop.n1 : ℝ) := by exact_mod_cast hD.2.1
  have hcpos : 0 < controlSize P.pop := by
    unfold controlSize
    exact sub_pos.mpr (by exact_mod_cast hD.2.2)
  have hNsum : (n : ℝ) = controlSize P.pop + (P.pop.n1 : ℝ) := by
    unfold controlSize
    ring
  have hV1 : 0 ≤ V1 := by dsimp [V1]; exact popVar_nonneg hn u
  have hV0 : 0 ≤ V0 := by dsimp [V0]; exact popVar_nonneg hn v
  have hcovUpper : popCov u v ≤ Real.sqrt V1 * Real.sqrt V0 := by
    dsimp [V1, V0]
    exact popCov_le_sqrt_mul hn u v
  have hprodNonneg : 0 ≤ Real.sqrt V1 * Real.sqrt V0 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hXiCov : (-δ) * (Real.sqrt V1 * Real.sqrt V0) ≤ popCov u v := by
    change -δ * Real.sqrt (popVar u) * Real.sqrt (popVar v) ≤ popCov u v at hcov
    dsimp [V1, V0]
    nlinarith [hcov]
  have hprodZero : Real.sqrt V1 * Real.sqrt V0 = 0 := by
    by_contra hne
    have hpos : 0 < Real.sqrt V1 * Real.sqrt V0 :=
      lt_of_le_of_ne hprodNonneg (Ne.symm hne)
    have hcoef : 1 < -δ := by linarith
    have hstrict : Real.sqrt V1 * Real.sqrt V0 <
        (-δ) * (Real.sqrt V1 * Real.sqrt V0) := by
      nlinarith [mul_pos (sub_pos.mpr hcoef) hpos]
    linarith
  have hVzero : V1 = 0 ∨ V0 = 0 := by
    rcases mul_eq_zero.mp hprodZero with hz | hz
    · left
      have hs := Real.sq_sqrt hV1
      rw [hz] at hs
      dsimp [V1]
      nlinarith
    · right
      have hs := Real.sq_sqrt hV0
      rw [hz] at hs
      dsimp [V0]
      nlinarith
  have hVprod : V1 * V0 = 0 := by
    rcases hVzero with h | h
    · rw [h]
      ring
    · rw [h]
      ring
  have hcovZero : popCov u v = 0 := by
    rw [hprodZero] at hXiCov hcovUpper
    simp only [mul_zero, zero_mul] at hXiCov hcovUpper
    exact le_antisymm hcovUpper hXiCov

  have hXiProj : AronowAudit.P002.Xi (toCovPopulation P) δ e A B r :=
    (SAP.P002a.Bridge.xi_eq P δ e A B r).mp ⟨hD, hm, hc, hlo, hhi, hcov, hfour, hx, hx4, hRayleigh⟩
  have hDProj : AronowAudit.P002.ValidDesign (toPopulation P.pop) := hXiProj.1
  have hnPos : 0 < n := by omega
  have hdet : (AronowAudit.P002.gram (toCovPopulation P).x Finset.univ).det ≠ 0 :=
    AronowAudit.P002.Wave1.T2C_population_det (toCovPopulation P).x e A hnPos he
      (AronowAudit.P002.Wave1.T2C_Xi_covariates (toCovPopulation P) δ e A B r hXiProj)
  have hpoint (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
      oracleTau P (late P.pop) S = groupMean S u - groupMean Sᶜ v := by
    have hSProj : S ∈ AronowAudit.P002.assignments (toPopulation P.pop) := by
      simpa only [SAP.P002a.Bridge.assignments_eq] using hS
    have hproj := (AronowAudit.P002.corrected_oracle_expansion (toCovPopulation P)
      hDProj hXiProj.2.1 hXiProj.2.2.1 hx hdet S hSProj).2
    simpa only [SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation,
      SAP.P002a.Bridge.oracleTau_eq, SAP.P002a.Bridge.late_eq,
      SAP.P002a.Bridge.residual_eq, SAP.P002a.Bridge.groupMean_eq, u, v] using hproj
  have hstat : designVariance P.pop (oracleTau P (late P.pop)) =
      designVariance P.pop (fun S => groupMean S u - groupMean Sᶜ v) := by
    apply designVariance_congr P.pop
    exact hpoint
  have hcontrastProj := AronowAudit.P002.Wave1.NV_contrast_variance
    (toPopulation P.pop) hDProj u v
  have hcontrast : designVariance P.pop (fun S => groupMean S u - groupMean Sᶜ v) =
      popVar u / (P.pop.n1 : ℝ) + popVar v / controlSize P.pop -
        popVar (fun i => u i - v i) / (n : ℝ) := by
    simpa only [SAP.P002a.Bridge.toPopulation, SAP.P002a.Bridge.designVariance_eq,
      SAP.P002a.Bridge.popVar_eq, SAP.P002a.Bridge.groupMean_eq,
      SAP.P002a.controlSize, AronowAudit.P002.controlSize] using hcontrastProj
  have hform : designVariance P.pop (oracleTau P (late P.pop)) =
      V1 / (P.pop.n1 : ℝ) + V0 / controlSize P.pop -
        popVar (fun i => u i - v i) / (n : ℝ) := by
    rw [hstat, hcontrast]
  have hdiff : popVar (fun i => u i - v i) = V1 + V0 - 2 * popCov u v := by
    dsimp [V1, V0]
    exact popVar_sub_identity u v
  rw [hdiff, hcovZero] at hform
  have hcoef1 : (P.pop.n1 : ℝ) / (n : ℝ) ≤ 1-r := (div_le_iff₀ hnR).2 hhi
  have hcoef0 : controlSize P.pop / (n : ℝ) ≤ 1-r := by
    apply (div_le_iff₀ hnR).2
    unfold controlSize
    nlinarith
  have hscale0 : V0 / controlSize P.pop - V0 / (n : ℝ) =
      ((P.pop.n1 : ℝ) / (n : ℝ)) * (V0 / controlSize P.pop) := by
    rw [hNsum]
    field_simp [ne_of_gt hnR, ne_of_gt hcpos]
    <;> ring
  have hscale1 : V1 / (P.pop.n1 : ℝ) - V1 / (n : ℝ) =
      (controlSize P.pop / (n : ℝ)) * (V1 / (P.pop.n1 : ℝ)) := by
    rw [hNsum]
    field_simp [ne_of_gt hnR, ne_of_gt ht]
    <;> ring
  have hfinal : designVariance P.pop (oracleTau P (late P.pop)) ≤
      (1-r) * (V1 / (P.pop.n1 : ℝ) + V0 / controlSize P.pop) := by
    rcases hVzero with hV1zero | hV0zero
    · have hform0 : designVariance P.pop (oracleTau P (late P.pop)) =
          ((P.pop.n1 : ℝ) / (n : ℝ)) * (V0 / controlSize P.pop) := by
        have h' : designVariance P.pop (oracleTau P (late P.pop)) =
            V0 / controlSize P.pop - V0 / (n : ℝ) := by
          simpa [hV1zero] using hform
        rw [hscale0] at h'
        exact h'
      have hbound : ((P.pop.n1 : ℝ) / (n : ℝ)) * (V0 / controlSize P.pop) ≤
          (1-r) * (V0 / controlSize P.pop) :=
        mul_le_mul_of_nonneg_right hcoef1 (div_nonneg hV0 hcpos.le)
      simpa [hV1zero] using hform0.le.trans hbound
    · have hform1 : designVariance P.pop (oracleTau P (late P.pop)) =
          (controlSize P.pop / (n : ℝ)) * (V1 / (P.pop.n1 : ℝ)) := by
        have h' : designVariance P.pop (oracleTau P (late P.pop)) =
            V1 / (P.pop.n1 : ℝ) - V1 / (n : ℝ) := by
          simpa [hV0zero] using hform
        rw [hscale1] at h'
        exact h'
      have hbound : (controlSize P.pop / (n : ℝ)) * (V1 / (P.pop.n1 : ℝ)) ≤
          (1-r) * (V1 / (P.pop.n1 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef0 (div_nonneg hV1 ht.le)
      simpa [hV0zero] using hform1.le.trans hbound
  exact ⟨hVprod, hfinal⟩
