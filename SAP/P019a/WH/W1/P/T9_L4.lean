import SAP.P019a.WH.W1.Leaves
import AronowAudit.P019.Wave1.Gap.GLP019B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T9_L4

open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open AronowAudit.P019.Wave1
open scoped BigOperators Topology
open Classical

private noncomputable def pairMap (j : Fin 5) (e : Fin 5 → ℝ) : ℝ × ℝ :=
  (correlatedNormals e j, correlatedNormals e 4)

private noncomputable def affinePair (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2) / Real.sqrt 2, p.2)

private lemma measurable_affinePair : Measurable affinePair := by
  change Measurable (fun p : ℝ × ℝ => ((p.1 + p.2) / Real.sqrt 2, p.2))
  fun_prop

private lemma aemeasurable_pairMap (j : Fin 5) :
    AEMeasurable (pairMap j) wholeGaussianFive := by
  change AEMeasurable (fun e : Fin 5 → ℝ =>
    (AronowAudit.P019.correlatedNormals e j, AronowAudit.P019.correlatedNormals e 4))
      wholeGaussianFive
  exact (((measurable_pi_apply j).comp frc_correlated_continuous.measurable).prodMk
    ((measurable_pi_apply (4 : Fin 5)).comp frc_correlated_continuous.measurable)).aemeasurable

private lemma pairMap_law (j : Fin 5) (hj : j.val < 4) :
    wholeGaussianFive.map (pairMap j) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map affinePair := by
  change (frc_gaussian 5).map (pairMap j) =
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map affinePair
  let q : ℝ := (Real.sqrt 2)⁻¹
  let c : Fin 2 → ℝ := ![q, q]
  let d : Fin 2 → ℝ := ![0, 1]
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hq : q ^ 2 + q ^ 2 = 1 := by
    dsimp [q]
    field_simp
    nlinarith [hs]
  have ha : (∑ l : Fin 5, (frc_row j l) ^ 2) = ∑ l : Fin 2, (c l) ^ 2 := by
    rw [frc_row_norm]
    simpa [c, Fin.sum_univ_succ] using hq.symm
  have hb : (∑ l : Fin 5, (frc_row 4 l) ^ 2) = ∑ l : Fin 2, (d l) ^ 2 := by
    rw [frc_row_norm]
    norm_num [d, Fin.sum_univ_succ]
  have hj4 : j ≠ (4 : Fin 5) := by
    intro h
    subst j
    norm_num at hj
  have hab : (∑ l : Fin 5, frc_row j l * frc_row 4 l) =
      ∑ l : Fin 2, c l * d l := by
    rw [frc_row_dot, if_neg hj4]
    simp [frc_rho, c, d, Fin.sum_univ_succ, q]
  have hrows := frc_pair_eq (frc_row j) (frc_row 4) c d ha hb hab
  have hlin : (frc_gaussian 5).map (pairMap j) =
      (frc_gaussian 2).map (fun e => (q * e 0 + q * e 1, e 1)) := by
    convert hrows using 1
    · congr 1
      funext e
      simpa only [SAP.P019a.Bridge.correlatedNormals_eq] using
        (Prod.ext (frc_row_eval j e).symm (frc_row_eval 4 e).symm)
    · congr 1
      funext e
      simp [c, d, Fin.sum_univ_succ]
  let pe : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ
  have hpe (e : Fin 2 → ℝ) : pe e = (e 0, e 1) := by
    ext <;> simp [pe]
  have hcomp : affinePair ∘ pe = (fun e : Fin 2 → ℝ => (q * e 0 + q * e 1, e 1)) := by
    funext e
    rw [Function.comp_apply, hpe]
    change (((e 0) + (e 1)) / Real.sqrt 2, e 1) = (q * e 0 + q * e 1, e 1)
    apply Prod.ext
    · dsimp [q]
      field_simp <;> ring
    · rfl
  have hlin2 : (frc_gaussian 2).map (fun e : Fin 2 → ℝ => (q * e 0 + q * e 1, e 1)) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map affinePair := by
    calc
      _ = (frc_gaussian 2).map (affinePair ∘ pe) := by rw [hcomp]
      _ = ((frc_gaussian 2).map pe).map affinePair :=
        (Measure.map_map measurable_affinePair pe.measurable).symm
      _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map affinePair := by
        rw [(measurePreserving_piFinTwo
          (fun _ : Fin 2 => gaussianReal 0 1)).map_eq]
  exact hlin.trans hlin2

private lemma wholeG_eq_frcG : wholeFisherG = frc_g := by
  funext x
  rfl

private lemma wholeH_eq_frcH : wholeFisherH = frc_h ((Real.sqrt 2)⁻¹) ((Real.sqrt 2)⁻¹) := by
  funext t
  unfold wholeFisherH frc_h
  apply integral_congr_ae
  filter_upwards with a
  rw [wholeG_eq_frcG]
  congr 1
  field_simp
  ring

end SAP.P019a.WH.W1.P.T9_L4

open SAP.P019a.WH.W1.P.T9_L4 SAP.P019a.WH.W1 AronowAudit.P019.Wave1
open MeasureTheory ProbabilityTheory

theorem SAP.P019a.WH.W1.T9_L4_proof : SAP.P019a.WH.W1.T9_L4 := by
  intro j hj
  let q : ℝ := (Real.sqrt 2)⁻¹
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : q ^ 2 + q ^ 2 = 1 := by
    dsimp [q]
    field_simp
    nlinarith [hs]
  have hg := wholeG_eq_frcG
  have hleft : MemLp (fun e : Fin 5 → ℝ => wholeFisherG (correlatedNormals e j)) 2
      wholeGaussianFive := by
    simpa [wholeGaussianFive, frc_gaussian, hg, SAP.P019a.Bridge.correlatedNormals_eq]
      using (frc_margin_memLp j)
  have hright : MemLp (fun e : Fin 5 → ℝ => wholeFisherG (correlatedNormals e 4)) 2
      wholeGaussianFive := by
    simpa [wholeGaussianFive, frc_gaussian, hg, SAP.P019a.Bridge.correlatedNormals_eq]
      using (frc_margin_memLp 4)
  have hpairInt : Integrable
      (fun e : Fin 5 → ℝ => wholeFisherG (correlatedNormals e j) *
        wholeFisherG (correlatedNormals e 4)) wholeGaussianFive := hleft.integrable_mul hright
  have hcross :
      (∫ e : Fin 5 → ℝ, wholeFisherG (correlatedNormals e j) *
        wholeFisherG (correlatedNormals e 4) ∂wholeGaussianFive) =
      ∫ t : ℝ, wholeFisherH t * wholeFisherG t ∂gaussianReal 0 1 := by
    let Q : ℝ × ℝ → ℝ := fun p => wholeFisherG p.1 * wholeFisherG p.2
    have hgc : Continuous wholeFisherG := by simpa only [hg] using frc_g_continuous
    have hQcont : Continuous Q := by
      change Continuous (fun p : ℝ × ℝ => wholeFisherG p.1 * wholeFisherG p.2)
      exact (hgc.comp continuous_fst).mul (hgc.comp continuous_snd)
    have hQmap : AEStronglyMeasurable Q (wholeGaussianFive.map (pairMap j)) :=
      hQcont.aestronglyMeasurable
    have hQprod : AEStronglyMeasurable Q
        (((gaussianReal 0 1).prod (gaussianReal 0 1)).map affinePair) :=
      hQcont.aestronglyMeasurable
    have hLin : HasLaw (fun p : ℝ × ℝ => (p.1 + p.2) / Real.sqrt 2)
        (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h := frc_product_linear q q hq
      convert h using 1
      funext p
      dsimp [q]
      field_simp <;> ring
    have hX : MemLp (fun p : ℝ × ℝ => wholeFisherG ((p.1 + p.2) / Real.sqrt 2)) 2
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h := hLin.memLp_comp frc_g_memLp
      change MemLp (fun p : ℝ × ℝ => frc_g ((p.1 + p.2) / Real.sqrt 2)) 2
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) at h
      simpa only [hg] using h
    have hYlaw : HasLaw Prod.snd (gaussianReal 0 1)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := measurePreserving_snd.hasLaw
    have hY : MemLp (fun p : ℝ × ℝ => wholeFisherG p.2) 2
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h := hYlaw.memLp_comp frc_g_memLp
      change MemLp (fun p : ℝ × ℝ => frc_g p.2) 2
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) at h
      simpa only [hg] using h
    have hprod : Integrable
        (fun p : ℝ × ℝ => wholeFisherG ((p.1 + p.2) / Real.sqrt 2) *
          wholeFisherG p.2) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := hX.integrable_mul hY
    calc
      _ = ∫ z, Q z ∂wholeGaussianFive.map (pairMap j) := by
        exact (integral_map (aemeasurable_pairMap j) hQmap).symm
      _ = ∫ z, Q z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)).map affinePair :=
        by rw [pairMap_law j hj]
      _ = ∫ p, Q (affinePair p) ∂(gaussianReal 0 1).prod (gaussianReal 0 1) :=
        integral_map measurable_affinePair.aemeasurable hQprod
      _ = ∫ t, ∫ a, wholeFisherG ((a + t) / Real.sqrt 2) * wholeFisherG t
          ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
        change (∫ p : ℝ × ℝ,
          wholeFisherG ((p.1 + p.2) / Real.sqrt 2) * wholeFisherG p.2
            ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) = _
        exact integral_prod_symm _ hprod
      _ = ∫ t, wholeFisherH t * wholeFisherG t ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards with t
        change (∫ a, wholeFisherG ((a + t) / Real.sqrt 2) * wholeFisherG t
          ∂gaussianReal 0 1) = wholeFisherH t * wholeFisherG t
        rw [integral_mul_const]
        rfl
  have hmeanj : (∫ e : Fin 5 → ℝ, wholeFisherG (correlatedNormals e j)
      ∂wholeGaussianFive) = 2 := by
    simpa [wholeGaussianFive, frc_gaussian, hg, SAP.P019a.Bridge.correlatedNormals_eq]
      using frc_margin_mean j
  have hmean4 : (∫ e : Fin 5 → ℝ, wholeFisherG (correlatedNormals e 4)
      ∂wholeGaussianFive) = 2 := by
    simpa [wholeGaussianFive, frc_gaussian, hg, SAP.P019a.Bridge.correlatedNormals_eq]
      using frc_margin_mean 4
  have hmeanh : (∫ t : ℝ, wholeFisherH t ∂gaussianReal 0 1) = 2 := by
    rw [wholeH_eq_frcH]
    exact frc_h_mean q q hq
  have hmeang : (∫ t : ℝ, wholeFisherG t ∂gaussianReal 0 1) = 2 := by
    simpa only [hg] using frc_g_mean
  unfold wholeCovariance
  rw [hcross, hmeanj, hmean4, hmeanh, hmeang]
