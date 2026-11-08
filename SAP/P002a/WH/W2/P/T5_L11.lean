import SAP.P002a.WH.W2.Leaves
import AronowAudit.P002.Wave1.Theorem2.Reassignment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W2.P.T5_L11

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

local instance T5_L11_normalNullSingleton :
    NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma constant_effect_residuals_eq {n k} (P : AronowAudit.P002.CovPopulation n k)
    (δ e A B r : ℝ) (hP : AronowAudit.P002.Xi P δ e A B r)
    (hy : ∃ β : ℝ, ∀ i, P.pop.y i true = P.pop.y i false + β) :
    AronowAudit.P002.residual P true (AronowAudit.P002.late P.pop) =
      AronowAudit.P002.residual P false (AronowAudit.P002.late P.pop) := by
  have hwt := AronowAudit.P002.Wave1.GP0022B2b_SH_w_baseline P.pop
    hP.2.2.1 hy true
  have hwf := AronowAudit.P002.Wave1.GP0022B2b_SH_w_baseline P.pop
    hP.2.2.1 hy false
  have hpsi : AronowAudit.P002.psi P true (AronowAudit.P002.late P.pop) =
      AronowAudit.P002.psi P false (AronowAudit.P002.late P.pop) := by
    simp [AronowAudit.P002.psi, hwt, hwf]
  funext i
  simp only [AronowAudit.P002.residual, hwt, hwf, hpsi]

lemma constant_effect_oracle_variance_eq {n k} (P : AronowAudit.P002.CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : AronowAudit.P002.Xi P δ e A B r)
    (hres : AronowAudit.P002.residual P true (AronowAudit.P002.late P.pop) =
      AronowAudit.P002.residual P false (AronowAudit.P002.late P.pop)) :
    AronowAudit.P002.designVariance P.pop
        (AronowAudit.P002.oracleTau P (AronowAudit.P002.late P.pop)) =
      AronowAudit.P002.Wave1.T2C_oracleConservative P := by
  have hx := AronowAudit.P002.Wave1.T2C_Xi_covariates P δ e A B r hP
  have hn : 0 < n := by have := hP.1.1; omega
  have hg := AronowAudit.P002.Wave1.T2C_population_det P.x e A hn he hx
  have hD5 := (AronowAudit.P002.Wave1.oracle_variances_proof P hP.1
    (AronowAudit.P002.late P.pop) (fun _ => 0) hx.1 hg).1
  have hzero : AronowAudit.P002.popVar (fun i =>
      AronowAudit.P002.residual P true (AronowAudit.P002.late P.pop) i-
      AronowAudit.P002.residual P false (AronowAudit.P002.late P.pop) i) = 0 := by
    have hdiff : (fun i => AronowAudit.P002.residual P true
        (AronowAudit.P002.late P.pop) i-AronowAudit.P002.residual P false
        (AronowAudit.P002.late P.pop) i) = fun _ => (0 : ℝ) := by
      funext i
      rw [hres]
      ring
    rw [hdiff]
    simp [AronowAudit.P002.popVar, AronowAudit.P002.mean]
  rw [hzero, zero_div, sub_zero] at hD5
  simpa [AronowAudit.P002.Wave1.T2C_oracleConservative] using hD5

lemma local_probability_mono {n : ℕ} (P : SAP.P002a.Population n)
    {E F : Finset (Fin n) → Prop}
    (hEF : ∀ S ∈ SAP.P002a.assignments P, E S → F S) :
    SAP.P002a.probability P E ≤ SAP.P002a.probability P F := by
  simpa only [SAP.P002a.Bridge.probability_eq, SAP.P002a.Bridge.toPopulation] using
    (AronowAudit.P002.Wave1.T2C_probability_mono (SAP.P002a.Bridge.toPopulation P) hEF)

lemma local_probability_union {n : ℕ} (P : SAP.P002a.Population n)
    (E F : Finset (Fin n) → Prop) :
    SAP.P002a.probability P (fun S => E S ∨ F S) ≤
      SAP.P002a.probability P E+SAP.P002a.probability P F := by
  simpa only [SAP.P002a.Bridge.probability_eq, SAP.P002a.Bridge.toPopulation] using
    (AronowAudit.P002.Wave1.T2C_probability_union (SAP.P002a.Bridge.toPopulation P) E F)

theorem fixed_baseline_cdf
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (k : ℕ)
    (P : ∀ j, SAP.P002a.CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ j, SAP.P002a.Xi (P j) δ e A B r)
    (hy : ∀ j, ∃ β : ℝ, ∀ i, (P j).pop.y i true = (P j).pop.y i false + β)
    (hnondeg : ∀ j, 0 < SAP.P002a.popVar
      (SAP.P002a.residual (P j) false (SAP.P002a.late (P j).pop))) :
    ∀ t : ℝ, 0 < t → Tendsto (fun j => SAP.P002a.probability (P j).pop (fun S =>
      SAP.P002a.adjustedAR (P j) (fun i => (P j).pop.y i false) S ≤ ENNReal.ofReal t))
      atTop (nhds (SAP.P002a.W2AbsNormalCDF t)) := by
  let Q (j : ℕ) := SAP.P002a.Bridge.toCovPopulation (P j)
  have hQ (j : ℕ) : AronowAudit.P002.Xi (Q j) δ e A B r := by
    simpa only [Q, SAP.P002a.Bridge.xi_eq] using hP j
  have hyQ (j : ℕ) : ∃ β : ℝ, ∀ i,
      (Q j).pop.y i true = (Q j).pop.y i false + β := by
    rcases hy j with ⟨β, hβ⟩
    refine ⟨β, ?_⟩
    intro i
    simpa [Q, SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using hβ i
  have hndQ (j : ℕ) : 0 < AronowAudit.P002.popVar
      (AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop)) := by
    simpa only [Q, SAP.P002a.Bridge.popVar_eq, SAP.P002a.Bridge.residual_eq,
      SAP.P002a.Bridge.late_eq, SAP.P002a.Bridge.toCovPopulation,
      SAP.P002a.Bridge.toPopulation] using hnondeg j
  have hresQ (j : ℕ) : AronowAudit.P002.residual (Q j) true
      (AronowAudit.P002.late (Q j).pop) = AronowAudit.P002.residual (Q j) false
      (AronowAudit.P002.late (Q j).pop) :=
    constant_effect_residuals_eq (Q j) δ e A B r (hQ j) (hyQ j)
  have hHQ (j : ℕ) : 0 < AronowAudit.P002.Wave1.T2C_totalH (Q j) := by
    have hcenter := AronowAudit.P002.Wave1.T2C_residual_centered (Q j).x _
      (AronowAudit.P002.Wave1.T2C_Xi_residual_score (Q j) δ e A B r he (hQ j) false)
    have hn : 0 < sizes j := by have := (hQ j).1.1; omega
    have hvar := AronowAudit.P002.Wave1.T2C_centered_variance hn
      (AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop)) hcenter
    have hfactor : 0 < (sizes j : ℝ)/((sizes j : ℝ)-1) := by
      have hnR : (1 : ℝ) < sizes j := by exact_mod_cast (by have := (hQ j).1.1; omega)
      positivity
    have hmnonneg : 0 ≤ AronowAudit.P002.mean (fun i =>
        AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop) i^2) := by
      unfold AronowAudit.P002.mean
      apply div_nonneg
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      · exact Nat.cast_nonneg _
    have hmpos : 0 < AronowAudit.P002.mean (fun i =>
        AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop) i^2) := by
      have hnd := hndQ j
      rw [hvar] at hnd
      nlinarith [hnd, hfactor, hmnonneg]
    have heq : AronowAudit.P002.Wave1.T2C_totalH (Q j) =
        2*AronowAudit.P002.mean (fun i =>
          AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop) i^2) := by
      unfold AronowAudit.P002.Wave1.T2C_totalH AronowAudit.P002.Wave1.T2C_residualH
      rw [hresQ j]
      ring
    rw [heq]
    positivity
  have hVCQ (j : ℕ) : AronowAudit.P002.designVariance (Q j).pop
      (AronowAudit.P002.oracleTau (Q j) (AronowAudit.P002.late (Q j).pop)) =
      AronowAudit.P002.Wave1.T2C_oracleConservative (Q j) :=
    constant_effect_oracle_variance_eq (Q j) δ e A B r he (hQ j) (hresQ j)
  have hVQpos (j : ℕ) : 0 < AronowAudit.P002.designVariance (Q j).pop
      (AronowAudit.P002.oracleTau (Q j) (AronowAudit.P002.late (Q j).pop)) :=
    AronowAudit.P002.Wave1.T2C_oracle_variance_pos (Q j) δ e A B r
      hk hδ he hA hB hr (hQ j) (hHQ j)
  have hobsQ (j : ℕ) (S : Finset (Fin (sizes j))) :
      AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S =
        fun i => (Q j).pop.y i false :=
    AronowAudit.P002.Wave1.GP0022B2b_SH_observedW_baseline (Q j).pop
      (hQ j).2.2.1 (hyQ j) S

  intro t ht
  let V (j : ℕ) := SAP.P002a.designVariance (P j).pop
    (SAP.P002a.oracleTau (P j) (SAP.P002a.late (P j).pop))
  let C (j : ℕ) := AronowAudit.P002.Wave1.T2C_oracleConservative (Q j)
  let X (j : ℕ) (S : Finset (Fin (sizes j))) :=
    SAP.P002a.adjustedTau (P j) (SAP.P002a.observedW (P j).pop
      (SAP.P002a.late (P j).pop) S) S
  let O (j : ℕ) (S : Finset (Fin (sizes j))) :=
    SAP.P002a.oracleTau (P j) (SAP.P002a.late (P j).pop) S
  let s (j : ℕ) (S : Finset (Fin (sizes j))) :=
    SAP.P002a.adjustedSigma2 (P j) (SAP.P002a.observedW (P j).pop
      (SAP.P002a.late (P j).pop) S) S
  let R (a : ℝ) (j : ℕ) (S : Finset (Fin (sizes j))) := |O j S/Real.sqrt (V j)| ≤ a
  let N (η : ℝ) (j : ℕ) (S : Finset (Fin (sizes j))) :=
    η ≤ |(X j S-O j S)/Real.sqrt (V j)|
  let G (κ : ℝ) (j : ℕ) (S : Finset (Fin (sizes j))) :=
    κ ≤ |s j S/C j-1|
  let F (u : ℝ) (j : ℕ) (S : Finset (Fin (sizes j))) :=
    SAP.P002a.adjustedAR (P j) (fun i => (P j).pop.y i false) S ≤ ENNReal.ofReal u

  have hVC (j : ℕ) : V j = C j := by
    have h := hVCQ j
    simpa only [Q, V, C, SAP.P002a.Bridge.designVariance_eq,
      SAP.P002a.Bridge.oracleTau_eq, SAP.P002a.Bridge.late_eq,
      SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using h
  have hVpos (j : ℕ) : 0 < V j := by
    have h := hVQpos j
    simpa only [Q, V, SAP.P002a.Bridge.designVariance_eq,
      SAP.P002a.Bridge.oracleTau_eq, SAP.P002a.Bridge.late_eq,
      SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using h
  have hobs (j : ℕ) (S : Finset (Fin (sizes j))) :
      SAP.P002a.observedW (P j).pop (SAP.P002a.late (P j).pop) S =
        fun i => (P j).pop.y i false := by
    have h := hobsQ j S
    simpa only [Q, SAP.P002a.Bridge.observedW_eq, SAP.P002a.Bridge.late_eq,
      SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using h
  have htarget (u : ℝ) (j : ℕ) (S : Finset (Fin (sizes j))) :
      F u j S ↔ SAP.P002a.absStudent (X j S) (s j S) ≤ ENNReal.ofReal u := by
    simp [F, X, s, SAP.P002a.adjustedAR, hobs j S]
  have hsNonneg (j : ℕ) (S : Finset (Fin (sizes j))) : 0 ≤ s j S := by
    have h := AronowAudit.P002.Wave1.T2C_sigma_nonneg (Q j)
      (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S) S
    simpa only [Q, s, SAP.P002a.Bridge.adjustedSigma2_eq,
      SAP.P002a.Bridge.observedW_eq, SAP.P002a.Bridge.late_eq,
      SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation] using h

  have hR (a : ℝ) (ha : 0 ≤ a) :
      Tendsto (fun j => SAP.P002a.probability (P j).pop (fun S => R a j S)) atTop
        (nhds (SAP.P002a.W2AbsNormalCDF a)) := by
    have h := AronowAudit.P002.Wave1.T2C_oracle_abs_cdf sizes hsizes k Q δ e A B r
      hk hδ he hA hB hr hQ hHQ a ha
    simpa only [Q, R, O, V, SAP.P002a.W2AbsNormalCDF,
      AronowAudit.P002.Wave1.SH_absNormalCDF, SAP.P002a.Bridge.probability_eq,
      SAP.P002a.Bridge.oracleTau_eq, SAP.P002a.Bridge.designVariance_eq,
      SAP.P002a.Bridge.late_eq, SAP.P002a.Bridge.toCovPopulation,
      SAP.P002a.Bridge.toPopulation] using h
  have hN (η : ℝ) (hη : 0 < η) :
      Tendsto (fun j => SAP.P002a.probability (P j).pop (fun S => N η j S)) atTop
        (nhds 0) := by
    have h := AronowAudit.P002.Wave1.T2C_observed_numerator_oracle_limit sizes hsizes k Q
      δ e A B r hk hδ he hA hB hr hQ hHQ η hη
    simpa only [Q, N, X, O, V, SAP.P002a.Bridge.probability_eq,
      SAP.P002a.Bridge.adjustedTau_eq, SAP.P002a.Bridge.observedW_eq,
      SAP.P002a.Bridge.oracleTau_eq, SAP.P002a.Bridge.designVariance_eq,
      SAP.P002a.Bridge.late_eq, SAP.P002a.Bridge.toCovPopulation,
      SAP.P002a.Bridge.toPopulation] using h
  have hG (κ : ℝ) (hκ : 0 < κ) :
      Tendsto (fun j => SAP.P002a.probability (P j).pop (fun S => G κ j S)) atTop
        (nhds 0) := by
    have h := AronowAudit.P002.Wave1.T2C_observed_sigma_limit sizes hsizes k Q δ e A B r
      he hr.1 hQ hHQ κ hκ
    simpa only [Q, G, C, s, SAP.P002a.Bridge.probability_eq,
      SAP.P002a.Bridge.adjustedSigma2_eq, SAP.P002a.Bridge.observedW_eq,
      SAP.P002a.Bridge.late_eq, SAP.P002a.Bridge.toCovPopulation,
      SAP.P002a.Bridge.toPopulation] using h

  have hcont : ContinuousAt SAP.P002a.W2AbsNormalCDF t := by
    unfold SAP.P002a.W2AbsNormalCDF
    exact (continuousAt_const.mul
      (AronowAudit.P053.NormalCompletion.cdf_continuousAt
        (ProbabilityTheory.gaussianReal 0 1) t)).sub continuousAt_const
  apply tendsto_order.2
  constructor
  · intro z hz
    have hevent : ∀ᶠ a in nhdsWithin t (Set.Iio t), z < SAP.P002a.W2AbsNormalCDF a :=
      (hcont.tendsto.mono_left inf_le_left).eventually (eventually_gt_nhds hz)
    have hepos : ∀ᶠ a in nhdsWithin t (Set.Iio t), 0 < a :=
      (eventually_gt_nhds ht).filter_mono inf_le_left
    obtain ⟨a, ⟨hFa, ha0⟩, hat⟩ := ((hevent.and hepos).and self_mem_nhdsWithin).exists
    let c : ℝ := (a+t)/2
    let η : ℝ := (t-a)/4
    let κ : ℝ := (t^2-c^2)/t^2
    have hct : c < t := by dsimp [c]; linarith
    have hη : 0 < η := by dsimp [η]; linarith
    have hmargin : a+η < c := by dsimp [c, η]; linarith
    have hκ : 0 < κ := by
      dsimp [κ]
      exact div_pos (by nlinarith) (sq_pos_of_pos ht)
    have hlim := ((hR a ha0.le).sub (hN η hη)).sub (hG κ hκ)
    simp only [sub_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).1 z hFa] with j hj
    have hinc : SAP.P002a.probability (P j).pop (fun S => R a j S) ≤
        SAP.P002a.probability (P j).pop
          (fun S => F t j S ∨ (N η j S ∨ G κ j S)) := by
      apply local_probability_mono (P j).pop
      intro S hS hraw
      by_cases hn : N η j S
      · exact Or.inr (Or.inl hn)
      by_cases hg : G κ j S
      · exact Or.inr (Or.inr hg)
      apply Or.inl
      have hrawX : |X j S/Real.sqrt (V j)| ≤ c := by
        have hnsmall : |(X j S-O j S)/Real.sqrt (V j)| < η := lt_of_not_ge hn
        have heq : X j S/Real.sqrt (V j) = O j S/Real.sqrt (V j)+
            (X j S-O j S)/Real.sqrt (V j) := by ring
        rw [heq]
        calc
          _ ≤ |O j S/Real.sqrt (V j)|+|(X j S-O j S)/Real.sqrt (V j)| := abs_add_le _ _
          _ ≤ a+η := add_le_add hraw hnsmall.le
          _ ≤ c := le_of_lt hmargin
      have hgood0 : |s j S/V j-1| < κ := by
        have hgsmall : |s j S/C j-1| < κ := lt_of_not_ge hg
        rw [hVC j]
        exact hgsmall
      have hstudent := AronowAudit.P002.Wave1.T2C_U_student_lower
        (X j S) (s j S) (V j) (V j) t c (hsNonneg j S) (hVpos j) (hVpos j)
        le_rfl ht (le_of_lt (by dsimp [c]; linarith)) hct hrawX hgood0
      exact (htarget t j S).mpr hstudent
    have hNG := local_probability_union (P j).pop
      (fun S => N η j S) (fun S => G κ j S)
    have hUnion := local_probability_union (P j).pop
      (fun S => F t j S) (fun S => N η j S ∨ G κ j S)
    have hunion : SAP.P002a.probability (P j).pop
        (fun S => F t j S ∨ (N η j S ∨ G κ j S)) ≤
        SAP.P002a.probability (P j).pop (fun S => F t j S)+
          (SAP.P002a.probability (P j).pop (fun S => N η j S)+
            SAP.P002a.probability (P j).pop (fun S => G κ j S)) := by
      exact hUnion.trans (add_le_add le_rfl hNG)
    have hbound : SAP.P002a.probability (P j).pop (fun S => R a j S) ≤
        SAP.P002a.probability (P j).pop (fun S => F t j S)+
          (SAP.P002a.probability (P j).pop (fun S => N η j S)+
            SAP.P002a.probability (P j).pop (fun S => G κ j S)) := by
      exact hinc.trans hunion
    have hdiff : SAP.P002a.probability (P j).pop (fun S => R a j S)-
        SAP.P002a.probability (P j).pop (fun S => N η j S)-
        SAP.P002a.probability (P j).pop (fun S => G κ j S) ≤
        SAP.P002a.probability (P j).pop (fun S => F t j S) := by linarith
    exact hj.trans_le hdiff
  · intro z hz
    have hevent : ∀ᶠ b in nhdsWithin t (Set.Ioi t), SAP.P002a.W2AbsNormalCDF b < z :=
      (hcont.tendsto.mono_left inf_le_left).eventually (eventually_lt_nhds hz)
    obtain ⟨b, hFb, htb⟩ := (hevent.and self_mem_nhdsWithin).exists
    let c : ℝ := (t+b)/2
    let η : ℝ := (b-c)/2
    let κ : ℝ := (c^2-t^2)/t^2
    have htc : t < c := by dsimp [c]; linarith
    have hcb : c < b := by dsimp [c]; linarith
    have hη : 0 < η := by dsimp [η]; linarith
    have hmargin : c+η < b := by dsimp [c, η]; linarith
    have hκ : 0 < κ := by
      dsimp [κ]
      exact div_pos (by nlinarith) (sq_pos_of_pos ht)
    have hlim := ((hR b (le_of_lt (ht.trans htb))).add (hN η hη)).add (hG κ hκ)
    simp only [add_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).2 z hFb] with j hj
    have hinc : SAP.P002a.probability (P j).pop (fun S => F t j S) ≤
        SAP.P002a.probability (P j).pop
          (fun S => R b j S ∨ (N η j S ∨ G κ j S)) := by
      apply local_probability_mono (P j).pop
      intro S hS hfeasible
      by_cases hn : N η j S
      · exact Or.inr (Or.inl hn)
      by_cases hg : G κ j S
      · exact Or.inr (Or.inr hg)
      apply Or.inl
      have hstudent := (htarget t j S).mp hfeasible
      have hgood0 : |s j S/V j-1| < κ := by
        have hgsmall : |s j S/C j-1| < κ := lt_of_not_ge hg
        rw [hVC j]
        exact hgsmall
      have hrawX := AronowAudit.P002.Wave1.T2C_U_student_upper
        (X j S) (s j S) (V j) t c (hsNonneg j S) (hVpos j) ht htc hstudent hgood0
      have hnsmall : |(X j S-O j S)/Real.sqrt (V j)| < η := lt_of_not_ge hn
      have heq : O j S/Real.sqrt (V j) = X j S/Real.sqrt (V j)-
          (X j S-O j S)/Real.sqrt (V j) := by ring
      change |O j S/Real.sqrt (V j)| ≤ b
      rw [heq]
      calc
        _ ≤ |X j S/Real.sqrt (V j)|+|(X j S-O j S)/Real.sqrt (V j)| := abs_sub _ _
        _ ≤ c+η := add_le_add hrawX hnsmall.le
        _ ≤ b := le_of_lt hmargin
    have hNG := local_probability_union (P j).pop
      (fun S => N η j S) (fun S => G κ j S)
    have hUnion := local_probability_union (P j).pop
      (fun S => R b j S) (fun S => N η j S ∨ G κ j S)
    have hunion : SAP.P002a.probability (P j).pop
        (fun S => R b j S ∨ (N η j S ∨ G κ j S)) ≤
        SAP.P002a.probability (P j).pop (fun S => R b j S)+
          (SAP.P002a.probability (P j).pop (fun S => N η j S)+
            SAP.P002a.probability (P j).pop (fun S => G κ j S)) := by
      exact hUnion.trans (add_le_add le_rfl hNG)
    have hbound : SAP.P002a.probability (P j).pop (fun S => F t j S) ≤
        SAP.P002a.probability (P j).pop (fun S => R b j S)+
          (SAP.P002a.probability (P j).pop (fun S => N η j S)+
            SAP.P002a.probability (P j).pop (fun S => G κ j S)) := by
      exact hinc.trans hunion
    have hj' : SAP.P002a.probability (P j).pop (fun S => R b j S)+
        (SAP.P002a.probability (P j).pop (fun S => N η j S)+
          SAP.P002a.probability (P j).pop (fun S => G κ j S)) < z := by
      simpa only [add_assoc] using hj
    exact hbound.trans_lt hj'

end
end SAP.P002a.WH.W2.P.T5_L11

theorem SAP.P002a.WH.W2.T5_L11_proof : SAP.P002a.WH.W2.T5_L11 := by
  intro sizes hsizes k P δ e A B r hk hδ he hA hB hr hP hy hnondeg t ht
  exact SAP.P002a.WH.W2.P.T5_L11.fixed_baseline_cdf sizes hsizes k P δ e A B r
    hk hδ he hA hB hr hP hy hnondeg t ht
