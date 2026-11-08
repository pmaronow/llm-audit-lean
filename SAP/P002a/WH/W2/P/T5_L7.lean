import SAP.P002a.WH.W2.Leaves
import AronowAudit.P002.Wave1.Gap.Theorem2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace SAP.P002a.WH.W2.P.T5_L7

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Topology
attribute [local instance] Classical.propDecidable

end

end SAP.P002a.WH.W2.P.T5_L7

local instance T5_normalNullSingleton :
    MeasureTheory.NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

open Filter MeasureTheory

theorem SAP.P002a.WH.W2.T5_L7_proof : SAP.P002a.WH.W2.T5_L7 := by
  classical
  intro k δ e A B r α hk hδ he hA hB hr hα
  let qcdf : ℝ := 1-α/2
  have hqcdf0 : 0 < qcdf := by dsimp [qcdf]; linarith [hα.2]
  have hqcdf1 : qcdf < 1 := by dsimp [qcdf]; linarith [hα.1]
  obtain ⟨q, hq⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := qcdf) hqcdf0 hqcdf1
  have hq0 : 0 < q := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero, hq]
    dsimp [qcdf]
    linarith [hα.1]
  let t : ℝ := Real.sqrt (1-r)
  have ht0 : 0 < t := by
    dsimp [t]
    apply Real.sqrt_pos.2
    linarith [hr.2]
  have ht1 : t < 1 := by
    have htSq : t^2 = 1-r := by
      dsimp [t]
      rw [Real.sq_sqrt (by linarith [hr.2] : 0 ≤ 1-r)]
    nlinarith [ht0, htSq, hr.1]
  let c : ℝ := (q+q/t)/2
  have hqdiv : q < q/t := (lt_div_iff₀ ht0).2 (by nlinarith [hq0, ht1])
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hqc : q < c := by dsimp [c]; linarith
  have hcqt : c < q/t := by dsimp [c]; linarith
  let d : ℝ := t*c
  have hdq : d < q := by
    dsimp [d]
    calc
      t*c < t*(q/t) := mul_lt_mul_of_pos_left hcqt ht0
      _ = q := by field_simp
  have hd0 : 0 < d := mul_pos ht0 hc0
  let a : ℝ := (d+q)/2
  have hda : d < a := by dsimp [a]; linarith
  have haq : a < q := by dsimp [a]; linarith
  have ha0 : 0 < a := lt_trans hd0 hda
  let b : ℝ := (a+q)/2
  have hab : a < b := by dsimp [b]; linarith
  have hbq : b < q := by dsimp [b]; linarith
  have hqF : AronowAudit.P002.Wave1.SH_absNormalCDF q = 1-α := by
    dsimp [AronowAudit.P002.Wave1.SH_absNormalCDF, qcdf]
    rw [hq]
    ring
  have hFc : 1-α < AronowAudit.P002.Wave1.SH_absNormalCDF c := by
    dsimp [AronowAudit.P002.Wave1.SH_absNormalCDF]
    have hs := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hqc
    rw [hq] at hs
    dsimp [qcdf] at hs
    linarith
  have hFb : AronowAudit.P002.Wave1.SH_absNormalCDF b < 1-α := by
    dsimp [AronowAudit.P002.Wave1.SH_absNormalCDF]
    have hs := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hbq
    rw [hq] at hs
    dsimp [qcdf] at hs
    linarith
  let γ : ℝ := min ((AronowAudit.P002.Wave1.SH_absNormalCDF c-(1-α))/2) (α/2)
  have hγ0 : 0 < γ := by
    dsimp [γ]
    apply lt_min
    · linarith
    · linarith [hα.1]
  have hγα : γ < α := by
    dsimp [γ]
    exact (min_le_right _ _).trans_lt (by linarith [hα.1])
  let x : ℝ := 1-α+γ
  have hx0 : 0 < x := by dsimp [x]; linarith [hα.2, hγ0]
  have hxc : x < AronowAudit.P002.Wave1.SH_absNormalCDF c := by
    dsimp [x]
    have hγgap : γ ≤ (AronowAudit.P002.Wave1.SH_absNormalCDF c-(1-α))/2 :=
      min_le_left _ _
    linarith
  refine ⟨γ, hγ0, hγα, ?_⟩
  intro sizes hsizes P hP hpositive hvariance
  let c1 : ℝ := (a+d+(a-d)/2)/2
  let ε : ℝ := (a-d)/2
  let κ : ℝ := (a^2-c1^2)/a^2
  let K := AronowAudit.P002.Wave1.T2C_pooledK k e A
    (AronowAudit.P002.Wave1.T2C_RK k e A B r)
  have hdε : 0 < ε := by dsimp [ε]; linarith [hda]
  have hdεa : d+ε < a := by dsimp [ε]; linarith [hda]
  have hc1lo : d+ε < c1 := by dsimp [c1, ε]; linarith
  have hc1a : c1 < a := by dsimp [c1]; linarith
  have hc1nonneg : 0 ≤ c1 := by linarith [hd0, hc1lo]
  have hκ : 0 < κ := by
    dsimp [κ]
    exact div_pos (by nlinarith [ha0, hc1a]) (sq_pos_of_pos ha0)
  have hK : 0 ≤ K := by
    dsimp [K, AronowAudit.P002.Wave1.T2C_pooledK, AronowAudit.P002.Wave1.T2C_RK]
    positivity
  have hfixed := AronowAudit.P002.Wave1.T2C_fixed_cdf_uniform k e A r K a b (1-α)
    hk he hA hr hK ha0 hab hFb
  have hfixedseq := hsizes.tendsto_atTop.eventually hfixed
  let Q := fun j => SAP.P002a.Bridge.toCovPopulation (P j)
  have hPQ : ∀ j, AronowAudit.P002.Xi (Q j) δ e A B r := by
    intro j
    simpa only [Q, SAP.P002a.Bridge.xi_eq] using hP j
  have hpositiveQ : ∀ j, 0 < AronowAudit.P002.popVar
        (AronowAudit.P002.residual (Q j) true (AronowAudit.P002.late (Q j).pop))+
      AronowAudit.P002.popVar
        (AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop)) := by
    intro j
    simpa only [Q, SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation,
      SAP.P002a.Bridge.popVar_eq, SAP.P002a.Bridge.residual_eq,
      SAP.P002a.Bridge.late_eq] using hpositive j
  have hH : ∀ j, 0 < AronowAudit.P002.Wave1.T2C_totalH (Q j) := by
    intro j
    have hn : 2 ≤ sizes j := by have hv := (hPQ j).1.1; omega
    have hnpos : 0 < sizes j := by omega
    have hmean (a : Bool) := AronowAudit.P002.Wave1.T2C_residual_centered
      (Q j).x _ (AronowAudit.P002.Wave1.T2C_Xi_residual_score (Q j) δ e A B r he
        (hPQ j) a)
    have hvarTrue := AronowAudit.P002.Wave1.T2C_centered_variance hnpos
      (AronowAudit.P002.residual (Q j) true (AronowAudit.P002.late (Q j).pop)) (hmean true)
    have hvarFalse := AronowAudit.P002.Wave1.T2C_centered_variance hnpos
      (AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop)) (hmean false)
    have hsum : AronowAudit.P002.popVar
          (AronowAudit.P002.residual (Q j) true (AronowAudit.P002.late (Q j).pop))+
        AronowAudit.P002.popVar
          (AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop)) =
        (sizes j : ℝ)/((sizes j : ℝ)-1)*AronowAudit.P002.Wave1.T2C_totalH (Q j) := by
      rw [hvarTrue, hvarFalse]
      unfold AronowAudit.P002.Wave1.T2C_totalH AronowAudit.P002.Wave1.T2C_residualH
      ring
    have hnR : (1:ℝ) < (sizes j : ℝ) := by exact_mod_cast (show 1 < sizes j by omega)
    have hfactor : 0 < (sizes j : ℝ)/((sizes j : ℝ)-1) :=
      div_pos (by exact_mod_cast hnpos) (sub_pos.mpr hnR)
    have hprod : 0 < (sizes j : ℝ)/((sizes j : ℝ)-1)*
        AronowAudit.P002.Wave1.T2C_totalH (Q j) := by
      rw [← hsum]
      exact hpositiveQ j
    exact (mul_pos_iff_of_pos_left hfactor).mp hprod
  have hvarianceQ : ∀ j, AronowAudit.P002.designVariance (Q j).pop
      (AronowAudit.P002.oracleTau (Q j) (AronowAudit.P002.late (Q j).pop)) ≤
        (1-r)*(AronowAudit.P002.popVar
          (AronowAudit.P002.residual (Q j) true (AronowAudit.P002.late (Q j).pop))/
            ((Q j).pop.n1 : ℝ)+AronowAudit.P002.popVar
          (AronowAudit.P002.residual (Q j) false (AronowAudit.P002.late (Q j).pop))/
            AronowAudit.P002.controlSize (Q j).pop) := by
    intro j
    simpa only [Q, SAP.P002a.Bridge.toCovPopulation, SAP.P002a.Bridge.toPopulation,
      SAP.P002a.Bridge.designVariance_eq, SAP.P002a.Bridge.oracleTau_eq,
      SAP.P002a.Bridge.late_eq, SAP.P002a.Bridge.popVar_eq,
      SAP.P002a.Bridge.residual_eq, SAP.P002a.controlSize,
      AronowAudit.P002.controlSize] using hvariance j
  let V := fun j => AronowAudit.P002.designVariance (Q j).pop
    (AronowAudit.P002.oracleTau (Q j) (AronowAudit.P002.late (Q j).pop))
  let C := fun j => AronowAudit.P002.Wave1.T2C_oracleConservative (Q j)
  let O := fun j S => AronowAudit.P002.oracleTau (Q j)
    (AronowAudit.P002.late (Q j).pop) S
  let X := fun j S => AronowAudit.P002.adjustedTau (Q j)
    (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S) S
  let s := fun j S => AronowAudit.P002.adjustedSigma2 (Q j)
    (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S) S
  let R := fun j S => |O j S/Real.sqrt (V j)| ≤ c
  let E := fun j S => ε ≤ |(X j S-O j S)/Real.sqrt (V j)|
  let G := fun j S => κ ≤ |s j S/C j-1|
  let F := fun j S => ¬ (0 < AronowAudit.P002.Wave1.T2C_pooledH (Q j).x
      (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S) ∧
    AronowAudit.P002.mean (fun i => AronowAudit.P002.Wave1.T2C_pooledResidual (Q j).x
        (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S) i^4) ≤
      K*(AronowAudit.P002.Wave1.T2C_pooledH (Q j).x
        (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S))^2)
  have hR := AronowAudit.P002.Wave1.T2C_oracle_abs_cdf sizes hsizes k Q δ e A B r
    hk hδ he hA hB hr hPQ hH c hc0.le
  have hE := AronowAudit.P002.Wave1.T2C_observed_numerator_oracle_limit sizes hsizes k Q δ e A B r
    hk hδ he hA hB hr hPQ hH ε hdε
  have hG := AronowAudit.P002.Wave1.T2C_observed_sigma_limit sizes hsizes k Q δ e A B r
    he hr.1 hPQ hH κ hκ
  have hF := AronowAudit.P002.Wave1.T2C_observed_pooled_limit sizes hsizes k Q δ e A B r
    he hr.1 hPQ hH
  have hlim : Filter.Tendsto (fun j => AronowAudit.P002.probability (Q j).pop (R j)-
      AronowAudit.P002.probability (Q j).pop (E j)-
      AronowAudit.P002.probability (Q j).pop (G j)-
      AronowAudit.P002.probability (Q j).pop (F j))
      atTop (nhds (AronowAudit.P002.Wave1.SH_absNormalCDF c)) := by
    simpa only [sub_zero] using ((hR.sub hE).sub hG).sub hF
  filter_upwards [hfixedseq, (tendsto_order.1 hlim).1 x hxc] with j hj hxj
  have hV : 0 < V j := AronowAudit.P002.Wave1.T2C_oracle_variance_pos
    (Q j) δ e A B r hk hδ he hA hB hr (hPQ j) (hH j)
  have hC : 0 < C j := by
    apply hV.trans_le
    exact AronowAudit.P002.Wave1.T2C_oracle_variance_upper (Q j) δ e A B r he (hPQ j)
  have hscale : V j ≤ (1-r)*C j := by
    exact hvarianceQ j
  have hVC : V j ≤ C j := by
    have hrle : 1-r ≤ 1 := by linarith [hr.1]
    calc
      V j ≤ (1-r)*C j := hscale
      _ ≤ C j := by
        calc
          (1-r)*C j ≤ 1*C j := mul_le_mul_of_nonneg_right hrle hC.le
          _ = C j := by ring
  have hrootC : 0 < Real.sqrt (C j) := Real.sqrt_pos.2 hC
  have hrootV : 0 < Real.sqrt (V j) := Real.sqrt_pos.2 hV
  have hrootScale : Real.sqrt (V j) ≤ t*Real.sqrt (C j) := by
    have hs := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_mul (by linarith [hr.2] : 0 ≤ 1-r)] at hs
    simpa only [t] using hs
  have hU : AronowAudit.P002.probability (Q j).pop (fun S =>
        AronowAudit.P002.adjustedAccepted (Q j) (AronowAudit.P002.late (Q j).pop) α S ∨
        (E j S ∨ (G j S ∨ F j S))) ≤
      AronowAudit.P002.adjustedCoverage (Q j) (AronowAudit.P002.late (Q j).pop) α+
        (AronowAudit.P002.probability (Q j).pop (E j)+
          (AronowAudit.P002.probability (Q j).pop (G j)+
            AronowAudit.P002.probability (Q j).pop (F j))) :=
    (AronowAudit.P002.Wave1.T2C_probability_union _ _ _).trans (add_le_add le_rfl
      ((AronowAudit.P002.Wave1.T2C_probability_union _ _ _).trans (add_le_add le_rfl
        (AronowAudit.P002.Wave1.T2C_probability_union _ _ _))))
  have hinc : AronowAudit.P002.probability (Q j).pop (R j) ≤
      AronowAudit.P002.probability (Q j).pop (fun S =>
      AronowAudit.P002.adjustedAccepted (Q j) (AronowAudit.P002.late (Q j).pop) α S ∨
        (E j S ∨ (G j S ∨ F j S))) := by
    apply AronowAudit.P002.Wave1.T2C_probability_mono
    intro S hS hR
    by_cases hE : E j S
    · exact Or.inr (Or.inl hE)
    by_cases hG : G j S
    · exact Or.inr (Or.inr (Or.inl hG))
    by_cases hF : F j S
    · exact Or.inr (Or.inr (Or.inr hF))
    have hpool := not_not.mp hF
    have hcdf := hj (Q j)
      (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S)
      (hPQ j).1 (hPQ j).2.2.2.1 (hPQ j).2.2.2.2.1
      (AronowAudit.P002.Wave1.T2C_Xi_covariates (Q j) δ e A B r (hPQ j))
      hpool.1 hpool.2
    have hq := AronowAudit.P002.Wave1.T2C_C_quantile_lower (Q j).pop (hPQ j).1 _ α hα
      (ENNReal.ofReal a) hcdf
    have hratioRoot : Real.sqrt (V j)/Real.sqrt (C j) ≤ t :=
      (div_le_iff₀ hrootC).2 (by nlinarith [hrootScale])
    have hrootRatNonneg : 0 ≤ Real.sqrt (V j)/Real.sqrt (C j) :=
      div_nonneg (Real.sqrt_nonneg _) hrootC.le
    have hstd : |X j S/Real.sqrt (C j)| ≤ c1 := by
      have horacleEq : O j S/Real.sqrt (C j) =
          (O j S/Real.sqrt (V j))*(Real.sqrt (V j)/Real.sqrt (C j)) := by
        field_simp
      have horacle : |O j S/Real.sqrt (C j)| ≤ d := by
        change |O j S/Real.sqrt (V j)| ≤ c at hR
        rw [horacleEq, abs_mul, abs_of_nonneg hrootRatNonneg]
        calc
          (abs (O j S/Real.sqrt (V j)))*(Real.sqrt (V j)/Real.sqrt (C j)) ≤
              c*(Real.sqrt (V j)/Real.sqrt (C j)) :=
            mul_le_mul_of_nonneg_right hR hrootRatNonneg
          _ ≤ c*t := mul_le_mul_of_nonneg_left hratioRoot hc0.le
          _ = d := by dsimp [d]; ring
      have hratioVC : Real.sqrt (V j)/Real.sqrt (C j) ≤ 1 := by
        exact (div_le_iff₀ hrootC).2 (by nlinarith [hrootScale, ht1, hrootC])
      have herrorEq : (X j S-O j S)/Real.sqrt (C j) =
          ((X j S-O j S)/Real.sqrt (V j))*(Real.sqrt (V j)/Real.sqrt (C j)) := by
        field_simp
      have hsmall : |(X j S-O j S)/Real.sqrt (C j)| < ε := by
        have hEnot : ¬ ε ≤ |(X j S-O j S)/Real.sqrt (V j)| := by
          simpa only [E] using hE
        rw [herrorEq, abs_mul, abs_of_nonneg hrootRatNonneg]
        have hstrict : |(X j S-O j S)/Real.sqrt (V j)| < ε := lt_of_not_ge hEnot
        calc
          (abs ((X j S-O j S)/Real.sqrt (V j)))*(Real.sqrt (V j)/Real.sqrt (C j)) ≤
              |(X j S-O j S)/Real.sqrt (V j)| :=
            mul_le_of_le_one_right (abs_nonneg _) hratioVC
          _ < ε := hstrict
      have heq : X j S/Real.sqrt (C j) = O j S/Real.sqrt (C j)+
          (X j S-O j S)/Real.sqrt (C j) := by ring
      rw [heq]
      have htri := abs_add_le (O j S/Real.sqrt (C j))
        ((X j S-O j S)/Real.sqrt (C j))
      dsimp [c1, ε] at *
      linarith
    have hgood : |s j S/C j-1| < (a^2-c1^2)/a^2 := by
      have hnot : ¬ κ ≤ |s j S/C j-1| := by simpa only [G] using hG
      have hlt : |s j S/C j-1| < κ := lt_of_not_ge hnot
      simpa only [κ] using hlt
    have hstat := AronowAudit.P002.Wave1.T2C_U_student_lower (X j S) (s j S)
      (C j) (C j) a c1 (AronowAudit.P002.Wave1.T2C_sigma_nonneg (Q j)
        (AronowAudit.P002.observedW (Q j).pop (AronowAudit.P002.late (Q j).pop) S) S)
      hC hC (le_rfl) ha0 hc1nonneg hc1a hstd hgood
    exact Or.inl (hstat.trans hq.le)
  have hbound : AronowAudit.P002.probability (Q j).pop (R j)-
      AronowAudit.P002.probability (Q j).pop (E j)-
      AronowAudit.P002.probability (Q j).pop (G j)-
      AronowAudit.P002.probability (Q j).pop (F j) ≤
        AronowAudit.P002.adjustedCoverage (Q j) (AronowAudit.P002.late (Q j).pop) α := by
    linarith [hinc.trans hU]
  rw [SAP.P002a.Bridge.adjustedCoverage_eq (P j)]
  have hl : AronowAudit.P002.late (Q j).pop = SAP.P002a.late (P j).pop := by
    simpa only [Q, SAP.P002a.Bridge.toCovPopulation] using
      (SAP.P002a.Bridge.late_eq (P j).pop).symm
  rw [← hl]
  have hh := hxj.trans_le hbound
  simpa only [x] using hh.le
