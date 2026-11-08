import SAP.P022.WH.W1.Leaves
import AronowAudit.Shared.MapTailB.QuantileBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace SAP.P022.WH.W1.P.T17_L4

open SAP.P022 SAP.P022.WH.W1 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

def mixMeasure (J H : JointLaw) (w : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - w) • (J : Measure (ℝ × ℝ)) +
    ENNReal.ofReal w • (H : Measure (ℝ × ℝ))

theorem mixMeasure_probability (J H : JointLaw) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) : IsProbabilityMeasure (mixMeasure J H w) := by
  constructor
  simp only [mixMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hw1) hw]
  norm_num

noncomputable def mixLaw (J H : JointLaw) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) : JointLaw :=
  ⟨mixMeasure J H w, mixMeasure_probability J H w hw hw1⟩

theorem mixLaw_cdf (J H : JointLaw) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hJ : J ∈ compatibleLaws H) (t : Bool) (x : ℝ) :
    lawCDF (mixLaw J H w hw hw1) t x = lawCDF H t x := by
  change (mixMeasure J H w {p : ℝ × ℝ | (if t then p.1 else p.2) ≤ x}).toReal =
    ((H : Measure (ℝ × ℝ)) {p : ℝ × ℝ | (if t then p.1 else p.2) ≤ x}).toReal
  rw [mixMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1)]
  have hcdf : ((J : Measure (ℝ × ℝ))
      {p : ℝ × ℝ | (if t then p.1 else p.2) ≤ x}).toReal =
      ((H : Measure (ℝ × ℝ))
        {p : ℝ × ℝ | (if t then p.1 else p.2) ≤ x}).toReal := hJ t x
  rw [hcdf]
  ring

theorem mixLaw_compatible (J H : JointLaw) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hJ : J ∈ compatibleLaws H) : mixLaw J H w hw hw1 ∈ compatibleLaws H := by
  intro t x
  exact mixLaw_cdf J H w hw hw1 hJ t x

def coord (t : Bool) : ℝ × ℝ → ℝ := fun p => if t then p.1 else p.2

theorem coord_measurable (t : Bool) : Measurable (coord t) := by
  cases t
  · exact measurable_snd
  · exact measurable_fst

theorem compatible_mean_eq (H J : JointLaw) (hJ : J ∈ compatibleLaws H) (t : Bool) :
    lawMean J t = lawMean H t := by
  have hJA : J ∈ AronowAudit.P022.compatibleLaws H := by
    simpa only [SAP.P022.Bridge.compatibleLaws_eq] using hJ
  calc
    lawMean J t = AronowAudit.P022.lawMean J t := (SAP.P022.Bridge.lawMean_eq J t).symm
    _ = AronowAudit.P022.lawMean H t := TailB_lawMean_eq_of_compatible H J hJA t
    _ = lawMean H t := SAP.P022.Bridge.lawMean_eq H t

theorem lawVariance_eq_of_compatible (H J : JointLaw) (hJ : J ∈ compatibleLaws H)
    (t : Bool) : lawVariance J t = lawVariance H t := by
  have hJA : J ∈ AronowAudit.P022.compatibleLaws H := by
    simpa only [SAP.P022.Bridge.compatibleLaws_eq] using hJ
  have hmarg := (TailB_compatibleLaws_iff_marginals H J).mp hJA
  have hmean := compatible_mean_eq H J hJ t
  have hcoord : (J : Measure (ℝ × ℝ)).map (coord t) =
      (H : Measure (ℝ × ℝ)).map (coord t) := by
    cases t
    · change (J : Measure (ℝ × ℝ)).map Prod.snd =
        (H : Measure (ℝ × ℝ)).map Prod.snd
      exact hmarg.2
    · change (J : Measure (ℝ × ℝ)).map Prod.fst =
        (H : Measure (ℝ × ℝ)).map Prod.fst
      exact hmarg.1
  let f : ℝ → ℝ := fun x => (x - lawMean H t) ^ 2
  have hf : Measurable f := by fun_prop
  have hmap (K : JointLaw) :
      (∫ p, f (coord t p) ∂(K : Measure (ℝ × ℝ))) =
        ∫ x, f x ∂((K : Measure (ℝ × ℝ)).map (coord t)) := by
    symm
    exact integral_map (coord_measurable t).aemeasurable hf.aestronglyMeasurable
  change (∫ p, (coord t p - lawMean J t) ^ 2 ∂(J : Measure (ℝ × ℝ))) =
    ∫ p, (coord t p - lawMean H t) ^ 2 ∂(H : Measure (ℝ × ℝ))
  rw [hmean]
  change (∫ p, f (coord t p) ∂(J : Measure (ℝ × ℝ))) =
    ∫ p, f (coord t p) ∂(H : Measure (ℝ × ℝ))
  rw [hmap J, hcoord, ← hmap H]

theorem mixLaw_nonsingular (J H : JointLaw) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hH : NonsingularLaw H) : NonsingularLaw (mixLaw J H w hw.le hw1) := by
  have hnonzero : ENNReal.ofReal w ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hw
  have hac : (H : Measure (ℝ × ℝ)) ≪ mixMeasure J H w := by
    have hs := Measure.absolutelyContinuous_smul (μ := (H : Measure (ℝ × ℝ))) hnonzero
    have hadd := hs.add_right (ENNReal.ofReal (1 - w) • (J : Measure (ℝ × ℝ)))
    simpa [mixMeasure, add_comm] using hadd
  intro a b c hab hae
  apply hH a b c hab
  exact hac.ae_le hae

theorem mixLaw_thirdMoments (J H : JointLaw) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hJ : LawThirdMomentsFinite J) (hH : LawThirdMomentsFinite H) :
    LawThirdMomentsFinite (mixLaw J H w hw hw1) := by
  intro t
  exact ((hJ t).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((hH t).smul_measure ENNReal.ofReal_ne_top)

theorem mixLaw_covariance (J H : JointLaw) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hJc : J ∈ compatibleLaws H) (hfunc : LawFunctionalsDefined H) :
    lawCovariance (mixLaw J H w hw hw1) =
      (1 - w) * lawCovariance J + w * lawCovariance H := by
  have hHc : H ∈ compatibleLaws H := by intro t x; rfl
  have hmJ := compatible_mean_eq H J hJc
  have hmM := compatible_mean_eq H (mixLaw J H w hw hw1)
    (mixLaw_compatible J H w hw hw1 hJc)
  let f : ℝ × ℝ → ℝ := fun p =>
    (p.1 - lawMean H true) * (p.2 - lawMean H false)
  have hIj : Integrable f (J : Measure (ℝ × ℝ)) := by
    have hi := (hfunc.1 J hJc).2
    simpa only [hmJ true, hmJ false, f] using hi
  have hIH : Integrable f (H : Measure (ℝ × ℝ)) := by
    exact (hfunc.1 H hHc).2
  change (∫ p, (p.1 - lawMean (mixLaw J H w hw hw1) true) *
        (p.2 - lawMean (mixLaw J H w hw hw1) false)
        ∂(mixLaw J H w hw hw1 : Measure (ℝ × ℝ))) =
    (1 - w) * (∫ p, (p.1 - lawMean J true) * (p.2 - lawMean J false)
      ∂(J : Measure (ℝ × ℝ))) +
    w * (∫ p, (p.1 - lawMean H true) * (p.2 - lawMean H false)
      ∂(H : Measure (ℝ × ℝ)))
  simp_rw [hmM, hmJ]
  change (∫ p, f p ∂mixMeasure J H w) =
    (1 - w) * (∫ p, f p ∂(J : Measure (ℝ × ℝ))) +
      w * (∫ p, f p ∂(H : Measure (ℝ × ℝ)))
  rw [mixMeasure, integral_add_measure
    (hIj.smul_measure ENNReal.ofReal_ne_top)
    (hIH.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hw,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1)]

theorem mixLaw_trueVariance_affine (J H : JointLaw) (θ ρ w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hJc : J ∈ compatibleLaws H) (hfunc : LawFunctionalsDefined H) :
    limitingTrueVariance (mixLaw J H w hw hw1) θ ρ =
      (1 - w) * limitingTrueVariance J θ ρ + w * limitingTrueVariance H θ ρ := by
  have hMc := mixLaw_compatible J H w hw hw1 hJc
  have hvarM t := lawVariance_eq_of_compatible H (mixLaw J H w hw hw1) hMc t
  have hvarJ t := lawVariance_eq_of_compatible H J hJc t
  have hcovM := mixLaw_covariance J H w hw hw1 hJc hfunc
  unfold limitingTrueVariance
  rw [hvarM true, hvarM false, hvarJ true, hvarJ false, hcovM]
  ring

end
end SAP.P022.WH.W1.P.T17_L4

open SAP.P022.WH.W1.P.T17_L4

theorem SAP.P022.WH.W1.T17_L4_proof : SAP.P022.WH.W1.T17_L4 := by
  intro hL3 H θ ρ hθ hθ1 hρ hρ1 hfunc hthird hns v hv hvU
  rcases hL3 H θ ρ hfunc hthird with ⟨hthirdCompat, hAtt⟩
  obtain ⟨A, hAc, hAcov⟩ := hAtt
  have hHc : H ∈ compatibleLaws H := by intro t x; rfl
  have hcovHle : lawCovariance H ≤ sSup (lawCovariance '' compatibleLaws H) :=
    le_csSup hfunc.2.2.1 ⟨H, hHc, rfl⟩
  let U : ℝ := limitingBound H θ ρ .H
  let s : ℝ := limitingTrueVariance H θ ρ
  have hgap : 0 ≤ U - s := by
    have heq : U - s = 2 * (sSup (lawCovariance '' compatibleLaws H) - lawCovariance H) := by
      dsimp [U, s]
      unfold limitingBound limitingTrueVariance
      simp only [ite_true]
      ring
    rw [heq]
    linarith
  have hAvar : limitingTrueVariance A θ ρ = U := by
    have hvar t := lawVariance_eq_of_compatible H A hAc t
    dsimp [U]
    unfold limitingTrueVariance limitingBound
    simp only [ite_true, hvar true, hvar false, hAcov]
  have hgapv : 0 < U - v := by dsimp [U]; linarith
  let w : ℝ := min (1 / 2) ((U - v) / (2 * (U - s + 1)))
  have hw : 0 < w := by
    dsimp [w]
    apply lt_min
    · norm_num
    · apply div_pos hgapv
      positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    have := min_le_left (1 / 2 : ℝ) ((U - v) / (2 * (U - s + 1)))
    norm_num at this ⊢
  have hwD : w * (U - s) ≤ (U - v) / 2 := by
    have hwb := min_le_right (1 / 2 : ℝ) ((U - v) / (2 * (U - s + 1)))
    have hD : 0 ≤ U - s := hgap
    have hratio : 0 ≤ (U - s) / (U - s + 1) ∧ (U - s) / (U - s + 1) ≤ 1 := by
      constructor
      · positivity
      · rw [div_le_one (by linarith : 0 < U - s + 1)]
        linarith
    have hfrac : (U - v) * (U - s) / (2 * (U - s + 1)) ≤ (U - v) / 2 := by
      calc
        (U - v) * (U - s) / (2 * (U - s + 1)) =
            ((U - v) / 2) * ((U - s) / (U - s + 1)) := by
              field_simp [ne_of_gt (by linarith : 0 < U - s + 1)]
        _ ≤ (U - v) / 2 :=
          mul_le_of_le_one_right (by positivity) hratio.2
    calc
      w * (U - s) ≤ ((U - v) / (2 * (U - s + 1))) * (U - s) :=
        mul_le_mul_of_nonneg_right hwb hD
      _ = (U - v) * (U - s) / (2 * (U - s + 1)) := by ring
      _ ≤ (U - v) / 2 := hfrac
  let M := mixLaw A H w hw.le hw1
  have hMc : M ∈ compatibleLaws H := mixLaw_compatible A H w hw.le hw1 hAc
  have hMthird : LawThirdMomentsFinite M :=
    mixLaw_thirdMoments A H w hw.le hw1 (hthirdCompat A hAc).1 hthird
  have hMns : NonsingularLaw M := mixLaw_nonsingular A H w hw hw1 hns
  have hMvar : limitingTrueVariance M θ ρ = (1 - w) * U + w * s := by
    have hAffine := mixLaw_trueVariance_affine A H θ ρ w hw.le hw1 hAc hfunc
    calc
      limitingTrueVariance M θ ρ = limitingTrueVariance (mixLaw A H w hw.le hw1) θ ρ := rfl
      _ = (1 - w) * limitingTrueVariance A θ ρ + w * limitingTrueVariance H θ ρ := hAffine
      _ = (1 - w) * U + w * s := by rw [hAvar]
  have hMv : v < limitingTrueVariance M θ ρ := by
    rw [hMvar]
    have heq : (1 - w) * U + w * s = U - w * (U - s) := by ring
    rw [heq]
    nlinarith
  exact ⟨M, hMc, hMthird, hMns, hMv⟩
