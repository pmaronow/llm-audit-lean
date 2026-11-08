import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace SAP.P046.WH.W1.P.T4_L3

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
open AronowAudit.P046
open AronowAudit.P046.RegressionExample

private lemma score_measurable : Measurable SAP.P046.RegressionExample.score :=
  (measurable_of_countable SAP.P046.RegressionExample.scoreL).comp
    (measurable_threshold id (fun _ => (1/2 : ℝ)) measurable_id measurable_const)

private lemma prediction_measurable (theta : ℝ) : Measurable (SAP.P046.RegressionExample.prediction theta) :=
  (measurable_of_countable (SAP.P046.RegressionExample.predictionL theta)).comp
    (measurable_threshold id (fun _ => (1/2 : ℝ)) measurable_id measurable_const)

private lemma bit_and (l z : Bool) : AronowAudit.P046.bit (l && z) =
    AronowAudit.P046.bit l * AronowAudit.P046.bit z := by
  cases l <;> cases z <;> norm_num [AronowAudit.P046.bit]

@[simp] private lemma sap_bit_eq_audit_bit (b : Bool) :
    SAP.P046.bit b = AronowAudit.P046.bit b := by
  cases b <;> rfl

private lemma score_cases (w : ℝ) :
    SAP.P046.RegressionExample.score w = if w ≤ (1/2 : ℝ) then 1/4 else 3/4 := by
  unfold SAP.P046.RegressionExample.score
  by_cases hw : w ≤ (1/2 : ℝ) <;>
    simp [SAP.P046.RegressionExample.scoreL, hw]

private lemma wholeH_measurable : Measurable wholeH :=
  (measurable_X.mul measurable_Y).div (score_measurable.comp measurable_fst)

private lemma wholeA_measurable : Measurable wholeA :=
  ((measurable_X.mul (measurable_Y.sub
      ((prediction_measurable 0).comp measurable_fst))).div
    (score_measurable.comp measurable_fst)).add
      ((prediction_measurable 0).comp measurable_fst)

private lemma wholeH_generate (w u v : ℝ) :
    wholeH (SAP.P046.RegressionExample.generate ((w,u),v)) =
      H (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
        (decide (v ≤ SAP.P046.RegressionExample.score w)) := by
  let l := decide (w ≤ (1/2 : ℝ))
  let z := decide (u ≤ (1/10 : ℝ))
  let x := decide (v ≤ SAP.P046.RegressionExample.score w)
  have hg : SAP.P046.RegressionExample.generate ((w,u),v) = (w,(x,(l && z,l && z))) := rfl
  have hy : Y (w,(x,(l && z,l && z))) = AronowAudit.P046.bit l * AronowAudit.P046.bit z := by
    change (1 - SAP.P046.bit x) * SAP.P046.bit (l && z) +
      SAP.P046.bit x * SAP.P046.bit (l && z) = _
    calc
      _ = SAP.P046.bit (l && z) := by ring
      _ = AronowAudit.P046.bit (l && z) := sap_bit_eq_audit_bit _
      _ = AronowAudit.P046.bit l * AronowAudit.P046.bit z := bit_and l z
  rw [hg]
  simp only [wholeH, W, X]
  rw [hy]
  rfl

private lemma wholeA_generate (w u v : ℝ) :
    wholeA (SAP.P046.RegressionExample.generate ((w,u),v)) =
      A (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
        (decide (v ≤ SAP.P046.RegressionExample.score w)) := by
  let l := decide (w ≤ (1/2 : ℝ))
  let z := decide (u ≤ (1/10 : ℝ))
  let x := decide (v ≤ SAP.P046.RegressionExample.score w)
  have hg : SAP.P046.RegressionExample.generate ((w,u),v) = (w,(x,(l && z,l && z))) := rfl
  have hy : Y (w,(x,(l && z,l && z))) = AronowAudit.P046.bit l * AronowAudit.P046.bit z := by
    change (1 - SAP.P046.bit x) * SAP.P046.bit (l && z) +
      SAP.P046.bit x * SAP.P046.bit (l && z) = _
    calc
      _ = SAP.P046.bit (l && z) := by ring
      _ = AronowAudit.P046.bit (l && z) := sap_bit_eq_audit_bit _
      _ = AronowAudit.P046.bit l * AronowAudit.P046.bit z := bit_and l z
  rw [hg]
  simp only [wholeA, W, X]
  rw [hy]
  rfl

private lemma wholeH_regressionSample (w : ℝ) (z x : Bool) :
    wholeH (wholeRegressionSample (n := 1) (fun _ => w) (fun _ => z)
      (fun _ => x) 0) =
      H (decide (w ≤ (1/2 : ℝ))) z x := by
  let l := decide (w ≤ (1/2 : ℝ))
  have ho : wholeRegressionSample (n := 1) (fun _ => w) (fun _ => z)
      (fun _ => x) 0 = (w,(x,(l && z,l && z))) := rfl
  have hy : Y (w,(x,(l && z,l && z))) =
      AronowAudit.P046.bit l * AronowAudit.P046.bit z := by
    change (1 - SAP.P046.bit x) * SAP.P046.bit (l && z) +
      SAP.P046.bit x * SAP.P046.bit (l && z) = _
    calc
      _ = SAP.P046.bit (l && z) := by ring
      _ = AronowAudit.P046.bit (l && z) := sap_bit_eq_audit_bit _
      _ = AronowAudit.P046.bit l * AronowAudit.P046.bit z := bit_and l z
  rw [ho]
  simp only [wholeH, W, X]
  rw [hy]
  rfl

private lemma wholeA_regressionSample (w : ℝ) (z x : Bool) :
    wholeA (wholeRegressionSample (n := 1) (fun _ => w) (fun _ => z)
      (fun _ => x) 0) =
      A (decide (w ≤ (1/2 : ℝ))) z x := by
  let l := decide (w ≤ (1/2 : ℝ))
  have ho : wholeRegressionSample (n := 1) (fun _ => w) (fun _ => z)
      (fun _ => x) 0 = (w,(x,(l && z,l && z))) := rfl
  have hy : Y (w,(x,(l && z,l && z))) =
      AronowAudit.P046.bit l * AronowAudit.P046.bit z := by
    change (1 - SAP.P046.bit x) * SAP.P046.bit (l && z) +
      SAP.P046.bit x * SAP.P046.bit (l && z) = _
    calc
      _ = SAP.P046.bit (l && z) := by ring
      _ = AronowAudit.P046.bit (l && z) := sap_bit_eq_audit_bit _
      _ = AronowAudit.P046.bit l * AronowAudit.P046.bit z := bit_and l z
  rw [ho]
  simp only [wholeA, W, X]
  rw [hy]
  rfl

private lemma finite_memLp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] (ν : Measure A) [IsFiniteMeasure ν]
    (f : B → ℝ) (g : A → B) (hg : Measurable g) (p : ℝ≥0∞) :
    MemLp (fun a => f (g a)) p ν := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun b => ‖f b‖)
  exact MemLp.of_bound ((measurable_of_countable f).comp hg).aestronglyMeasurable C
    (ae_of_all _ (fun a => hC (g a)))

/-- Integration of every scalar function constant on the eight generated cells. -/
private lemma table_integral (f : Unit → ℝ) (hf : Measurable f)
    (g : Bool → Bool → Bool → ℝ)
    (he : ∀ w u v, f (SAP.P046.RegressionExample.generate ((w,u),v)) =
      g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
        (decide (v ≤ SAP.P046.RegressionExample.score w))) :
    (∫ o, f o ∂ (SAP.P046.RegressionExample.study.law)) = atomE g := by
  letI : IsProbabilityMeasure AronowAudit.P046.unitUniform :=
    AronowAudit.P046.unitUniform_probability
  let ν := (AronowAudit.P046.unitUniform.prod AronowAudit.P046.unitUniform).prod
    AronowAudit.P046.unitUniform
  haveI : IsFiniteMeasure ν := by infer_instance
  have ml := AronowAudit.P046.measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.1.1)
    (fun _ => (1/2 : ℝ)) measurable_fst.fst measurable_const
  have mz := AronowAudit.P046.measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.1.2)
    (fun _ => (1/10 : ℝ)) measurable_fst.snd measurable_const
  have mx := AronowAudit.P046.measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.2)
    (fun z => SAP.P046.RegressionExample.score z.1.1) measurable_snd (score_measurable.comp measurable_fst.fst)
  have hi : Integrable (fun z : (ℝ × ℝ) × ℝ => f (SAP.P046.RegressionExample.generate z)) ν := by
    have hb := finite_memLp ν
      (fun b : Bool × Bool × Bool => g b.1 b.2.1 b.2.2)
      (fun z => (decide (z.1.1 ≤ (1/2 : ℝ)), decide (z.1.2 ≤ (1/10 : ℝ)),
        decide (z.2 ≤ SAP.P046.RegressionExample.score z.1.1))) (ml.prodMk (mz.prodMk mx)) 1
    simpa only [he] using memLp_one_iff_integrable.1 hb
  change (∫ o, f o ∂Measure.map SAP.P046.RegressionExample.generate ν) = _
  have hmap : (∫ o, f o ∂Measure.map SAP.P046.RegressionExample.generate ν) =
      ∫ z, f (SAP.P046.RegressionExample.generate z) ∂ν :=
    integral_map measurable_generate.aemeasurable hf.aestronglyMeasurable
  rw [hmap]
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  simp_rw [he]
  have hp (w : ℝ) : 0 ≤ SAP.P046.RegressionExample.score w ∧ SAP.P046.RegressionExample.score w ≤ 1 := by
    rw [score_cases]
    split_ifs <;> norm_num
  have hv (w u : ℝ) :
      (∫ v, g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
        (decide (v ≤ SAP.P046.RegressionExample.score w)) ∂AronowAudit.P046.unitUniform) =
      bernE (SAP.P046.RegressionExample.score w) (g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))) :=
    AronowAudit.P046.unitUniform_bernE (SAP.P046.RegressionExample.score w) (hp w).1 (hp w).2 _
  simp_rw [hv]
  have hu (w : ℝ) :
      (∫ u, bernE (SAP.P046.RegressionExample.score w) (g (decide (w ≤ (1/2 : ℝ)))
        (decide (u ≤ (1/10 : ℝ)))) ∂AronowAudit.P046.unitUniform) =
      bernE (1/10) (fun z => bernE (SAP.P046.RegressionExample.score w)
        (g (decide (w ≤ (1/2 : ℝ))) z)) :=
    AronowAudit.P046.unitUniform_bernE (1/10) (by norm_num) (by norm_num)
      (fun z => bernE (SAP.P046.RegressionExample.score w) (g (decide (w ≤ (1/2 : ℝ))) z))
  simp_rw [hu]
  change (∫ w, bernE (1/10) (fun z => bernE (SAP.P046.RegressionExample.scoreL (decide (w ≤ (1/2 : ℝ))))
    (fun x => g (decide (w ≤ (1/2 : ℝ))) z x)) ∂AronowAudit.P046.unitUniform) = _
  rw [AronowAudit.P046.unitUniform_bernE (1/2) (by norm_num) (by norm_num)
    (fun l => bernE (1/10) (fun z => bernE (SAP.P046.RegressionExample.scoreL l) (fun x => g l z x)))]
  norm_num [bernE, atomE, SAP.P046.RegressionExample.scoreL]
  ring

private lemma table_mass (s : Set Unit) (hs : MeasurableSet s)
    (g : Bool → Bool → Bool → ℝ)
    (he : ∀ w u v, s.indicator (fun _ : Unit => (1 : ℝ))
        (SAP.P046.RegressionExample.generate ((w,u),v)) =
      g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
        (decide (v ≤ SAP.P046.RegressionExample.score w))) :
    SAP.P046.RegressionExample.study.law s = ENNReal.ofReal (atomE g) := by
  letI := probability_continuity_mean.1
  haveI : IsZeroOrProbabilityMeasure SAP.P046.RegressionExample.study.law :=
    ⟨Or.inr probability_continuity_mean.1.measure_univ⟩
  haveI : IsFiniteMeasure SAP.P046.RegressionExample.study.law := by infer_instance
  have hi := table_integral (s.indicator (fun _ : Unit => (1 : ℝ)))
    (measurable_const.indicator hs) g he
  change (∫ o, s.indicator (1 : Unit → ℝ) o ∂ (SAP.P046.RegressionExample.study.law)) = _ at hi
  rw [integral_indicator_one hs] at hi
  calc
    SAP.P046.RegressionExample.study.law s = ENNReal.ofReal (SAP.P046.RegressionExample.study.law.real s) :=
      (ofReal_measureReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal (atomE g) := congrArg ENNReal.ofReal hi

private lemma mass_high :
    SAP.P046.RegressionExample.study.law {o | 1/2 < W o} = ENNReal.ofReal (1/2 : ℝ) := by
  let s : Set Unit := {o | 1/2 < W o}
  let g : Bool → Bool → Bool → ℝ := fun l _ _ => if l then 0 else 1
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const measurable_fst
  have he : ∀ w u v, s.indicator (fun _ : Unit => (1 : ℝ))
      (SAP.P046.RegressionExample.generate ((w,u),v)) =
        g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
          (decide (v ≤ SAP.P046.RegressionExample.score w)) := by
    intro w u v
    have hp : SAP.P046.RegressionExample.score w =
        (if w ≤ (1/2 : ℝ) then 1/4 else 3/4) :=
      score_cases w
    by_cases hw : w ≤ (1/2 : ℝ)
    · have dhw := decide_eq_true hw
      simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, W, hw, dhw]
    · have dhw : decide (w ≤ (1/2 : ℝ)) = false :=
        decide_eq_false_iff_not.mpr hw
      simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, W, hw, dhw]
  have hm := table_mass s hs g he
  have hv : atomE g = 1/2 := by norm_num [g, atomE, bernE]
  simpa [s] using hm.trans (congrArg ENNReal.ofReal hv)

private lemma mass_low_control :
    SAP.P046.RegressionExample.study.law {o | W o ≤ 1/2 ∧ X o = 0} = ENNReal.ofReal (3/8 : ℝ) := by
  let s : Set Unit := {o | W o ≤ 1/2 ∧ X o = 0}
  let g : Bool → Bool → Bool → ℝ := fun l _ x => if l && !x then 1 else 0
  have hs : MeasurableSet s := by
    exact (measurableSet_Iic.preimage measurable_fst).inter
      (measurableSet_eq_fun measurable_X measurable_const)
  have he : ∀ w u v, s.indicator (fun _ : Unit => (1 : ℝ))
      (SAP.P046.RegressionExample.generate ((w,u),v)) =
        g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
          (decide (v ≤ SAP.P046.RegressionExample.score w)) := by
    intro w u v
    have hp : SAP.P046.RegressionExample.score w =
        (if w ≤ (1/2 : ℝ) then 1/4 else 3/4) := score_cases w
    by_cases hw : w ≤ (1/2 : ℝ)
    · have dhw := decide_eq_true hw
      by_cases hx : v ≤ SAP.P046.RegressionExample.score w
      · have dhx := decide_eq_true hx
        simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, SAP.P046.bit, hw, hx, dhw, dhx, hp]
      · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
        simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, SAP.P046.bit, hw, hx, dhw, dhx, hp]
    · have dhw : decide (w ≤ (1/2 : ℝ)) = false := decide_eq_false_iff_not.mpr hw
      by_cases hx : v ≤ SAP.P046.RegressionExample.score w
      · have dhx := decide_eq_true hx
        simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, SAP.P046.bit, hw, hx, dhw, dhx, hp]
      · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
        simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, SAP.P046.bit, hw, hx, dhw, dhx, hp]
  have hm := table_mass s hs g he
  have hv : atomE g = 3/8 := by norm_num [g, atomE, bernE]
  simpa [s] using hm.trans (congrArg ENNReal.ofReal hv)

private lemma mass_low_treated_yzero :
    SAP.P046.RegressionExample.study.law {o | W o ≤ 1/2 ∧ X o = 1 ∧ Y1 o = 0} =
      ENNReal.ofReal (9/80 : ℝ) := by
  let s : Set Unit := {o | W o ≤ 1/2 ∧ X o = 1 ∧ Y1 o = 0}
  let g : Bool → Bool → Bool → ℝ := fun l z x => if l && !z && x then 1 else 0
  have hs : MeasurableSet s := by
    exact (measurableSet_Iic.preimage measurable_fst).inter
      ((measurableSet_eq_fun measurable_X measurable_const).inter
        (measurableSet_eq_fun measurable_Y1 measurable_const))
  have he : ∀ w u v, s.indicator (fun _ : Unit => (1 : ℝ))
      (SAP.P046.RegressionExample.generate ((w,u),v)) =
        g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
          (decide (v ≤ SAP.P046.RegressionExample.score w)) := by
    intro w u v
    have hp : SAP.P046.RegressionExample.score w = (if w ≤ (1/2 : ℝ) then 1/4 else 3/4) :=
      score_cases w
    by_cases hw : w ≤ (1/2 : ℝ)
    · have dhw := decide_eq_true hw
      by_cases hu : u ≤ (1/10 : ℝ)
      · have dhu := decide_eq_true hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
      · have dhu : decide (u ≤ (1/10 : ℝ)) = false := decide_eq_false_iff_not.mpr hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
    · have dhw : decide (w ≤ (1/2 : ℝ)) = false := decide_eq_false_iff_not.mpr hw
      by_cases hu : u ≤ (1/10 : ℝ)
      · have dhu := decide_eq_true hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
      · have dhu : decide (u ≤ (1/10 : ℝ)) = false := decide_eq_false_iff_not.mpr hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
  have hm := table_mass s hs g he
  have hv : atomE g = 9/80 := by norm_num [g, atomE, bernE]
  simpa [s] using hm.trans (congrArg ENNReal.ofReal hv)

private lemma mass_low_treated_yone :
    SAP.P046.RegressionExample.study.law {o | W o ≤ 1/2 ∧ X o = 1 ∧ Y1 o = 1} =
      ENNReal.ofReal (1/80 : ℝ) := by
  let s : Set Unit := {o | W o ≤ 1/2 ∧ X o = 1 ∧ Y1 o = 1}
  let g : Bool → Bool → Bool → ℝ := fun l z x => if l && z && x then 1 else 0
  have hs : MeasurableSet s := by
    exact (measurableSet_Iic.preimage measurable_fst).inter
      ((measurableSet_eq_fun measurable_X measurable_const).inter
        (measurableSet_eq_fun measurable_Y1 measurable_const))
  have he : ∀ w u v, s.indicator (fun _ : Unit => (1 : ℝ))
      (SAP.P046.RegressionExample.generate ((w,u),v)) =
        g (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ)))
          (decide (v ≤ SAP.P046.RegressionExample.score w)) := by
    intro w u v
    have hp : SAP.P046.RegressionExample.score w = (if w ≤ (1/2 : ℝ) then 1/4 else 3/4) :=
      score_cases w
    by_cases hw : w ≤ (1/2 : ℝ)
    · have dhw := decide_eq_true hw
      by_cases hu : u ≤ (1/10 : ℝ)
      · have dhu := decide_eq_true hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
      · have dhu : decide (u ≤ (1/10 : ℝ)) = false := decide_eq_false_iff_not.mpr hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
    · have dhw : decide (w ≤ (1/2 : ℝ)) = false := decide_eq_false_iff_not.mpr hw
      by_cases hu : u ≤ (1/10 : ℝ)
      · have dhu := decide_eq_true hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
      · have dhu : decide (u ≤ (1/10 : ℝ)) = false := decide_eq_false_iff_not.mpr hu
        by_cases hx : v ≤ SAP.P046.RegressionExample.score w
        · have dhx := decide_eq_true hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
        · have dhx : decide (v ≤ SAP.P046.RegressionExample.score w) = false := decide_eq_false_iff_not.mpr hx
          simp_all [s, g, SAP.P046.RegressionExample.generate, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL, W, X, Y1, SAP.P046.bit, hw, hu, hx, dhw, dhu, dhx, hp]
  have hm := table_mass s hs g he
  have hv : atomE g = 1/80 := by norm_num [g, atomE, bernE]
  simpa [s] using hm.trans (congrArg ENNReal.ofReal hv)

private lemma wholeH_bound : ∀ o, ‖wholeH o‖ ≤ 4 := by
  rintro ⟨w,x,y0,y1⟩
  by_cases hw : w ≤ (1/2 : ℝ)
  · have dhw := decide_eq_true hw
    cases x <;> cases y0 <;> cases y1 <;>
      norm_num [wholeH, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL,
        W, X, Y, Y0, Y1, AronowAudit.P046.bit, htTerm, hw, dhw]
  · have dhw : decide (w ≤ (1/2 : ℝ)) = false := decide_eq_false_iff_not.mpr hw
    cases x <;> cases y0 <;> cases y1 <;>
      norm_num [wholeH, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL,
        W, X, Y, Y0, Y1, AronowAudit.P046.bit, htTerm, hw, dhw]

private lemma wholeA_bound : ∀ o, ‖wholeA o‖ ≤ 3 := by
  rintro ⟨w,x,y0,y1⟩
  by_cases hw : w ≤ (1/2 : ℝ)
  · have dhw := decide_eq_true hw
    cases x <;> cases y0 <;> cases y1 <;>
      norm_num [wholeA, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL,
        SAP.P046.RegressionExample.prediction, SAP.P046.RegressionExample.predictionL,
        W, X, Y, Y0, Y1, AronowAudit.P046.bit, adjustedTerm, hw, dhw]
  · have dhw : decide (w ≤ (1/2 : ℝ)) = false := decide_eq_false_iff_not.mpr hw
    cases x <;> cases y0 <;> cases y1 <;>
      norm_num [wholeA, SAP.P046.RegressionExample.score, SAP.P046.RegressionExample.scoreL,
        SAP.P046.RegressionExample.prediction, SAP.P046.RegressionExample.predictionL,
        W, X, Y, Y0, Y1, AronowAudit.P046.bit, adjustedTerm, hw, dhw]

private lemma wholeH_L2 : MemLp wholeH 2 SAP.P046.RegressionExample.study.law := by
  letI := probability_continuity_mean.1
  haveI : IsZeroOrProbabilityMeasure SAP.P046.RegressionExample.study.law :=
    ⟨Or.inr probability_continuity_mean.1.measure_univ⟩
  haveI : IsFiniteMeasure SAP.P046.RegressionExample.study.law := by infer_instance
  exact MemLp.of_bound wholeH_measurable.aestronglyMeasurable 4
    (ae_of_all _ wholeH_bound)

private lemma wholeA_L2 : MemLp wholeA 2 SAP.P046.RegressionExample.study.law := by
  letI := probability_continuity_mean.1
  haveI : IsZeroOrProbabilityMeasure SAP.P046.RegressionExample.study.law :=
    ⟨Or.inr probability_continuity_mean.1.measure_univ⟩
  haveI : IsFiniteMeasure SAP.P046.RegressionExample.study.law := by infer_instance
  exact MemLp.of_bound wholeA_measurable.aestronglyMeasurable 3
    (ae_of_all _ wholeA_bound)

private lemma wholeH_sq_L2 : MemLp (fun o => wholeH o ^ 2) 1 SAP.P046.RegressionExample.study.law := by
  letI := probability_continuity_mean.1
  haveI : IsZeroOrProbabilityMeasure SAP.P046.RegressionExample.study.law :=
    ⟨Or.inr probability_continuity_mean.1.measure_univ⟩
  haveI : IsFiniteMeasure SAP.P046.RegressionExample.study.law := by infer_instance
  apply MemLp.of_bound ((wholeH_measurable.pow_const 2).aestronglyMeasurable) 16
  exact ae_of_all _ (fun o => by
    have h := wholeH_bound o
    rw [Real.norm_eq_abs] at h
    have hn := abs_nonneg (wholeH o)
    have hs : |wholeH o| ^ 2 ≤ 16 := by nlinarith
    simpa [Real.norm_eq_abs, sq_abs] using hs)

private lemma wholeA_sq_L2 : MemLp (fun o => wholeA o ^ 2) 1 SAP.P046.RegressionExample.study.law := by
  letI := probability_continuity_mean.1
  haveI : IsZeroOrProbabilityMeasure SAP.P046.RegressionExample.study.law :=
    ⟨Or.inr probability_continuity_mean.1.measure_univ⟩
  haveI : IsFiniteMeasure SAP.P046.RegressionExample.study.law := by infer_instance
  apply MemLp.of_bound ((wholeA_measurable.pow_const 2).aestronglyMeasurable) 9
  exact ae_of_all _ (fun o => by
    have h := wholeA_bound o
    rw [Real.norm_eq_abs] at h
    have hn := abs_nonneg (wholeA o)
    have hs : |wholeA o| ^ 2 ≤ 9 := by nlinarith
    simpa [Real.norm_eq_abs, sq_abs] using hs)

private lemma wholeH_mean : (∫ o, wholeH o ∂ (SAP.P046.RegressionExample.study.law)) = 1/20 := by
  rw [table_integral wholeH wholeH_measurable H wholeH_generate]
  exact atom_moments.1

private lemma wholeA_mean : (∫ o, wholeA o ∂ (SAP.P046.RegressionExample.study.law)) = 1/20 := by
  rw [table_integral wholeA wholeA_measurable A wholeA_generate]
  exact atom_moments.2.1

private lemma wholeH_second :
    (∫ o, wholeH o ^ 2 ∂ (SAP.P046.RegressionExample.study.law)) = 1/5 := by
  rw [table_integral (fun o => wholeH o ^ 2)
    (wholeH_measurable.pow_const 2) (fun l z x => H l z x ^ 2)
    (fun w u v => by rw [wholeH_generate])]
  exact atom_moments.2.2.1

private lemma wholeA_second :
    (∫ o, wholeA o ^ 2 ∂ (SAP.P046.RegressionExample.study.law)) = 17/40 := by
  rw [table_integral (fun o => wholeA o ^ 2)
    (wholeA_measurable.pow_const 2) (fun l z x => A l z x ^ 2)
    (fun w u v => by rw [wholeA_generate])]
  exact atom_moments.2.2.2

private lemma wholeH_variance : variance wholeH SAP.P046.RegressionExample.study.law = 79/400 := by
  rw [variance_eq_integral wholeH_measurable.aemeasurable, wholeH_mean]
  rw [table_integral (fun o => (wholeH o - 1/20)^2)
    ((wholeH_measurable.sub_const _).pow_const 2)
    (fun l z x => (H l z x - 1/20)^2)
    (fun w u v => by rw [wholeH_generate])]
  exact atom_variances.1

private lemma wholeA_variance : variance wholeA SAP.P046.RegressionExample.study.law = 169/400 := by
  rw [variance_eq_integral wholeA_measurable.aemeasurable, wholeA_mean]
  rw [table_integral (fun o => (wholeA o - 1/20)^2)
    ((wholeA_measurable.sub_const _).pow_const 2)
    (fun l z x => (A l z x - 1/20)^2)
    (fun w u v => by rw [wholeA_generate])]
  exact atom_variances.2.1

private lemma y1_generate (w u v : ℝ) :
    Y1 (SAP.P046.RegressionExample.generate ((w,u),v)) =
      outcomeL (decide (w ≤ (1/2 : ℝ))) (decide (u ≤ (1/10 : ℝ))) := by
  cases hl : decide (w ≤ (1/2 : ℝ)) <;> cases hz : decide (u ≤ (1/10 : ℝ)) <;>
    norm_num [Y1, SAP.P046.RegressionExample.generate, outcomeL, AronowAudit.P046.bit, SAP.P046.bit, hl, hz]

private lemma y1_mean : (∫ o, Y1 o ∂ (SAP.P046.RegressionExample.study.law)) = 1/20 := by
  rw [table_integral Y1 measurable_Y1 (fun l z _ => outcomeL l z) y1_generate]
  norm_num [atomE, bernE, outcomeL, AronowAudit.P046.bit, SAP.P046.bit]

private lemma y1_variance : variance Y1 SAP.P046.RegressionExample.study.law = 19/400 := by
  rw [variance_eq_integral measurable_Y1.aemeasurable, y1_mean]
  rw [table_integral (fun o => (Y1 o - 1/20)^2)
    ((measurable_Y1.sub_const _).pow_const 2)
    (fun l z _ => (outcomeL l z - 1/20)^2)
    (fun w u v => by rw [y1_generate])]
  norm_num [atomE, bernE, outcomeL, AronowAudit.P046.bit, SAP.P046.bit]

/-- The pointwise scalar table generated by the split and the two Boolean bits. -/
private lemma pointwise_table : ∀ (w : ℝ) (z x : Bool),
    let o := wholeRegressionSample (n := 1) (fun _ => w) (fun _ => z) (fun _ => x) 0
    (if w ≤ 1/2 then
        wholeH o = 4 * bit x * bit z ∧
          wholeA o = 4 * bit x * bit z + (1/2 : ℝ) * (1 - 4 * bit x)
      else wholeH o = 0 ∧ wholeA o = 0) := by
  intro w z x
  dsimp only
  rw [wholeH_regressionSample, wholeA_regressionSample]
  by_cases hw : w ≤ (1/2 : ℝ)
  · have dhw := decide_eq_true hw
    simp only [if_pos hw, dhw]
    cases z <;> cases x <;>
      norm_num [H, A, AronowAudit.P046.htTerm, AronowAudit.P046.adjustedTerm, outcomeL,
        SAP.P046.RegressionExample.scoreL, SAP.P046.RegressionExample.predictionL,
        AronowAudit.P046.RegressionExample.scoreL, AronowAudit.P046.RegressionExample.predictionL, AronowAudit.P046.bit, SAP.P046.bit] <;> ring_nf
  · have dhw : decide (w ≤ (1/2 : ℝ)) = false := decide_eq_false_iff_not.mpr hw
    simp only [if_neg hw, dhw]
    norm_num [H, A, AronowAudit.P046.htTerm, AronowAudit.P046.adjustedTerm, outcomeL,
      SAP.P046.RegressionExample.scoreL, SAP.P046.RegressionExample.predictionL,
      AronowAudit.P046.RegressionExample.scoreL, AronowAudit.P046.RegressionExample.predictionL, AronowAudit.P046.bit, SAP.P046.bit]

private lemma table_ae : ∀ᵐ o ∂SAP.P046.RegressionExample.study.law,
    (1 / 2 < W o → wholeH o = 0 ∧ wholeA o = 0) ∧
    (W o ≤ 1 / 2 ∧ X o = 0 → wholeA o = 1 / 2) ∧
    (W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 0 → wholeA o = -3 / 2) ∧
    (W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 1 → wholeA o = 5 / 2) ∧
    0 ≤ wholeH o ∧ wholeH o ≤ 4 ∧ -3 / 2 ≤ wholeA o ∧ wholeA o ≤ 5 / 2 := by
  let P : Unit → Prop := fun o =>
    (1 / 2 < W o → wholeH o = 0 ∧ wholeA o = 0) ∧
    (W o ≤ 1 / 2 ∧ X o = 0 → wholeA o = 1 / 2) ∧
    (W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 0 → wholeA o = -3 / 2) ∧
    (W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 1 → wholeA o = 5 / 2) ∧
    0 ≤ wholeH o ∧ wholeH o ≤ 4 ∧ -3 / 2 ≤ wholeA o ∧ wholeA o ≤ 5 / 2
  have hset : MeasurableSet {o | P o} := by
    dsimp [P]
    have hH : Measurable wholeH := wholeH_measurable
    have hA : Measurable wholeA := wholeA_measurable
    have hW : Measurable W := measurable_fst
    have hX : Measurable X := measurable_X
    have hY1 : Measurable Y1 := measurable_Y1
    measurability
  apply (ae_map_iff measurable_generate.aemeasurable hset).2
  apply ae_of_all
  intro q
  rcases q with ⟨⟨w,u⟩,v⟩
  let z := decide (u ≤ (1/10 : ℝ))
  let x := decide (v ≤ SAP.P046.RegressionExample.score w)
  change P (wholeRegressionSample (n := 1) (fun _ => w) (fun _ => z) (fun _ => x) 0)
  have htable := pointwise_table w z x
  dsimp [P]
  rw [wholeH_regressionSample, wholeA_regressionSample]
  by_cases hw : w ≤ (1/2 : ℝ)
  · cases z <;> cases x <;>
      simp_all [wholeRegressionSample, W, X, Y1, SAP.P046.bit, AronowAudit.P046.bit, hw, htable, H, A,
        AronowAudit.P046.htTerm, AronowAudit.P046.adjustedTerm, outcomeL,
        AronowAudit.P046.RegressionExample.scoreL,
        AronowAudit.P046.RegressionExample.predictionL] <;> norm_num
  · have hhigh : ¬ w ≤ (1/2 : ℝ) := hw
    cases z <;> cases x <;>
      simp_all [wholeRegressionSample, W, X, Y1, SAP.P046.bit, AronowAudit.P046.bit, hw, hhigh, htable, H, A,
        AronowAudit.P046.htTerm, AronowAudit.P046.adjustedTerm, outcomeL,
        AronowAudit.P046.RegressionExample.scoreL,
        AronowAudit.P046.RegressionExample.predictionL] <;> norm_num <;> simp [if_neg (not_le_of_gt hw)] <;> norm_num

theorem proof_internal : SAP.P046.WH.W1.T4_L3 := by
  letI := probability_continuity_mean.1
  haveI : IsZeroOrProbabilityMeasure SAP.P046.RegressionExample.study.law :=
    ⟨Or.inr probability_continuity_mean.1.measure_univ⟩
  haveI : IsFiniteMeasure SAP.P046.RegressionExample.study.law := by infer_instance
  refine ⟨pointwise_table, table_ae, mass_high, mass_low_control,
    mass_low_treated_yzero, mass_low_treated_yone,
    wholeH_L2.integrable (by norm_num), wholeA_L2.integrable (by norm_num),
    wholeH_sq_L2.integrable (by norm_num), wholeA_sq_L2.integrable (by norm_num),
    wholeH_mean, wholeA_mean, wholeH_second, wholeA_second,
    wholeH_variance, wholeA_variance, y1_variance⟩

end
end SAP.P046.WH.W1.P.T4_L3


theorem SAP.P046.WH.W1.T4_L3_proof : SAP.P046.WH.W1.T4_L3 :=
  SAP.P046.WH.W1.P.T4_L3.proof_internal
