import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectFullIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Exact whole-position integrals of the limiting donor-count kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem marked_exp_abs_integral {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, Real.exp (-c*|t|)) = 2/c := by
  rw [integral_comp_abs (f := fun t => Real.exp (-c*t)),marked_exp_tail hc]
  simp only [mul_zero,Real.exp_zero]
  ring

/-- The overlap is nonnegative and is bounded by each query distance. -/
theorem marked_directional_overlap_bounds (t u : ℝ) :
    0 ≤ markedDirectionalOverlap t u ∧ markedDirectionalOverlap t u ≤ |t| ∧
      markedDirectionalOverlap t u ≤ |u| := by
  have ht : max t 0+max (-t) 0 = |t| := by
    rcases le_total 0 t with h | h
    · simp [max_eq_left h,max_eq_right (neg_nonpos.mpr h),abs_of_nonneg h]
    · simp [max_eq_right h,max_eq_left (neg_nonneg.mpr h),abs_of_nonpos h]
  have hu : max u 0+max (-u) 0 = |u| := by
    rcases le_total 0 u with h | h
    · simp [max_eq_left h,max_eq_right (neg_nonpos.mpr h),abs_of_nonneg h]
    · simp [max_eq_right h,max_eq_left (neg_nonneg.mpr h),abs_of_nonpos h]
  refine ⟨add_nonneg (le_min (le_max_right _ _) (le_max_right _ _))
    (le_min (le_max_right _ _) (le_max_right _ _)),?_,?_⟩
  · exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans_eq ht
  · exact (add_le_add (min_le_right _ _) (min_le_right _ _)).trans_eq hu

def markedSignedSurvival (d s t u : ℝ) : ℝ :=
  Real.exp (-d*(s*(|t|+|u|)-s^2*markedDirectionalOverlap t u))

theorem marked_signed_survival_continuous (d s : ℝ) :
    Continuous (fun q : ℝ × ℝ => markedSignedSurvival d s q.1 q.2) := by
  unfold markedSignedSurvival markedDirectionalOverlap
  fun_prop

theorem marked_signed_survival_envelope {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hs1 : s ≤ 1)
    (t u : ℝ) :
    |markedSignedSurvival d s t u| ≤ Real.exp (-(d*s/2)*(|t|+|u|)) := by
  obtain ⟨hH0,hHt,hHu⟩ := marked_directional_overlap_bounds t u
  have hH : markedDirectionalOverlap t u ≤ (|t|+|u|)/2 := by linarith
  have hs2 : s^2 ≤ s := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hs2 hH0
  have h2 := mul_le_mul_of_nonneg_left hH hs.le
  rw [markedSignedSurvival,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem marked_signed_survival_integrable {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hs1 : s ≤ 1) :
    Integrable (fun q : ℝ × ℝ => markedSignedSurvival d s q.1 q.2) := by
  have hc : 0 < d*s/2 := half_pos (mul_pos hd hs)
  have hi := (marked_integrable_exp_abs hc).mul_prod (marked_integrable_exp_abs hc)
  have hb : Integrable (fun q : ℝ × ℝ => Real.exp (-(d*s/2)*(|q.1|+|q.2|))) := by
    convert hi using 1
    funext q
    rw [← Real.exp_add]
    congr 1
    ring
  apply hb.mono' (marked_signed_survival_continuous d s).measurable.aestronglyMeasurable
  exact ae_of_all _ (fun q => by
    simpa only [Real.norm_eq_abs] using marked_signed_survival_envelope hd hs hs1 q.1 q.2)

theorem marked_signed_survival_inner_integrable {d s : ℝ} (hd : 0 < d) (hs : 0 < s)
    (hs1 : s ≤ 1) (t : ℝ) : Integrable (fun u : ℝ => markedSignedSurvival d s t u) := by
  have hc : 0 < d*s/2 := half_pos (mul_pos hd hs)
  apply (marked_integrable_exp_abs hc).mono'
    ((marked_signed_survival_continuous d s).comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs]
  apply (marked_signed_survival_envelope hd hs hs1 t u).trans
  apply Real.exp_le_exp.mpr
  nlinarith [abs_nonneg t]

theorem marked_signed_survival_neg_neg (d s t u : ℝ) :
    markedSignedSurvival d s (-t) (-u) = markedSignedSurvival d s t u := by
  simp only [markedSignedSurvival,abs_neg,markedDirectionalOverlap,neg_neg]
  congr 2
  ring

theorem marked_signed_survival_positive (d s t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    markedSignedSurvival d s t u = markedJointSurvival d s t u := by
  simp only [markedSignedSurvival,markedJointSurvival,markedDirectionalOverlap,
    abs_of_nonneg ht,abs_of_nonneg hu,max_eq_left ht,max_eq_left hu,
    max_eq_right (neg_nonpos.mpr ht),max_eq_right (neg_nonpos.mpr hu),min_self,add_zero]

theorem marked_signed_survival_opposite (d s t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    markedSignedSurvival d s t (-u) = Real.exp (-(d*s)*t)*Real.exp (-(d*s)*u) := by
  simp only [markedSignedSurvival,markedDirectionalOverlap,abs_neg,neg_neg,
    abs_of_nonneg ht,abs_of_nonneg hu,max_eq_left ht,max_eq_right (neg_nonpos.mpr hu),
    max_eq_right (neg_nonpos.mpr ht),max_eq_left hu,min_eq_right ht,min_eq_left hu,
    zero_add,mul_zero,sub_zero,← Real.exp_add]
  congr 1
  ring

/-- The two same-side quadrants retain the joint survival integral; the two
opposite quadrants have the product of the marginal gap integrals. -/
theorem marked_signed_survival_integral {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hs1 : s ≤ 1) :
    (∫ q : ℝ × ℝ, markedSignedSurvival d s q.1 q.2) =
      2*((∫ a : ℝ in Set.Ioi 0, ∫ b : ℝ in Set.Ioi 0, markedJointSurvival d s a b)+
        (1/(d*s))^2) := by
  have hi := marked_signed_survival_integrable hd hs hs1
  rw [Measure.volume_eq_prod] at hi
  have hinner := marked_signed_survival_inner_integrable hd hs hs1
  let J : ℝ → ℝ := fun t => ∫ u : ℝ, markedSignedSurvival d s t u
  have heven (t : ℝ) : J (-t) = J t := by
    change (∫ u : ℝ, markedSignedSurvival d s (-t) u) = _
    rw [← integral_neg_eq_self (fun u : ℝ => markedSignedSurvival d s (-t) u)]
    exact integral_congr_ae (ae_of_all _ (fun u => marked_signed_survival_neg_neg d s t u))
  have habs (t : ℝ) : J t = J |t| := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht,heven]
  have hquad : Integrable (fun q : ℝ × ℝ => markedSignedSurvival d s q.1 q.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    hi.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have hji : IntegrableOn (fun a => ∫ b : ℝ in Set.Ioi 0, markedJointSurvival d s a b) (Set.Ioi 0) := by
    apply hquad.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
    exact marked_signed_survival_positive d s a b ha.le hb.le
  have hsplit (a : ℝ) (ha : 0 ≤ a) : J a =
      (∫ b : ℝ in Set.Ioi 0, markedJointSurvival d s a b)+Real.exp (-(d*s)*a)/(d*s) := by
    have hline := intervalIntegral.integral_Iic_add_Ioi ((hinner a).integrableOn (s := Set.Iic 0))
      ((hinner a).integrableOn (s := Set.Ioi 0))
    change (∫ u : ℝ, markedSignedSurvival d s a u) = _
    rw [← hline]
    have hleft : (∫ u : ℝ in Set.Iic 0, markedSignedSurvival d s a u) =
        Real.exp (-(d*s)*a)/(d*s) := by
      have hneg := integral_comp_neg_Ioi 0 (fun u => markedSignedSurvival d s a u)
      simp only [neg_zero] at hneg
      rw [← hneg]
      calc
        _ = ∫ b : ℝ in Set.Ioi 0, Real.exp (-(d*s)*a)*Real.exp (-(d*s)*b) :=
          setIntegral_congr_fun measurableSet_Ioi (fun b hb => marked_signed_survival_opposite d s a b ha hb.le)
        _ = _ := by rw [integral_const_mul,marked_exp_tail (mul_pos hd hs)]; simp; ring
    have hright : (∫ u : ℝ in Set.Ioi 0, markedSignedSurvival d s a u) =
        ∫ b : ℝ in Set.Ioi 0, markedJointSurvival d s a b :=
      setIntegral_congr_fun measurableSet_Ioi (fun b hb => marked_signed_survival_positive d s a b ha hb.le)
    rw [hleft,hright,add_comm]
  rw [Measure.volume_eq_prod,integral_prod _ hi]
  change (∫ t : ℝ, J t) = _
  have heabs : (∫ t : ℝ, J t) = ∫ t : ℝ, J |t| :=
    integral_congr_ae (ae_of_all _ habs)
  rw [heabs,integral_comp_abs]
  have heq : (∫ a : ℝ in Set.Ioi 0, J a) =
      (∫ a : ℝ in Set.Ioi 0, ∫ b : ℝ in Set.Ioi 0, markedJointSurvival d s a b)+(1/(d*s))^2 := by
    calc
      _ = ∫ a : ℝ in Set.Ioi 0, (∫ b : ℝ in Set.Ioi 0, markedJointSurvival d s a b)+
          Real.exp (-(d*s)*a)/(d*s) :=
        setIntegral_congr_fun measurableSet_Ioi (fun a ha => hsplit a ha.le)
      _ = _ := by
        rw [integral_add hji ((integrableOn_exp_mul_Ioi (neg_neg_of_pos (mul_pos hd hs)) 0).div_const _),
          integral_div,marked_exp_tail (mul_pos hd hs)]
        simp only [mul_zero,Real.exp_zero]
        ring
  rw [heq]

/-- The unmarked same-side union integral, including the endpoint `s=1`. -/
theorem marked_union_positive_integral {d : ℝ} (hd : 0 < d) :
    (∫ a : ℝ in Set.Ioi 0, ∫ b : ℝ in Set.Ioi 0, markedJointSurvival d 1 a b) = 2/d^2 := by
  have hinner (a : ℝ) (ha : 0 ≤ a) :
      (∫ b : ℝ in Set.Ioi 0, markedJointSurvival d 1 a b) =
        a*Real.exp (-d*a)+Real.exp (-d*a)/d := by
    have hc : Continuous (fun b => markedJointSurvival d 1 a b) := by unfold markedJointSurvival; fun_prop
    have htail : IntegrableOn (fun b => markedJointSurvival d 1 a b) (Set.Ioi a) := by
      apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) a).congr_fun _ measurableSet_Ioi
      intro b hb
      change Real.exp (-d*b) = markedJointSurvival d 1 a b
      rw [markedJointSurvival,min_eq_left hb.le]
      congr 1
      ring
    rw [← intervalIntegral.integral_interval_add_Ioi' (hc.intervalIntegrable 0 a) htail,
      marked_joint_survival_tail hd (by norm_num : (0 : ℝ) < 1)]
    have he : (∫ b : ℝ in (0 : ℝ)..a, markedJointSurvival d 1 a b) = a*Real.exp (-d*a) := by
      rw [intervalIntegral.integral_of_le ha]
      calc
        _ = ∫ b : ℝ in Set.Ioc 0 a, Real.exp (-d*a) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro b hb
          rw [markedJointSurvival,min_eq_right hb.2]
          congr 1
          ring
        _ = _ := by
          simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,
            ENNReal.toReal_ofReal ha,smul_eq_mul]
    rw [he]
    norm_num
  calc
    _ = ∫ a : ℝ in Set.Ioi 0, a*Real.exp (-d*a)+Real.exp (-d*a)/d :=
      setIntegral_congr_fun measurableSet_Ioi (fun a ha => hinner a ha.le)
    _ = _ := by
      have hsi := marked_signed_survival_integrable hd (by norm_num : (0 : ℝ) < 1) le_rfl
      rw [Measure.volume_eq_prod] at hsi
      have hqi := hsi.mono_measure (Measure.prod_mono
        (Measure.restrict_le_self (μ := (volume : Measure ℝ)) (s := Set.Ioi 0))
        (Measure.restrict_le_self (μ := (volume : Measure ℝ)) (s := Set.Ioi 0)))
      have hji : IntegrableOn (fun a => ∫ b : ℝ in Set.Ioi 0, markedJointSurvival d 1 a b) (Set.Ioi 0) := by
        apply hqi.integral_prod_left.congr
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
        exact marked_signed_survival_positive d 1 a b ha.le hb.le
      have hsum : IntegrableOn (fun a => a*Real.exp (-d*a)+Real.exp (-d*a)/d) (Set.Ioi 0) := by
        apply hji.congr
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact hinner a ha.le
      have hi : IntegrableOn (fun a : ℝ => a*Real.exp (-d*a)) (Set.Ioi 0) := by
        convert hsum.sub ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) 0).div_const d) using 1
        funext a
        simp only [Pi.sub_apply]
        ring
      rw [integral_add hi ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) 0).div_const _),
        integral_div,marked_exp_tail hd]
      have he := marked_exp_moment hd 1
      simp only [pow_one,Nat.factorial_one,Nat.cast_one] at he
      simp only [← neg_mul] at he
      rw [he]
      simp only [mul_zero,Real.exp_zero]
      ring

theorem marked_union_full_integral {d : ℝ} (hd : 0 < d) :
    (∫ q : ℝ × ℝ, Real.exp (-d*markedDirectionalSpan q.1 q.2)) = 6/d^2 := by
  have he (q : ℝ × ℝ) : Real.exp (-d*markedDirectionalSpan q.1 q.2) =
      markedSignedSurvival d 1 q.1 q.2 := by simp [markedSignedSurvival,markedDirectionalSpan]
  simp_rw [he]
  rw [marked_signed_survival_integral hd (by norm_num : (0 : ℝ) < 1) le_rfl,
    marked_union_positive_integral hd]
  field_simp
  <;> ring

theorem marked_shared_full_integral {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hs1 : s < 1) :
    (∫ q : ℝ × ℝ, markedSignedSurvival d s q.1 q.2) =
      2*(4-s)/(d^2*s^2*(2-s)) := by
  rw [marked_signed_survival_integral hd hs hs1.le,marked_joint_survival_integral hd hs hs1]
  field_simp [hd.ne',hs.ne',(show (2-s : ℝ) ≠ 0 by linarith)]
  <;> ring

end AronowAudit.P001.TailA
