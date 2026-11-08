import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Direct integrations of the shared-site two-replica survival function. -/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace AronowAudit.P001.TailA

set_option maxHeartbeats 1000000

/-- Elementary exponential tail integral, with the positive rate convention. -/
theorem marked_exp_tail {c : ℝ} (hc : 0 < c) (a : ℝ) :
    (∫ x : ℝ in Ioi a, Real.exp (-c*x)) = Real.exp (-c*a)/c := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hc)]
  ring

/-- Polynomial moments of an exponential survival function. -/
theorem marked_exp_moment {c : ℝ} (hc : 0 < c) (k : ℕ) :
    (∫ x : ℝ in Ioi 0, x^k * Real.exp (-(c*x))) =
      (k.factorial : ℝ) / c^(k+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show (0 : ℝ) < (k : ℝ)+1 by positivity) hc
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h,Real.Gamma_nat_eq_factorial]
  rw [show (k : ℝ)+1 = ((k+1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast]
  simp only [one_div, inv_pow]
  ring

/-- The joint one-side survival for two independently marked replicas of shared sites. -/
def markedJointSurvival (d s a b : ℝ) : ℝ :=
  Real.exp (-d*(s*(a+b)-s^2*min a b))

theorem marked_joint_survival_symmetric (d s a b : ℝ) :
    markedJointSurvival d s a b = markedJointSurvival d s b a := by
  simp only [markedJointSurvival, min_comm, add_comm]

theorem marked_joint_survival_upper (d s a b : ℝ) (hab : a ≤ b) :
    markedJointSurvival d s a b =
      Real.exp (-(d*s*(1-s))*a) * Real.exp (-(d*s)*b) := by
  rw [markedJointSurvival, min_eq_left hab, ← Real.exp_add]
  congr 1
  ring

/-- Integrate the upper triangle without assuming independent replica cells. -/
theorem marked_joint_survival_tail {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (a : ℝ) :
    (∫ b : ℝ in Ioi a, markedJointSurvival d s a b) =
      Real.exp (-(d*s*(2-s))*a)/(d*s) := by
  have hds : 0 < d*s := mul_pos hd hs
  calc
    _ = ∫ b : ℝ in Ioi a,
        Real.exp (-(d*s*(1-s))*a) * Real.exp (-(d*s)*b) :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun b hb => marked_joint_survival_upper d s a b hb.le)
    _ = Real.exp (-(d*s*(1-s))*a) * (Real.exp (-(d*s)*a)/(d*s)) := by
      rw [integral_const_mul, marked_exp_tail hds]
    _ = _ := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

/-- One triangle of the mixed gap moment. -/
theorem marked_joint_survival_triangle {d s : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hs2 : s < 2) :
    (∫ a : ℝ in Ioi 0, ∫ b : ℝ in Ioi a, markedJointSurvival d s a b) =
      1/(d^2*s^2*(2-s)) := by
  simp only [marked_joint_survival_tail hd hs, integral_div]
  rw [marked_exp_tail (mul_pos (mul_pos hd hs) (sub_pos.mpr hs2))]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  <;> ring

theorem marked_joint_survival_inner {d s : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hs1 : s < 1) {a : ℝ} (ha : 0 ≤ a) :
    (∫ b : ℝ in Ioi 0, markedJointSurvival d s a b) =
      Real.exp (-(d*s)*a)/(d*s*(1-s)) -
        Real.exp (-(d*s*(2-s))*a)/(d*s*(1-s)) +
        Real.exp (-(d*s*(2-s))*a)/(d*s) := by
  have hds : 0 < d*s := mul_pos hd hs
  have hq : 0 < d*s*(1-s) := mul_pos hds (sub_pos.mpr hs1)
  have htail : IntegrableOn (fun b => markedJointSurvival d s a b) (Ioi a) := by
    have hi : IntegrableOn (fun b =>
        Real.exp (-(d*s*(1-s))*a) * Real.exp (-(d*s)*b)) (Ioi a) :=
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hds) a).const_mul _
    apply hi.congr_fun _ measurableSet_Ioi
    intro b hb
    exact (marked_joint_survival_upper d s a b hb.le).symm
  have hcont : Continuous (fun b => markedJointSurvival d s a b) := by
    unfold markedJointSurvival
    fun_prop
  have hsplit := intervalIntegral.integral_interval_add_Ioi'
    (hcont.intervalIntegrable 0 a) htail
  rw [← hsplit, marked_joint_survival_tail hd hs]
  have hlower : (∫ b : ℝ in (0 : ℝ)..a, markedJointSurvival d s a b) =
      Real.exp (-(d*s)*a) *
        ((1-Real.exp (-(d*s*(1-s))*a))/(d*s*(1-s))) := by
    rw [intervalIntegral.integral_of_le ha]
    calc
      _ = ∫ b : ℝ in Ioc 0 a,
          Real.exp (-(d*s)*a) * Real.exp (-(d*s*(1-s))*b) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro b hb
        rw [marked_joint_survival_symmetric,
          marked_joint_survival_upper d s b a hb.2, mul_comm]
      _ = _ := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le ha,
          ← intervalIntegral.integral_Ioi_sub_Ioi
            (integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) 0) ha,
          marked_exp_tail hq, marked_exp_tail hq]
        simp only [mul_zero, Real.exp_zero]
        ring
  rw [hlower]
  have hexp : Real.exp (-(d*s)*a) * Real.exp (-(d*s*(1-s))*a) =
      Real.exp (-(d*s*(2-s))*a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_div_assoc, mul_sub, mul_one, hexp, sub_div]

/-- The full mixed one-side gap moment, integrating both triangles. -/
theorem marked_joint_survival_integral {d s : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hs1 : s < 1) :
    (∫ a : ℝ in Ioi 0, ∫ b : ℝ in Ioi 0, markedJointSurvival d s a b) =
      2/(d^2*s^2*(2-s)) := by
  have hds : 0 < d*s := mul_pos hd hs
  have hγ : 0 < d*s*(2-s) := mul_pos hds (by linarith)
  have hβ := integrableOn_exp_mul_Ioi (neg_neg_of_pos hds) 0
  have hγi := integrableOn_exp_mul_Ioi (neg_neg_of_pos hγ) 0
  calc
    _ = ∫ a : ℝ in Ioi 0,
        Real.exp (-(d*s)*a)/(d*s*(1-s)) -
          Real.exp (-(d*s*(2-s))*a)/(d*s*(1-s)) +
          Real.exp (-(d*s*(2-s))*a)/(d*s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact marked_joint_survival_inner hd hs hs1 ha.le
    _ = _ := by
      rw [integral_add
        (f := fun a => Real.exp (-(d*s)*a)/(d*s*(1-s)) -
          Real.exp (-(d*s*(2-s))*a)/(d*s*(1-s)))
        (g := fun a => Real.exp (-(d*s*(2-s))*a)/(d*s))
        ((hβ.div_const _).sub (hγi.div_const _)) (hγi.div_const _),
        integral_sub (f := fun a => Real.exp (-(d*s)*a)/(d*s*(1-s)))
          (g := fun a => Real.exp (-(d*s*(2-s))*a)/(d*s*(1-s)))
          (hβ.div_const _) (hγi.div_const _)]
      simp only [integral_div, marked_exp_tail hds, marked_exp_tail hγ,
        mul_zero, Real.exp_zero]
      field_simp [hd.ne',hs.ne',(sub_pos.mpr hs1).ne',
        (show (2-s : ℝ) ≠ 0 by linarith)]
      <;> ring

/-- The common-cell intersection uses the diagonal survival, not a product of marginals. -/
theorem marked_joint_survival_diagonal {d s : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hs2 : s < 2) :
    (∫ a : ℝ in Ioi 0, markedJointSurvival d s a a) =
      1/(d*s*(2-s)) := by
  have heq : (fun a => markedJointSurvival d s a a) =
      fun a => Real.exp (-(d*s*(2-s))*a) := by
    funext a
    simp only [markedJointSurvival, min_self]
    congr 1
    ring
  rw [heq, marked_exp_tail (mul_pos (mul_pos hd hs) (sub_pos.mpr hs2))]
  simp only [mul_zero, Real.exp_zero]

/-- Combining the same-side mixed gap integral and the independent opposite sides
gives the mixed lengths of the two half-gap cells. -/
theorem marked_cell_length_cross_integral {d s : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hs1 : s < 1) :
    ((∫ a : ℝ in Ioi 0, ∫ b : ℝ in Ioi 0, markedJointSurvival d s a b) +
      (1/(d*s))^2)/2 = (4-s)/(2*d^2*s^2*(2-s)) := by
  rw [marked_joint_survival_integral hd hs hs1]
  field_simp [hd.ne',hs.ne',(show (2-s : ℝ) ≠ 0 by linarith)]
  <;> ring

/-- Replica gap lengths are correlated even though their retention marks are independent. -/
theorem marked_joint_survival_covariance {d s : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hs1 : s < 1) :
    (∫ a : ℝ in Ioi 0, ∫ b : ℝ in Ioi 0, markedJointSurvival d s a b) -
      (1/(d*s))^2 = s/(d^2*s^2*(2-s)) := by
  rw [marked_joint_survival_integral hd hs hs1]
  field_simp [hd.ne',hs.ne',(show (2-s : ℝ) ≠ 0 by linarith)]
  <;> ring

/-- The actual intersection length of two cells with left and right half-gap endpoints. -/
theorem marked_cell_intersection_length (L₁ R₁ L₂ R₂ : ℝ)
    (hL₁ : 0 ≤ L₁) (hR₁ : 0 ≤ R₁) (hL₂ : 0 ≤ L₂) (hR₂ : 0 ≤ R₂) :
    volume.real (Icc (-L₁/2) (R₁/2) ∩ Icc (-L₂/2) (R₂/2)) =
      (min L₁ L₂+min R₁ R₂)/2 := by
  have hl : max (-L₁/2) (-L₂/2) = -(min L₁ L₂)/2 := by
    rcases le_total L₁ L₂ with h | h
    · rw [min_eq_left h,max_eq_left (by linarith)]
    · rw [min_eq_right h,max_eq_right (by linarith)]
  have hr : min (R₁/2) (R₂/2) = (min R₁ R₂)/2 := by
    rcases le_total R₁ R₂ with h | h
    · rw [min_eq_left h,min_eq_left (by linarith)]
    · rw [min_eq_right h,min_eq_right (by linarith)]
  have hnonneg : 0 ≤ min (R₁/2) (R₂/2) - max (-L₁/2) (-L₂/2) := by
    rw [hl,hr]
    have := le_min hL₁ hL₂
    have := le_min hR₁ hR₂
    linarith
  rw [Measure.real,Icc_inter_Icc,Real.volume_Icc,ENNReal.toReal_ofReal hnonneg,hl,hr]
  ring

/-- Include the separate central retention probabilities in the compound cross moment. -/
theorem marked_cross_constant_integral {d s : ℝ} (m : ℝ)
    (hd : 0 < d) (hs : 0 < s) (hs1 : s < 1) :
    1+2*m/d+s^2*(m*(∫ a : ℝ in Ioi 0, markedJointSurvival d s a a)+
      m^2*((∫ a : ℝ in Ioi 0, ∫ b : ℝ in Ioi 0,
        markedJointSurvival d s a b)+(1/(d*s))^2)/2) =
      1+2*(m/d)+s*(m/d)/(2-s)+(m/d)^2*(4-s)/(2*(2-s)) := by
  rw [marked_joint_survival_diagonal hd hs (by linarith),
    marked_joint_survival_integral hd hs hs1]
  field_simp [hd.ne',hs.ne',(show (2-s : ℝ) ≠ 0 by linarith)]
  <;> ring

end AronowAudit.P001.TailA
