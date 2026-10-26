import AronowAudit.P009.P009_MixingBasics
import AronowAudit.P009.P009_NormalCompletion
namespace AronowAudit.P009.CommonCompletion
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

lemma common_mean {n : ℕ} (hn : 0 < n) (E : Experiment n) (p : ℝ)
    (hCommon : ∀ z, E.design.mass z =
      if z = (fun _ => true) then p else if z = (fun _ => false) then 1-p else 0)
    (F : Assignment n → ℝ) :
    mean E.design F = p*F (fun _=>true)+(1-p)*F (fun _=>false) := by
  have hne : (fun _ : Fin n => true) ≠ (fun _=>false) := by
    intro h; have := congrFun h ⟨0,hn⟩; contradiction
  have hm (z : Assignment n) : E.design.mass z*F z =
      (if z=(fun _=>true) then p*F z else 0)+
      (if z=(fun _=>false) then (1-p)*F z else 0) := by
    rw [hCommon]
    split_ifs <;> simp_all
  unfold mean
  simp_rw [hm]
  simp [Finset.sum_add_distrib]

lemma common_prob {n : ℕ} (hn : 0 < n) (E : Experiment n) (p : ℝ)
    (hCommon : ∀ z, E.design.mass z =
      if z = (fun _ => true) then p else if z = (fun _ => false) then 1-p else 0)
    (A : Assignment n → Prop) :
    prob E.design A = p*(if A (fun _=>true) then 1 else 0)+
      (1-p)*(if A (fun _=>false) then 1 else 0) :=
  common_mean hn E p hCommon _

lemma common_alpha {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hCommon : ∀ z, E.design.mass z =
      if z = (fun _ => true) then p else if z = (fun _ => false) then 1-p else 0)
    (i j : Fin n) : alpha E.design (masked E i) (masked E j) = p*(1-p) := by
  have hpos : 0 < p*(1-p) := mul_pos hp.1 (by linarith)
  apply le_antisymm
  · apply MixingBasics.alpha_le_of_event_bound
    intro S T
    simp_rw [common_prob hn E p hCommon]
    by_cases hs1 : masked E i (fun _=>true) ∈ S <;>
      by_cases hs0 : masked E i (fun _=>false) ∈ S <;>
      by_cases ht1 : masked E j (fun _=>true) ∈ T <;>
      by_cases ht0 : masked E j (fun _=>false) ∈ T <;>
      simp [hs1,hs0,ht1,ht0,abs_of_pos hp.1,abs_of_pos (sub_pos.mpr hp.2)] <;> first | nlinarith | (apply abs_le.mpr; constructor <;> nlinarith)
  · have hiT : masked E i (fun _=>true) i = true := by simp [masked,Interferes]
    have hiF : masked E i (fun _=>false) i = false := by simp [masked]
    have hjT : masked E j (fun _=>true) j = true := by simp [masked,Interferes]
    have hjF : masked E j (fun _=>false) j = false := by simp [masked]
    have h := MixingBasics.event_abs_le_alpha E.design (masked E i) (masked E j)
      {z | z i=true} {z | z j=true}
    simp_rw [common_prob hn E p hCommon] at h
    simp only [Set.mem_setOf_eq,hiT,hiF,hjT,hjF,Bool.false_eq_true,not_false_eq_true,
      and_self,ite_true,ite_false,mul_one,mul_zero,add_zero] at h
    have he : p-p*p=p*(1-p) := by ring
    rw [he,abs_of_pos hpos] at h
    exact h

theorem common_assignment_mixing_completed {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (p θ : ℝ) (hp : 0 < p ∧ p < 1) (hNo : NoInterference E)
    (hCommon : ∀ z, E.design.mass z =
      if z = (fun _ => true) then p else if z = (fun _ => false) then 1-p else 0) :
    (∀ i j, i ≠ j → alpha E.design (masked E i) (masked E j) = p*(1-p)) ∧
    alphaExt E θ = ((n:ℝ)-1)*Real.rpow (p*(1-p)) θ ∧
    alphaExt E 1 = ((n:ℝ)-1)*p*(1-p) := by
  have ha (i j : Fin n) := common_alpha hn E p hp hCommon i j
  have hp0 : p*(1-p) ≠ 0 := (mul_pos hp.1 (by linarith : 0 < 1-p)).ne'
  have he (t : ℝ) : alphaExt E t=((n:ℝ)-1)*Real.rpow (p*(1-p)) t := by
    unfold alphaExt
    simp_rw [ha,SparseCompletion.noI_d E hNo]
    simp only [mixPower,hp0,ite_false]
    have hr (i : Fin n) : (∑ j, (1-(if i=j then (1:ℝ) else 0))*Real.rpow (p*(1-p)) t)=
        ((n:ℝ)-1)*Real.rpow (p*(1-p)) t := by
      rw [show (fun j : Fin n => (1-(if i=j then (1:ℝ) else 0))*Real.rpow (p*(1-p)) t)=
        (fun j => Real.rpow (p*(1-p)) t-(if i=j then Real.rpow (p*(1-p)) t else 0)) by
          funext j; split_ifs <;> ring]
      simp [Finset.sum_sub_distrib,mul_sub,sub_mul]
    simp_rw [hr]
    simp [hn.ne']
  exact ⟨fun i j _ => ha i j, he θ, by simpa only [Real.rpow_eq_pow,Real.rpow_one,mul_assoc] using he 1⟩
/-- The actual growing common-assignment family violates Assumption 5: its normalized coefficient has a strictly positive limit. -/
theorem common_assignment_mixing_sequence (S : Study) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hNo : ∀ t, NoInterference (S.experiment t))
    (hCommon : ∀ t z, (S.experiment t).design.mass z =
      if z=(fun _=>true) then p else if z=(fun _=>false) then 1-p else 0) :
    Tendsto (fun t=>alphaExt (S.experiment t) 1/size S t) Filter.atTop (nhds (p*(1-p))) ∧
    ¬ LittleO (fun t=>alphaExt (S.experiment t) 1) (size S) := by
  have hN : Tendsto (size S) Filter.atTop Filter.atTop := by
    exact tendsto_natCast_atTop_iff.mpr S.grows
  have hinv : Tendsto (fun t=>p*(1-p)/size S t) Filter.atTop (nhds 0) :=
    hN.const_div_atTop _
  have he (t : ℕ) : alphaExt (S.experiment t) 1/size S t=p*(1-p)-p*(1-p)/size S t := by
    rw [(common_assignment_mixing_completed (S.positive t) _ p 1 hp (hNo t) (hCommon t)).2.2]
    change (((S.N t:ℝ)-1)*p*(1-p))/(S.N t:ℝ)=_
    have hn : (S.N t:ℝ)≠0 := by exact_mod_cast (S.positive t).ne'
    dsimp [size]
    field_simp
  have hlim : Tendsto (fun t=>alphaExt (S.experiment t) 1/size S t) Filter.atTop (nhds (p*(1-p))) := by
    simpa only [he,sub_zero] using tendsto_const_nhds.sub hinv
  refine ⟨hlim,?_⟩
  intro hzero
  have heq := tendsto_nhds_unique hlim hzero
  have hp0 : 0 < p*(1-p) := mul_pos hp.1 (by linarith)
  linarith
end
end AronowAudit.P009.CommonCompletion

namespace AronowAudit.P009
open scoped BigOperators
open Filter
noncomputable section
theorem common_assignment_mixing {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (p θ : ℝ) (hp : 0 < p ∧ p < 1) (hNo : NoInterference E)
    (hCommon : ∀ z, E.design.mass z =
      if z = (fun _ => true) then p else if z = (fun _ => false) then 1-p else 0) :
    (∀ i j, i ≠ j → alpha E.design (masked E i) (masked E j) = p*(1-p)) ∧
    alphaExt E θ = ((n:ℝ)-1)*Real.rpow (p*(1-p)) θ ∧
    alphaExt E 1 = ((n:ℝ)-1)*p*(1-p) := by
  exact CommonCompletion.common_assignment_mixing_completed hn E p θ hp hNo hCommon
end
end AronowAudit.P009
