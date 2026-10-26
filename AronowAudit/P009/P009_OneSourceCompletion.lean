/- Exact arbitrary-size one-source spillover formulas, finite update identities, interference graph counts and weighted means. -/
import AronowAudit.P009.P009_NormalCompletion
namespace AronowAudit.P009.OneSourceCompletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

lemma source_xi {n : ℕ} (hn : 0 < n) (b : ℕ) (c : Fin n→ℝ) (i j : Fin n) (hij : i≠j) (a : Bool) :
    xi (fairExperiment n (oneSourceOutcome b c)) i j a =
      if 0 < i.val ∧ i.val < b ∧ j.val=0 then 2*bit a else 0 := by
  let o : Fin n:=⟨0,hn⟩
  have hjo : j.val=0 ↔ j=o := by simp only [o,Fin.ext_iff]
  have he (z : Assignment n) :
      oneSourceOutcome b c i (Function.update (Function.update z i a) j true)-
      oneSourceOutcome b c i (Function.update (Function.update z i a) j false)=
      if 0 < i.val ∧ i.val < b ∧ j.val=0 then 2*bit a else 0 := by
    by_cases hi : 0 < i.val ∧ i.val < b
    · have hio : i≠o := by intro h;have:=congrArg Fin.val h; dsimp [o] at this;omega
      by_cases hj : j=o
      · subst j
        simp [oneSourceOutcome,hi,Function.update_apply,hio,bit,o]
      · have hjv : j.val≠0 := by intro hv; exact hj (Fin.ext hv)
        simp [oneSourceOutcome,hi,Function.update_apply,hij,(Ne.symm hij),hio,hj,hjv,(Ne.symm hjv),o,Fin.ext_iff,hi.1.ne',hi.1.ne]
    · have hnot : ¬(0 < i.val ∧ i.val < b ∧ j.val=0) := by tauto
      simp [oneSourceOutcome,hi,hnot,Function.update_apply,hij,(Ne.symm hij)]
  unfold xi
  exact (congrArg (mean (fairLaw n)) (funext he)).trans (mean_const _ _)

lemma source_interferes {n : ℕ} (hn : 0 < n) (b : ℕ) (c : Fin n→ℝ) (i j : Fin n) :
    Interferes (fairExperiment n (oneSourceOutcome b c)) i j ↔
      i=j ∨ i.val=0 ∧ 0 < j.val ∧ j.val < b := by
  let o : Fin n:=⟨0,hn⟩
  constructor
  · rintro (he|⟨z,z',ha,hnv⟩)
    · exact Or.inl he
    · by_cases hij : i=j
      · exact Or.inl hij
      · right
        have hjagree := ha j (Ne.symm hij)
        have hia : 0 < j.val ∧ j.val < b := by
          by_contra h
          apply hnv
          change oneSourceOutcome b c j z=oneSourceOutcome b c j z'
          simp [oneSourceOutcome,h,hjagree]
        have hio : i=o := by
          by_contra h
          have hoagree := ha o (Ne.symm h)
          apply hnv
          change oneSourceOutcome b c j z=oneSourceOutcome b c j z'
          simpa [oneSourceOutcome,hia,o,hjagree,hoagree]
        exact ⟨by simpa [o] using congrArg Fin.val hio,hia⟩
  · rintro (he|⟨hi,hj,hjb⟩)
    · exact Or.inl he
    · have hio : i=o := Fin.ext hi
      subst i
      have hjo : j≠o := by intro h;have:=congrArg Fin.val h; dsimp [o] at this;omega
      let z : Assignment n:=Function.update (fun _=>false) j true
      refine Or.inr ⟨z,Function.update z o true,?_,?_⟩
      · intro l hl
        simp [Function.update_of_ne hl]
      · change oneSourceOutcome b c j z≠oneSourceOutcome b c j (Function.update z o true)
        simp [oneSourceOutcome,hj,hjb,z,Function.update_apply,hjo,(Ne.symm hjo),o,bit]

lemma source_dependent {n : ℕ} (hn : 0 < n) (b : ℕ) (hb : 1 ≤ b) (c : Fin n→ℝ) (i j : Fin n) :
    Dependent (fairExperiment n (oneSourceOutcome b c)) i j ↔ i=j ∨ i.val < b ∧ j.val < b := by
  simp only [Dependent,source_interferes hn]
  constructor
  · rintro ⟨l,hi,hj⟩
    rcases hi with hi|⟨hl,hi,hib⟩ <;> rcases hj with hj|⟨hl',hj,hjb⟩
    · exact Or.inl (hi.symm.trans hj)
    · subst l; exact Or.inr ⟨by omega,hjb⟩
    · subst l; exact Or.inr ⟨hib,by omega⟩
    · exact Or.inr ⟨hib,hjb⟩
  · rintro (rfl|⟨hi,hj⟩)
    · exact ⟨i,Or.inl rfl,Or.inl rfl⟩
    · refine ⟨⟨0,hn⟩,?_,?_⟩
      · by_cases hz : i.val=0
        · left; exact Fin.ext hz.symm
        · right; exact ⟨rfl,by omega,hi⟩
      · by_cases hz : j.val=0
        · left; exact Fin.ext hz.symm
        · right; exact ⟨rfl,by omega,hj⟩

lemma source_count_lt {n : ℕ} (b : ℕ) (hb : b ≤ n) :
    (∑ i : Fin n,if i.val < b then (1:ℝ) else 0)=b := by
  have hc : (Finset.univ.filter (fun i : Fin n=>i.val < b)).card=b := by
    rw [Fin.card_filter_val_lt,Nat.min_eq_right hb]
  rw [←Finset.sum_filter]
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using congrArg (fun a : ℕ=>(a:ℝ)) hc

lemma source_davg {n : ℕ} (hn : 0 < n) (b : ℕ) (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n→ℝ) :
    (n:ℝ)*dAvg (fairExperiment n (oneSourceOutcome b c))=n+(b:ℝ)*((b:ℝ)-1) := by
  have hrow (i : Fin n) : degree (fairExperiment n (oneSourceOutcome b c)) i=
      if i.val < b then (b:ℝ) else 1 := by
    unfold degree d
    simp only [source_dependent hn b hb.1]
    by_cases hi : i.val < b
    · simp only [if_pos hi]
      have he (j : Fin n) : (i=j ∨ i.val < b ∧ j.val < b) ↔ j.val < b := by constructor <;> aesop
      simp_rw [he]
      exact source_count_lt b hb.2
    · simp only [hi,false_and,or_false,if_false]
      simp
  unfold dAvg
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  rw [mul_div_cancel₀ _ hn0]
  simp_rw [hrow]
  have he (i : Fin n) : (if i.val < b then (b:ℝ) else 1)=1+((b:ℝ)-1)*(if i.val < b then 1 else 0) := by split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,source_count_lt b hb.2]
  simp
  ring

lemma source_ybreve {n : ℕ} (hn : 0 < n) (b : ℕ) (c : Fin n→ℝ) :
    yBreve (fairExperiment n (oneSourceOutcome b c)) ⟨0,hn⟩=1/2+c ⟨0,hn⟩ := by
  let E:=fairExperiment n (oneSourceOutcome b c)
  have hp (a : Bool) : potential E ⟨0,hn⟩ a=(fun _=>bit a+c ⟨0,hn⟩) := by
    funext z
    simp [potential,E,fairExperiment,oneSourceOutcome]
  unfold yBreve
  rw [SparseCompletion.fair_marginal]
  simp_rw [BernoulliCompletion.conditional_observed_eq_potential_mean _ (SparseCompletion.fair_BER _ _)]
  change (1-1/2)*mean E.design (potential E ⟨0,hn⟩ true)+(1/2)*mean E.design (potential E ⟨0,hn⟩ false)=_
  rw [hp,hp,mean_const,mean_const]
  norm_num [bit]
  ring

lemma source_cross {n : ℕ} (hn : 0 < n) (b : ℕ) (c : Fin n→ℝ) (i j : Fin n) (hij : i≠j) :
    xiBreve (fairExperiment n (oneSourceOutcome b c)) i j *
      xiBreve (fairExperiment n (oneSourceOutcome b c)) j i=0 := by
  unfold xiBreve
  rw [source_xi hn b c i j hij true,source_xi hn b c i j hij false,
    source_xi hn b c j i (Ne.symm hij) true,source_xi hn b c j i (Ne.symm hij) false]
  by_cases hi : 0 < i.val ∧ i.val < b ∧ j.val=0
  · have hj : ¬(0 < j.val ∧ j.val < b ∧ i.val=0) := by omega
    simp [hi,hj]
  · simp [hi]

lemma source_count_affected {n : ℕ} (hn : 0 < n) (b : ℕ) (hb : 1 ≤ b ∧ b ≤ n) :
    (∑ i : Fin n,if 0 < i.val ∧ i.val < b then (1:ℝ) else 0)=(b:ℝ)-1 := by
  let o : Fin n:=⟨0,hn⟩
  have he (i : Fin n) : (if 0 < i.val ∧ i.val < b then (1:ℝ) else 0)=
      (if i.val < b then 1 else 0)-(if i=o then 1 else 0) := by
    by_cases hi : i=o
    · subst i; simp [o,show 0 < b by omega]
    · have hpos : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact hi (Fin.ext hz)
      simp [hi,hpos]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,source_count_lt b hb.2]
  simp

theorem corrected_one_source_spillover_completed {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) :
    let E := fairExperiment n (oneSourceOutcome b c)
    (∀ i j, i ≠ j → xi E i j false = 0 ∧
      xi E i j true = (if 0 < i.val ∧ i.val < b ∧ j.val = 0 then 2 else 0) ∧
      xiBreve E i j*xiBreve E j i = 0) ∧
    yBreve E ⟨0,hn⟩ = 1/2+c ⟨0,hn⟩ ∧
    B1 E = (2+4*c ⟨0,hn⟩)*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) := by
  let E:=fairExperiment n (oneSourceOutcome b c)
  let o : Fin n:=⟨0,hn⟩
  let C : ℝ:=2+4*c o
  have hterm (i j : Fin n) : (if j=i then 0 else xiBreve E i j*xiBreve E j i+
      2*yBreve E j*(xi E i j true-xi E i j false))=
      if 0 < i.val ∧ i.val < b ∧ j=o then C else 0 := by
    by_cases hij : i=j
    · subst j
      have hf : ¬(0 < i.val ∧ i.val < b ∧ i=o) := by intro h; have:=congrArg Fin.val h.2.2;dsimp [o] at this;omega
      simp [hf]
    · rw [if_neg (Ne.symm hij),source_cross hn b c i j hij,source_xi hn b c i j hij true,
        source_xi hn b c i j hij false]
      by_cases hia : 0 < i.val ∧ i.val < b ∧ j=o
      · have hj : j=o:=hia.2.2
        have hv : j.val=0:=by simpa [o] using congrArg Fin.val hj
        simp only [hia,hv,and_true,if_true,bit,ite_true,Bool.false_eq_true,ite_false,mul_one,mul_zero,zero_add,sub_zero]
        simp only [o,Fin.val_mk,true_and,ite_true,sub_zero]
        rw [source_ybreve hn b c]
        dsimp [C,o]
        ring
      · have hv : ¬(0 < i.val ∧ i.val < b ∧ j.val=0) := by
          intro h; apply hia;exact ⟨h.1,h.2.1,Fin.ext h.2.2⟩
        simp [hia,hv]
  refine ⟨?_,source_ybreve hn b c,?_⟩
  · intro i j hij
    exact ⟨by rw [source_xi hn b c i j hij false];simp [bit],
      by rw [source_xi hn b c i j hij true];simp [bit],source_cross hn b c i j hij⟩
  · change B1 E=_
    unfold B1
    simp_rw [hterm]
    have hrow (i : Fin n) : (∑ j : Fin n,if 0 < i.val ∧ i.val < b ∧ j=o then C else 0)=
        C*(if 0 < i.val ∧ i.val < b then 1 else 0) := by
      by_cases hi : 0 < i.val ∧ i.val < b
      · simp [hi]
      · have hh (j : Fin n) : ¬(0 < i.val ∧ i.val < b ∧ j=o) := by tauto
        simp [hh,hi]
    simp_rw [hrow]
    rw [←Finset.mul_sum,source_count_affected hn b hb,source_davg hn b hb c]

end
end AronowAudit.P009.OneSourceCompletion

namespace AronowAudit.P009
open scoped BigOperators
noncomputable section
/-- T33, corrected untreated spillover in the one-source illustration,
Supplement B p. 8: xi_ij(0)=ZERO; the printed B1 already uses that value. -/
theorem corrected_one_source_spillover {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ) :
    let E := fairExperiment n (oneSourceOutcome b c)
    (∀ i j, i ≠ j → xi E i j false = 0 ∧
      xi E i j true = (if 0 < i.val ∧ i.val < b ∧ j.val = 0 then 2 else 0) ∧
      xiBreve E i j*xiBreve E j i = 0) ∧
    yBreve E ⟨0,hn⟩ = 1/2+c ⟨0,hn⟩ ∧
    B1 E = (2+4*c ⟨0,hn⟩)*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) := by
  exact OneSourceCompletion.corrected_one_source_spillover_completed hn b hb c

end
end AronowAudit.P009
