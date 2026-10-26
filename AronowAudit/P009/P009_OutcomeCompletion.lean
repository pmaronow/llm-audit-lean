import AronowAudit.P009.P009_BernoulliCompletion
namespace AronowAudit.P009.OutcomeCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem incoming_le_degree {n : ℕ} (E : Experiment n) (i : Fin n) :
    (incoming E i:ℝ)≤degree E i := by
  classical
  have hcount : (incoming E i:ℝ)=∑j,if Interferes E j i then (1:ℝ) else 0 := by
    simp only [incoming,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hcount]
  unfold degree d
  apply Finset.sum_le_sum
  intro j _
  by_cases h : Interferes E j i
  · have hd : Dependent E i j:=⟨j,h,Or.inl rfl⟩
    simp [h,hd]
  · simp only [if_neg h]
    split_ifs <;> norm_num

theorem moment_atom_lower {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n)
    (q : ℝ) :
    prob E.design (fun w=>∀j,Interferes E j i→w j=z j)*|E.outcome i z|^q≤
      mean E.design (fun w=>|E.outcome i w|^q) := by
  classical
  have he : prob E.design (fun w=>∀j,Interferes E j i→w j=z j)*|E.outcome i z|^q=
      mean E.design (fun w=>if ∀j,Interferes E j i→w j=z j then |E.outcome i z|^q else 0) := by
    unfold prob mean
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only
    split_ifs <;> ring
  rw [he]
  unfold mean
  apply Finset.sum_le_sum
  intro w _
  apply mul_le_mul_of_nonneg_left _ (E.design.nonneg w)
  dsimp only
  split_ifs with h
  · have hy := BernoulliCompletion.outcome_dependsOn E i h
    rw [hy]
  · exact Real.rpow_nonneg (abs_nonneg _) _

theorem incoming_outcome_bound {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (i : Fin n) (z : Assignment n) :
    |E.outcome i z|≤Real.rpow k (1+(incoming E i:ℝ)/q) := by
  classical
  have hk : 0<k:=hReg.1
  have hq : 0<q:=lt_of_lt_of_le (by norm_num) hReg.2.1
  have ha := (bernoulli_atom_bounds E k q s hReg hBER
    (Finset.univ.filter (fun j=>Interferes E j i)) z).1
  have ha' : k⁻¹^(incoming E i)≤prob E.design (fun w=>∀j,Interferes E j i→w j=z j) := by
    simpa only [incoming,Finset.mem_filter,Finset.mem_univ,true_and] using ha
  have hm : mean E.design (fun w=>|E.outcome i w|^q)≤k^q := by
    simpa only [Real.rpow_eq_pow] using hReg.2.2.2.2.1 i
  have hb : k⁻¹^(incoming E i)*|E.outcome i z|^q≤k^q :=
    (mul_le_mul_of_nonneg_right ha' (Real.rpow_nonneg (abs_nonneg _) _)).trans
      ((moment_atom_lower E i z q).trans hm)
  have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hk.le (incoming E i))
  rw [←mul_assoc,←mul_pow,mul_inv_cancel₀ hk.ne',one_pow,one_mul] at hb'
  simp only [Real.rpow_eq_pow]
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) (Real.rpow_nonneg hk.le _) hq).mp
  rw [←Real.rpow_mul hk.le]
  have hex : (1+(incoming E i:ℝ)/q)*q=(incoming E i:ℝ)+q := by field_simp;ring
  rw [hex,Real.rpow_add hk,Real.rpow_natCast]
  exact hb'

theorem bounded_degree_outcome_bound_completed {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (D : ℕ)
    (hDegree : ∀i,degree E i≤D) :
    (∀i z,|E.outcome i z|≤Real.rpow k (1+(incoming E i:ℝ)/q)) ∧
    (∀i z,|E.outcome i z|≤Real.rpow k (1+(D:ℝ)/q)) := by
  refine ⟨incoming_outcome_bound E k q s hReg hBER,?_⟩
  intro i z
  apply (incoming_outcome_bound E k q s hReg hBER i z).trans
  have hk : 1≤k := by
    have hb:=hReg.2.2.2.1 i
    have hi : k⁻¹≤1 := by linarith [inv_pos.mpr hReg.1]
    exact (inv_le_one₀ hReg.1).mp hi
  simp only [Real.rpow_eq_pow]
  apply Real.rpow_le_rpow_of_exponent_le hk
  have hq : 0≤q:=le_trans (by norm_num) hReg.2.1
  simpa only [add_comm] using add_le_add_left (div_le_div_of_nonneg_right ((incoming_le_degree E i).trans (hDegree i)) hq) 1
end
end AronowAudit.P009.OutcomeCompletion

namespace AronowAudit.P009
/-- T8's finite basis for the q≥2 correction: every
incoming-mask atom under regular Bernoulli assignment has mass at least
k^(-incoming(i)), so moment bounds and bounded local degree bound all outcomes. -/
theorem bounded_degree_outcome_bound {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (D : ℕ)
    (hDegree : ∀ i, degree E i ≤ D) :
    (∀ i z, |E.outcome i z| ≤ Real.rpow k (1+(incoming E i:ℝ)/q)) ∧
    (∀ i z, |E.outcome i z| ≤ Real.rpow k (1+(D:ℝ)/q)) := by
  exact OutcomeCompletion.bounded_degree_outcome_bound_completed E k q s hReg hBER D hDegree
end AronowAudit.P009

