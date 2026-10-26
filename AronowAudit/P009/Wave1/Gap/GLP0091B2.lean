import AronowAudit.P009.P009_NormalCompletion

namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/-! Block coordinates for the star experiment. -/

def dominatingTerm_index (m : ℕ) (u v : Fin m) : Fin (m*m) :=
  finProdFinEquiv (u, v)

def dominatingTerm_block {m : ℕ} (i : Fin (m*m)) : Fin m :=
  (finProdFinEquiv.symm i).1

def dominatingTerm_position {m : ℕ} (i : Fin (m*m)) : Fin m :=
  (finProdFinEquiv.symm i).2

def dominatingTerm_zero {m : ℕ} (hm : 2 ≤ m) : Fin m := ⟨0, by omega⟩

def dominatingTerm_one {m : ℕ} (hm : 2 ≤ m) : Fin m := ⟨1, by omega⟩

@[simp] theorem dominatingTerm_block_index (m : ℕ) (u v : Fin m) :
    dominatingTerm_block (dominatingTerm_index m u v) = u := by
  simp [dominatingTerm_block, dominatingTerm_index]

@[simp] theorem dominatingTerm_position_index (m : ℕ) (u v : Fin m) :
    dominatingTerm_position (dominatingTerm_index m u v) = v := by
  simp [dominatingTerm_position, dominatingTerm_index]

@[simp] theorem dominatingTerm_index_coords {m : ℕ} (i : Fin (m*m)) :
    dominatingTerm_index m (dominatingTerm_block i) (dominatingTerm_position i) = i := by
  exact finProdFinEquiv.apply_symm_apply i

@[simp] theorem dominatingTerm_index_eq {m : ℕ} (u v u' v' : Fin m) :
    dominatingTerm_index m u v = dominatingTerm_index m u' v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    exact Prod.mk.inj (finProdFinEquiv.injective h)
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem dominatingTerm_one_ne_zero {m : ℕ} (hm : 2 ≤ m) :
    dominatingTerm_one hm ≠ dominatingTerm_zero hm := by
  intro h
  have := congrArg Fin.val h
  norm_num [dominatingTerm_one, dominatingTerm_zero] at this

def dominatingTerm_parent {m : ℕ} (hm : 2 ≤ m) (i : Fin (m*m)) : Fin (m*m) :=
  dominatingTerm_index m (dominatingTerm_block i)
    (if dominatingTerm_position i = dominatingTerm_zero hm then
      dominatingTerm_one hm else dominatingTerm_zero hm)

@[simp] theorem dominatingTerm_parent_index {m : ℕ} (hm : 2 ≤ m) (u v : Fin m) :
    dominatingTerm_parent hm (dominatingTerm_index m u v) =
      dominatingTerm_index m u
        (if v = dominatingTerm_zero hm then dominatingTerm_one hm else dominatingTerm_zero hm) := by
  simp [dominatingTerm_parent]

@[simp] theorem dominatingTerm_block_parent {m : ℕ} (hm : 2 ≤ m) (i : Fin (m*m)) :
    dominatingTerm_block (dominatingTerm_parent hm i) = dominatingTerm_block i := by
  simp [dominatingTerm_parent]

theorem dominatingTerm_parent_ne {m : ℕ} (hm : 2 ≤ m) (i : Fin (m*m)) :
    dominatingTerm_parent hm i ≠ i := by
  intro h
  have he := congrArg dominatingTerm_position h
  simp only [dominatingTerm_parent, dominatingTerm_position_index] at he
  split_ifs at he with hi
  · exact dominatingTerm_one_ne_zero hm (he.trans hi)
  · exact hi he.symm

theorem dominatingTerm_outcome {m : ℕ} (hm : 2 ≤ m) (i : Fin (m*m))
    (z : Assignment (m*m)) :
    starOutcome m hm i z = bit (z i) + bit (z (dominatingTerm_parent hm i)) := by
  obtain ⟨⟨u, v⟩, rfl⟩ := finProdFinEquiv.surjective i
  have hm0 : 0 < m := by omega
  have hdiv : (v.val + m*u.val)/m = u.val := by
    rw [Nat.add_mul_div_left _ _ hm0, Nat.div_eq_of_lt v.isLt, zero_add]
  have hmod : (v.val + m*u.val)%m = v.val := by
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
  have hhub : u.val*m < m*m := Nat.mul_lt_mul_of_pos_right u.isLt hm0
  have hleaf : u.val*m+1 < m*m := by
    have := Nat.mul_le_mul_right m u.isLt
    nlinarith
  have hz : v.val = 0 ↔ v = dominatingTerm_zero hm := by
    simp [Fin.ext_iff, dominatingTerm_zero]
  change bit (z (dominatingTerm_index m u v)) + _ = _
  simp only [starOutcome, dominatingTerm_index, finProdFinEquiv_apply_val,
    hdiv, hmod, Nat.mod_eq_of_lt hhub, Nat.mod_eq_of_lt hleaf]
  change (bit (z (dominatingTerm_index m u v)) +
    if v.val = 0 then bit (z ⟨u.val*m+1, hleaf⟩) else bit (z ⟨u.val*m, hhub⟩)) =
      bit (z (dominatingTerm_index m u v)) +
        bit (z (dominatingTerm_parent hm (dominatingTerm_index m u v)))
  rw [dominatingTerm_parent_index]
  by_cases hv : v = dominatingTerm_zero hm
  · rw [if_pos hv]
    simp [hv, dominatingTerm_zero, dominatingTerm_one, dominatingTerm_index,
      finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  · have hv0 : v.val ≠ 0 := by simpa [hz] using hv
    rw [if_neg hv]
    simp [hv0, dominatingTerm_zero, dominatingTerm_index, finProdFinEquiv,
      Nat.mul_comm]

theorem dominatingTerm_interferes {m : ℕ} (hm : 2 ≤ m) (j i : Fin (m*m)) :
    Interferes (fairExperiment (m*m) (starOutcome m hm)) j i ↔
      j = i ∨ j = dominatingTerm_parent hm i := by
  have hy (z : Assignment (m*m)) :
      (fairExperiment (m*m) (starOutcome m hm)).outcome i z =
        ∑ l ∈ ({i, dominatingTerm_parent hm i} : Finset _), bit (z l) := by
    simp [fairExperiment, dominatingTerm_outcome, (dominatingTerm_parent_ne hm i).symm]
  simpa only [Finset.mem_insert, Finset.mem_singleton, or_self_left] using
    interferes_sum_bit (fairExperiment (m*m) (starOutcome m hm)) i j _ hy

theorem dominatingTerm_hub_incoming {m : ℕ} (hm : 2 ≤ m) (i : Fin (m*m)) :
    dominatingTerm_index m (dominatingTerm_block i) (dominatingTerm_zero hm) = i ∨
    dominatingTerm_index m (dominatingTerm_block i) (dominatingTerm_zero hm) =
      dominatingTerm_parent hm i := by
  by_cases hi : dominatingTerm_position i = dominatingTerm_zero hm
  · left
    simpa [hi] using dominatingTerm_index_coords i
  · right
    simp [dominatingTerm_parent, hi]

theorem dominatingTerm_dependent {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m)) :
    Dependent (fairExperiment (m*m) (starOutcome m hm)) i j ↔
      dominatingTerm_block i = dominatingTerm_block j := by
  simp only [Dependent, dominatingTerm_interferes]
  constructor
  · rintro ⟨l, hi, hj⟩
    have hli : dominatingTerm_block l = dominatingTerm_block i := by
      rcases hi with rfl | rfl <;> simp
    have hlj : dominatingTerm_block l = dominatingTerm_block j := by
      rcases hj with rfl | rfl <;> simp
    exact hli.symm.trans hlj
  · intro h
    refine ⟨dominatingTerm_index m (dominatingTerm_block i) (dominatingTerm_zero hm),
      dominatingTerm_hub_incoming hm i, ?_⟩
    rw [h]
    exact dominatingTerm_hub_incoming hm j

theorem dominatingTerm_sum_indices {m : ℕ} (f : Fin (m*m) → ℝ) :
    (∑ i, f i) = ∑ u : Fin m, ∑ v : Fin m, f (dominatingTerm_index m u v) := by
  rw [← finProdFinEquiv.sum_comp f, Fintype.sum_prod_type]
  rfl

theorem dominatingTerm_C1 {m : ℕ} (hm : 2 ≤ m) :
    C1 (fairExperiment (m*m) (starOutcome m hm)) = 2 := by
  have hs (i : Fin (m*m)) :
      (∑ j, I (fairExperiment (m*m) (starOutcome m hm)) j i) = 2 := by
    have he (j : Fin (m*m)) :
        I (fairExperiment (m*m) (starOutcome m hm)) j i =
          (if j = i then (1:ℝ) else 0) +
          (if j = dominatingTerm_parent hm i then (1:ℝ) else 0) := by
      simp only [I, dominatingTerm_interferes]
      by_cases hji : j = i <;> by_cases hjp : j = dominatingTerm_parent hm i <;>
        simp_all [dominatingTerm_parent_ne hm i]
    simp [he, Finset.sum_add_distrib]
    norm_num
  have hn : (m*m:ℝ) ≠ 0 := by
    have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  unfold C1 outgoing
  rw [Finset.sum_comm]
  simp [hs, Nat.cast_mul, hn]

theorem dominatingTerm_degree {m : ℕ} (hm : 2 ≤ m) (i : Fin (m*m)) :
    degree (fairExperiment (m*m) (starOutcome m hm)) i = m := by
  unfold degree
  rw [dominatingTerm_sum_indices]
  simp [d, dominatingTerm_dependent, eq_comm]

theorem dominatingTerm_dAvg {m : ℕ} (hm : 2 ≤ m) :
    dAvg (fairExperiment (m*m) (starOutcome m hm)) = m := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp [dAvg, dominatingTerm_degree, hm0]

theorem dominatingTerm_effect {m : ℕ} (hm : 2 ≤ m) (i : Fin (m*m))
    (z : Assignment (m*m)) :
    effect (fairExperiment (m*m) (starOutcome m hm)) i z = 1 := by
  simp [effect, potential, fairExperiment, dominatingTerm_outcome,
    Function.update_of_ne (dominatingTerm_parent_ne hm i), bit]

theorem dominatingTerm_msq {m : ℕ} (hm : 2 ≤ m) :
    msq (fairExperiment (m*m) (starOutcome m hm)) = 1 := by
  have hm0 : m ≠ 0 := by omega
  have he (i : Fin (m*m)) : effect (fairExperiment (m*m) (starOutcome m hm)) i =
      fun _ => 1 := funext (dominatingTerm_effect hm i)
  simp [msq, he, mean_const, hm0]

theorem dominatingTerm_xi {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m))
    (hij : i ≠ j) (a : Bool) :
    xi (fairExperiment (m*m) (starOutcome m hm)) i j a =
      if j = dominatingTerm_parent hm i then 1 else 0 := by
  have he (z : Assignment (m*m)) :
      starOutcome m hm i (Function.update (Function.update z i a) j true) -
      starOutcome m hm i (Function.update (Function.update z i a) j false) =
        if j = dominatingTerm_parent hm i then 1 else 0 := by
    rw [dominatingTerm_outcome, dominatingTerm_outcome]
    by_cases h : j = dominatingTerm_parent hm i
    · subst j
      simp [Function.update_of_ne (dominatingTerm_parent_ne hm i).symm, bit]
    · simp [Function.update_of_ne hij, Function.update_of_ne (Ne.symm h), h]
  unfold xi
  exact (congrArg (mean (fairLaw (m*m))) (funext he)).trans (mean_const _ _)

theorem dominatingTerm_xiBreve {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m))
    (hij : i ≠ j) :
    xiBreve (fairExperiment (m*m) (starOutcome m hm)) i j =
      if j = dominatingTerm_parent hm i then 1 else 0 := by
  rw [xiBreve, dominatingTerm_xi hm i j hij, dominatingTerm_xi hm i j hij]
  split_ifs <;> ring

theorem dominatingTerm_parent_parent_index {m : ℕ} (hm : 2 ≤ m) (u v : Fin m) :
    dominatingTerm_parent hm (dominatingTerm_parent hm (dominatingTerm_index m u v)) =
      dominatingTerm_index m u v ↔
        v = dominatingTerm_zero hm ∨ v = dominatingTerm_one hm := by
  by_cases hv : v = dominatingTerm_zero hm
  · simp [hv, dominatingTerm_parent_index]
  · simp [hv, dominatingTerm_parent_index, eq_comm]

theorem dominatingTerm_reciprocal_count {m : ℕ} (hm : 2 ≤ m) :
    (∑ i : Fin (m*m),
      if i = dominatingTerm_parent hm (dominatingTerm_parent hm i) then (1:ℝ) else 0) =
      2*m := by
  rw [dominatingTerm_sum_indices]
  have he (u v : Fin m) :
      (if dominatingTerm_index m u v =
          dominatingTerm_parent hm (dominatingTerm_parent hm (dominatingTerm_index m u v))
        then (1:ℝ) else 0) =
        (if v = dominatingTerm_zero hm then 1 else 0) +
          (if v = dominatingTerm_one hm then 1 else 0) := by
    have hp : (dominatingTerm_index m u v =
        dominatingTerm_parent hm (dominatingTerm_parent hm (dominatingTerm_index m u v))) ↔
        v = dominatingTerm_zero hm ∨ v = dominatingTerm_one hm :=
      eq_comm.trans (dominatingTerm_parent_parent_index hm u v)
    simp only [hp]
    by_cases hv0 : v = dominatingTerm_zero hm <;>
      by_cases hv1 : v = dominatingTerm_one hm <;>
      simp_all
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  ring

theorem dominatingTerm_B1 {m : ℕ} (hm : 2 ≤ m) :
    B1 (fairExperiment (m*m) (starOutcome m hm)) = 2/(m:ℝ)^2 := by
  let E := fairExperiment (m*m) (starOutcome m hm)
  have he (i j : Fin (m*m)) :
      (if j = i then 0 else xiBreve E i j * xiBreve E j i +
        2 * yBreve E j * (xi E i j true - xi E i j false)) =
      if j = dominatingTerm_parent hm i then
        (if i = dominatingTerm_parent hm (dominatingTerm_parent hm i) then 1 else 0) else 0 := by
    by_cases hji : j = i
    · subst j
      simp [(dominatingTerm_parent_ne hm i).symm]
    · rw [if_neg hji, dominatingTerm_xiBreve hm i j (Ne.symm hji),
        dominatingTerm_xiBreve hm j i hji,
        dominatingTerm_xi hm i j (Ne.symm hji), dominatingTerm_xi hm i j (Ne.symm hji)]
      by_cases hj : j = dominatingTerm_parent hm i
      · subst j
        simp
      · simp [hj]
  change B1 E = _
  unfold B1
  simp_rw [he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [dominatingTerm_reciprocal_count hm]
  change (2*(m:ℝ))/((m*m:ℕ)*dAvg E) = _
  rw [dominatingTerm_dAvg hm, Nat.cast_mul]
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

/-! Conditioning under the product law. -/

theorem dominatingTerm_one_numerator {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i : Fin n) (a : Bool) (f : Assignment n → ℝ) :
    mean E.design (fun z => if z i = a then f z else 0) =
      marginal E i a * mean E.design (fun z => f (Function.update z i a)) := by
  let F : Experiment n := ⟨E.design, fun _ => f⟩
  have hF : Bernoulli F := hb
  have hc := BernoulliCompletion.conditional_observed_eq_potential_mean F hF i a
  have hc' : mean E.design (fun z => if z i = a then f z else 0)/marginal E i a =
      mean E.design (fun z => f (Function.update z i a)) := by
    simp only [cmean, potential, F, marginal] at hc
    convert hc using 1 <;> congr 2 <;> funext z <;> split_ifs <;> rfl
  have he := (div_eq_iff (BernoulliCompletion.marginal_pos E hb i a).ne').mp hc'
  exact he.trans (mul_comm _ _)

theorem dominatingTerm_two_numerator {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    mean E.design (fun z => if z i = a ∧ z j = b then f z else 0) =
      (marginal E i a*marginal E j b) *
        mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  have he : (fun z : Assignment n => if z i = a ∧ z j = b then f z else 0) =
      fun z => if z i = a then (if z j = b then f z else 0) else 0 := by
    funext z; split_ifs <;> simp_all
  rw [he, dominatingTerm_one_numerator E hb i a]
  simp only [Function.update_of_ne (Ne.symm hij)]
  rw [dominatingTerm_one_numerator E hb j b]
  have hu (z : Assignment n) : Function.update (Function.update z j b) i a =
      Function.update (Function.update z i a) j b := by
    funext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [Function.update]
  simp_rw [hu]
  ring

theorem dominatingTerm_two_prob {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    prob E.design (fun z => z i = a ∧ z j = b) = marginal E i a*marginal E j b := by
  have h := dominatingTerm_two_numerator E hb i j hij a b (fun _ => 1)
  simp only [mean_const, mul_one] at h
  rw [← h]
  unfold prob
  congr 1
  funext z
  split_ifs <;> rfl

theorem dominatingTerm_two_cmean {n : ℕ} (E : Experiment n)
    (hb : Bernoulli E) (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (f : Assignment n → ℝ) :
    cmean E.design (fun z => z i = a ∧ z j = b) f =
      mean E.design (fun z => f (Function.update (Function.update z i a) j b)) := by
  rw [cmean, dominatingTerm_two_prob E hb i j hij]
  calc
    _ = (mean E.design (fun z => if z i = a ∧ z j = b then f z else 0)) /
        (marginal E i a*marginal E j b) := by
      congr 1
      congr 1
      funext z
      split_ifs <;> rfl
    _ = _ := by
      rw [dominatingTerm_two_numerator E hb i j hij]
      exact mul_div_cancel_left₀ _ (mul_ne_zero
        (BernoulliCompletion.marginal_pos E hb i a).ne'
        (BernoulliCompletion.marginal_pos E hb j b).ne')

theorem dominatingTerm_mean_bit (n : ℕ) (i : Fin n) :
    mean (fairLaw n) (fun z => bit (z i)) = 1/2 := by
  rw [SparseCompletion.fair_coordinate]
  norm_num [bit]

theorem dominatingTerm_fair_two_cmean {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (a b : Bool) (f : Assignment n → ℝ) :
    cmean (fairLaw n) (fun z => z i = a ∧ z j = b) f =
      mean (fairLaw n) (fun z => f (Function.update (Function.update z i a) j b)) := by
  exact dominatingTerm_two_cmean (fairExperiment n (fun _ _ => 0))
    (SparseCompletion.fair_BER _ _) i j hij a b f

/-! Centering removes all dependence on the two conditioned arms. -/

theorem dominatingTerm_fixed_outcome {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m))
    (hij : i ≠ j) (a b : Bool) (z : Assignment (m*m)) :
    starOutcome m hm i (Function.update (Function.update z i a) j b) =
      bit a + if dominatingTerm_parent hm i = j then bit b else bit (z (dominatingTerm_parent hm i)) := by
  rw [dominatingTerm_outcome]
  by_cases h : dominatingTerm_parent hm i = j
  · simp [Function.update_of_ne hij, h]
  · simp [Function.update_of_ne hij, Function.update_of_ne h,
      Function.update_of_ne (dominatingTerm_parent_ne hm i), h]

theorem dominatingTerm_fixed_outcome_swap {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m))
    (hij : i ≠ j) (a b : Bool) (z : Assignment (m*m)) :
    starOutcome m hm j (Function.update (Function.update z i a) j b) =
      bit b + if dominatingTerm_parent hm j = i then bit a else bit (z (dominatingTerm_parent hm j)) := by
  rw [Function.update_comm hij]
  exact dominatingTerm_fixed_outcome hm j i hij.symm b a z

theorem dominatingTerm_conditional_mean {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m))
    (hij : i ≠ j) (a b : Bool) :
    cmean (fairLaw (m*m)) (fun z => z i = a ∧ z j = b) (starOutcome m hm i) =
      bit a + if dominatingTerm_parent hm i = j then bit b else 1/2 := by
  rw [dominatingTerm_fair_two_cmean i j hij a b]
  simp_rw [dominatingTerm_fixed_outcome hm i j hij]
  by_cases h : dominatingTerm_parent hm i = j
  · simp [h, mean_const]
  · simp only [h, if_false]
    rw [mean_add, mean_const, dominatingTerm_mean_bit]

theorem dominatingTerm_conditional_mean_swap {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m))
    (hij : i ≠ j) (a b : Bool) :
    cmean (fairLaw (m*m)) (fun z => z i = a ∧ z j = b) (starOutcome m hm j) =
      bit b + if dominatingTerm_parent hm j = i then bit a else 1/2 := by
  have he : (fun z : Assignment (m*m) => z i = a ∧ z j = b) =
      (fun z => z j = b ∧ z i = a) := by funext z; exact propext and_comm
  rw [he]
  exact dominatingTerm_conditional_mean hm j i hij.symm b a

theorem dominatingTerm_ccov {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m*m))
    (hij : i ≠ j) (a b : Bool) :
    ccov (fairLaw (m*m)) (fun z => z i = a ∧ z j = b)
      (starOutcome m hm i) (starOutcome m hm j) =
      mean (fairLaw (m*m)) (fun z =>
        (if dominatingTerm_parent hm i = j then 0 else bit (z (dominatingTerm_parent hm i))-1/2) *
        (if dominatingTerm_parent hm j = i then 0 else bit (z (dominatingTerm_parent hm j))-1/2)) := by
  unfold ccov
  rw [dominatingTerm_conditional_mean hm i j hij,
    dominatingTerm_conditional_mean_swap hm i j hij]
  rw [dominatingTerm_fair_two_cmean i j hij a b]
  apply congrArg (mean (fairLaw (m*m)))
  funext z
  rw [dominatingTerm_fixed_outcome hm i j hij,
    dominatingTerm_fixed_outcome_swap hm i j hij]
  by_cases hi : dominatingTerm_parent hm i = j <;>
    by_cases hj : dominatingTerm_parent hm j = i <;> simp [hi, hj]

theorem dominatingTerm_B2 {m : ℕ} (hm : 2 ≤ m) :
    B2 (fairExperiment (m*m) (starOutcome m hm)) = 0 := by
  have he (i j : Fin (m*m)) :
      (if j = i then (0:ℝ) else
        ∑ a : Bool, ∑ b : Bool, (1-2*bit a)*(1-2*bit b)*
          ccov (fairLaw (m*m)) (fun z => z i = a ∧ z j = b)
            (starOutcome m hm i) (starOutcome m hm j)) = 0 := by
    by_cases hji : j = i
    · simp [hji]
    · simp_rw [if_neg hji, dominatingTerm_ccov hm i j (Ne.symm hji)]
      simp [Fintype.sum_bool, bit]
      ring
  unfold B2
  simp only [fairExperiment]
  simp_rw [he]
  simp

theorem dominatingTerm_regular {m : ℕ} (hm : 2 ≤ m) :
    Regular (fairExperiment (m*m) (starOutcome m hm)) 2 4 1 := by
  apply SparseCompletion.fair_regular_bounded
  intro i z
  rw [dominatingTerm_outcome]
  cases z i <;> cases z (dominatingTerm_parent hm i) <;> norm_num [bit]

theorem dominating_term_counterexample_proof :
    (∀ m (hm : 2 ≤ m), let E := fairExperiment (m*m) (starOutcome m hm)
      Bernoulli E ∧ Regular E 2 4 1 ∧ C1 E = 2 ∧ dAvg E = m ∧
      msq E = 1 ∧ B1 E = 2/(m:ℝ)^2 ∧ B2 E = 0 ∧
      0 < B1 E ∧ B1 E ≤ msq E / dAvg E) ∧
    Tendsto (fun t => ((t+2:ℕ):ℝ)/2) atTop atTop := by
  constructor
  · intro m hm
    dsimp only
    refine ⟨SparseCompletion.fair_BER _ _, dominatingTerm_regular hm,
      dominatingTerm_C1 hm, dominatingTerm_dAvg hm, dominatingTerm_msq hm,
      dominatingTerm_B1 hm, dominatingTerm_B2 hm, ?_, ?_⟩
    · rw [dominatingTerm_B1 hm]
      have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      positivity
    · rw [dominatingTerm_B1 hm, dominatingTerm_msq hm, dominatingTerm_dAvg hm]
      have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
      have hm0 : (0:ℝ) < m := by linarith
      apply (div_le_div_iff₀ (sq_pos_of_pos hm0) hm0).2
      nlinarith
  · exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)).atTop_div_const
      (by norm_num)

end
end AronowAudit.P009.Wave1
