import AronowAudit.P009.P009_AtomCompletion
namespace AronowAudit.P009.AtomCompletion
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def imageLaw {A B : Type*} [Fintype A] [Fintype B] (P : Law A) (F : A → B) : Law B where
  mass := fun b => ∑ a, if F a=b then P.mass a else 0
  nonneg := by intro b; exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [P.nonneg])
  total := by
    rw [Finset.sum_comm]
    simpa using P.total

lemma image_mean {A B : Type*} [Fintype A] [Fintype B]
    (P : Law A) (F : A → B) (G : B → ℝ) : mean (imageLaw P F) G=mean P (fun a=>G (F a)) := by
  unfold mean imageLaw
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

lemma image_prob {A B : Type*} [Fintype A] [Fintype B]
    (P : Law A) (F : A → B) (G : B → Prop) : prob (imageLaw P F) G=prob P (fun a=>G (F a)) :=
  image_mean P F _

lemma prefix_atom_bound {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (b : ℕ) (hb : b ≤ n)
    (a : Assignment b) :
    (imageLaw E.design (fun z : Assignment n => fun i : Fin b => z ⟨i.val, lt_of_lt_of_le i.isLt hb⟩)).mass a ≤
      (1-k⁻¹)^b := by
  let G := Finset.univ.filter (fun i : Fin n => i.val < b)
  let a' : Assignment n := fun i => if h : i.val < b then a ⟨i.val,h⟩ else false
  have hc : G.card=b := by
    dsimp [G]
    rw [Fin.card_filter_val_lt,Nat.min_eq_right hb]
  have he (z : Assignment n) :
      (fun i : Fin b => z ⟨i.val, lt_of_lt_of_le i.isLt hb⟩)=a ↔ ∀ i ∈ G, z i=a' i := by
    constructor
    · intro hz i hi
      have hi' : i.val < b := (Finset.mem_filter.mp hi).2
      have hh := congrFun hz ⟨i.val,hi'⟩
      simpa only [a',dif_pos hi'] using hh
    · intro hz
      funext i
      have hh := hz ⟨i.val,lt_of_lt_of_le i.isLt hb⟩ (by simp [G,i.isLt])
      simpa only [a',dif_pos i.isLt] using hh
  have hm : (imageLaw E.design (fun z : Assignment n => fun i : Fin b => z ⟨i.val, lt_of_lt_of_le i.isLt hb⟩)).mass a=
      prob E.design (fun z=>∀i∈G,z i=a' i) := by
    unfold imageLaw prob mean
    simp_rw [he]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp
  rw [hm]
  simpa only [hc] using (bernoulli_atom_bounds E k q s hReg hBER G a').2

theorem corrected_three_point_minimizer_completed (S : Study) (k q s α : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (hα : 0 < α ∧ α < 1) (b : ℕ → ℕ) (hb : ∀ t, b t ≤ S.N t)
    (hbInfinity : Tendsto b atTop atTop)
    (f : (t : ℕ) → Assignment (b t) → ℝ)
    (hf : ∀ t z, f t z = -1 ∨ f t z = 0 ∨ f t z = 1)
    (hmin : ∀ t (g : Assignment (b t) → ℝ),
      (∀ z, g z = -1 ∨ g z = 0 ∨ g z = 1) →
      approximationError (S.experiment t).design α
        (fun z => f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩)) ≤
      approximationError (S.experiment t).design α
        (fun z => g (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩))) :
    (∀ t, approximationError (S.experiment t).design α
      (fun z => f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩)) ≤
        2*(1-k⁻¹)^b t) ∧
    (∀ a : Bool, Tendsto (fun t => prob (S.experiment t).design (fun z =>
      f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩) = if a then 1 else -1))
      atTop (nhds (α/2))) := by
  have hobj (t : ℕ) : approximationError (S.experiment t).design α
      (fun z => f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩)) ≤ 2*(1-k⁻¹)^b t := by
    let R := fun z : Assignment (S.N t) => fun i : Fin (b t) => z ⟨i.val,lt_of_lt_of_le i.isLt (hb t)⟩
    let P := imageLaw (S.experiment t).design R
    obtain ⟨g,hg,hg1,hgm⟩ := three_point_atom_approximation_completed P ((1-k⁻¹)^b t) α
      (prefix_atom_bound _ k q s (hReg t) (hBER t) (b t) (hb t)) hα
    have hmin' := hmin t g hg
    have hgb : approximationError (S.experiment t).design α (fun z=>g (R z)) ≤ 2*(1-k⁻¹)^b t := by
      unfold approximationError
      change |prob _ (fun z=>g (R z)=1)-α/2|+|prob _ (fun z=>g (R z) = -1)-α/2| ≤ _
      have he1 := image_prob (S.experiment t).design R (fun w=>g w=1)
      have hem := image_prob (S.experiment t).design R (fun w=>g w = -1)
      change |prob (imageLaw (S.experiment t).design R) (fun w=>g w=1)-α/2| ≤ _ at hg1
      change |prob (imageLaw (S.experiment t).design R) (fun w=>g w = -1)-α/2| ≤ _ at hgm
      rw [he1] at hg1
      rw [hem] at hgm
      linarith
    exact hmin'.trans hgb
  refine ⟨hobj, ?_⟩
  have hk := (hReg 0).1
  have hk2 := BernoulliCompletion.regular_k_ge_two (S.positive 0) _ k q s (hReg 0)
  have hklo : 0 ≤ 1-k⁻¹ := by
    have hi : k⁻¹ ≤ 1 := (inv_le_one₀ hk).mpr (by linarith)
    linarith
  have hkhi : 1-k⁻¹ < 1 := by linarith [inv_pos.mpr hk]
  have hδ : Tendsto (fun t=>2*(1-k⁻¹)^b t) atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hklo hkhi).comp hbInfinity).const_mul 2
  have habs (t : ℕ) (a : Bool) :
      |prob (S.experiment t).design (fun z =>
      f t (fun i => z ⟨i.val,lt_of_lt_of_le i.isLt (hb t)⟩) = if a then 1 else -1)-α/2| ≤ 2*(1-k⁻¹)^b t := by
    have hh := hobj t
    unfold approximationError at hh
    cases a
    · simp only [Bool.false_eq_true,ite_false]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans hh
    · simp only [ite_true]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans hh
  intro a
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using (tendsto_const_nhds.sub hδ)) (by simpa using (tendsto_const_nhds.add hδ))
  · intro t
    have ha := (abs_le.mp (habs t a)).1
    linarith
  · intro t
    have ha := (abs_le.mp (habs t a)).2
    linarith
end
end AronowAudit.P009.AtomCompletion

namespace AronowAudit.P009
open scoped BigOperators
open Filter
noncomputable section
theorem corrected_three_point_minimizer (S : Study) (k q s α : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (hα : 0 < α ∧ α < 1) (b : ℕ → ℕ) (hb : ∀ t, b t ≤ S.N t)
    (hbInfinity : Tendsto b atTop atTop)
    (f : (t : ℕ) → Assignment (b t) → ℝ)
    (hf : ∀ t z, f t z = -1 ∨ f t z = 0 ∨ f t z = 1)
    (hmin : ∀ t (g : Assignment (b t) → ℝ),
      (∀ z, g z = -1 ∨ g z = 0 ∨ g z = 1) →
      approximationError (S.experiment t).design α
        (fun z => f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩)) ≤
      approximationError (S.experiment t).design α
        (fun z => g (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩))) :
    (∀ t, approximationError (S.experiment t).design α
      (fun z => f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩)) ≤
        2*(1-k⁻¹)^b t) ∧
    (∀ a : Bool, Tendsto (fun t => prob (S.experiment t).design (fun z =>
      f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩) = if a then 1 else -1))
      atTop (nhds (α/2))) := by
  exact AtomCompletion.corrected_three_point_minimizer_completed S k q s α hReg hBER hα b hb hbInfinity f hf hmin
end
end AronowAudit.P009
