import AronowAudit.P009.P009_BernoulliCompletion
namespace AronowAudit.P009.AtomCompletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

lemma subset_mass_below {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (w : Ω → ℝ)
    (δ a : ℝ) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hbound : ∀ x ∈ s, w x ≤ δ) (htotal : a ≤ ∑ x ∈ s, w x) :
    ∃ A ⊆ s, (∑ x ∈ A, w x) ≤ a ∧ a - (∑ x ∈ A, w x) ≤ δ := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨∅, Finset.Subset.rfl, ?_, ?_⟩ <;> simp_all
      linarith
  | @insert x s hx ih =>
      by_cases hs : a ≤ ∑ y ∈ s, w y
      · obtain ⟨A,hA,hAa,hAd⟩ := ih (fun y hy => hbound y (Finset.mem_insert_of_mem hy)) hs
        exact ⟨A, hA.trans (Finset.subset_insert x s), hAa, hAd⟩
      · refine ⟨s, Finset.subset_insert x s, (le_of_not_ge hs), ?_⟩
        rw [Finset.sum_insert hx] at htotal
        have hb := hbound x (Finset.mem_insert_self x s)
        linarith

lemma prob_finset {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Finset Ω) :
    prob P (fun ω => ω ∈ A) = ∑ ω ∈ A, P.mass ω := by
  classical
  simp only [prob, mean, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  simp

theorem three_point_atom_approximation_completed {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (δ α : ℝ) (hδ : ∀ ω, P.mass ω ≤ δ) (hα : 0 < α ∧ α < 1) :
    ∃ f : Ω → ℝ, (∀ ω, f ω = -1 ∨ f ω = 0 ∨ f ω = 1) ∧
      |prob P (fun ω => f ω = 1)-α/2| ≤ δ ∧
      |prob P (fun ω => f ω = -1)-α/2| ≤ δ := by
  have hne : Nonempty Ω := by
    by_contra h
    have : IsEmpty Ω := not_nonempty_iff.mp h
    have := P.total
    simp at this
  let ω := Classical.choice hne
  have hδ0 : 0 ≤ δ := (P.nonneg ω).trans (hδ ω)
  obtain ⟨A,hAu,hAa,hAd⟩ := subset_mass_below Finset.univ P.mass δ (α/2) hδ0
    (by linarith) (fun x _ => hδ x) (by rw [P.total]; linarith)
  let C := Finset.univ \ A
  have hCtotal : α/2 ≤ ∑ x ∈ C, P.mass x := by
    have hc := Finset.sum_sdiff hAu (f:=P.mass)
    rw [P.total] at hc
    dsimp [C]
    linarith
  obtain ⟨B,hBC,hBa,hBd⟩ := subset_mass_below C P.mass δ (α/2) hδ0
    (by linarith) (fun x _ => hδ x) hCtotal
  have hBA (x : Ω) (hx : x ∈ B) : x ∉ A := (Finset.mem_sdiff.mp (hBC hx)).2
  let f := fun x : Ω => if x ∈ A then (1:ℝ) else if x ∈ B then -1 else 0
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x
    dsimp [f]
    split_ifs <;> simp
  · have he : (fun x => f x = 1) = (fun x => x ∈ A) := by
      funext x
      dsimp [f]
      split_ifs <;> norm_num at * <;> simp_all
    rw [he, prob_finset, abs_of_nonpos (by linarith)]
    linarith
  · have he : (fun x => f x = -1) = (fun x => x ∈ B) := by
      funext x
      by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp_all [f] <;> norm_num
    rw [he, prob_finset, abs_of_nonpos (by linarith)]
    linarith
end
end AronowAudit.P009.AtomCompletion

namespace AronowAudit.P009
noncomputable section
theorem three_point_atom_approximation {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (δ α : ℝ) (hδ : ∀ ω, P.mass ω ≤ δ) (hα : 0 < α ∧ α < 1) :
    ∃ f : Ω → ℝ, (∀ ω, f ω = -1 ∨ f ω = 0 ∨ f ω = 1) ∧
      |prob P (fun ω => f ω = 1)-α/2| ≤ δ ∧
      |prob P (fun ω => f ω = -1)-α/2| ≤ δ := by
  exact AtomCompletion.three_point_atom_approximation_completed P δ α hδ hα
end
end AronowAudit.P009
