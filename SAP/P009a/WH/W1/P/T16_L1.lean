import SAP.P009a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.WH.W1.P.T16_L1

open SAP.P009a.WH.W1
open Bridge
open scoped BigOperators Topology Classical

noncomputable section

private theorem bool_set_cases (S : Set Bool) :
    S = ∅ ∨ S = Set.univ ∨ S = {false} ∨ S = {true} := by
  classical
  by_cases hf : false ∈ S <;> by_cases ht : true ∈ S
  · right
    left
    ext x
    cases x <;> simp [hf, ht]
  · right
    right
    left
    ext x
    cases x <;> simp [hf, ht]
  · right
    right
    right
    ext x
    cases x <;> simp [hf, ht]
  · left
    ext x
    cases x <;> simp [hf, ht]

private theorem probability_empty_event {Ω : Type} [Fintype Ω]
    (P : FiniteDistribution Ω) : probability P (fun _ => False) = 0 := by
  rw [probability_correspondence]
  simp [AronowAudit.P009.prob, AronowAudit.P009.mean]

private theorem probability_full_event {Ω : Type} [Fintype Ω]
    (P : FiniteDistribution Ω) : probability P (fun _ => True) = 1 := by
  rw [probability_correspondence]
  simp [AronowAudit.P009.prob, AronowAudit.P009.mean_const]

private theorem probability_false_eq_complement {Ω : Type} [Fintype Ω]
    (P : FiniteDistribution Ω) (X : Ω → Bool) :
    probability P (fun ω => X ω = false) =
      1 - probability P (fun ω => X ω = true) := by
  have hc := AronowAudit.P009.probability_complement (toProjectDistribution P)
    (fun ω => X ω = true)
  calc
    probability P (fun ω => X ω = false) =
        AronowAudit.P009.prob (toProjectDistribution P) (fun ω => X ω = false) :=
      probability_correspondence P _
    _ = AronowAudit.P009.prob (toProjectDistribution P) (fun ω => ¬ X ω = true) := by
      congr 1
      funext ω
      cases X ω <;> simp
    _ = 1 - AronowAudit.P009.prob (toProjectDistribution P) (fun ω => X ω = true) := hc
    _ = 1 - probability P (fun ω => X ω = true) := by
      rw [← probability_correspondence]

private theorem boolean_event_bound {Ω : Type} [Fintype Ω]
    (P : FiniteDistribution Ω) (X : Ω → Bool) :
    ∀ S T : Set Bool,
      |probability P (fun ω => X ω ∈ S ∧ X ω ∈ T) -
        probability P (fun ω => X ω ∈ S) * probability P (fun ω => X ω ∈ T)| ≤
        probability P (fun ω => X ω = true) *
          (1 - probability P (fun ω => X ω = true)) := by
  let p := probability P (fun ω => X ω = true)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    rw [probability_correspondence]
    exact AronowAudit.P009.probability_nonnegative (toProjectDistribution P)
      (fun ω => X ω = true)
  have hp1 : p ≤ 1 := by
    dsimp [p]
    rw [probability_correspondence]
    exact AronowAudit.P009.MixingBasics.probability_le_one (toProjectDistribution P)
      (fun ω => X ω = true)
  have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hfalse : probability P (fun ω => X ω = false) = 1 - p := by
    simpa [p] using probability_false_eq_complement P X
  have htrue : probability P (fun ω => X ω = true) = p := rfl
  have hzero : probability P (fun _ : Ω => False) = 0 := probability_empty_event P
  have hone : probability P (fun _ : Ω => True) = 1 := probability_full_event P
  intro S T
  rcases bool_set_cases S with hS | hS | hS | hS <;>
    rcases bool_set_cases T with hT | hT | hT | hT
  all_goals
    simp [hS, hT, hfalse, htrue, hzero, hone]
    try simp only [abs_of_nonneg hp0, abs_of_nonneg h1mp]
    first
    | rw [abs_le]
      constructor <;> nlinarith [mul_nonneg hp0 h1mp]
    | nlinarith [mul_nonneg hp0 h1mp]

end
end SAP.P009a.WH.W1.P.T16_L1

open SAP.P009a.WH.W1.P.T16_L1
open SAP.P009a
open SAP.P009a.Bridge
open SAP.P009a.WH.W1
open scoped BigOperators Topology Classical

theorem SAP.P009a.WH.W1.T16_L1_proof : SAP.P009a.WH.W1.T16_L1 := by
  classical
  intro Ω hΩ P X b
  let p := probability P (fun ω => X ω = true)
  let q := probability P (fun ω => X ω = b)
  have hupper : mixingCoefficient P X X ≤ p * (1 - p) := by
    rw [mixing_correspondence]
    apply AronowAudit.P009.MixingBasics.alpha_le_of_event_bound
      (toProjectDistribution P) X X (p * (1 - p))
    intro S T
    simpa only [probability_correspondence, p] using boolean_event_bound P X S T
  have hq0 : 0 ≤ q := by
    dsimp [q]
    rw [probability_correspondence]
    exact AronowAudit.P009.probability_nonnegative (toProjectDistribution P)
      (fun ω => X ω = b)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [probability_correspondence]
    exact AronowAudit.P009.MixingBasics.probability_le_one (toProjectDistribution P)
      (fun ω => X ω = b)
  have hqvar : q * (1 - q) = p * (1 - p) := by
    dsimp [q, p]
    cases b
    · rw [probability_false_eq_complement]
      ring
    · rfl
  have hlow : q * (1 - q) ≤ mixingCoefficient P X X := by
    have h := AronowAudit.P009.MixingBasics.event_abs_le_alpha
      (toProjectDistribution P) X X ({b} : Set Bool) ({b} : Set Bool)
    have h' : |probability P (fun ω => X ω ∈ ({b} : Set Bool) ∧
        X ω ∈ ({b} : Set Bool)) -
        probability P (fun ω => X ω ∈ ({b} : Set Bool)) *
          probability P (fun ω => X ω ∈ ({b} : Set Bool))| ≤
        mixingCoefficient P X X := by
      simpa only [probability_correspondence, mixing_correspondence,
        Set.mem_singleton_iff] using h
    have hevent : probability P (fun ω => X ω ∈ ({b} : Set Bool) ∧
        X ω ∈ ({b} : Set Bool)) -
        probability P (fun ω => X ω ∈ ({b} : Set Bool)) *
          probability P (fun ω => X ω ∈ ({b} : Set Bool)) = q * (1 - q) := by
      simp only [Set.mem_singleton_iff, and_self]
      dsimp [q]
      ring
    have h'' : |q * (1 - q)| ≤ mixingCoefficient P X X := by
      rw [← hevent]
      exact h'
    rw [abs_of_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hq1))] at h''
    exact h''
  apply le_antisymm
  · calc
      mixingCoefficient P X X ≤ p * (1 - p) := hupper
      _ = q * (1 - q) := hqvar.symm
  · exact hlow
