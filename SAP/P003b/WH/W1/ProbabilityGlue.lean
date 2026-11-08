import SAP.P003b.WH.W1.T7Exports

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1
open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- Sum a conditional finite-uniform bound over the histories that actually occur. -/
lemma average_history {A H : Type*} [Fintype A] [Nonempty A]
    (history : A → H) (E : A → Prop) (δ : ℝ)
    (hc : ∀ h, 0 < uniformProb (fun a => history a = h) →
      uniformProb (fun a => history a = h ∧ E a) /
        uniformProb (fun a => history a = h) ≤ δ) :
    uniformProb E ≤ δ := by
  classical
  let hs : Finset H := Finset.univ.image history
  have hf (h : H) (hh : h ∈ hs) : 0 < uniformProb (fun a => history a = h) := by
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hh
    unfold uniformProb
    apply div_pos
    · exact_mod_cast (Finset.card_pos.mpr ⟨a,by simp [ha]⟩)
    · exact_mod_cast Fintype.card_pos
  have htotal : (Fintype.card A : ℝ) =
      ∑ h ∈ hs, ((Finset.univ.filter fun a => history a = h).card : ℝ) := by
    have ht := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset A))
      (t := hs) (f := history) (by intro a _; exact Finset.mem_image.mpr ⟨a,by simp,rfl⟩)
    exact_mod_cast ht
  have hevent : ((Finset.univ.filter E).card : ℝ) =
      ∑ h ∈ hs, ((Finset.univ.filter fun a => history a = h ∧ E a).card : ℝ) := by
    have ht := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter E)
      (t := hs) (f := history) (by intro a _; exact Finset.mem_image.mpr ⟨a,by simp,rfl⟩)
    simp only [Finset.filter_filter] at ht
    have hswap (h : H) :
        (Finset.univ.filter fun a => E a ∧ history a = h) =
        (Finset.univ.filter fun a => history a = h ∧ E a) := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,and_comm]
    simp_rw [hswap] at ht
    exact_mod_cast ht
  have hsum : ∑ h ∈ hs, uniformProb (fun a => history a = h) = 1 := by
    unfold uniformProb
    rw [← Finset.sum_div,← htotal]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)
  calc
    uniformProb E = ∑ h ∈ hs, uniformProb (fun a => history a = h ∧ E a) := by
      unfold uniformProb
      rw [hevent,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro h hh
      congr 2
      congr 1
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ ≤ ∑ h ∈ hs, δ*uniformProb (fun a => history a = h) := by
      apply Finset.sum_le_sum
      intro h hh
      exact (div_le_iff₀ (hf h hh)).mp (hc h (hf h hh))
    _ = δ := by rw [← Finset.mul_sum,hsum,mul_one]

lemma endpointErrors (hupper : W1T7Conditional false) (hlower : W1T7Conditional true) :
    W1T7Errors := by
  intro n m K o α ε ht hm ho hK hα hε lo badReject
  have hmn : m ≤ n := by dsimp [Counts.total] at ht; omega
  letI : Nonempty (Assignment n m) :=
    AronowAudit.P003.Wave1.GLP0032B6_assignment_nonempty n m hmn
  have hc : W1T7Conditional lo := by cases lo <;> assumption
  have hslot (i : Fin (testBudget n)) :
      uniformProb (w1Error lo badReject i.val α ε o : W1Pool n m K → Prop) ≤
        Real.exp (-2*(K : ℝ)*ε^2) := by
    apply average_history (w1History lo i.val α ε o)
    intro h hp
    exact (hc n m K o α ε ht hm ho hK hα hε i.val i.isLt h hp).2.2 badReject
  have hu := AronowAudit.P003.Wave1.GLP0032B6_prob_union
    (fun i : Fin (testBudget n) => w1Error lo badReject i.val α ε o :
      Fin (testBudget n) → W1Pool n m K → Prop)
  simp only [uniformProb_eq] at hu
  have he : (fun p : W1Pool n m K => ∃ i < testBudget n, w1Error lo badReject i α ε o p) =
      (fun p => ∃ i : Fin (testBudget n), w1Error lo badReject i.val α ε o p) := by
    funext p
    apply propext
    exact ⟨fun ⟨i,hi,he⟩ => ⟨⟨i,hi⟩,he⟩,fun ⟨i,he⟩ => ⟨i.val,i.isLt,he⟩⟩
  rw [he]
  calc
    _ ≤ ∑ i : Fin (testBudget n), uniformProb (w1Error lo badReject i.val α ε o) := hu
    _ ≤ ∑ _ : Fin (testBudget n), Real.exp (-2*(K : ℝ)*ε^2) :=
      Finset.sum_le_sum (fun i _ => hslot i)
    _ = _ := by simp

/-- Discard an independent nuisance coordinate from a finite uniform probability. -/
lemma probability_first {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (E : A → Prop) : uniformProb (fun ω : A × B => E ω.1) = uniformProb E := by
  rw [← uniformProb_eq, AronowAudit.P003.Wave1.GLP0032B6_prob_avg,
    AronowAudit.P003.Wave1.GLP0032B6_avg_prod]
  change AronowAudit.P003.Wave1.GLP0032B6_avg (fun _ : B =>
    AronowAudit.P003.Wave1.GLP0032B6_avg (fun a : A => if E a then 1 else 0)) = _
  rw [AronowAudit.P003.Wave1.GLP0032B6_avg_const]
  exact (AronowAudit.P003.Wave1.GLP0032B6_prob_avg E).symm.trans (uniformProb_eq E)

end
end SAP.P003b.WH.W1
