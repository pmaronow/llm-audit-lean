import AronowAudit.P004.Wave1.FiniteConditioning.FC3

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- A function of retained coordinates is fixed by conditioning. -/
theorem conditionOn_of_depends {N : ℕ} (p : Fin N → ℝ) (hp : Admissible p)
    (K : Finset (Fin N)) (F : Assignment N → ℝ)
    (hF : ∀ z z', (∀ k ∈ K, z k = z' k) → F z = F z') :
    conditionOn p K F = F := by
  classical
  funext z
  have hconst : conditionOn p K (fun _ => (1 : ℝ)) z = 1 :=
    (fc2_proof p hp K).1 1 z
  have hpull := (fc2_proof p hp K).2.2.2 F (fun _ => 1) hF z
  simpa only [mul_one, hconst] using hpull

/-- Both tower identities. The second uses expectation preservation on each `I`-cylinder. -/
theorem fc4_proof : FC4 := by
  classical
  intro N p hp I J hIJ U
  constructor
  · apply conditionOn_of_depends p hp J
    intro z z' hzz'
    apply fc1_proof p I U z z'
    intro i hi
    exact hzz' i (hIJ hi)
  · funext z
    let F : Assignment N → ℝ := fun w => if ∀ i ∈ I, w i = z i then 1 else 0
    have hF : ∀ w w', (∀ j ∈ J, w j = w' j) → F w = F w' := by
      intro w w' hww'
      have he : (∀ i ∈ I, w i = z i) ↔ (∀ i ∈ I, w' i = z i) := by
        constructor
        · intro hw i hi
          exact (hww' i (hIJ hi)).symm.trans (hw i hi)
        · intro hw' i hi
          exact (hww' i (hIJ hi)).trans (hw' i hi)
      dsimp only [F]
      exact if_congr he rfl rfl
    have hmask (V : Assignment N → ℝ) :
        (fun w => F w * V w) =
          (fun w => if ∀ i ∈ I, w i = z i then V w else 0) := by
      funext w
      dsimp only [F]
      split_ifs <;> simp only [one_mul, zero_mul]
    have hpull : conditionOn p J (fun w => F w * U w) =
        (fun w => F w * conditionOn p J U w) := by
      funext w
      exact (fc2_proof p hp J).2.2.2 F U hF w
    have hnum :
        expect p (fun w => if ∀ i ∈ I, w i = z i then conditionOn p J U w else 0) =
          expect p (fun w => if ∀ i ∈ I, w i = z i then U w else 0) := by
      rw [← hmask (conditionOn p J U), ← hmask U]
      calc
        expect p (fun w => F w * conditionOn p J U w) =
            expect p (conditionOn p J (fun w => F w * U w)) := by rw [hpull]
        _ = expect p (fun w => F w * U w) := fc3_proof p hp J (fun w => F w * U w)
    change expect p (fun w => if ∀ i ∈ I, w i = z i then conditionOn p J U w else 0) /
        (∏ i ∈ I, coin (p i) (z i)) =
      expect p (fun w => if ∀ i ∈ I, w i = z i then U w else 0) /
        (∏ i ∈ I, coin (p i) (z i))
    rw [hnum]

end
end AronowAudit.P004.Wave1.FiniteConditioning
