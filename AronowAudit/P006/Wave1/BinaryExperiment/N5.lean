import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

set_option autoImplicit false
namespace AronowAudit.P006.Wave1.BinaryExperiment
open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

theorem n5_proof : N5 := by
  classical
  intro _h1 h3 n hn y1 μhat
  let E := binExp n hn y1 μhat
  have hconstant (π : Bool → ℝ) (hπ : Admissible π) (i : Fin n) (f : Bool → ℝ) :
      (E.law π)[fun ω => f (ω i).1 | E.covariateSigma i] =ᵐ[E.law π]
        fun ω => f (ω i).1 := by
    have h := h3 n hn y1 μhat π hπ i (fun a => f a.1)
    refine h.trans (Filter.Eventually.of_forall ?_)
    intro ω
    simp [Fintype.sum_bool, coinMass]
    <;> ring
  refine ⟨?_, ?_, ?_⟩
  · intro π hπ i
    exact ⟨hconstant π hπ i (fun _ => 0), hconstant π hπ i y1⟩
  · intro π hπ i
    have h := h3 n hn y1 μhat π hπ i (fun a => bit a.2)
    refine h.trans (Filter.Eventually.of_forall ?_)
    intro ω
    simp [Fintype.sum_bool, coinMass, bit, binExp]
  · intro π hπ i B _hB
    let f : Bool → ℝ := fun x => B.indicator (fun _ => (1 : ℝ)) (0, y1 x)
    have hleft := h3 n hn y1 μhat π hπ i (fun a => bit a.2 * f a.1)
    have hright := hconstant π hπ i f
    have hl : (E.law π)[fun ω => bit (E.T π i ω) * f (E.X i ω) |
        E.covariateSigma i] =ᵐ[E.law π] fun ω => π (E.X i ω) * f (E.X i ω) := by
      simpa [Fintype.sum_bool, coinMass, bit, E, binExp] using hleft
    show (E.law π)[fun ω => bit (E.T π i ω) * f (E.X i ω) | E.covariateSigma i] =ᵐ[E.law π]
      fun ω => π (E.X i ω) * (E.law π)[fun η => f (η i).1 | E.covariateSigma i] ω
    filter_upwards [hl, hright] with ω hL hR
    rw [hL, hR] <;> rfl

end
end AronowAudit.P006.Wave1.BinaryExperiment
