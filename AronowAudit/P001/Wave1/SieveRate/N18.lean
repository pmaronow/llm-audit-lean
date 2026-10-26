import AronowAudit.P001.Wave1.SieveRateBlueprint

/-!
# The finite design/response product law

The IID fields of N1 already give the first-n joint law. Restrict independence along
`Fin.val`, use the equal one-observation laws, and split the finite product of pairs.
This is equivalent to restriction of the infinite product, without reindexing a finset.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n18_proof : N18 := by
  intro hN1 n
  letI : IsProbabilityMeasure sieveMu := hN1.1
  let pair : Fin n → (ℕ → ℝ × ℝ) → ℝ × ℝ :=
    fun i ω => (sieveX i ω, sieveY i ω)
  have hmeas (i : Fin n) : Measurable (pair i) := hN1.2.1.1 i
  have hind : iIndepFun pair sieveMu :=
    hN1.2.1.2.1.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
  have hlaw (i : Fin n) : sieveMu.map (pair i) = sieveNu :=
    (hN1.2.1.2.2 i).map_eq.trans hN1.2.2.1
  have hfinite : sieveMu.map (fun ω => fun i : Fin n => pair i ω) =
      Measure.pi (fun _ : Fin n => sieveNu) := by
    calc
      sieveMu.map (fun ω => fun i : Fin n => pair i ω) =
          Measure.pi (fun i : Fin n => sieveMu.map (pair i)) :=
        hind.map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable)
      _ = Measure.pi (fun _ : Fin n => sieveNu) := by simp only [hlaw]
  let split : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have hcollect : Measurable (fun ω => fun i : Fin n => pair i ω) :=
    Measurable.of_eval hmeas
  have hfirst : firstN n = split ∘ (fun ω => fun i : Fin n => pair i ω) := rfl
  calc
    sieveMu.map (firstN n) =
        (sieveMu.map (fun ω => fun i : Fin n => pair i ω)).map split := by
      simpa only [hfirst] using (Measure.map_map split.measurable hcollect).symm
    _ = (Measure.pi (fun _ : Fin n => sieveNu)).map split := by rw [hfinite]
    _ = (unifVec n).prod (gaussVec n) := by
      exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
        (fun _ => uniformLaw 0 1) (fun _ => gaussianReal 0 1)).map_eq

end

end AronowAudit.P001.Wave1.SieveRate
