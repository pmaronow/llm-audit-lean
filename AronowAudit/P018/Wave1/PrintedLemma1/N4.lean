import AronowAudit.P018.Wave1.PrintedLemma1.N3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace AronowAudit.P018.Wave1.PrintedLemma1
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

def d01 : Dyad 3 := ⟨{0,1}, by decide⟩
def d02 : Dyad 3 := ⟨{0,2}, by decide⟩
def d12 : Dyad 3 := ⟨{1,2}, by decide⟩

theorem dyad_three : (Finset.univ : Finset (Dyad 3)) = {d01,d02,d12} := by decide

theorem score_intercept (ω : Fin 3 → ℝ) :
    scoreSum nonlinearKernel ω 0 =
      (ω 0 + ω 1)^2 + (ω 0 + ω 2)^2 + (ω 1 + ω 2)^2 - 2 := by
  simp only [scoreSum, Finset.sum_apply, dyad_three]
  rw [Finset.sum_insert (by decide : d01 ∉ ({d02, d12} : Finset (Dyad 3))),
    Finset.sum_insert (by decide : d02 ∉ ({d12} : Finset (Dyad 3))),
    Finset.sum_singleton]
  simp only [score, Pi.smul_apply, smul_eq_mul, epsilon_formula]
  simp [design, nonlinearKernel, d01, d02, d12, firstUnit, secondUnit, members]
  <;> ring

theorem n4_proof : N4 := by
  change covariance (fun ω : Fin 3 → ℝ => scoreSum nonlinearKernel ω 0)
    (fun ω : Fin 3 → ℝ => scoreSum nonlinearKernel ω 0)
    (Measure.pi (fun _ : Fin 3 => uniformUnitLaw)) = _
  have hf : (fun ω : Fin 3 → ℝ => scoreSum nonlinearKernel ω 0) =
      (fun ω => (ω 0 + ω 1)^2 + (ω 0 + ω 2)^2 + (ω 1 + ω 2)^2 - 2) :=
    funext score_intercept
  rw [hf]
  exact covariance_self (by fun_prop)
end
end AronowAudit.P018.Wave1.PrintedLemma1
