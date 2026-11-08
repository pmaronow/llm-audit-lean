import SAP.P004b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

def T27Statement : Prop :=
  BoundedOutcomes sparsePopulation ∧ QuadraticSpacing sparsePopulation ∧
  NEDConditions sparsePopulation (1/2) 1 ∧ KernelConditions uniformKernel ∧
  Tendsto sparseBandwidth atTop atTop ∧
  Asymptotics.IsLittleO atTop sparseBandwidth (fun N => (N : ℝ)^(1/6 : ℝ)) ∧
  (∀ N, 3 ≤ N → WellDefined (sparsePopulation N) 1) ∧
  LiminfAtLeast (kernelHomophily sparsePopulation (1/2) 1 uniformKernel sparseBandwidth) 0 ∧
  Tendsto (fun N : ℕ => (N : ℝ)*variance (fun _ => 1/2)
    (linearHajek (fun _ => 1/2) (circleAverage (sparsePopulation N) 1))) atTop (nhds 0) ∧
  Tendsto (fun N => prob (fun _ : Fin N => 1/2) (fun z => ¬ SparseGood z)) atTop (nhds 0) ∧
  (∀ N (hN : 10 ≤ N) (z : Assignment N), SparseGood z →
    let R := circleAverage (sparsePopulation N) 1
    let Q := distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N)
    ValidInterval R Q z ∧
      (GuardedInterval (1/2) R Q (-2) 2 z ↔ z ⟨0, by omega⟩ = true)) ∧
  (∀ N (hN : 0 < N), prob (fun _ : Fin N => 1/2) (fun z => z ⟨0,hN⟩ = true) = 1/2) ∧
  0 < 2*(1-normalCDF 2) ∧ 2*(1-normalCDF 2) < 1 ∧
  (3/4 : ℝ) ≤ 1-2*(1-normalCDF 2)

def T28Statement : Prop :=
  ∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
  ∀ (P : PopulationSequence Space) (p d : ℝ)
    (K : ℝ → ℝ) (bandwidth : ℕ → ℝ) (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d)
    (hb : BoundedOutcomes P) (hWD : ∀ N, WellDefined (P N) d)
    (hNED : NEDConditions P p d) (hmetric : MetricNodeDistances P) (hspacing : QuadraticSpacing P) (hK : KernelConditions K)
    (hbpos : ∀ N, 0 < bandwidth N) (hbdiv : Tendsto bandwidth atTop atTop)
    (hbrate : Asymptotics.IsLittleO atTop bandwidth (fun N => (N : ℝ)^(1/6 : ℝ)))
    (hhom : LiminfAtLeast (kernelHomophily P p d K bandwidth) 0),
    let R := circleSequence P d
    let D := fun N => nodeSeparation (P N)
    let Vhac := fun N z => kernelVariance z (residual (R N) z) (distanceKernel (D N) K (bandwidth N))
    InProb (fun _ _ => p) (fun N z => armRestricted (fun z => N*(Vhac N z-nedV1 p (R N) (D N) K (bandwidth N) z)) z) ∧
    InProb (fun _ _ => p) (fun N z => armRestricted (fun z => N*(nedV1 p (R N) (D N) K (bandwidth N) z-
      nedV2 p (R N) (D N) K (bandwidth N) z)) z) ∧
    InProb (fun _ _ => p) (fun N z => armRestricted (fun z => N*(nedV2 p (R N) (D N) K (bandwidth N) z-
      expect (fun _ => p) (nedV2 p (R N) (D N) K (bandwidth N)))) z) ∧
    LiminfAtLeast (fun N => (N : ℝ)*(expect (fun _ => p) (nedV2 p (R N) (D N) K (bandwidth N))-
      variance (fun _ => p) (linearHajek (fun _ => p) (R N)))) 0 ∧
    (Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (R N))) →
      ∀ α : ℝ, 0 < α → α < 1 → FiniteQuantile (α/2) → FiniteQuantile (1-α/2) →
      Conservative (fun N => prob (fun _ => p)
        (GuardedInterval p (R N) (distanceKernel (D N) K (bandwidth N))
          (normalQuantile (α/2)) (normalQuantile (1-α/2)))) α)

end
end SAP.P004b
