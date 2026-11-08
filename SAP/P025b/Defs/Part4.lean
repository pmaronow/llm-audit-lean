import Mathlib
import SAP.P025b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

/-- The two-unit census refutes the printed boundary proof steps. -/
def T12Statement : Prop :=
  (∀ i : Fin 2, inclusion censusDesign i = 1) ∧
  Monotone binaryTwo ∧
  (∀ k : ℕ, upperWeights (n := 2) 1 k = fun _ => 1) ∧
  ((1 : ℝ)/(1:ℝ) = 1 ∧
    upperValue binaryTwo (fun _ => 1) 1 0 = 1/2 ∧
    upperValue binaryTwo (fun _ => 1) 1 1 = 1/2 ∧
    upperValue binaryTwo (fun _ => 1) 1 2 = 1/2 ∧
    upperValue binaryTwo (fun _ => 1) 1 1 - upperValue binaryTwo (fun _ => 1) 1 0 ≤ 0 ∧
    ¬ upperValue binaryTwo (fun _ => 1) 1 0 ≤ binaryTwo 0 ∧
    IsLeast {k : Fin 2 | upperValue binaryTwo (fun _ => 1) 1 k.val ≥
      upperValue binaryTwo (fun _ => 1) 1 (k.val+1)} (0 : Fin 2) ∧
    upperCut binaryTwo (fun _ => 1) 1 (1 : Fin 2) ∧
    ((0:ℝ)*0-0+1*1*(0-1) = -1) ∧
    ((0:ℝ)-0*1+1*1*(0-1) = -1) ∧
    ¬ ratio binaryTwo (fun _ => 1) ![1,1] > ratio binaryTwo (fun _ => 1) ![1,1])

/-- The two pooled extrema converge, with their eventual domain made explicit. -/
def PooledConvergence {N J : ℕ} {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    (d : FiniteDesign (Fin N) κ) (cls : Fin N → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) : Prop :=
  ∀ᵐ ω ∂jointLaw d,
    (∀ᶠ h in atTop, pooledNonempty d h ω) ∧
    Tendsto (fun h => pooledLower d cls y α β h ω) atTop
      (nhds (lowerEndpoint y (classTotal d cls) α β)) ∧
    Tendsto (fun h => pooledUpper d cls y α β h ω) atTop
      (nhds (upperEndpoint y (classTotal d cls) α β))

/-- The repaired proposition includes both the unconditional and separated forms. -/
def T13Statement : Prop :=
  ∀ {N J : ℕ}, 0 < N → 0 < J →
    ∀ {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
      (d : FiniteDesign (Fin N) κ) (cls : Fin N → Fin J),
      Function.Surjective cls → ∀ (y : Fin J → ℝ), StrictMono y →
      ∀ (α β : ℝ), 0 < α → α ≤ β → β ≤ 1 →
      (∀ i, α ≤ inclusion d i ∧ inclusion d i ≤ β) →
      PooledConvergence d cls y α β ∧
      (separation y (classTotal d cls) (β/α) → PooledConvergence d cls y α β)

/-- A random six-unit design violates separation but has constant pooled extrema. -/
def T14Statement : Prop :=
  (∀ i : Fin 3 × Fin 2, inclusion pairDesign i = 1/2) ∧
  (∀ j : Fin 3, classTotal pairDesign Prod.fst j = 1) ∧
  (∀ ω : Fin 2 × Fin 2 × Fin 2, ∀ j : Fin 3,
    classCount pairDesign Prod.fst j ω = 1) ∧
  upperValue threeOutcomes (fun _ => 1) 2 1 = 2 ∧
  upperValue threeOutcomes (fun _ => 1) 2 2 = 2 ∧
  IsLeast (attainable threeOutcomes (fun _ => 1) (1/4) (1/2)) (5/4) ∧
  IsGreatest (attainable threeOutcomes (fun _ => 1) (1/4) (1/2)) 2 ∧
  (∀ ω : ℕ → Fin 2 × Fin 2 × Fin 2, ∀ h : ℕ, 0 < h → pooledNonempty pairDesign h ω) ∧
  ((∀ i : Fin 3 × Fin 2, (1/4 : ℝ) ≤ inclusion pairDesign i ∧ inclusion pairDesign i ≤ 1/2) ∧
    ¬ separation threeOutcomes (classTotal pairDesign Prod.fst) 2 ∧
    lowerEndpoint threeOutcomes (classTotal pairDesign Prod.fst) (1/4) (1/2) = 5/4 ∧
    upperEndpoint threeOutcomes (classTotal pairDesign Prod.fst) (1/4) (1/2) = 2 ∧
    (∀ ω : ℕ → Fin 2 × Fin 2 × Fin 2, ∀ h : ℕ, 0 < h →
      pooledLower pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω = 5/4 ∧
      pooledUpper pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω = 2) ∧
    (∀ ω : ℕ → Fin 2 × Fin 2 × Fin 2,
      Tendsto (fun h => pooledLower pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω) atTop (nhds (5/4)) ∧
      Tendsto (fun h => pooledUpper pairDesign Prod.fst threeOutcomes (1/4) (1/2) h ω) atTop (nhds 2)))

end
end SAP.P025b
