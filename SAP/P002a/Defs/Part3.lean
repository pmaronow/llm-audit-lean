import SAP.P002a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

def negativeDeltaModel (m : ℕ) : CovPopulation (12*m) 1 where
  pop := {y := fun i _ => if i.val % 2 = 0 then -1 else 1,
          d := fun _ a => a, n1 := 2*m}
  x := fun i _ => if i.val % 4 < 2 then -1 else 1

def centringModel : Population 4 where
  y := fun i a => (if i.val < 2 then -1 else 1) + (if a then 2 else 0)
  d := fun _ a => a
  n1 := 2

def signModel (m : ℕ) : Population (2*m) where
  y := fun i _ => if i.val < m then -1 else 1
  d := fun _ a => a
  n1 := m

def interceptExampleX (i : Fin 2) (_ : Fin 1) : ℝ := if i = 0 then 2 else -2

def leastRayleigh {n k : ℕ} (x : Fin n → Fin k → ℝ) : ℝ :=
  sInf {t | ∃ b : Fin k → ℝ, normSq b=1 ∧ mean (fun i => (dotProduct (x i) b)^2)=t}

def infCoverageTheta (n : ℕ) (δ r A α : ℝ) : ℝ≥0∞ :=
  ⨅ β : ℝ, ⨅ P : {P : Population n // Theta P δ r A ∧ late P = β},
    ENNReal.ofReal (coverage P.val β α)

def infCoverageXi (n k : ℕ) (δ e A B r α : ℝ) : ℝ≥0∞ :=
  ⨅ β : ℝ, ⨅ P : {P : CovPopulation n k // Xi P δ e A B r ∧ late P.pop = β},
    ENNReal.ofReal (adjustedCoverage P.val β α)

def degenerateModel (n : ℕ) (β : ℝ) : Population n where
  y := fun _ a => if a then β else 0
  d := fun _ a => a
  n1 := n/2

def gridX {n : ℕ} (i : Fin n) (_ : Fin 1) : ℝ := (2*((i.val : ℝ)+1)-(n : ℝ)-1)/(n : ℝ)

def degenerateCovModel (n : ℕ) (β : ℝ) : CovPopulation n 1 :=
  ⟨degenerateModel n β, gridX⟩

def RandomizationSequence {Ω : Type*} [MeasurableSpace Ω] {sizes : ℕ → ℕ}
    (P : ∀ j, Population (sizes j)) (μ : Measure Ω)
    (Z : ∀ j, Ω → Finset (Fin (sizes j))) : Prop :=
  ∀ j (E : Finset (Fin (sizes j)) → Prop),
    MeasurableSet {ω | E (Z j ω)} ∧
      μ {ω | E (Z j ω)} = ENNReal.ofReal (probability (P j) E)

def nearSingularModel (m : ℕ) : CovPopulation (2*m) 1 :=
  let t : Fin (2*m) → ℝ := fun i => (2*(i.val % m : ℕ)-(m : ℝ)+1)/((m : ℝ)-1)
  let vm : ℝ := ((m : ℝ)+1)/(3*((m : ℝ)-1))
  let η : ℝ := 1/(2 : ℝ)^((2*m)^2)
  {pop := {y := fun i _ => t i+(1/10)*(t i^2-vm), d := fun _ a => a, n1 := m},
   x := fun i _ => (if i.val < m then 1 else -1)+η*t i}

def oddNearModel (n : ℕ) : CovPopulation n 1 :=
  let x : Fin n → Fin 1 → ℝ := fun i _ => 2*(i.val : ℝ)/((n : ℝ)-1)-1
  {pop := {y := fun i _ => (1/10)*(x i 0^2-mean (fun l => x l 0^2)),
           d := fun _ a => a, n1 := n/2}, x := x}

def IndependentAssignments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (sizes : ℕ → ℕ) (Z : ∀ n, Ω → Finset (Fin (sizes n))) : Prop :=
  ∀ (I : Finset ℕ) (E : ∀ n, Finset (Fin (sizes n)) → Prop),
    μ {ω | ∀ n ∈ I, E n (Z n ω)} = ∏ n ∈ I, μ {ω | E n (Z n ω)}

/-- Sizes with a nonempty unadjusted parameter class. -/
def thetaSizes (δ r A : ℝ) : Set ℕ :=
  {n | ∃ P : Population n, Theta P δ r A}

/-- Sizes with a nonempty adjusted parameter class. -/
def xiSizes (k : ℕ) (δ e A B r : ℝ) : Set ℕ :=
  {n | ∃ P : CovPopulation n k, Xi P δ e A B r}

end
end SAP.P002a
