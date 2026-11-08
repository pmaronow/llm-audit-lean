import SAP.P004c.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004c
open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section

def designMatrix {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin 2) ℝ :=
  fun i a => if a = 0 then 1 else bit (z i)

def lambda {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ :=
  bit (z i) / armCount z true - (1-bit (z i)) / armCount z false

def sandwich {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let X := designMatrix z
  let A := (X.transpose * X)⁻¹
  A * (X.transpose * Matrix.of (fun i j => e i * e j * Q i j) * X) * A

def kernelVariance {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, lambda z i * lambda z j * e i * e j * Q i j

def spectralKernel {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) (trim : Bool) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ k, (if trim then max (values k) 0 else values k) * vectors i k * vectors j k

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

/-- Appendix C requires the node distances themselves to form a metric. -/
def MetricNodeDistances (P : PopulationSequence Space) : Prop :=
  ∀ N, (∀ i j, 0 ≤ nodeSeparation (P N) i j) ∧
    (∀ i j, nodeSeparation (P N) i j = 0 ↔ i = j) ∧
    (∀ i j, nodeSeparation (P N) i j = nodeSeparation (P N) j i) ∧
    (∀ i j k, nodeSeparation (P N) i k ≤
      nodeSeparation (P N) i j + nodeSeparation (P N) j k)

def conditionOn {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N))
    (U : Assignment N → ℝ) (z : Assignment N) : ℝ :=
  expect p (fun z' => if ∀ j ∈ J, z' j = z j then U z' else 0) /
    (∏ j ∈ J, coin (p j) (z j))

def l2Norm {N : ℕ} (p : Fin N → ℝ) (U : Assignment N → ℝ) : ℝ :=
  Real.sqrt (expect p (fun z => (U z)^2))

/-- Uniform L2 near-epoch dependence of size -4 on the actual assignment field. -/
def NEDConditions (P : PopulationSequence Space) (p d : ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, ∃ g : ∀ N, Fin N → ℝ, ∃ G : ℝ,
    (∀ s, 0 ≤ s → 0 ≤ ψ s) ∧ AntitoneOn ψ (Set.Ici 0) ∧
    Tendsto ψ atTop (nhds 0) ∧
    (∃ exponent : ℝ, 4 < exponent ∧ ∃ C S : ℝ, 0 < S ∧
      ∀ s, S ≤ s → ψ s ≤ C * s^(-exponent)) ∧
    (∀ N i, 0 < g N i ∧ g N i ≤ G) ∧
    (∀ N i s, 0 ≤ s → l2Norm (fun _ => p)
      (fun z => circleAverage (P N) d i z -
        conditionOn (fun _ => p) (ball (nodeSeparation (P N)) i s)
          (circleAverage (P N) d i) z) ≤ g N i*ψ s)

/-- The stronger spacing condition actually required by the credited NED theorem:
one eventual threshold works simultaneously for every radius. -/
def QuadraticSpacing (P : PopulationSequence Space) : Prop :=
  ∃ Cb : ℝ, 0 < Cb ∧ ∀ᶠ N in atTop, ∀ i s, 0 ≤ s →
    ((ball (nodeSeparation (P N)) i s).card : ℝ) ≤ Cb*(1+s^2)

def BoundedOutcomes (P : PopulationSequence Space) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ᶠ N in atTop, ∀ x z, |(P N).outcome x z| < b

end
end SAP.P004c
