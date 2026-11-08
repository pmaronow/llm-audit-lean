import SAP.P004b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

abbrev PopulationSequence (Space : ℕ → Type*) [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] := ∀ N, SpatialPopulation N (Space N)

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

def MetricNodeDistances (P : PopulationSequence Space) : Prop :=
  ∀ N, (∀ i j, 0 ≤ nodeSeparation (P N) i j) ∧
    (∀ i j, nodeSeparation (P N) i j = 0 ↔ i = j) ∧
    (∀ i j, nodeSeparation (P N) i j = nodeSeparation (P N) j i) ∧
    (∀ i j k, nodeSeparation (P N) i k ≤
      nodeSeparation (P N) i j + nodeSeparation (P N) j k)

def SpatialLocalConditions (P : PopulationSequence Space) : Prop :=
  (∃ b : ℝ, 0 < b ∧ ∀ᶠ N in atTop, ∀ x z, |(P N).outcome x z| < b) ∧
  (∃ h : ℝ → ℝ, (∀ d, 0 ≤ d → 0 ≤ h d) ∧
    ∀ d, 0 ≤ d → ∀ᶠ N in atTop,
      LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) (h d)) ∧
  (∃ c : ℝ → ℝ, ∀ r, 0 ≤ r → ∀ᶠ N in atTop, ∀ i,
    ((ball (nodeSeparation (P N)) i r).card : ℝ) ≤ c r)

def circleSequence (P : PopulationSequence Space) (d : ℝ) (N : ℕ) : CircleTable N :=
  circleAverage (P N) d

def uniformKernel (t : ℝ) : ℝ := if 0 ≤ t ∧ t ≤ 1 then 1 else 0

def distanceKernel {N : ℕ} (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => K (D i j/b)

def conditionOn {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N))
    (U : Assignment N → ℝ) (z : Assignment N) : ℝ :=
  expect p (fun z' => if ∀ j ∈ J, z' j = z j then U z' else 0) /
    (∏ j ∈ J, coin (p j) (z j))

def l2Norm {N : ℕ} (p : Fin N → ℝ) (U : Assignment N → ℝ) : ℝ :=
  Real.sqrt (expect p (fun z => (U z)^2))

def NEDConditions (P : PopulationSequence Space) (p d : ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, ∃ g : ∀ N, Fin N → ℝ, ∃ G : ℝ,
    (∀ s, 0 ≤ s → 0 ≤ ψ s) ∧ AntitoneOn ψ (Set.Ici 0) ∧
    Tendsto ψ atTop (nhds 0) ∧
    (∃ exponent : ℝ, 4 < exponent ∧ ∃ C S : ℝ, 0 < S ∧
      ∀ s, S ≤ s → ψ s ≤ C * s^(-exponent)) ∧
    (∀ N i, 0 < g N i ∧ g N i ≤ G) ∧
    (∀ N i s, 0 ≤ s → l2Norm (fun _ => p)
      (fun z => circleAverage (P N) d i z -
        conditionOn (fun _ => p) (ball (nodeSeparation (P N)) i s) (circleAverage (P N) d i) z) ≤ g N i*ψ s)

def QuadraticSpacing (P : PopulationSequence Space) : Prop :=
  ∃ Cb : ℝ, 0 < Cb ∧ ∀ᶠ N in atTop, ∀ i s, 0 ≤ s →
    ((ball (nodeSeparation (P N)) i s).card : ℝ) ≤ Cb*(1+s^2)

def BoundedOutcomes (P : PopulationSequence Space) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ᶠ N in atTop, ∀ x z, |(P N).outcome x z| < b

def KernelConditions (K : ℝ → ℝ) : Prop :=
  K 0 = 1 ∧ (∀ t, 1 < t → K t = 0) ∧
  (∃ Kmax : ℝ, ∀ t, 0 ≤ t → |K t| < Kmax) ∧
  ∃ ε C : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < C ∧ ∀ t, 0 ≤ t → t < ε → |K t-1| ≤ C*|t|

def kernelHomophily (P : PopulationSequence Space) (p d : ℝ)
    (K : ℝ → ℝ) (bandwidth : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ i, ∑ j, K (nodeSeparation (P N) i j / bandwidth N) *
    (nodeEffect (fun _ => p) (circleAverage (P N) d) i-ame (fun _ => p) (circleAverage (P N) d)) *
    (nodeEffect (fun _ => p) (circleAverage (P N) d) j-ame (fun _ => p) (circleAverage (P N) d))) / N

def nedEpsilon {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ)
    (i : Fin N) (z : Assignment N) : ℝ :=
  residualContrast (fun _ => p) R (fun _ a => if a then μ1 else μ0) i z / N

def nedVRow {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b μ1 μ0 : ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  ∑ j ∈ ball D i b, nedEpsilon p R μ1 μ0 i z * nedEpsilon p R μ1 μ0 j z * K (D i j/b)

def nedV1 {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℝ) (z : Assignment N) : ℝ :=
  ∑ i, nedVRow p R D K b (armMean R z true) (armMean R z false) i z

def nedV2 {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℝ) (z : Assignment N) : ℝ :=
  ∑ i, nedVRow p R D K b (barMu (fun _ => p) R true) (barMu (fun _ => p) R false) i z

def tailEnvelope (P : PopulationSequence Space) (φ : ℝ → ℝ) (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range (fun i : Fin N => ∑ j ∈ (ball (nodeSeparation (P N)) i (r N))ᶜ,
    φ (nodeSeparation (P N) i j)))

def sparseTable (N : ℕ) : CircleTable N :=
  fun i z => if i.val = 0 then 1/4+3/4*bit (z i) else 0

def sparsePopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {planePoint (((i : ℝ)+1)*N^2) 0}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin N, Measure.dirac (planePoint (((i : ℝ)+1)*N^2) 0)
  outcome := fun x z => ∑ i : Fin N, if x = planePoint (((i : ℝ)+1)*N^2) 0 then sparseTable N i z else 0
  bands := fun d => Set.Icc 0 d

def sparseBandwidth (N : ℕ) : ℝ := (⌊(N : ℝ)^(1/12 : ℝ)⌋₊ : ℝ)

end
end SAP.P004b
