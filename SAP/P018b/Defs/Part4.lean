import SAP.P018b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

def orderedSampleFacts : Prop :=
dyadMeat orderedWitness = !![91] ∧
    meat sixMembers orderedWitness = !![385] ∧
    (∑ i : Fin 4, outer (unitScore sixMembers orderedWitness i)
      (unitScore sixMembers orderedWitness i)) = !![476] ∧
    (∑ i : Fin 4, nonincidentMeat sixMembers (fun _ => 1)
      (fun d _ => orderedWitness d) i) = !![182] ∧
    (476 + 2 * 182 - 91 - 2 * 91 : ℝ) = 567 ∧ (567 : ℝ) ≠ 385

/-- Scores are arbitrary record vectors; substituting e_dt X_dt gives the paper's arrays. -/
def T15Statement : Prop :=
  (∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (s : E → Finset V) (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) (P : Mat k),
    let b := fun d => ∑ t, q d t
    (∀ i, orderedNonincidentMeat s T q i = (2 : ℝ) • nonincidentMeat s T q i) ∧
    (∑ i, orderedNonincidentMeat s T q i) =
      (2*((Fintype.card V : ℝ)-2)) • individualMeat T q ∧
    (∑ i, orderedClusterMeat s T q i) - dyadMeat b -
      ((Fintype.card V : ℝ)-2) • individualMeat T q =
        meat s b + ((Fintype.card V : ℝ)-2) • individualMeat T q ∧
    (∑ i, sandwich P (orderedClusterMeat s T q i)) - sandwich P (dyadMeat b) -
      ((Fintype.card V : ℝ)-2) • sandwich P (individualMeat T q) =
        sandwich P (meat s b) + ((Fintype.card V : ℝ)-2) • sandwich P (individualMeat T q) ∧
    (3 ≤ Fintype.card V → sandwich P (individualMeat T q) ≠ 0 →
      (∑ i, sandwich P (orderedClusterMeat s T q i)) - sandwich P (dyadMeat b) -
        ((Fintype.card V : ℝ)-2) • sandwich P (individualMeat T q) ≠ sandwich P (meat s b))) ∧
  (orderedSampleFacts ∧
    individualMeat (fun _ : Fin 6 => 1) (fun d _ => orderedWitness d) = !![91] ∧
    (∑ i : Fin 4, orderedNonincidentMeat sixMembers (fun _ => 1)
      (fun d _ => orderedWitness d) i) = !![364] ∧
    (476 + 182 - 91 - 2*91 : ℝ) = 385 ∧
    (476 + 364 - 91 - 2*91 : ℝ) = 567 ∧ (567 : ℝ) = 385+182 ∧
    (6^2 + 10^2 + 12^2 + 14^2 : ℝ) = 476)

/-- Every dyad is a distinct two-element unit set; records may be arbitrary. -/
def T16Statement : Prop :=
  ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (s : E → Finset V) (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) (P : Mat k),
    let b := fun d => ∑ t, q d t
    (meat s b = (∑ i, clusterMeat s T q i) - dyadMeat b -
      ((Fintype.card V : ℝ)-2) • individualMeat T q ∧
    sandwich P (meat s b) = (∑ i, sandwich P (clusterMeat s T q i)) -
      sandwich P (dyadMeat b) -
      ((Fintype.card V : ℝ)-2) • sandwich P (individualMeat T q)) ∧
    (meat s b - dyadMeat b = (∑ i, crossUnitMeat s b i) ∧
    (∀ i, clusterMeat s T q i = crossUnitMeat s b i +
      incidentDiagonalMeat s b i + nonincidentMeat s T q i) ∧
    (∑ i, incidentDiagonalMeat s b i) = (2 : ℝ) • dyadMeat b ∧
    (∑ i, nonincidentMeat s T q i) = ((Fintype.card V : ℝ)-2) • individualMeat T q ∧
    meat s b = dyadMeat b + (∑ i, crossUnitMeat s b i))

def negativeSampleFacts : Prop :=
sampleGram negativeX = !![6,10;10,20] ∧
    (sampleGram negativeX).det = 20 ∧
    sampleOLS negativeX negativeY = ![3,2/5] ∧
    (∀ d, fittedResidual negativeX negativeY d = negativeE d) ∧
    (∑ d, score (negativeX d) (negativeE d)) = 0 ∧
    sampleVariance sixMembers negativeX negativeY = !![-17/50,21/125;21/125,-58/625] ∧
    (sampleVariance sixMembers negativeX negativeY) 0 0 < 0 ∧
    (sampleVariance sixMembers negativeX negativeY) 1 1 < 0
def negativePopulationFacts : Prop :=
Standing finiteNegativeKernel ∧ populationGram finiteNegativeKernel = !![1,5/4;5/4,5/2] ∧
    populationBeta finiteNegativeKernel = ![1/3,11/15] ∧
    limitingTarget finiteNegativeKernel = !![1004/225,-48/125;-48/125,1856/5625] ∧
    (limitingTarget finiteNegativeKernel).PosDef ∧
    (unitSampleLaw finiteNegativeKernel 4 {ω |
      ∀ i : Fin 4, ω i = (i,true)}).toReal = 1/4096 ∧
    (∀ ω : Fin 4 → Fin 4 × Bool, (∀ i : Fin 4, ω i = (i,true)) →
      (sampleGram (design finiteNegativeKernel ω)).det = 20 ∧
      sampleVariance members (design finiteNegativeKernel ω) (response finiteNegativeKernel ω) =
        (!![-17/50,21/125;21/125,-58/625] : Mat 2))

def T17Statement : Prop := negativeSampleFacts ∧ negativePopulationFacts

/-- Structural and domain conclusions for arbitrary scores and symmetric bread. -/
def estimatorStructure : Prop :=
  ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (s : E → Finset V) (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (q : E → Vec k) (P : Mat k) (hP : P.transpose = P),
    let B : Matrix V E ℝ := Matrix.of (fun i d => if i ∈ s d then 1 else 0)
    let S : Matrix E (Fin k) ℝ := Matrix.of (fun d a => q d a)
    ((∀ d f, (B.transpose*B-(1 : Matrix E E ℝ)) d f =
      (if (s d ∩ s f).Nonempty then 1 else 0)) ∧
    meat s q = S.transpose*(B.transpose*B-(1 : Matrix E E ℝ))*S ∧
    meat s q = (B*S).transpose*(B*S)-S.transpose*S) ∧
    ((sandwich P (meat s q)).transpose = sandwich P (meat s q) ∧
    sandwich P (meat s q) =
      sandwich P (∑ i, outer (unitScore s q i) (unitScore s q i)) - sandwich P (dyadMeat q) ∧
    (sandwich P (∑ i, outer (unitScore s q i) (unitScore s q i))).PosSemidef ∧
    (sandwich P (dyadMeat q)).PosSemidef)

def T18Statement : Prop := estimatorStructure ∧
  (∀ v : ℝ, (∃ se, standardError v = some se) ↔ 0 ≤ v) ∧
  (∀ a b : ℝ, |max a 0 - max b 0| ≤ |a-b|) ∧
  (∀ N : ℝ, 0 ≤ N → ∀ v V : ℝ, 0 ≤ V → |N*max v 0-V| ≤ |N*v-V|) ∧
  (∀ N : ℝ, 0 ≤ N → ∀ v V : ℝ, 0 < V → v < 0 → V ≤ |N*v-V|) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℝ) (_hN : 0 ≤ N) (v : Ω → ℝ) (V : ℝ) (_hV : 0 < V),
    (μ {ω | v ω < 0}).toReal ≤ (μ {ω | V ≤ |N*v ω-V|}).toReal) ∧
  (∀ {Ω : ℕ → Type} [∀ N : ℕ, MeasurableSpace (Ω N)]
    (μ : ∀ N : ℕ, Measure (Ω N)) (hμ : ∀ N : ℕ, IsProbabilityMeasure (μ N))
    (v : ∀ N : ℕ, Ω N → ℝ) (V : ℕ → ℝ) (hV : ∀ N : ℕ, 0 ≤ V N),
    inProbability μ (fun N ω => (N : ℝ)*v N ω-V N) →
    inProbability μ (fun N ω => (N : ℝ)*max (v N ω) 0-V N)) ∧
  (∀ {Ω : ℕ → Type} [∀ N : ℕ, MeasurableSpace (Ω N)]
    (μ : ∀ N : ℕ, Measure (Ω N)) (hμ : ∀ N : ℕ, IsProbabilityMeasure (μ N))
    (v : ∀ N : ℕ, Ω N → ℝ) (V : ℝ) (hV : 0 < V),
    inProbability μ (fun N ω => (N : ℝ)*v N ω-V) →
    Tendsto (fun N : ℕ => (μ N {ω | v N ω < 0}).toReal) atTop (𝓝 0))

end SAP.P018b
