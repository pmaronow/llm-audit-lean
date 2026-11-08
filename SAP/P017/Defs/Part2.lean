import SAP.P017.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/- Explicit validator populations, potential outcomes, IID sampling laws, and estimators.
All fixed-sample assertions below require positive sample size. -/

def fairPair (a b : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac a + (1 / 2 : ℝ≥0∞) • Measure.dirac b

def uniform01 : Measure ℝ := volume.restrict (Ioo 0 1)

def ipwPopulation : Measure (ℝ × (ℝ × ℝ)) :=
  uniform01.prod ((fairPair (-1) 1).prod (fairPair 0 1))

def ipwY0 (ω : ℝ × (ℝ × ℝ)) : ℝ := ω.2.1

def ipwY1 (ω : ℝ × (ℝ × ℝ)) : ℝ := ω.2.1 + ω.1

def ipwEffect (ω : ℝ × (ℝ × ℝ)) : ℝ := ipwY1 ω - ipwY0 ω

def ipwObserved (ω : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (ω.2.2, ω.2.2 * ipwY1 ω + (1 - ω.2.2) * ipwY0 ω)

def ipwSummand (ω : ℝ × (ℝ × ℝ)) : ℝ :=
  2 * (ipwObserved ω).1 * (ipwObserved ω).2 -
    2 * (1 - (ipwObserved ω).1) * (ipwObserved ω).2

def iidSamples {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) : Measure (ℕ → Ω) :=
  Measure.infinitePi (fun _ : ℕ => G)

def empiricalObserved {Ω D : Type*} [MeasurableSpace D]
    (O : Ω → D) (n : ℕ) (s : ℕ → Ω) : Measure D :=
  (1 / (n : ℝ≥0∞)) • ∑ i ∈ Finset.range n, Measure.dirac (O (s i))

def sampleMean {Ω : Type*} (X : Ω → ℝ) (n : ℕ) (s : ℕ → Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X (s i)) / (n : ℝ)

def ipwBadEvent (b : ℝ) (n : ℕ) : Set (ℕ → ℝ × (ℝ × ℝ)) :=
  {s | ∀ i ∈ Finset.range n, (s i).2.1 = b ∧ (s i).2.2 = 0}

def normalPopulation : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (fairPair (-1) 1)

def normalY0 (_ : ℝ × ℝ) : ℝ := 0

def normalY1 (ω : ℝ × ℝ) : ℝ := ω.2

def normalEffect (ω : ℝ × ℝ) : ℝ := normalY1 ω - normalY0 ω

def normalMean (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ := sampleMean Prod.fst n s

def shiftedNormalMean (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ := normalMean n s + 1 / (n : ℝ)

def shiftedDifference (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ :=
  normalMean n s - clipReal 0 1 (shiftedNormalMean n s)

def normalZ (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ := sqrtN n * normalMean n s

def normalEpsilon (n : ℕ) (_ : ℕ → ℝ × ℝ) : ℝ := 1 / sqrtN n

def uniformHalfOpen01 : Measure ℝ := volume.restrict (Ico 0 1)

def slowEffectLaw : Measure ℝ :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 4 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 4 : ℝ≥0∞) • volume.restrict (Icc (-1) 1)

def slowPopulation : Measure (ℝ × (ℝ × (ℝ × ℝ))) :=
  (gaussianReal 0 1).prod (uniformHalfOpen01.prod (slowEffectLaw.prod (fairPair 0 1)))

def slowY0 (_ : ℝ × (ℝ × (ℝ × ℝ))) : ℝ := 0

def slowY1 (ω : ℝ × (ℝ × (ℝ × ℝ))) : ℝ := ω.2.2.1

def slowEffect (ω : ℝ × (ℝ × (ℝ × ℝ))) : ℝ := slowY1 ω - slowY0 ω

def slowObserved (ω : ℝ × (ℝ × (ℝ × ℝ))) : ℝ × (ℝ × (ℝ × ℝ)) :=
  (ω.1, (ω.2.1, (ω.2.2.2, ω.2.2.2 * slowY1 ω + (1 - ω.2.2.2) * slowY0 ω)))

def rareUniform (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  Int.fract (∑ i ∈ Finset.range n, (s i).2.1)

def rareFlag (p : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  if rareUniform n s < p n then 1 else 0

def smallNormalMean (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  sampleMean Prod.fst n s

def smallNormalClip (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  clipReal 0 (1 / 2) (smallNormalMean n s)

def rareEstimator (p : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  smallNormalClip n s + 10 * rareFlag p n s

def rareRemainder (p : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  sqrtN n * (smallNormalClip n s - smallNormalMean n s + 10 * rareFlag p n s)

def slowP (n : ℕ) : ℝ := 1 / ((1 + Nat.log 2 n : ℕ) : ℝ)

-- These probability instances are measure-definition and scalar-arithmetic glue.
instance fairPair_probability (a b : ℝ) : IsProbabilityMeasure (fairPair a b) := by
  constructor
  norm_num [fairPair, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

instance uniform01_probability : IsProbabilityMeasure uniform01 := by
  constructor
  simp [uniform01, Real.volume_Ioo]

instance ipwPopulation_probability : IsProbabilityMeasure ipwPopulation := by
  unfold ipwPopulation
  infer_instance

instance iidSamples_probability {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] : IsProbabilityMeasure (iidSamples G) := by
  unfold iidSamples
  infer_instance

instance normalPopulation_probability : IsProbabilityMeasure normalPopulation := by
  unfold normalPopulation
  infer_instance

instance uniformHalfOpen01_probability : IsProbabilityMeasure uniformHalfOpen01 := by
  constructor
  simp [uniformHalfOpen01, Real.volume_Ico]

instance slowEffectLaw_probability : IsProbabilityMeasure slowEffectLaw := by
  constructor
  norm_num [slowEffectLaw, Measure.add_apply, Measure.smul_apply, Real.volume_Icc]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

instance slowPopulation_probability : IsProbabilityMeasure slowPopulation := by
  unfold slowPopulation
  infer_instance

end
end SAP.P017
