import Mathlib

namespace AronowAudit.P021

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

/-!
P021: Aronow and Crawford, Statistics and Probability Letters 106 (2015), 100–102.
The outcome bound is an assumption, not a reduction. Degrees are indexed by
`Fin K`, with index k representing the printed degree k.val + 1. Sample
membership is a Boolean. The full joint probability law is unrestricted apart
from these supports and Conditions 1 and 2 (mean ignorability, not independence).
-/

/-- Section 2, p. 101: "Y has bounded support and ... D has support in the set
{1, ..., K}." This is the full state space [-B,B] × {1,...,K} × {0,1}.
For Corollary 1 the same B and K are used for every finite population. -/
abbrev RDSState (B : ℝ) (K : ℕ) := Set.Icc (-B) B × (Fin K × Bool)

/-- Section 2, p. 101: "the outcome ... denoted (Y, D, S)." -/
def outcome {B : ℝ} {K : ℕ} (x : RDSState B K) : ℝ := x.1.val

/-- Section 2, p. 101: "(reported) degree" in {1,...,K}; index k is degree k+1. -/
def degreeValue {K : ℕ} (k : Fin K) : ℝ := (k.val : ℝ) + 1

/-- Section 2, p. 101: "sampling indicator S = 1"; false denotes S=0. -/
def sampleIndicator {B : ℝ} {K : ℕ} (x : RDSState B K) : ℝ :=
  if x.2.2 then 1 else 0

/-- Section 2, p. 101, the event D=k used in the elementary conditionals. -/
def degreeCell {B : ℝ} {K : ℕ} (k : Fin K) (x : RDSState B K) : ℝ :=
  if x.2.1 = k then 1 else 0

/-- Section 2, p. 101, the event S=1,D=k used in the elementary conditionals. -/
def sampleCell {B : ℝ} {K : ℕ} (k : Fin K) (x : RDSState B K) : ℝ :=
  degreeCell k x * sampleIndicator x

variable {B : ℝ} {K : ℕ}

/-- The coordinate Y on the common compact support is continuous (Section 2).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem outcome_continuous : Continuous (outcome (B := B) (K := K)) :=
  continuous_subtype_val.comp continuous_fst

/-- The indicator S on the discrete sample coordinate is continuous (Section 2).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampleIndicator_continuous : Continuous (sampleIndicator (B := B) (K := K)) :=
  (continuous_of_discreteTopology (f := fun s : Bool => if s then (1 : ℝ) else 0)).comp
    (continuous_snd.comp continuous_snd)

/-- The degree-cell indicator is continuous because degree has finite discrete support.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem degreeCell_continuous (k : Fin K) : Continuous (degreeCell (B := B) k) :=
  (continuous_of_discreteTopology (f := fun d : Fin K => if d = k then (1 : ℝ) else 0)).comp
    (continuous_fst.comp continuous_snd)

/-- The joint sampled-degree indicator is continuous (Section 2 conditionals).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampleCell_continuous (k : Fin K) : Continuous (sampleCell (B := B) k) :=
  (degreeCell_continuous k).mul sampleIndicator_continuous

/-- Bounded continuous functions on the paper's compact support have finite integrals.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem continuous_integrable (F : Measure (RDSState B K)) [IsFiniteMeasure F]
    {g : RDSState B K → ℝ} (hg : Continuous g) : Integrable g F :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

/-- Section 2, p. 101: "E and Pr operators refer to ... this limiting distribution."
The population mean is the ordinary integral of Y under the full joint law F. -/
def populationMean (F : Measure (RDSState B K)) : ℝ := ∫ x, outcome x ∂F

/-- Pr[D=k] in Condition 1 and Eqs. (2)–(4), p. 101; an indicator integral. -/
def degreeMass (F : Measure (RDSState B K)) (k : Fin K) : ℝ := ∫ x, degreeCell k x ∂F

/-- Pr[S=1,D=k] underlying Bayes' identity Eq. (3), p. 101. -/
def sampledMass (F : Measure (RDSState B K)) (k : Fin K) : ℝ := ∫ x, sampleCell k x ∂F

/-- E[Y 1{D=k}], the numerator of E[Y|D=k] in Condition 1, p. 101. -/
def degreeMoment (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  ∫ x, degreeCell k x * outcome x ∂F

/-- E[Y 1{S=1,D=k}], the numerator of E[Y|S=1,D=k], p. 101. -/
def sampledMoment (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  ∫ x, sampleCell k x * outcome x ∂F

/-- Pr[S=1] in Eqs. (3)–(4), p. 101. -/
def sampleFraction (F : Measure (RDSState B K)) : ℝ := ∫ x, sampleIndicator x ∂F

/-- Pr[S=1|D=k] in Conditions 1–2, p. 101, evaluated only on positive-mass cells. -/
def samplingProbability (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  sampledMass F k / degreeMass F k

/-- E[Y|D=k] in Condition 1, p. 101, evaluated only on positive-mass cells. -/
def degreeMean (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  degreeMoment F k / degreeMass F k

/-- E[Y|S=1,D=k] in Condition 1 and Eq. (2), p. 101. -/
def sampledMean (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  sampledMoment F k / sampledMass F k

/-- Pr[D=k|S=1] in Eq. (2), p. 101. -/
def observedDegreeMass (F : Measure (RDSState B K)) (k : Fin K) : ℝ :=
  sampledMass F k / sampleFraction F

/-- Condition 1, p. 101: "For all k such that Pr[D=k]>0".
The support restriction is the validator's reading of the sums in (2)–(4). -/
def degreeSupport (F : Measure (RDSState B K)) : Finset (Fin K) :=
  by classical exact Finset.univ.filter fun k => 0 < degreeMass F k

/-- The support determined by the observed law of degree given S=1 (p. 101). -/
def observedSupport (F : Measure (RDSState B K)) : Finset (Fin K) :=
  by classical exact Finset.univ.filter fun k => 0 < observedDegreeMass F k

/-- Condition 1 (Ignorability), p. 101: "E[Y|S=1,D=k] = E[Y|D=k] and
Pr[S=1|D=k]>0" for all k with Pr[D=k]>0. This is equality of means only. -/
def Ignorability (F : Measure (RDSState B K)) : Prop :=
  ∀ k, 0 < degreeMass F k →
    sampledMean F k = degreeMean F k ∧ 0 < samplingProbability F k

/-- Condition 2, p. 101: "Pr[S=1|D=k] = c f(k), where f(.) is known and c
is an unknown scale parameter." No separate sign is imposed on c or f.
The condition is used only where Pr[D=k]>0 (validator's support convention). -/
def KnownSampling (F : Measure (RDSState B K)) (c : ℝ) (f : Fin K → ℝ) : Prop :=
  ∀ k, 0 < degreeMass F k → samplingProbability F k = c * f k

/-- Degree probabilities are nonnegative, as used in Proposition 1's proof. -/
theorem degreeMass_nonneg (F : Measure (RDSState B K)) (k : Fin K) :
    0 ≤ degreeMass F k := by
  apply integral_nonneg
  intro x
  unfold degreeCell
  split_ifs <;> norm_num

/-- Joint sampled-degree probabilities are nonnegative (Eq. (3), p. 101).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampledMass_nonneg (F : Measure (RDSState B K)) (k : Fin K) :
    0 ≤ sampledMass F k := by
  apply integral_nonneg
  intro x
  unfold sampleCell degreeCell sampleIndicator
  split_ifs <;> norm_num

/-- Degree-cell probabilities sum to one for a genuine joint probability law.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem degreeMass_sum (F : Measure (RDSState B K)) [IsProbabilityMeasure F] :
    ∑ k, degreeMass F k = 1 := by
  unfold degreeMass
  rw [← integral_finsetSum]
  · have heq : (fun x : RDSState B K => ∑ k : Fin K, degreeCell k x) = fun _ => 1 := by
      funext x
      simp [degreeCell]
    rw [heq]
    simp
  · intro k _
    exact continuous_integrable F (degreeCell_continuous k)

/-- Partitioning by degree gives the population mean (law of total expectation,
the step used in Eq. (4), p. 101), before normalizing each stratum.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem degreeMoment_sum (F : Measure (RDSState B K)) [IsProbabilityMeasure F] :
    ∑ k, degreeMoment F k = populationMean F := by
  unfold degreeMoment populationMean
  rw [← integral_finsetSum]
  · congr 1
    funext x
    simp [degreeCell]
  · intro k _
    exact continuous_integrable F ((degreeCell_continuous k).mul outcome_continuous)

/-- Partitioning Pr[S=1] by degree (Bayes' identity Eq. (3), p. 101).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampledMass_sum (F : Measure (RDSState B K)) [IsProbabilityMeasure F] :
    ∑ k, sampledMass F k = sampleFraction F := by
  unfold sampledMass sampleFraction
  rw [← integral_finsetSum]
  · congr 1
    funext x
    simp [sampleCell, degreeCell]
  · intro k _
    exact continuous_integrable F (sampleCell_continuous k)

/-- An unsupported degree has zero degree moment and sampled probability and
moment. Thus omitting it from (2)–(4) changes no non-null conditional quantity.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem null_degree (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (k : Fin K) (hk : degreeMass F k = 0) :
    degreeMoment F k = 0 ∧ sampledMass F k = 0 ∧ sampledMoment F k = 0 := by
  have ha : degreeCell k =ᵐ[F] (0 : RDSState B K → ℝ) :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => by unfold degreeCell; split_ifs <;> norm_num)
      (continuous_integrable F (degreeCell_continuous k))).mp hk
  refine ⟨integral_eq_zero_of_ae ?_, integral_eq_zero_of_ae ?_, integral_eq_zero_of_ae ?_⟩
  all_goals
    filter_upwards [ha] with x hx
    simp only [Pi.zero_apply] at hx
    simp [sampleCell, hx]

/-- Proposition 1's degree support is nonempty: its probabilities sum to one. -/
theorem degreeSupport_nonempty (F : Measure (RDSState B K)) [IsProbabilityMeasure F] :
    (degreeSupport F).Nonempty := by
  classical
  have hs : 0 < ∑ k, degreeMass F k := by rw [degreeMass_sum F]; norm_num
  obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => degreeMass_nonneg F k)).mp hs
  exact ⟨k, by simp [degreeSupport, hk]⟩

/-- Null degrees, precisely the cells excluded by Condition 1, have zero probability.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem degreeMass_zero_of_not_pos (F : Measure (RDSState B K)) (k : Fin K)
    (hk : ¬ 0 < degreeMass F k) : degreeMass F k = 0 :=
  le_antisymm (le_of_not_gt hk) (degreeMass_nonneg F k)

/-- The supported population degree probabilities sum to one (Eq. (4), p. 101).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem support_degreeMass_sum (F : Measure (RDSState B K)) [IsProbabilityMeasure F] :
    ∑ k ∈ degreeSupport F, degreeMass F k = 1 := by
  classical
  rw [← degreeMass_sum F]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  exact degreeMass_zero_of_not_pos F k (by simpa [degreeSupport] using hk)

/-- The supported degree moments sum to E[Y] (total expectation in Eq. (4)).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem support_degreeMoment_sum (F : Measure (RDSState B K)) [IsProbabilityMeasure F] :
    ∑ k ∈ degreeSupport F, degreeMoment F k = populationMean F := by
  classical
  rw [← degreeMoment_sum F]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  exact (null_degree F k (degreeMass_zero_of_not_pos F k
    (by simpa [degreeSupport] using hk))).1

/-- Condition 1 makes every supported joint sampled-degree probability positive.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampledMass_pos (F : Measure (RDSState B K)) (hI : Ignorability F)
    (k : Fin K) (hk : 0 < degreeMass F k) : 0 < sampledMass F k := by
  exact (div_pos_iff_of_pos_right hk).mp (hI k hk).2

/-- Under Condition 1 the sampling fraction is strictly positive (Proposition 1). -/
theorem sampleFraction_pos (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (hI : Ignorability F) : 0 < sampleFraction F := by
  classical
  obtain ⟨k, hk⟩ := degreeSupport_nonempty F
  rw [← sampledMass_sum F]
  exact Finset.sum_pos' (fun k _ => sampledMass_nonneg F k)
    ⟨k, Finset.mem_univ _, sampledMass_pos F hI k (by simpa [degreeSupport] using hk)⟩

/-- Condition 1 identifies degree support from the observed sample distribution.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem degreeSupport_eq_observedSupport (F : Measure (RDSState B K))
    [IsProbabilityMeasure F] (hI : Ignorability F) :
    degreeSupport F = observedSupport F := by
  classical
  ext k
  simp only [degreeSupport, observedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [observedDegreeMass, div_pos_iff_of_pos_right (sampleFraction_pos F hI)]
  constructor
  · exact sampledMass_pos F hI k
  · intro hs
    by_contra hp
    have hz := (null_degree F k (degreeMass_zero_of_not_pos F k hp)).2.1
    linarith

/-- Condition 2's elementary joint probability identity, used in Eq. (3).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampledMass_eq (F : Measure (RDSState B K)) (c : ℝ) (f : Fin K → ℝ)
    (hC : KnownSampling F c f) (k : Fin K) (hk : 0 < degreeMass F k) :
    sampledMass F k = (c * f k) * degreeMass F k := by
  exact (div_eq_iff hk.ne').mp (hC k hk)

/-- Mean ignorability and Condition 2 give the exact sampled stratum moment.
No independence of Y and S within strata is assumed (Proposition 1, Eq. (4)). -/
theorem sampledMoment_eq (F : Measure (RDSState B K)) (c : ℝ) (f : Fin K → ℝ)
    (hI : Ignorability F) (hC : KnownSampling F c f)
    (k : Fin K) (hk : 0 < degreeMass F k) :
    sampledMoment F k = (c * f k) * degreeMoment F k := by
  have ha := (sampledMass_pos F hI k hk).ne'
  have hm := (hI k hk).1
  unfold sampledMean degreeMean at hm
  calc
    sampledMoment F k = (sampledMoment F k / sampledMass F k) * sampledMass F k :=
      (div_mul_cancel₀ _ ha).symm
    _ = (degreeMoment F k / degreeMass F k) * ((c * f k) * degreeMass F k) := by
      rw [hm, sampledMass_eq F c f hC k hk]
    _ = (c * f k) * degreeMoment F k := by field_simp [hk.ne']

/-- The unknown scale c is nonzero; Condition 1, rather than separate sign
restrictions on c and f, guarantees this (Proposition 1). -/
theorem samplingScale_ne_zero (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c : ℝ) (f : Fin K → ℝ) (hI : Ignorability F) (hC : KnownSampling F c f) : c ≠ 0 := by
  classical
  obtain ⟨k, hk⟩ := degreeSupport_nonempty F
  have hp : 0 < degreeMass F k := by simpa [degreeSupport] using hk
  have hs := (hI k hp).2
  rw [hC k hp] at hs
  intro hc
  simp [hc] at hs

/-- On supported degrees c f(k)>0 and f(k)≠0 (Proposition 1's valid divisions). -/
theorem samplingProfile_nonzero (F : Measure (RDSState B K))
    (c : ℝ) (f : Fin K → ℝ) (hI : Ignorability F) (hC : KnownSampling F c f)
    (k : Fin K) (hk : 0 < degreeMass F k) : 0 < c * f k ∧ f k ≠ 0 := by
  have hs := (hI k hk).2
  rw [hC k hk] at hs
  refine ⟨hs, ?_⟩
  intro hf
  simp [hf] at hs

/-- Bayes' identity in Proposition 1, Eq. (3), p. 101:
p_k = (Pr[S=1]/c) (Pr[D=k|S=1]/f(k)), on positive-mass degrees. -/
theorem bayes_degree_identity (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c : ℝ) (f : Fin K → ℝ) (hI : Ignorability F) (hC : KnownSampling F c f)
    (k : Fin K) (hk : 0 < degreeMass F k) :
    degreeMass F k = (sampleFraction F / c) * (observedDegreeMass F k / f k) := by
  have hc := samplingScale_ne_zero F c f hI hC
  have hf := (samplingProfile_nonzero F c f hI hC k hk).2
  have hr := (sampleFraction_pos F hI).ne'
  unfold observedDegreeMass
  rw [sampledMass_eq F c f hC k hk]
  field_simp [hc, hf, hr]

/-- Inverse-profile observed degree weights are proportional to population
probabilities, including their common normalization (Eqs. (3)–(4)).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem inverse_weight_identity (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c : ℝ) (f : Fin K → ℝ) (hI : Ignorability F) (hC : KnownSampling F c f)
    (k : Fin K) (hk : 0 < degreeMass F k) :
    observedDegreeMass F k / f k = (c / sampleFraction F) * degreeMass F k := by
  have hf := (samplingProfile_nonzero F c f hI hC k hk).2
  have hr := (sampleFraction_pos F hI).ne'
  unfold observedDegreeMass
  rw [sampledMass_eq F c f hC k hk]
  field_simp [hf, hr]

/-- The denominator in Eq. (2) is c/Pr[S=1] and is nonzero (Proposition 1). -/
theorem inverse_weight_denominator (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c : ℝ) (f : Fin K → ℝ) (hI : Ignorability F) (hC : KnownSampling F c f) :
    (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) = c / sampleFraction F := by
  classical
  calc
    (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) =
        ∑ k ∈ degreeSupport F, (c / sampleFraction F) * degreeMass F k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact inverse_weight_identity F c f hI hC k (by simpa [degreeSupport] using hk)
    _ = c / sampleFraction F := by rw [← Finset.mul_sum, support_degreeMass_sum F, mul_one]

/-- Total expectation with the common means from Condition 1 (Eq. (4), p. 101).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem mean_ignorability_sum (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (hI : Ignorability F) :
    (∑ k ∈ degreeSupport F, sampledMean F k * degreeMass F k) = populationMean F := by
  classical
  rw [← support_degreeMoment_sum F]
  apply Finset.sum_congr rfl
  intro k hk
  have hp : 0 < degreeMass F k := by simpa [degreeSupport] using hk
  rw [(hI k hp).1]
  exact div_mul_cancel₀ _ hp.ne'

/-- Proposition 1, Eq. (2), p. 101. For a full joint probability law of bounded
Y, positive integer D≤K and S∈{0,1}, Conditions 1 and 2 identify E[Y] by the
ratio of observed degree probabilities and sampled conditional means. The sums
use positive-mass degrees, exactly the validator's interpretation of (2)–(4).
The conclusion also proves positivity, observable support, Eq. (3), and the
nonzero denominator, without requiring c>0 or f>0 separately. -/
theorem proposition_one (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c : ℝ) (f : Fin K → ℝ) (hI : Ignorability F) (hC : KnownSampling F c f) :
    0 < sampleFraction F ∧ degreeSupport F = observedSupport F ∧ c ≠ 0 ∧
    (∀ k ∈ degreeSupport F, 0 < c * f k ∧ f k ≠ 0 ∧
      degreeMass F k = (sampleFraction F / c) * (observedDegreeMass F k / f k)) ∧
    (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) = c / sampleFraction F ∧
    (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) ≠ 0 ∧
    populationMean F =
      (∑ k ∈ degreeSupport F, sampledMean F k * (observedDegreeMass F k / f k)) /
        (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) := by
  classical
  have hr := sampleFraction_pos F hI
  have hc := samplingScale_ne_zero F c f hI hC
  have hd := inverse_weight_denominator F c f hI hC
  have hz : c / sampleFraction F ≠ 0 := div_ne_zero hc hr.ne'
  have hdNZ : (∑ k ∈ degreeSupport F, observedDegreeMass F k / f k) ≠ 0 := by
    rw [hd]
    exact hz
  refine ⟨hr, degreeSupport_eq_observedSupport F hI, hc, ?_, hd, hdNZ, ?_⟩
  · intro k hk
    have hp : 0 < degreeMass F k := by simpa [degreeSupport] using hk
    exact ⟨(samplingProfile_nonzero F c f hI hC k hp).1,
      (samplingProfile_nonzero F c f hI hC k hp).2,
      bayes_degree_identity F c f hI hC k hp⟩
  · have hn : (∑ k ∈ degreeSupport F, sampledMean F k * (observedDegreeMass F k / f k)) =
        (c / sampleFraction F) * populationMean F := by
      calc
        _ = ∑ k ∈ degreeSupport F, (c / sampleFraction F) *
            (sampledMean F k * degreeMass F k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [inverse_weight_identity F c f hI hC k (by simpa [degreeSupport] using hk)]
          ring
        _ = _ := by rw [← Finset.mul_sum, mean_ignorability_sum F hI]
    rw [hn, hd, mul_div_cancel_left₀ _ hz]

/-- Eq. (2) as a functional of the observed law and the known profile only.
Its summation support is the observed degree support, so it contains no c or ρ. -/
def observedMeanFunctional (q m f : Fin K → ℝ) : ℝ := by
  classical
  exact (∑ k ∈ Finset.univ.filter (fun k => 0 < q k), m k * (q k / f k)) /
    (∑ k ∈ Finset.univ.filter (fun k => 0 < q k), q k / f k)

/-- Proposition 1's identification formula depends only on observed conditional
degree probabilities, sampled stratum means and f (Eq. (2), p. 101). -/
theorem proposition_one_observed (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c : ℝ) (f : Fin K → ℝ) (hI : Ignorability F) (hC : KnownSampling F c f) :
    populationMean F = observedMeanFunctional (observedDegreeMass F) (sampledMean F) f := by
  have h := (proposition_one F c f hI hC).2.2.2.2.2.2
  rw [degreeSupport_eq_observedSupport F hI] at h
  exact h

/-- Identification also means that any two admissible full-data laws with the
same observed degree probabilities and stratum means have the same E[Y]; their
unknown sampling scales can differ (Proposition 1, p. 101). These are the only
features of the conditional observed law used by Eq. (2). -/
theorem population_mean_identified (F G : Measure (RDSState B K))
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] (cF cG : ℝ) (f : Fin K → ℝ)
    (hIF : Ignorability F) (hIG : Ignorability G)
    (hCF : KnownSampling F cF f) (hCG : KnownSampling G cG f)
    (hq : observedDegreeMass F = observedDegreeMass G)
    (hm : ∀ k, 0 < observedDegreeMass F k → sampledMean F k = sampledMean G k) :
    populationMean F = populationMean G := by
  classical
  rw [proposition_one_observed F cF f hIF hCF, proposition_one_observed G cG f hIG hCG]
  unfold observedMeanFunctional
  rw [← hq]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hm k (by simpa using hk)]

/-- Eq. (1), p. 100, uses inverse degree; positive printed degrees are k.val+1.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem degreeValue_pos (k : Fin K) : 0 < degreeValue k := by
  unfold degreeValue
  positivity

/-- Every degree in the standing support is at least one (Section 2, p. 101).
Auxiliary lemma for Corollary 1, p. 101. -/
theorem degreeValue_ge_one (k : Fin K) : 1 ≤ degreeValue k := by
  unfold degreeValue
  have hn : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg k.val
  linarith

/-- E[SY/D]'s test function; its finite empirical average is the population-
normalized numerator of Eq. (1). This is a derived object for Corollary 1. -/
def inverseDegreeNumerator (x : RDSState B K) : ℝ :=
  sampleIndicator x * outcome x / degreeValue x.2.1

/-- E[S/D]'s test function; its finite empirical average is the population-
normalized denominator of Eq. (1). This is a derived object for Corollary 1. -/
def inverseDegreeDenominator (x : RDSState B K) : ℝ :=
  sampleIndicator x / degreeValue x.2.1

/-- The degree coordinate is continuous on the paper's discrete degree support.
Auxiliary lemma for Corollary 1, p. 101. -/
theorem degree_continuous : Continuous (fun x : RDSState B K => degreeValue x.2.1) :=
  (continuous_of_discreteTopology (f := degreeValue (K := K))).comp
    (continuous_fst.comp continuous_snd)

/-- SY/D is continuous on the common bounded support (Corollary 1's moment step). -/
theorem inverseDegreeNumerator_continuous :
    Continuous (inverseDegreeNumerator (B := B) (K := K)) :=
  (sampleIndicator_continuous.mul outcome_continuous).div degree_continuous
    (fun x => (degreeValue_pos x.2.1).ne')

/-- S/D is continuous on the common bounded support (Corollary 1's moment step). -/
theorem inverseDegreeDenominator_continuous :
    Continuous (inverseDegreeDenominator (B := B) (K := K)) :=
  sampleIndicator_continuous.div degree_continuous (fun x => (degreeValue_pos x.2.1).ne')

/-- On the common support, |SY/D|≤B, 0≤S/D≤1 and 0≤S≤1. These are the
bounded test functions used to pass from weak convergence to moments in
Corollary 1, p. 101 (validator derivation, item (d)). -/
theorem inverse_degree_test_bounds (hB : 0 ≤ B) (x : RDSState B K) :
    |inverseDegreeNumerator x| ≤ B ∧
    0 ≤ inverseDegreeDenominator x ∧ inverseDegreeDenominator x ≤ 1 ∧
    0 ≤ sampleIndicator x ∧ sampleIndicator x ≤ 1 := by
  have hd := degreeValue_pos x.2.1
  have hd1 := degreeValue_ge_one x.2.1
  have hy : |outcome x| ≤ B := abs_le.mpr x.1.property
  cases hs : x.2.2
  · simp [inverseDegreeNumerator, inverseDegreeDenominator, sampleIndicator, hs, hB]
  · have hs1 : sampleIndicator x = 1 := by simp [sampleIndicator, hs]
    unfold inverseDegreeNumerator inverseDegreeDenominator
    rw [hs1]
    simp only [one_mul]
    refine ⟨?_, (one_div_pos.mpr hd).le, ?_, by norm_num, by norm_num⟩
    · rw [abs_div, abs_of_pos hd]
      apply (div_le_iff₀ hd).mpr
      exact hy.trans (by nlinarith)
    · exact (div_le_one hd).mpr hd1

/-- The exact degree partition of E[S/D], derived for Corollary 1. -/
theorem inverse_degree_denominator_partition (F : Measure (RDSState B K))
    [IsProbabilityMeasure F] :
    (∫ x, inverseDegreeDenominator x ∂F) = ∑ k, sampledMass F k / degreeValue k := by
  simp_rw [sampledMass, ← integral_div]
  rw [← integral_finsetSum]
  · congr 1
    funext x
    simp [inverseDegreeDenominator, sampleCell, degreeCell, div_eq_mul_inv]
  · intro k _
    exact continuous_integrable F ((sampleCell_continuous k).div_const _)

/-- The exact degree partition of E[SY/D], derived for Corollary 1. -/
theorem inverse_degree_numerator_partition (F : Measure (RDSState B K))
    [IsProbabilityMeasure F] :
    (∫ x, inverseDegreeNumerator x ∂F) = ∑ k, sampledMoment F k / degreeValue k := by
  simp_rw [sampledMoment, ← integral_div]
  rw [← integral_finsetSum]
  · congr 1
    funext x
    simp [inverseDegreeNumerator, sampleCell, degreeCell, div_eq_mul_inv]
  · intro k _
    exact continuous_integrable F (((sampleCell_continuous k).mul outcome_continuous).div_const _)

/-- For f(k)=ak, Conditions 1 and 2 imply b=ca>0. Neither a nor c needs a
separate sign assumption (Corollary 1, p. 101). -/
theorem degree_sampling_scale_pos (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c a : ℝ) (hI : Ignorability F)
    (hC : KnownSampling F c (fun k => a * degreeValue k)) : 0 < c * a := by
  classical
  obtain ⟨k, hk⟩ := degreeSupport_nonempty F
  have hp : 0 < degreeMass F k := by simpa [degreeSupport] using hk
  have hs := (hI k hp).2
  rw [hC k hp] at hs
  by_contra hb
  have hneg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) (degreeValue_pos k).le
  nlinarith

/-- At f(k)=ak, sampled degree probabilities are ca·k·p_k, also for null
degrees (Corollary 1, exact fixed-law lemma). -/
theorem degree_proportional_sampledMass (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c a : ℝ) (hC : KnownSampling F c (fun k => a * degreeValue k)) (k : Fin K) :
    sampledMass F k = (c * a) * degreeValue k * degreeMass F k := by
  by_cases hk : 0 < degreeMass F k
  · rw [sampledMass_eq F c _ hC k hk]
    ring
  · have hz := degreeMass_zero_of_not_pos F k hk
    rw [(null_degree F k hz).2.1, hz]
    ring

/-- At f(k)=ak, sampled degree outcome moments are ca·k times population
degree moments; this uses mean ignorability only (Corollary 1). -/
theorem degree_proportional_sampledMoment (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c a : ℝ) (hI : Ignorability F)
    (hC : KnownSampling F c (fun k => a * degreeValue k)) (k : Fin K) :
    sampledMoment F k = (c * a) * degreeValue k * degreeMoment F k := by
  by_cases hk : 0 < degreeMass F k
  · rw [sampledMoment_eq F c _ hI hC k hk]
    ring
  · have hz := null_degree F k (degreeMass_zero_of_not_pos F k hk)
    rw [hz.2.2, hz.1]
    ring

/-- The exact limiting-law moments for Corollary 1: b=ca>0,
E[S/D]=b and E[SY/D]=b E[Y], hence their ratio equals the population mean.
This is Proposition 1 specialized to f(k) proportional to k, p. 101. -/
theorem vh_limit_moments (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c a : ℝ) (hI : Ignorability F)
    (hC : KnownSampling F c (fun k => a * degreeValue k)) :
    0 < c * a ∧
    (∫ x, inverseDegreeDenominator x ∂F) = c * a ∧
    (∫ x, inverseDegreeNumerator x ∂F) = (c * a) * populationMean F ∧
    (∫ x, inverseDegreeNumerator x ∂F) / (∫ x, inverseDegreeDenominator x ∂F) =
      populationMean F := by
  have hb := degree_sampling_scale_pos F c a hI hC
  have hd : (∫ x, inverseDegreeDenominator x ∂F) = c * a := by
    rw [inverse_degree_denominator_partition]
    calc
      (∑ k, sampledMass F k / degreeValue k) = ∑ k, (c * a) * degreeMass F k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [degree_proportional_sampledMass F c a hC k]
        field_simp [(degreeValue_pos k).ne']
      _ = _ := by rw [← Finset.mul_sum, degreeMass_sum F, mul_one]
  have hn : (∫ x, inverseDegreeNumerator x ∂F) = (c * a) * populationMean F := by
    rw [inverse_degree_numerator_partition]
    calc
      (∑ k, sampledMoment F k / degreeValue k) = ∑ k, (c * a) * degreeMoment F k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [degree_proportional_sampledMoment F c a hI hC k]
        field_simp [(degreeValue_pos k).ne']
      _ = _ := by rw [← Finset.mul_sum, degreeMoment_sum F]
  refine ⟨hb, hd, hn, ?_⟩
  rw [hn, hd, mul_div_cancel_left₀ _ hb.ne']

/-- Each realized finite population has N units with (y,d,s), as in the opening
sentence of Section 2, p. 101. Its empirical law is (1/N)∑ⱼδ_(yⱼ,dⱼ,sⱼ);
`empiricalAverage z g` is exactly its integral of g, represented by a finite sum.
It is used only with N>0. -/
def empiricalAverage {N : ℕ} (z : Fin N → RDSState B K) (g : RDSState B K → ℝ) : ℝ :=
  (∑ j, g (z j)) / (N : ℝ)

/-- Eq. (1), p. 100: the RDS sample consists of units with S=1, under the
validator's joint-empirical-law reading of Section 2's sampling indicator. -/
def sampleSet {N : ℕ} (z : Fin N → RDSState B K) : Finset (Fin N) :=
  Finset.univ.filter fun j => (z j).2.2 = true

/-- Eq. (1), p. 100: "For an RDS sample of size n"; n is the number of S=1 units. -/
def sampleSize {N : ℕ} (z : Fin N → RDSState B K) : ℕ := (sampleSet z).card

/-- Volz–Heckathorn estimator, Eq. (1), p. 100:
"sum y_i d_i^{-1} / sum d_i^{-1}" over sampled units.
Lean's total division assigns 0 when the sample is empty; the empty-sample
event is proved to have probability tending to zero below. -/
def vhEstimator {N : ℕ} (z : Fin N → RDSState B K) : ℝ :=
  (∑ j ∈ sampleSet z, outcome (z j) / degreeValue (z j).2.1) /
    (∑ j ∈ sampleSet z, 1 / degreeValue (z j).2.1)

/-- Eq. (1)'s numerator equals the sum of SY/D over every population unit.
Auxiliary lemma for Corollary 1, p. 101. -/
theorem vh_numerator_sum {N : ℕ} (z : Fin N → RDSState B K) :
    (∑ j ∈ sampleSet z, outcome (z j) / degreeValue (z j).2.1) =
      ∑ j, inverseDegreeNumerator (z j) := by
  rw [sampleSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases hs : (z j).2.2 <;> simp [inverseDegreeNumerator, sampleIndicator, hs]

/-- Eq. (1)'s denominator equals the sum of S/D over every population unit.
Auxiliary lemma for Corollary 1, p. 101. -/
theorem vh_denominator_sum {N : ℕ} (z : Fin N → RDSState B K) :
    (∑ j ∈ sampleSet z, 1 / degreeValue (z j).2.1) =
      ∑ j, inverseDegreeDenominator (z j) := by
  rw [sampleSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases hs : (z j).2.2 <;> simp [inverseDegreeDenominator, sampleIndicator, hs]

/-- The finite plug-in identity for every N>0: Eq. (1) is A_N/B_N where
A_N=(1/N)∑SY/D and B_N=(1/N)∑S/D (Corollary 1 finite lemma (c)). -/
theorem vh_empirical_ratio {N : ℕ} (hN : 0 < N) (z : Fin N → RDSState B K) :
    vhEstimator z = empiricalAverage z inverseDegreeNumerator /
      empiricalAverage z inverseDegreeDenominator := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold vhEstimator empiricalAverage
  rw [vh_numerator_sum z, vh_denominator_sum z]
  exact (div_div_div_cancel_right₀ hNr _ _).symm

/-- A nonempty finite sample has a positive inverse-degree denominator and
B_N>0 (Corollary 1 finite lemma (c), Eq. (1)). -/
theorem vh_finite_denominator_pos {N : ℕ} (hN : 0 < N)
    (z : Fin N → RDSState B K) (hn : 0 < sampleSize z) :
    0 < ∑ j ∈ sampleSet z, 1 / degreeValue (z j).2.1 ∧
    0 < empiricalAverage z inverseDegreeDenominator := by
  have hs : 0 < ∑ j ∈ sampleSet z, 1 / degreeValue (z j).2.1 :=
    Finset.sum_pos (fun j _ => one_div_pos.mpr (degreeValue_pos _))
      (Finset.card_pos.mp hn)
  refine ⟨hs, ?_⟩
  unfold empiricalAverage
  rw [← vh_denominator_sum]
  exact div_pos hs (by exact_mod_cast hN)

/-- The empirical sample proportion is n/N=∫S dF_N (finite lemma (c)).
Auxiliary lemma for Corollary 1, p. 101. -/
theorem empirical_sample_fraction {N : ℕ} (z : Fin N → RDSState B K) :
    empiricalAverage z sampleIndicator = (sampleSize z : ℝ) / (N : ℝ) := by
  unfold empiricalAverage sampleSize
  congr 1
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [sampleSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases hs : (z j).2.2 <;> simp [sampleIndicator, hs]

/-- Section 2, first sentence, p. 101: "sequence of populations and samples
converging weakly to a joint limit distribution". For random realized empirical
laws this is convergence in probability of their integrals against EVERY
bounded continuous test function, as specified by the validators. On the
compact common support every continuous real test function is bounded.
F is the fixed full joint limiting law; N_r is the positive population size. -/
def EmpiricalWeakInProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Measure (RDSState B K)) (N : ℕ → ℕ)
    (z : (r : ℕ) → Ω → Fin (N r) → RDSState B K) : Prop :=
  ∀ g : RDSState B K → ℝ, Continuous g →
    TendstoInMeasure P (fun r ω => empiricalAverage (z r ω) g) atTop
      (fun _ => ∫ x, g x ∂F)

/-- A finite empirical average of a continuous test function is measurable
when the realized finite population coordinates are measurable.
Auxiliary lemma for Corollary 1, p. 101. -/
theorem empiricalAverage_measurable {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (z : Ω → Fin N → RDSState B K)
    (hz : ∀ j, Measurable (fun ω => z ω j))
    (g : RDSState B K → ℝ) (hg : Continuous g) :
    Measurable (fun ω => empiricalAverage (z ω) g) := by
  unfold empiricalAverage
  exact (Finset.measurable_fun_sum Finset.univ (fun j _ => hg.measurable.comp (hz j))).div_const _

/-- A ratio with a nonzero deterministic denominator limit preserves convergence
in probability. This is Corollary 1's limit step, proved by the subsequence
characterization of convergence in measure, rather than assumed as an axiom. -/
theorem ratio_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (A H : ℕ → Ω → ℝ) (u b : ℝ)
    (hA : ∀ r, Measurable (A r)) (hH : ∀ r, Measurable (H r)) (hb : b ≠ 0)
    (hAu : TendstoInMeasure P A atTop (fun _ => u))
    (hHb : TendstoInMeasure P H atTop (fun _ => b)) :
    TendstoInMeasure P (fun r ω => A r ω / H r ω) atTop (fun _ => u / b) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun r => ((hA r).div (hH r)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hmA⟩ := (hAu.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ls, hls, hlH⟩ := (hHb.comp (hns.comp hms).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms ∘ ls, hms.comp hls, ?_⟩
  filter_upwards [hmA, hlH] with ω hωA hωH
  exact (hωA.comp hls.tendsto_atTop).div hωH hb

/-- Corollary 1, p. 101, with Eq. (1), p. 100. Assume common outcome and degree
bounds, convergence in probability of the realized joint empirical laws to a
fixed full law F, mean ignorability in F, and Condition 2 with f(k)=ak, a≠0.
Then the actual finite-sample VH estimator converges in probability to E_F[Y].
The convergence premise is weak empirical convergence, not a separate assumed
moment limit or convergence of design-averaged marginal laws. No independence,
random-walk, connected-network or growing-sample-size condition is added. -/
theorem corollary_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (_hB : 0 ≤ B) (_hK : 0 < K) (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r)
    (z : (r : ℕ) → Ω → Fin (N r) → RDSState B K)
    (hz : ∀ r j, Measurable (fun ω => z r ω j))
    (hweak : EmpiricalWeakInProbability P F N z)
    (c a : ℝ) (_ha : a ≠ 0) (hI : Ignorability F)
    (hC : KnownSampling F c (fun k => a * degreeValue k)) :
    TendstoInMeasure P (fun r ω => vhEstimator (z r ω)) atTop
      (fun _ => populationMean F) := by
  have hlim := vh_limit_moments F c a hI hC
  have hA := hweak inverseDegreeNumerator inverseDegreeNumerator_continuous
  have hH := hweak inverseDegreeDenominator inverseDegreeDenominator_continuous
  rw [hlim.2.1] at hH
  rw [hlim.2.2.1] at hA
  have hr := ratio_tendstoInMeasure P
    (fun r ω => empiricalAverage (z r ω) inverseDegreeNumerator)
    (fun r ω => empiricalAverage (z r ω) inverseDegreeDenominator)
    ((c * a) * populationMean F) (c * a)
    (fun r => empiricalAverage_measurable (z r) (hz r) _ inverseDegreeNumerator_continuous)
    (fun r => empiricalAverage_measurable (z r) (hz r) _ inverseDegreeDenominator_continuous)
    hlim.1.ne' hA hH
  simp only [mul_div_cancel_left₀ _ hlim.1.ne'] at hr
  apply hr.congr_left
  intro r
  exact Filter.Eventually.of_forall (fun ω => (vh_empirical_ratio (hN r) (z r ω)).symm)

/-- "Known to scale" (abstract, p. 100): rescaling f by any nonzero real
constant leaves Eq. (2)'s observable ratio unchanged, including its support.
Auxiliary lemma for Corollary 1, p. 101. -/
theorem observedMeanFunctional_scale (q m f : Fin K → ℝ) (a : ℝ) (ha : a ≠ 0) :
    observedMeanFunctional q m (fun k => a * f k) = observedMeanFunctional q m f := by
  classical
  unfold observedMeanFunctional
  have hw : ∀ k, q k / (a * f k) = (q k / f k) / a := by
    intro k
    rw [mul_comm a, div_mul_eq_div_div]
  simp_rw [hw, ← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div]
  exact div_div_div_cancel_right₀ ha _ _

/-- Every conditional sampling probability is at most one because it comes
from a full probability law, not unconstrained stratum numbers (Condition 2).
Auxiliary lemma for Corollary 1, p. 101. -/
theorem samplingProbability_le_one (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (k : Fin K) (hk : 0 < degreeMass F k) : samplingProbability F k ≤ 1 := by
  have hm : sampledMass F k ≤ degreeMass F k := by
    apply integral_mono (continuous_integrable F (sampleCell_continuous k))
      (continuous_integrable F (degreeCell_continuous k))
    intro x
    unfold sampleCell degreeCell sampleIndicator
    split_ifs <;> norm_num
  exact (div_le_one hk).mpr hm

/-- At degree-proportional sampling, every supported degree is at most 1/b
where b=ca>0 (Corollary 1 exact lemma (g)). -/
theorem supported_degree_bound (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (c a : ℝ) (hI : Ignorability F)
    (hC : KnownSampling F c (fun k => a * degreeValue k))
    (k : Fin K) (hk : 0 < degreeMass F k) : degreeValue k ≤ 1 / (c * a) := by
  have hb := degree_sampling_scale_pos F c a hI hC
  have hle := samplingProbability_le_one F k hk
  rw [hC k hk] at hle
  apply (le_div_iff₀ hb).mpr
  nlinarith

/-- The exact ratio error identity and bound for any finite stage, Corollary 1
finite lemma (e): when H≥b/2>0, |A/H−μ|≤(2/b)(|A−bμ|+|μ||H−b|). -/
theorem ratio_error_bound (A H b μ : ℝ) (hb : 0 < b) (hH : b / 2 ≤ H) :
    |A / H - μ| = |A - μ * H| / H ∧
    |A / H - μ| ≤ (2 / b) * (|A - b * μ| + |μ| * |H - b|) := by
  have hHp : 0 < H := (half_pos hb).trans_le hH
  have heq : A / H - μ = (A - μ * H) / H := by field_simp [hHp.ne']
  have habs : |A / H - μ| = |A - μ * H| / H := by
    rw [heq, abs_div, abs_of_pos hHp]
  have htri : |A - μ * H| ≤ |A - b * μ| + |μ| * |H - b| := by
    calc
      |A - μ * H| = |(A - b * μ) + μ * (b - H)| := by congr 1; ring
      _ ≤ |A - b * μ| + |μ * (b - H)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_sub_comm b H]
  have hinv : 1 / H ≤ 2 / b := by
    apply (div_le_div_iff₀ hHp hb).mpr
    nlinarith
  refine ⟨habs, ?_⟩
  calc
    |A / H - μ| = |A - μ * H| * (1 / H) := by rw [habs]; ring
    _ ≤ (|A - b * μ| + |μ| * |H - b|) * (1 / H) :=
      mul_le_mul_of_nonneg_right htri (by positivity)
    _ ≤ (|A - b * μ| + |μ| * |H - b|) * (2 / b) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

/-- The finite epsilon estimate underlying the event bound for Corollary 1. -/
theorem ratio_error_small (A H b μ ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hH : b / 2 ≤ H)
    (hA : |A - b * μ| < ε * b / (4 * (1 + |μ|)))
    (hD : |H - b| < ε * b / (4 * (1 + |μ|))) : |A / H - μ| < ε := by
  have hμ : 0 < 1 + |μ| := by positivity
  have hinner : |A - b * μ| + |μ| * |H - b| <
      ε * b / (4 * (1 + |μ|)) + |μ| * (ε * b / (4 * (1 + |μ|))) :=
    add_lt_add_of_lt_of_le hA (mul_le_mul_of_nonneg_left hD.le (abs_nonneg μ))
  have hid : (2 / b) * (ε * b / (4 * (1 + |μ|)) +
      |μ| * (ε * b / (4 * (1 + |μ|)))) = ε / 2 := by
    field_simp [hb.ne', hμ.ne']
    ring
  have hlt := mul_lt_mul_of_pos_left hinner (show (0 : ℝ) < 2 / b by positivity)
  rw [hid] at hlt
  exact (ratio_error_bound A H b μ hb hH).2.trans_lt (hlt.trans (by linarith))

/-- Corollary 1 finite lemma (e), the probability union bound at any fixed
population: the ratio's error event is controlled by three moment-error events
with t=εb/[4(1+|μ|)]. No independence is used. -/
theorem ratio_error_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A H : Ω → ℝ) (b μ ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    P {ω | ε < |A ω / H ω - μ|} ≤
      P {ω | b / 2 ≤ |H ω - b|} +
      P {ω | ε * b / (4 * (1 + |μ|)) ≤ |A ω - b * μ|} +
      P {ω | ε * b / (4 * (1 + |μ|)) ≤ |H ω - b|} := by
  have hsub : {ω | ε < |A ω / H ω - μ|} ⊆
      {ω | b / 2 ≤ |H ω - b|} ∪
        ({ω | ε * b / (4 * (1 + |μ|)) ≤ |A ω - b * μ|} ∪
          {ω | ε * b / (4 * (1 + |μ|)) ≤ |H ω - b|}) := by
    intro ω hω
    by_cases hhalf : b / 2 ≤ |H ω - b|
    · exact Or.inl hhalf
    · by_cases hnum : ε * b / (4 * (1 + |μ|)) ≤ |A ω - b * μ|
      · exact Or.inr (Or.inl hnum)
      · by_cases hden : ε * b / (4 * (1 + |μ|)) ≤ |H ω - b|
        · exact Or.inr (Or.inr hden)
        · have hg : b / 2 ≤ H ω := by
            have h := (abs_lt.mp (lt_of_not_ge hhalf)).1
            linarith
          have hs := ratio_error_small (A ω) (H ω) b μ ε hb hε hg
            (lt_of_not_ge hnum) (lt_of_not_ge hden)
          exact False.elim (lt_asymm hs hω)
  calc
    _ ≤ P ({ω | b / 2 ≤ |H ω - b|} ∪
        ({ω | ε * b / (4 * (1 + |μ|)) ≤ |A ω - b * μ|} ∪
          {ω | ε * b / (4 * (1 + |μ|)) ≤ |H ω - b|})) := measure_mono hsub
    _ ≤ P {ω | b / 2 ≤ |H ω - b|} +
        P ({ω | ε * b / (4 * (1 + |μ|)) ≤ |A ω - b * μ|} ∪
          {ω | ε * b / (4 * (1 + |μ|)) ≤ |H ω - b|}) := measure_union_le _ _
    _ ≤ _ := by
      rw [add_assoc]
      exact add_le_add le_rfl (measure_union_le (μ := P) _ _)

/-- The deterministic case of Corollary 1, p. 101: ordinary weak convergence
of the realized finite empirical laws gives ordinary convergence of Eq. (1)
to E_F[Y]. The common bounded supports remain part of the state space. -/
theorem corollary_one_deterministic (_hB : 0 ≤ B) (_hK : 0 < K)
    (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r)
    (z : (r : ℕ) → Fin (N r) → RDSState B K)
    (hweak : ∀ g : RDSState B K → ℝ, Continuous g →
      Tendsto (fun r => empiricalAverage (z r) g) atTop (𝓝 (∫ x, g x ∂F)))
    (c a : ℝ) (_ha : a ≠ 0) (hI : Ignorability F)
    (hC : KnownSampling F c (fun k => a * degreeValue k)) :
    Tendsto (fun r => vhEstimator (z r)) atTop (𝓝 (populationMean F)) := by
  have hlim := vh_limit_moments F c a hI hC
  have hA := hweak inverseDegreeNumerator inverseDegreeNumerator_continuous
  have hH := hweak inverseDegreeDenominator inverseDegreeDenominator_continuous
  have hr := hA.div hH (by rw [hlim.2.1]; exact hlim.1.ne')
  rw [hlim.2.2.2] at hr
  have hv : (fun r => vhEstimator (z r)) =
      (fun r => empiricalAverage (z r) inverseDegreeNumerator /
        empiricalAverage (z r) inverseDegreeDenominator) :=
    funext fun r => vh_empirical_ratio (hN r) (z r)
  rw [hv]
  exact hr

/-- An empty finite sample has B_N=0, with the same population normalization
used in the ratio error bound (Corollary 1 finite lemma (e)). -/
theorem empty_sample_denominator {N : ℕ} (z : Fin N → RDSState B K)
    (hn : sampleSize z = 0) : empiricalAverage z inverseDegreeDenominator = 0 := by
  have he : sampleSet z = ∅ := Finset.card_eq_zero.mp hn
  unfold empiricalAverage
  rw [← vh_denominator_sum, he]
  simp

/-- Under Corollary 1's hypotheses the empty-sample event has probability
tending to zero; hence it does not affect the consistency conclusion. -/
theorem empty_sample_probability_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (N : ℕ → ℕ) (z : (r : ℕ) → Ω → Fin (N r) → RDSState B K)
    (hweak : EmpiricalWeakInProbability P F N z)
    (c a : ℝ) (hI : Ignorability F)
    (hC : KnownSampling F c (fun k => a * degreeValue k)) :
    Tendsto (fun r => P {ω | sampleSize (z r ω) = 0}) atTop (𝓝 0) := by
  have hlim := vh_limit_moments F c a hI hC
  have hH := hweak inverseDegreeDenominator inverseDegreeDenominator_continuous
  rw [hlim.2.1] at hH
  have ht := tendstoInMeasure_iff_dist.mp hH ((c * a) / 2) (half_pos hlim.1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) ?_
  intro r
  apply measure_mono
  intro ω hω
  change (c * a) / 2 ≤ dist (empiricalAverage (z r ω) inverseDegreeDenominator) (c * a)
  rw [empty_sample_denominator (z r ω) hω]
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hlim.1]
  linarith [hlim.1]

/-- Weak empirical convergence also gives n_r/N_r→Pr_F[S=1]>0, the third
bounded continuous test functional for Corollary 1 (finite lemma (d)). -/
theorem sample_fraction_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Measure (RDSState B K)) [IsProbabilityMeasure F]
    (N : ℕ → ℕ) (z : (r : ℕ) → Ω → Fin (N r) → RDSState B K)
    (hweak : EmpiricalWeakInProbability P F N z) (hI : Ignorability F) :
    0 < sampleFraction F ∧
    TendstoInMeasure P (fun r ω => (sampleSize (z r ω) : ℝ) / (N r : ℝ)) atTop
      (fun _ => sampleFraction F) := by
  refine ⟨sampleFraction_pos F hI, ?_⟩
  have h := hweak sampleIndicator sampleIndicator_continuous
  exact h.congr_left (fun r => Filter.Eventually.of_forall (fun ω =>
    empirical_sample_fraction (z r ω)))

/-- The indicator-integral definition of Pr[D=k] is exactly the ordinary
real-valued probability of that event under F (Section 2, p. 101).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem degreeMass_eq_measureReal (F : Measure (RDSState B K)) (k : Fin K) :
    degreeMass F k = F.real {x | x.2.1 = k} := by
  classical
  have hm : MeasurableSet {x : RDSState B K | x.2.1 = k} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  have he : degreeCell (B := B) k =
      ({x : RDSState B K | x.2.1 = k}).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp [degreeCell, Set.indicator]
  unfold degreeMass
  rw [he]
  exact integral_indicator_one hm

/-- The joint sampled-degree indicator integral is Pr[S=1,D=k] under F,
the event probability in Bayes' identity Eq. (3), p. 101.
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampledMass_eq_measureReal (F : Measure (RDSState B K)) (k : Fin K) :
    sampledMass F k = F.real {x | x.2.1 = k ∧ x.2.2 = true} := by
  classical
  have hm : MeasurableSet {x : RDSState B K | x.2.1 = k ∧ x.2.2 = true} :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)
  have he : sampleCell (B := B) k =
      ({x : RDSState B K | x.2.1 = k ∧ x.2.2 = true}).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hd : x.2.1 = k <;>
      cases hs : x.2.2 <;> simp [sampleCell, degreeCell, sampleIndicator, Set.indicator, hd, hs]
  unfold sampledMass
  rw [he]
  exact integral_indicator_one hm

/-- The sampling-fraction indicator integral is Pr[S=1] under the full
limiting law F (Eqs. (3)–(4), p. 101).
Auxiliary lemma for Proposition 1, p. 101. -/
theorem sampleFraction_eq_measureReal (F : Measure (RDSState B K)) :
    sampleFraction F = F.real {x | x.2.2 = true} := by
  classical
  have hm : MeasurableSet {x : RDSState B K | x.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have he : sampleIndicator (B := B) (K := K) =
      ({x : RDSState B K | x.2.2 = true}).indicator (fun _ => (1 : ℝ)) := by
    funext x
    cases hs : x.2.2 <;> simp [sampleIndicator, Set.indicator, hs]
  unfold sampleFraction
  rw [he]
  exact integral_indicator_one hm

end

#print axioms AronowAudit.P021.outcome_continuous
#print axioms AronowAudit.P021.sampleIndicator_continuous
#print axioms AronowAudit.P021.degreeCell_continuous
#print axioms AronowAudit.P021.sampleCell_continuous
#print axioms AronowAudit.P021.continuous_integrable
#print axioms AronowAudit.P021.degreeMass_nonneg
#print axioms AronowAudit.P021.sampledMass_nonneg
#print axioms AronowAudit.P021.degreeMass_sum
#print axioms AronowAudit.P021.degreeMoment_sum
#print axioms AronowAudit.P021.sampledMass_sum
#print axioms AronowAudit.P021.null_degree
#print axioms AronowAudit.P021.degreeSupport_nonempty
#print axioms AronowAudit.P021.degreeMass_zero_of_not_pos
#print axioms AronowAudit.P021.support_degreeMass_sum
#print axioms AronowAudit.P021.support_degreeMoment_sum
#print axioms AronowAudit.P021.sampledMass_pos
#print axioms AronowAudit.P021.sampleFraction_pos
#print axioms AronowAudit.P021.degreeSupport_eq_observedSupport
#print axioms AronowAudit.P021.sampledMass_eq
#print axioms AronowAudit.P021.sampledMoment_eq
#print axioms AronowAudit.P021.samplingScale_ne_zero
#print axioms AronowAudit.P021.samplingProfile_nonzero
#print axioms AronowAudit.P021.bayes_degree_identity
#print axioms AronowAudit.P021.inverse_weight_identity
#print axioms AronowAudit.P021.inverse_weight_denominator
#print axioms AronowAudit.P021.mean_ignorability_sum
#print axioms AronowAudit.P021.proposition_one
#print axioms AronowAudit.P021.proposition_one_observed
#print axioms AronowAudit.P021.population_mean_identified
#print axioms AronowAudit.P021.degreeValue_pos
#print axioms AronowAudit.P021.degreeValue_ge_one
#print axioms AronowAudit.P021.degree_continuous
#print axioms AronowAudit.P021.inverseDegreeNumerator_continuous
#print axioms AronowAudit.P021.inverseDegreeDenominator_continuous
#print axioms AronowAudit.P021.inverse_degree_test_bounds
#print axioms AronowAudit.P021.inverse_degree_denominator_partition
#print axioms AronowAudit.P021.inverse_degree_numerator_partition
#print axioms AronowAudit.P021.degree_sampling_scale_pos
#print axioms AronowAudit.P021.degree_proportional_sampledMass
#print axioms AronowAudit.P021.degree_proportional_sampledMoment
#print axioms AronowAudit.P021.vh_limit_moments
#print axioms AronowAudit.P021.vh_numerator_sum
#print axioms AronowAudit.P021.vh_denominator_sum
#print axioms AronowAudit.P021.vh_empirical_ratio
#print axioms AronowAudit.P021.vh_finite_denominator_pos
#print axioms AronowAudit.P021.empirical_sample_fraction
#print axioms AronowAudit.P021.empiricalAverage_measurable
#print axioms AronowAudit.P021.ratio_tendstoInMeasure
#print axioms AronowAudit.P021.corollary_one
#print axioms AronowAudit.P021.observedMeanFunctional_scale
#print axioms AronowAudit.P021.samplingProbability_le_one
#print axioms AronowAudit.P021.supported_degree_bound
#print axioms AronowAudit.P021.ratio_error_bound
#print axioms AronowAudit.P021.ratio_error_small
#print axioms AronowAudit.P021.ratio_error_probability_bound
#print axioms AronowAudit.P021.corollary_one_deterministic
#print axioms AronowAudit.P021.empty_sample_denominator
#print axioms AronowAudit.P021.empty_sample_probability_tendsto
#print axioms AronowAudit.P021.sample_fraction_tendstoInMeasure
#print axioms AronowAudit.P021.degreeMass_eq_measureReal
#print axioms AronowAudit.P021.sampledMass_eq_measureReal
#print axioms AronowAudit.P021.sampleFraction_eq_measureReal

end AronowAudit.P021
