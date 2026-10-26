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
The sums in (2)–(4) are restricted to positive-mass degrees. -/
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
The condition is used only where Pr[D=k]>0 (positive-mass degree support). -/
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
use positive-mass degrees in (2)–(4).
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

/-- Eq. (1), p. 100: the RDS sample consists of units with S=1, using the
joint empirical law of Section 2's sampling indicator. -/
def sampleSet {N : ℕ} (z : Fin N → RDSState B K) : Finset (Fin N) :=
  Finset.univ.filter fun j => (z j).2.2 = true


/-- Volz–Heckathorn estimator, Eq. (1), p. 100:
"sum y_i d_i^{-1} / sum d_i^{-1}" over sampled units.
Lean's total division assigns 0 when the sample is empty. -/
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


/-- Section 2, first sentence, p. 101: "sequence of populations and samples
converging weakly to a joint limit distribution". For random realized empirical
laws this is convergence in probability of their integrals against every
bounded continuous test function. On the compact common support every
continuous real test function is bounded.
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


end

end AronowAudit.P021
