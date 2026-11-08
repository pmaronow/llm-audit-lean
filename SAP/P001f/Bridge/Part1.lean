import SAP.P001f.Defs
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f.Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem conditionalMean_iff {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) :
    ConditionalMean μ X Y m ↔ AronowAudit.P001.IsCEF μ X Y m := Iff.rfl

theorem conditionalIndependence_iff {Ω E F G : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X) (Y : Ω → F) (Z : Ω → G) :
    ConditionallyIndependent μ X hX Y Z ↔ AronowAudit.P001.CI μ X hX Y Z := Iff.rfl

theorem independentCopies_iff {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) :
    IndependentCopies μ X ↔ AronowAudit.P001.IID μ X := Iff.rfl

theorem sampleAverage_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    sampleAverage X n = AronowAudit.P001.sampleMean X n := rfl

theorem realDensity_iff (ν : Measure ℝ) (f : ℝ → ℝ) :
    RealDensity ν f ↔ AronowAudit.P001.HasPDF ν f := Iff.rfl

theorem vectorDensity_iff {K : ℕ} (ν : Measure (Fin K → ℝ)) (f : (Fin K → ℝ) → ℝ) :
    RealDensity ν f ↔ AronowAudit.P001.HasVectorPDF ν f := Iff.rfl

theorem eventMean_eq {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (Y : Ω → ℝ) (x : E) :
    eventMean μ X Y x = AronowAudit.P001.conditionalMeanAt μ X Y x := rfl

theorem finiteMean_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n) (Y : Fin n → ℝ) :
    finiteMean P.weight Y = AronowAudit.P001.fmean P Y := rfl

theorem finiteProbability_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n)
    (A : Fin n → Prop) [DecidablePred A] :
    finiteProbability P.weight A = AronowAudit.P001.fprob P A := by
  classical
  unfold finiteProbability AronowAudit.P001.fprob
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : A i <;> simp only [h, ite_true, ite_false]

theorem finiteEventMean_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n)
    (Y X : Fin n → ℝ) (x : ℝ) :
    finiteEventMean P.weight Y X x = AronowAudit.P001.fcond P Y X x := rfl

theorem finiteConditionalIndependence_iff {n : ℕ} {E F G : Type*}
    (P : AronowAudit.P001.FiniteLaw n) (Y : Fin n → E) (Z : Fin n → F) (X : Fin n → G) :
    FiniteConditionalIndependence P.weight Y Z X ↔ AronowAudit.P001.FCondIndep P Y Z X := by
  classical
  simp only [FiniteConditionalIndependence, AronowAudit.P001.FCondIndep,
    ← finiteProbability_eq]

theorem logit_eq (a b x : ℝ) :
    logisticProbability a b x = AronowAudit.P001.logitProbability a b x := rfl

theorem groupedLogLikelihood_eq (N r : Fin 3 → ℝ) (a b : ℝ) :
    groupedLogLikelihood N r a b = AronowAudit.P001.groupedLogitLikelihood N r a b := rfl

theorem samplePDA_eq {Ω : Type*} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ)
    (mhat : ℕ → Ω → (Fin K → ℝ) → ℝ) (n : ℕ) (ω : Ω) (k : Fin K) :
    samplePDA X mhat n ω k = AronowAudit.P001.pluginPDA X mhat n ω k := rfl

theorem mixtureLikelihood_eq {n : ℕ} (y : Fin n → ℝ) (θ : Fin 7 → ℝ) :
    mixtureSampleLikelihood y θ = AronowAudit.P001.mixtureLikelihood y θ := rfl

theorem validMixture_iff (θ : Fin 7 → ℝ) :
    ValidMixture θ ↔ AronowAudit.P001.MixtureAdmissible θ := Iff.rfl

end
end SAP.P001f.Bridge
