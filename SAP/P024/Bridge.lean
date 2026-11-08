import SAP.P024.Defs
import AronowAudit.P024.P024_Designs
import AronowAudit.P024.P024_IndependentCompletion
import AronowAudit.P024.Wave1.Gap.DecisionT7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024.Bridge
open scoped BigOperators
noncomputable section

/-- Preserve the entire finite law, including its validity certificates. -/
def toDesign {Ω : Type*} [Fintype Ω] (d : Design Ω) : AronowAudit.P024.Design Ω :=
  ⟨d.mass, d.nonneg, d.total⟩

/-- Preserve sizes, positivity, and every individual potential outcome. -/
def toPopulation {K : ℕ} (P : ClusterPopulation K) : AronowAudit.P024.ClusterPopulation K :=
  ⟨P.size, P.positive, P.y0, P.y1⟩

theorem expectation_eq {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) :
    AronowAudit.P024.expectation (toDesign d) X = expectation d X := rfl

theorem probability_eq {Ω : Type*} [Fintype Ω] (d : Design Ω) (Q : Ω → Prop) :
    AronowAudit.P024.probability (toDesign d) Q = probability d Q := rfl

theorem uniform_eq (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    toDesign (uniformDesign Ω) = AronowAudit.P024.uniformDesign Ω := rfl

theorem variance_eq {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) :
    AronowAudit.P024.variance (toDesign d) X = variance d X := rfl

theorem overlap_eq {I Ω : Type*} [Fintype I] [Fintype Ω]
    (d : Design Ω) (z : Ω → I → Bool) :
    AronowAudit.P024.overlap (toDesign d) z = overlap d z := rfl

theorem ht_eq {I Ω : Type*} (E : Finset I) (z : Ω → I → Bool) (y0 y1 π : I → ℝ) :
    AronowAudit.P024.htEstimate E z y0 y1 π = htEstimate E z y0 y1 π := rfl

theorem randomizationP_eq {Ω : Type*} [Fintype Ω] (D : Ω → ℝ) :
    AronowAudit.P024.randomizationP D = randomizationP D := rfl

theorem calendarHT_eq : AronowAudit.P024.calendarHT = calendarHT := rfl
theorem calendarBeforeAfter_eq : AronowAudit.P024.calendarBeforeAfter = calendarBeforeAfter := rfl
theorem calendarObservedBeforeAfter_eq :
    AronowAudit.P024.calendarObservedBeforeAfter = calendarObservedBeforeAfter := rfl

theorem clusterDIM_eq {J : Type*} [Fintype J] (n y0 y1 : J → ℝ) (z : J → Bool) :
    AronowAudit.P024.clusterDIM n y0 y1 z = clusterDIM n y0 y1 z := rfl

theorem clusterMean0_eq {K : ℕ} (P : ClusterPopulation K) :
    AronowAudit.P024.clusterMean0 (toPopulation P) = clusterMean0 P := rfl
theorem clusterMean1_eq {K : ℕ} (P : ClusterPopulation K) :
    AronowAudit.P024.clusterMean1 (toPopulation P) = clusterMean1 P := rfl
theorem clusterWeight_eq {K : ℕ} (P : ClusterPopulation K) :
    AronowAudit.P024.clusterWeight (toPopulation P) = clusterWeight P := rfl
theorem populationEffect_eq {K : ℕ} (P : ClusterPopulation K) :
    AronowAudit.P024.populationEffect (toPopulation P) = populationEffect P := rfl
theorem populationEstimator_eq {K : ℕ} (P : ClusterPopulation K)
    (empty : Finset (Fin K) → ℝ) :
    AronowAudit.P024.populationEstimator (toPopulation P) empty = populationEstimator P empty := rfl
theorem maxClusterWeight_eq {k : ℕ} (P : ClusterPopulation (k+2)) :
    AronowAudit.P024.maxClusterWeight (toPopulation P) = maxClusterWeight P := rfl

theorem dominant_eq (k : ℕ) :
    toPopulation (dominantPopulation k) = AronowAudit.P024.dominantPopulation k := rfl
theorem dominantValue_eq (K m : ℝ) (b : Bool) :
    AronowAudit.P024.dominantValue K m b = dominantValue K m b := rfl
theorem conditionalNonemptyDesign_eq (k : ℕ) :
    toDesign (conditionalNonemptyDesign k) = AronowAudit.P024.conditionalNonemptyDesign k := rfl
theorem halfClusterDesign_eq (n : ℕ) :
    toDesign (halfClusterDesign n) = AronowAudit.P024.halfClusterDesign n := rfl
theorem halfDominantRatio_eq : AronowAudit.P024.halfDominantRatio = halfDominantRatio := rfl

theorem independentLaw_eq {K : ℕ} (d : Design (Finset (Fin K))) (p : ℝ) :
    AronowAudit.P024.independentClusterLaw (toDesign d) p ↔ independentClusterLaw d p := Iff.rfl
theorem completeLaw_eq {K : ℕ} (d : Design (Finset (Fin K))) (m : ℕ) :
    AronowAudit.P024.completeClusterLaw (toDesign d) m ↔ completeClusterLaw d m := Iff.rfl
theorem bernoulliDesign_eq (K : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    toDesign (bernoulliDesign K p hp0 hp1) = AronowAudit.P024.bernoulliDesign K p hp0 hp1 := rfl

/-- The conditional expectations use exactly the original normalized finite masses. -/
theorem conditionalMass_eq (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (s : NonemptyAllocations k) :
    (AronowAudit.P024.bernoulliNonemptyDesign k p hp hp1).mass s =
      bernoulliConditionalMass k p s := rfl
theorem conditionalExpectation_eq (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (X : NonemptyAllocations k → ℝ) :
    AronowAudit.P024.expectation (AronowAudit.P024.bernoulliNonemptyDesign k p hp hp1) X =
      bernoulliConditionalExpectation k p X := rfl

theorem blockedHT_eq {B Ω : Type*} [Fintype B]
    (I : B → Type*) [∀ b, Fintype (I b)] (m : B → ℕ)
    (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ) :
    AronowAudit.P024.blockedHT I m z y0 y1 = blockedHT I m z y0 y1 := rfl

end
end SAP.P024.Bridge
