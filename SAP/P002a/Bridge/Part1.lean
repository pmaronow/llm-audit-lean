import SAP.P002a.Defs
import AronowAudit.P002.P002_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SAP.P002a.Bridge
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology

def toPopulation {n : ℕ} (P : SAP.P002a.Population n) : AronowAudit.P002.Population n :=
  ⟨P.y, P.d, P.n1⟩

def fromPopulation {n : ℕ} (P : AronowAudit.P002.Population n) : SAP.P002a.Population n :=
  ⟨P.y, P.d, P.n1⟩

def toCovPopulation {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    AronowAudit.P002.CovPopulation n k := ⟨toPopulation P.pop, P.x⟩

def fromCovPopulation {n k : ℕ} (P : AronowAudit.P002.CovPopulation n k) :
    SAP.P002a.CovPopulation n k := ⟨fromPopulation P.pop, P.x⟩

theorem population_roundtrip {n : ℕ} (P : SAP.P002a.Population n) :
    fromPopulation (toPopulation P) = P := rfl

theorem project_population_roundtrip {n : ℕ} (P : AronowAudit.P002.Population n) :
    toPopulation (fromPopulation P) = P := rfl

theorem covPopulation_roundtrip {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    fromCovPopulation (toCovPopulation P) = P := rfl

theorem project_covPopulation_roundtrip {n k : ℕ} (P : AronowAudit.P002.CovPopulation n k) :
    toCovPopulation (fromCovPopulation P) = P := rfl

/-! The scalar and matrix definitions have the same bodies. -/

theorem binary_eq : @SAP.P002a.binary = @AronowAudit.P002.binary := rfl
theorem mean_eq : @SAP.P002a.mean = @AronowAudit.P002.mean := rfl
theorem groupMean_eq : @SAP.P002a.groupMean = @AronowAudit.P002.groupMean := rfl
theorem popVar_eq : @SAP.P002a.popVar = @AronowAudit.P002.popVar := rfl
theorem popCov_eq : @SAP.P002a.popCov = @AronowAudit.P002.popCov := rfl
theorem groupCov_eq : @SAP.P002a.groupCov = @AronowAudit.P002.groupCov := rfl
theorem groupVar_eq : @SAP.P002a.groupVar = @AronowAudit.P002.groupVar := rfl
theorem armMean_eq : @SAP.P002a.armMean = @AronowAudit.P002.armMean := rfl
theorem absStudent_eq : @SAP.P002a.absStudent = @AronowAudit.P002.absStudent := rfl
theorem fourthNorm_eq : @SAP.P002a.fourthNorm = @AronowAudit.P002.fourthNorm := rfl
theorem augmented_eq : @SAP.P002a.augmented = @AronowAudit.P002.augmented := rfl
theorem xCirc_eq : @SAP.P002a.xCirc = @AronowAudit.P002.xCirc := rfl
theorem normSq_eq : @SAP.P002a.normSq = @AronowAudit.P002.normSq := rfl
theorem gram_eq : @SAP.P002a.gram = @AronowAudit.P002.gram := rfl
theorem score_eq : @SAP.P002a.score = @AronowAudit.P002.score := rfl
theorem rss_eq : @SAP.P002a.rss = @AronowAudit.P002.rss := rfl
theorem ols_eq : @SAP.P002a.ols = @AronowAudit.P002.ols := rfl
theorem slopeDot_eq : @SAP.P002a.slopeDot = @AronowAudit.P002.slopeDot := rfl
theorem leastRayleigh_eq : @SAP.P002a.leastRayleigh = @AronowAudit.P002.leastRayleigh := rfl

/-! Population quantities agree after copying the three data fields. -/

theorem compliers_eq {n : ℕ} (P : SAP.P002a.Population n) :
    compliers P = AronowAudit.P002.compliers (toPopulation P) := rfl
theorem late_eq {n : ℕ} (P : SAP.P002a.Population n) :
    late P = AronowAudit.P002.late (toPopulation P) := rfl
theorem w_eq {n : ℕ} (P : SAP.P002a.Population n) (a : Bool) (β : ℝ) :
    w P a β = AronowAudit.P002.w (toPopulation P) a β := rfl
theorem v_eq {n : ℕ} (P : SAP.P002a.Population n) (a : Bool) (β : ℝ) :
    v P a β = AronowAudit.P002.v (toPopulation P) a β := rfl
theorem validDesign_eq {n : ℕ} (P : SAP.P002a.Population n) :
    ValidDesign P = AronowAudit.P002.ValidDesign (toPopulation P) := rfl
theorem assignments_eq {n : ℕ} (P : SAP.P002a.Population n) :
    assignments P = AronowAudit.P002.assignments (toPopulation P) := rfl
theorem expectation_eq {n : ℕ} (P : SAP.P002a.Population n) :
    expectation P = AronowAudit.P002.expectation (toPopulation P) := rfl
theorem designVariance_eq {n : ℕ} (P : SAP.P002a.Population n) :
    designVariance P = AronowAudit.P002.designVariance (toPopulation P) := rfl
theorem probability_eq {n : ℕ} (P : SAP.P002a.Population n) :
    probability P = AronowAudit.P002.probability (toPopulation P) := rfl
theorem observedW_eq {n : ℕ} (P : SAP.P002a.Population n) (β : ℝ) :
    observedW P β = AronowAudit.P002.observedW (toPopulation P) β := rfl
theorem rawTau_eq {n : ℕ} (P : SAP.P002a.Population n) :
    rawTau P = AronowAudit.P002.rawTau (toPopulation P) := rfl
theorem tau_eq {n : ℕ} (P : SAP.P002a.Population n) :
    tau P = AronowAudit.P002.tau (toPopulation P) := rfl
theorem rawSigma2_eq {n : ℕ} (P : SAP.P002a.Population n) :
    rawSigma2 P = AronowAudit.P002.rawSigma2 (toPopulation P) := rfl
theorem rawAR_eq {n : ℕ} (P : SAP.P002a.Population n) :
    rawAR P = AronowAudit.P002.rawAR (toPopulation P) := rfl
theorem quantile_eq {n : ℕ} (P : SAP.P002a.Population n) :
    quantile P = AronowAudit.P002.quantile (toPopulation P) := rfl
theorem coverage_eq {n : ℕ} (P : SAP.P002a.Population n) :
    coverage P = AronowAudit.P002.coverage (toPopulation P) := rfl
theorem theta_eq {n : ℕ} (P : SAP.P002a.Population n) (δ r A : ℝ) :
    Theta P δ r A = AronowAudit.P002.Theta (toPopulation P) δ r A := rfl

theorem psi_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    psi P = AronowAudit.P002.psi (toCovPopulation P) := rfl
theorem residual_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    residual P = AronowAudit.P002.residual (toCovPopulation P) := rfl
theorem fitted_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    fitted P = AronowAudit.P002.fitted (toCovPopulation P) := rfl
theorem adjustedTau_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    adjustedTau P = AronowAudit.P002.adjustedTau (toCovPopulation P) := rfl
theorem oracleTau_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    oracleTau P = AronowAudit.P002.oracleTau (toCovPopulation P) := rfl
theorem oracleStar_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    oracleStar P = AronowAudit.P002.oracleStar (toCovPopulation P) := rfl
theorem adjustedSigma2_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    adjustedSigma2 P = AronowAudit.P002.adjustedSigma2 (toCovPopulation P) := rfl
theorem adjustedCoverage_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) :
    adjustedCoverage P = AronowAudit.P002.adjustedCoverage (toCovPopulation P) := rfl
theorem xi_eq {n k : ℕ} (P : SAP.P002a.CovPopulation n k) (δ e A B r : ℝ) :
    Xi P δ e A B r = AronowAudit.P002.Xi (toCovPopulation P) δ e A B r := rfl

theorem randomizationSequence_eq {Ω : Type*} [MeasurableSpace Ω] {sizes : ℕ → ℕ}
    (P : ∀ n, SAP.P002a.Population (sizes n)) (μ : Measure Ω)
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) :
    RandomizationSequence P μ Z =
      AronowAudit.P002.RandomizationSequence (fun n => toPopulation (P n)) μ Z := rfl

end
end SAP.P002a.Bridge
