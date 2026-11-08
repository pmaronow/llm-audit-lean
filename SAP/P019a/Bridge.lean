import SAP.P019a.Defs
import AronowAudit.P019.P019_Audit
import AronowAudit.P019.Wave1.Gap.GLP019B3
import AronowAudit.P019.Wave1.Gap.GP019B4
import AronowAudit.P019.Wave1.Gap.GP019B4b
import AronowAudit.P019.Wave1.Gap.GLP019B4
import AronowAudit.P019.Wave1.Gap.GP019B5b
import AronowAudit.P019.Wave1.Gap.GLP019B1
import AronowAudit.P019.Wave1.Gap.GLP019B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.Bridge
open SAP.P019a Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

/-- Preserve masses and their validity certificates. -/
def toLaw (P : FiniteLaw Ω) : AronowAudit.P019.FiniteLaw Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

/-- Preserve all six observable coordinates and the law. -/
def toStudy (S : Study Ω) : AronowAudit.P019.Study Ω :=
  ⟨toLaw S.law, S.W, S.X, S.Y, S.Z, S.V⟩

theorem mean_eq (P : FiniteLaw Ω) (f : Ω → ℝ) : (toLaw P).mean f = P.mean f := rfl

theorem prob_eq (P : FiniteLaw Ω) (D : Ω → Prop) [DecidablePred D] :
    (toLaw P).prob D = P.prob D := rfl

theorem ce_eq (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] :
    (toLaw P).ce f D = P.ce f D := rfl

theorem iid_eq (P : FiniteLaw Ω) (n : ℕ) : (toLaw P).iid n = toLaw (P.iid n) := rfl

theorem standing_eq (S : Study Ω) : (toStudy S).standing = S.standing := rfl

theorem cellMean_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) (c : ℝ) :
    (toStudy S).cellMean s z y c = S.cellMean s z y c := rfl

theorem betaPsi_eq (S : Study Ω) (ω : Ω) : (toStudy S).betaPsi ω = S.betaPsi ω := rfl

theorem beta_eq (S : Study Ω) : (toStudy S).beta = S.beta := rfl

theorem betaHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    (toStudy S).betaHat s c1 c0 = S.betaHat s c1 c0 := rfl

theorem betaVarianceHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) :
    (toStudy S).betaVarianceHat s cV = S.betaVarianceHat s cV := rfl

theorem latentVectorFibre_eq (S : Fin 5 → Study Ω) (ω : Ω) :
    AronowAudit.P019.latentVectorFibre (fun j => toStudy (S j)) ω = latentVectorFibre S ω := rfl

theorem jointAssignment_eq (P : FiniteLaw Ω) (S : Fin 5 → Study Ω) :
    AronowAudit.P019.jointAssignmentStable (toLaw P) (fun j => toStudy (S j)) =
      jointAssignmentStable P S := rfl

theorem weakLimit_eq {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → E) (Q : Measure E) :
    WeakLimit P T Q ↔ AronowAudit.P019.WeakLimit (toLaw P) T Q := Iff.rfl

theorem finiteSampleWitness_eq : toStudy finiteSampleWitness =
    AronowAudit.P019.finiteSampleWitness := rfl

theorem distributionWitness_eq : toStudy distributionWitness =
    AronowAudit.P019.distributionWitness := rfl

theorem diagnosisWitness_eq : toStudy diagnosisWitness =
    AronowAudit.P019.diagnosisWitness := rfl

theorem sequentialStudy_eq (j : Fin 5) : toStudy (sequentialStudy j) =
    AronowAudit.P019.sequentialStudy j := rfl

theorem uniformFin_eq (n : ℕ) (hn : 0 < n) :
    toLaw (uniformFin n hn) = AronowAudit.P019.uniformFin n hn := rfl

theorem correlatedNormals_eq : correlatedNormals = AronowAudit.P019.correlatedNormals := rfl

theorem fisherStatistic_eq (p : Fin 5 → ℝ) :
    fisherStatistic p = AronowAudit.P019.fisherStatistic p := rfl

theorem chiSquareTen_eq : chiSquareTen = AronowAudit.P019.chiSquareTen := rfl

theorem continuousVariance_eq (P : Measure ℝ) :
    continuousVariance P = AronowAudit.P019.continuousVariance P := rfl

theorem sequential_betaHat_eq (j : Fin 5) {n : ℕ} (s : Fin n → Fin 128) (c1 c0 : ℝ) :
    (sequentialStudy j).betaHat s c1 c0 = (AronowAudit.P019.sequentialStudy j).betaHat s c1 c0 := rfl

theorem sequential_betaVarianceHat_eq (j : Fin 5) {n : ℕ} (s : Fin n → Fin 128) (cV : ℝ) :
    (sequentialStudy j).betaVarianceHat s cV =
      (AronowAudit.P019.sequentialStudy j).betaVarianceHat s cV := rfl

/-- The source's total division has exactly this explicitly guarded completion. -/
theorem studentized_eq (estimate null varianceEstimate : ℝ) :
    studentized estimate null varianceEstimate = (estimate-null) / Real.sqrt varianceEstimate := by
  by_cases h : 0 < varianceEstimate
  · simp [studentized, h]
  · simp [studentized, h, Real.sqrt_eq_zero_of_nonpos (le_of_not_gt h)]

theorem normalPValue_eq (estimate null varianceEstimate : ℝ) :
    normalPValue estimate null varianceEstimate =
      AronowAudit.P019.normalPValue estimate null varianceEstimate := by
  simp only [normalPValue, studentized_eq, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg varianceEstimate), AronowAudit.P019.normalPValue, neg_div]
  rfl

theorem sequentialFisherLimit_eq : sequentialFisherLimit =
    AronowAudit.P019.sequentialFisherLimit := by
  simp only [sequentialFisherLimit, normalPValue_eq]
  rfl

end
end SAP.P019a.Bridge
