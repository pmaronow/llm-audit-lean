import SAP.P019b.Defs
import AronowAudit.P019.Wave1.Gap.GP019B1
import AronowAudit.P019.Wave1.Gap.GP019B2b
import AronowAudit.P019.Wave1.Gap.GLP019B2
import AronowAudit.P019.Wave1.Gap.GP019B3b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b.Bridge

open MeasureTheory
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

/-- Preserve all atom masses and their validity certificates. -/
def toLaw (P : FiniteLaw Ω) : AronowAudit.P019.FiniteLaw Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

/-- Preserve the population law and every observed variable. -/
def toStudy (S : Study Ω) : AronowAudit.P019.Study Ω :=
  ⟨toLaw S.law, S.W, S.X, S.Y, S.Z, S.V⟩

theorem mean_eq (P : FiniteLaw Ω) (f : Ω → ℝ) :
    (toLaw P).mean f = P.mean f := rfl

theorem prob_eq (P : FiniteLaw Ω) (D : Ω → Prop) [DecidablePred D] :
    (toLaw P).prob D = P.prob D := rfl

theorem ce_eq (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] :
    (toLaw P).ce f D = P.ce f D := rfl

theorem variance_eq (P : FiniteLaw Ω) (f : Ω → ℝ) :
    (toLaw P).variance f = P.variance f := rfl

theorem cv_eq (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] :
    (toLaw P).cv f D = P.cv f D := rfl

theorem iid_eq (P : FiniteLaw Ω) (n : ℕ) :
    (toLaw P).iid n = toLaw (P.iid n) := rfl

theorem monotone_iff (S : Study Ω) :
    (toStudy S).monotone ↔ S.monotone := Iff.rfl

theorem noLiarsDesign_iff (S : Study Ω) :
    (toStudy S).noLiarsDesign ↔ S.noLiarsDesign := Iff.rfl

theorem independent_iff (S : Study Ω) :
    (toStudy S).treatmentIndependent ↔ S.treatmentIndependent := Iff.rfl

theorem nondegenerate_iff (S : Study Ω) :
    (toStudy S).nondegenerate ↔ S.nondegenerate := Iff.rfl

theorem standing_iff (S : Study Ω) :
    (toStudy S).standing ↔ S.standing := Iff.rfl

theorem tripleIndependent_iff (P : FiniteLaw Ω) (W : Ω → ℕ) (R Q Z : Ω → Bool) :
    AronowAudit.P019.tripleIndependent (toLaw P) W R Q Z ↔
      tripleIndependent P W R Q Z := Iff.rfl

theorem mu_eq (S : Study Ω) : (toStudy S).mu = S.mu := rfl
theorem truthRate_eq (S : Study Ω) : (toStudy S).truthRate = S.truthRate := rfl
theorem gamma_eq (S : Study Ω) : (toStudy S).gamma = S.gamma := rfl
theorem listMean_eq (S : Study Ω) (z y : Bool) :
    (toStudy S).listMean z y = S.listMean z y := rfl
theorem combined_eq (S : Study Ω) : (toStudy S).combined = S.combined := rfl
theorem beta_eq (S : Study Ω) : (toStudy S).beta = S.beta := rfl
theorem delta_eq (S : Study Ω) : (toStudy S).delta = S.delta := rfl

theorem muHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    (toStudy S).muHat s c1 c0 = S.muHat s c1 c0 := rfl
theorem standardHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    (toStudy S).standardHat s c1 c0 = S.standardHat s c1 c0 := rfl
theorem muVarianceHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 cV : ℝ) :
    (toStudy S).muVarianceHat s c1 c0 cV = S.muVarianceHat s c1 c0 cV := rfl
theorem sigmaSq_eq (S : Study Ω) : (toStudy S).sigmaSq = S.sigmaSq := rfl
theorem standardSigmaSq_eq (S : Study Ω) :
    (toStudy S).standardSigmaSq = S.standardSigmaSq := rfl
theorem betaHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    (toStudy S).betaHat s c1 c0 = S.betaHat s c1 c0 := rfl
theorem betaVarianceHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) :
    (toStudy S).betaVarianceHat s cV = S.betaVarianceHat s cV := rfl
theorem deltaHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    (toStudy S).deltaHat s c1 c0 = S.deltaHat s c1 c0 := rfl
theorem deltaVarianceHat_eq (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) :
    (toStudy S).deltaVarianceHat s cV = S.deltaVarianceHat s cV := rfl

theorem weakLimit_iff {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → E) (Q : Measure E) :
    AronowAudit.P019.WeakLimit (toLaw P) T Q ↔ WeakLimit P T Q := Iff.rfl

theorem probabilityLimit_iff (P : FiniteLaw Ω)
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (a : ℝ) :
    AronowAudit.P019.ProbabilityLimit (toLaw P) T a ↔ ProbabilityLimit P T a := Iff.rfl

theorem rootNTight_iff (S : Study Ω) (c1 c0 : ℝ) :
    AronowAudit.P019.RootNTight (toStudy S) c1 c0 ↔ RootNTight S c1 c0 := Iff.rfl

theorem normalCDF_eq (t : ℝ) : AronowAudit.P019.normalCDF t = normalCDF t := rfl
theorem normalQuantile_eq (u : ℝ) :
    AronowAudit.P019.normalQuantile u = normalQuantile u := rfl
theorem normalPValue_eq (e v a : ℝ) :
    AronowAudit.P019.normalPValue e v a = normalPValue e v a := rfl

theorem planningS_eq (p1 p2 : ℝ) :
    AronowAudit.P019.planningS p1 p2 = planningS p1 p2 := rfl
theorem planningV_eq (p1 p2 : ℝ) :
    AronowAudit.P019.planningV p1 p2 = planningV p1 p2 := rfl
theorem favoredTail_eq (n p1 p2 c : ℝ) :
    AronowAudit.P019.favoredTail n p1 p2 c = favoredTail n p1 p2 c := rfl
theorem oppositeTail_eq (n p1 p2 c : ℝ) :
    AronowAudit.P019.oppositeTail n p1 p2 c = oppositeTail n p1 p2 c := rfl
theorem planningPower_eq (n p1 p2 c : ℝ) :
    AronowAudit.P019.twoSidedPlanningPower n p1 p2 c =
      twoSidedPlanningPower n p1 p2 c := rfl

theorem cnnWitness_eq : AronowAudit.P019.cnnWitness = toStudy cnnWitness := rfl
theorem cnnReading_eq (b : Bool) (ω : Fin 12) :
    AronowAudit.P019.cnnReading b ω = cnnReading b ω := rfl
theorem cnnWatching_eq (b : Bool) (ω : Fin 12) :
    AronowAudit.P019.cnnWatching b ω = cnnWatching b ω := rfl
theorem ceilingBeta_eq (ρ : ℝ) :
    AronowAudit.P019.ceilingBeta AronowAudit.P019.printedAffected ρ =
      ceilingBeta printedAffected ρ := rfl

end
end SAP.P019b.Bridge
