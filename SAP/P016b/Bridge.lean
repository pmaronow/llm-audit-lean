import SAP.P016b.Defs
import AronowAudit.P016.P016_Interference
import AronowAudit.P016.Wave1.Gap.GLP027P016P031P016B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b.Bridge
open SAP.P016b
open scoped BigOperators Classical
noncomputable section

/-- Preserve the finite law's weights and its two normalization certificates. -/
def toProjectLaw {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) :
    AronowAudit.P016.FiniteLaw Ω := ⟨P.weight, P.nonneg, P.total⟩

theorem weight_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) :
    (toProjectLaw P).weight = P.weight := rfl

theorem uniformLaw_eq (Ω : Type) [Fintype Ω] [Nonempty Ω] :
    toProjectLaw (uniformLaw Ω) = AronowAudit.P016.uniformLaw Ω := rfl

theorem mass_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (E : Ω → Prop) :
    AronowAudit.P016.mass (toProjectLaw P) E = mass P E := rfl

theorem upperP_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) :
    AronowAudit.P016.upperP (toProjectLaw P) s z = upperP P s z := rfl

theorem lowerP_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) :
    AronowAudit.P016.lowerP (toProjectLaw P) s z = lowerP P s z := rfl

theorem iidMass_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (m : ℕ)
    (E : (Fin m → Ω) → Prop) :
    AronowAudit.P016.iidMass (toProjectLaw P) m E = iidMass P m E := rfl

theorem balanced_eq (n m : ℕ) : AronowAudit.P016.Balanced n m = Balanced n m := rfl

theorem groupSize_eq {n : ℕ} (z : Assignment n) (g : Bool) :
    AronowAudit.P016.groupSize z g = groupSize z g := rfl

theorem groupMean_eq {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) :
    AronowAudit.P016.groupMean u z g = groupMean u z g := rfl

theorem rss_eq {n : ℕ} (u : Outcome n) (z : Assignment n) :
    AronowAudit.P016.rss u z = rss u z := rfl

theorem ecdf_eq {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (x : ℝ) :
    AronowAudit.P016.ecdf u z g x = ecdf u z g x := rfl

theorem sampleECDF_eq {n : ℕ} (u : Outcome n) (x : ℝ) :
    AronowAudit.P016.sampleECDF u x = sampleECDF u x := rfl

theorem ks_eq {n : ℕ} (u : Outcome n) (z : Assignment n) :
    AronowAudit.P016.ks u z = ks u z := rfl

theorem signedKS_eq {n : ℕ} (u : Outcome n) (z : Assignment n) :
    AronowAudit.P016.signedKS u z = signedKS u z := rfl

theorem additiveAdjust_eq {n : ℕ} (Y : Outcome n) (z : Assignment n) (t : ℝ) :
    AronowAudit.P016.additiveAdjust Y z t = additiveAdjust Y z t := rfl

theorem multiplicativeAdjust_eq {n : ℕ} (Y : Outcome n) (z : Assignment n) (a : ℝ) :
    AronowAudit.P016.multiplicativeAdjust Y z a = multiplicativeAdjust Y z a := rfl

theorem effectIncreasing_eq {n : ℕ} (T : Outcome n → Assignment n → ℝ) :
    AronowAudit.P016.EffectIncreasing T = EffectIncreasing T := rfl

theorem effectIncreasingOnGroups_eq {n : ℕ} (T : Outcome n → Assignment n → ℝ) :
    AronowAudit.P016.EffectIncreasingOnGroups T = EffectIncreasingOnGroups T := rfl

theorem rawP_eq {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) :
    AronowAudit.P016.rawP ref obs = rawP ref obs := rfl

theorem exchangeable_eq {B : ℕ} (μ : MeasureTheory.Measure (ReferenceVector B)) :
    AronowAudit.P016.Exchangeable μ = Exchangeable μ := rfl

theorem correctedLower_eq {B : ℕ} (t : ReferenceVector B) :
    AronowAudit.P016.correctedLower t = correctedLower t := rfl

theorem correctedUpper_eq {B : ℕ} (t : ReferenceVector B) :
    AronowAudit.P016.correctedUpper t = correctedUpper t := rfl

theorem uniformMass_eq (Ω : Type) [Fintype Ω] (E : Ω → Prop) :
    AronowAudit.P016.uniformMass Ω E = uniformMass Ω E := rfl

theorem uniformExpectation_eq (Ω : Type) [Fintype Ω] (f : Ω → ℝ) :
    AronowAudit.P016.uniformExpectation Ω f = uniformExpectation Ω f := rfl

theorem binomialMixture_eq (M B c : ℕ) :
    AronowAudit.P016.binomialMixture M B c = binomialMixture M B c := rfl

theorem evenMedian_eq {m : ℕ} (v : Outcome (2*m)) :
    AronowAudit.P016.evenMedian v = evenMedian v := rfl

theorem discrepancy_eq {n : ℕ} (y : Outcome n) (z : Assignment n) (t a : ℝ) :
    AronowAudit.P016.discrepancy y z t a = discrepancy y z t a := rfl

theorem calibrationY_eq : AronowAudit.P016.calibrationY = calibrationY := rfl
theorem calibrationZ_eq : AronowAudit.P016.calibrationZ = calibrationZ := rfl

theorem modelMultiplier_eq {n : ℕ} (S : Fin n → Fin n → ℝ) (β τ : ℝ)
    (z : Assignment n) (i : Fin n) :
    AronowAudit.P016.modelMultiplier S β τ z i = modelMultiplier S β τ z i := rfl

theorem modelMap_eq {n : ℕ} (S : Fin n → Fin n → ℝ) (β τ : ℝ)
    (y : Outcome n) (z w : Assignment n) :
    AronowAudit.P016.modelMap S β τ y z w = modelMap S β τ y z w := rfl

/-- Instantiate the exported witness at an assignment with two units in each group. -/
theorem ks_not_effectIncreasingOnGroups :
    ¬ EffectIncreasingOnGroups (ks (n := 4)) ∧
    ¬ EffectIncreasingOnGroups (signedKS (n := 4)) := by
  have h0 : 0 < groupSize (complete4 0) false := by
    decide
  have h1 : 0 < groupSize (complete4 0) true := by
    decide
  have hw := AronowAudit.P016.t11_ks_witness
  constructor <;> intro h
  · have hi : AronowAudit.P016.ks AronowAudit.P016.u4 (AronowAudit.P016.complete4 0) ≤
        AronowAudit.P016.ks ![2,3,2,3] (AronowAudit.P016.complete4 0) :=
      h (complete4 0) h0 h1 u4 ![2,3,2,3] hw.1
    rw [hw.2.1, hw.2.2.1] at hi
    norm_num at hi
  · have hi : AronowAudit.P016.signedKS AronowAudit.P016.u4 (AronowAudit.P016.complete4 0) ≤
        AronowAudit.P016.signedKS ![2,3,2,3] (AronowAudit.P016.complete4 0) :=
      h (complete4 0) h0 h1 u4 ![2,3,2,3] hw.1
    rw [hw.2.2.2.1, hw.2.2.2.2.1] at hi
    norm_num at hi

/-- The three credited weak bounds, plus event inclusion for the strict cutoffs. -/
theorem exactValidity : ExactValidity := by
  intro Ω _ P hP s α hα hα1
  have hU : mass P (fun z => upperP P s z ≤ α) ≤ α :=
    AronowAudit.P016.t12_upper_valid (toProjectLaw P) hP s α hα hα1
  have hL : mass P (fun z => lowerP P s z ≤ α) ≤ α :=
    AronowAudit.P016.t12_lower_valid (toProjectLaw P) hP s α hα hα1
  have h2 : mass P (fun z => doubledP (lowerP P s z) (upperP P s z) ≤ α) ≤ α :=
    AronowAudit.P016.t12_two_tail_valid (toProjectLaw P) hP s α hα hα1
  refine ⟨hU, hL, h2, ?_, ?_, ?_⟩
  · exact (AronowAudit.P016.mass_mono (toProjectLaw P)
      (fun z (h : upperP P s z < α) => h.le)).trans hU
  · exact (AronowAudit.P016.mass_mono (toProjectLaw P)
      (fun z (h : lowerP P s z < α) => h.le)).trans hL
  · exact (AronowAudit.P016.mass_mono (toProjectLaw P)
      (fun z (h : doubledP (lowerP P s z) (upperP P s z) < α) => h.le)).trans h2

end
end SAP.P016b.Bridge
