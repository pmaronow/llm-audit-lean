import SAP.P001d.Defs
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.Bridge

theorem prob_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) :
    prob μ A = AronowAudit.P001.prob μ A := rfl

theorem cp_iff {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) :
    CP μ Z c ↔ AronowAudit.P001.CP μ Z c := Iff.rfl

theorem iid_iff {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : IID μ X ↔ AronowAudit.P001.IID μ X := Iff.rfl

theorem cef_iff {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) :
    IsCEF μ X Y m ↔ AronowAudit.P001.IsCEF μ X Y m := Iff.rfl

theorem kernelDensity_eq {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) :
    kernelDensity K h X = AronowAudit.P001.kernelDensity K h X := rfl

theorem kernelCDF_eq {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) :
    kernelCDF K h X = AronowAudit.P001.kernelCDF K h X := rfl

theorem heavyBootstrapLaw_eq : heavyBootstrapLaw = AronowAudit.P001.heavyBootstrapLaw := rfl

theorem sampleMedian_eq {n : ℕ} : @sampleMedian n = @AronowAudit.P001.sampleMedian n := rfl

theorem regularHeavyFunctional_eq : regularHeavyFunctional = AronowAudit.P001.regularHeavyFunctional := rfl

theorem bootVar_eq {n : ℕ} (T : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    bootVar T x = AronowAudit.P001.bootVar T x := rfl

theorem firstSample_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    firstSample X n ω = AronowAudit.P001.firstSample X n ω := rfl

theorem finiteSampleMean_eq {n : ℕ} :
    @finiteSampleMean n = @AronowAudit.P001.finiteSampleMean n := rfl

theorem bootstrapWeak_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (sizes : ℕ → ℕ) (T : {n : ℕ} → (Fin n → ℝ) → ℝ)
    (ν : Measure ℝ) : BootstrapWeakCP μ X sizes T ν ↔
      AronowAudit.P001.BootstrapWeakCP μ X sizes T ν := Iff.rfl

theorem clusterAverage_eq {Ω : Type*} {m : ℕ} (X : ℕ → Ω → Fin m → ℝ) :
    clusterAverage X = AronowAudit.P001.clusterAverage X := rfl

theorem clusterMean_eq {Ω : Type*} {m : ℕ} (X : ℕ → Ω → Fin m → ℝ) :
    clusterMean X = AronowAudit.P001.clusterMean X := rfl

theorem olsRSS_eq {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ) :
    olsRSS X Y = AronowAudit.P001.olsRSS X Y := rfl

theorem olsCoef_eq {n K : ℕ} (X : Matrix (Fin n) (Fin K) ℝ) (Y : Fin n → ℝ) :
    olsCoef X Y = AronowAudit.P001.olsCoef X Y := rfl

theorem robustCov_eq {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (e : Fin n → ℝ) :
    robustCov X e = AronowAudit.P001.robustCov X e := rfl

theorem classicalCov_eq {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (s2 : ℝ) :
    classicalCov X s2 = AronowAudit.P001.classicalCov X s2 := rfl

theorem slopePenalty_eq {K : ℕ} (b : Fin (K+1) → ℝ) :
    slopePenalty b = AronowAudit.P001.slopePenalty b := rfl

theorem lassoCriterion_eq {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (lam : ℝ) : lassoCriterion X Y lam = AronowAudit.P001.lassoCriterion X Y lam := rfl

theorem normalDensity_eq (m s : ℝ) : normalDensity m s = AronowAudit.P001.normalDensity m s := rfl

theorem finiteMean_eq (X : Fin 4 → ℝ) :
    finiteMean X = AronowAudit.P001.fmean AronowAudit.P001.heteroskedasticLaw X := rfl

theorem finiteProb_eq (A : Fin 4 → Prop) :
    finiteProb A = @AronowAudit.P001.fprob 4 AronowAudit.P001.heteroskedasticLaw A
      (fun i => Classical.propDecidable (A i)) := rfl

theorem project_finiteProb_eq (A : Fin 4 → Prop) [d : DecidablePred A] :
    AronowAudit.P001.fprob AronowAudit.P001.heteroskedasticLaw A = finiteProb A := by
  have hd : d = (fun i => Classical.propDecidable (A i)) := Subsingleton.elim _ _
  cases hd
  rfl

theorem finiteCond_eq (Y X : Fin 4 → ℝ) (x : ℝ) :
    finiteCond Y X x = AronowAudit.P001.fcond AronowAudit.P001.heteroskedasticLaw Y X x := rfl

theorem finiteCov_eq (X Y : Fin 4 → ℝ) :
    finiteCov X Y = AronowAudit.P001.fcov AronowAudit.P001.heteroskedasticLaw X Y := rfl

theorem heteroX_eq : heteroX = AronowAudit.P001.heteroX := rfl
theorem heteroY_eq : heteroY = AronowAudit.P001.heteroY := rfl
theorem heteroResidual_eq : heteroResidual = AronowAudit.P001.heteroResidual := rfl

/-- Reindexing a limit by the positive sample sizes changes no asymptotic assertion. -/
theorem cp_succ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ) (c : ℝ) (h : AronowAudit.P001.CP μ Z c) :
    CP μ (fun n => Z (n+1)) c := by
  intro ε hε
  exact (h ε hε).comp (tendsto_add_atTop_nat 1)

/-- Transport the existing Gaussian moment certificates through its density representation. -/
theorem normalDensity_certificates (m s : ℝ) (hs : 0 < s) :
    (∀ y, 0 ≤ normalDensity m s y) ∧ Integrable (normalDensity m s) volume ∧
    Integrable (fun y => y*normalDensity m s y) volume := by
  let v : ℝ≥0 := ⟨s^2, sq_nonneg _⟩
  have hv : v ≠ 0 := by
    intro h
    have he : s^2 = 0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
    exact hs.ne' (sq_eq_zero_iff.mp he)
  have hd : normalDensity m s = gaussianPDFReal m v :=
    AronowAudit.P001.normalDensity_eq_gaussianPDFReal m s hs
  have hi : Integrable (fun y : ℝ => y) (gaussianReal m v) :=
    (memLp_id_gaussianReal 2).integrable (by norm_num)
  rw [gaussianReal_of_var_ne_zero _ hv] at hi
  have hh := (integrable_withDensity_iff_integrable_smul₀'
    (measurable_gaussianPDF m v).aemeasurable
    (ae_of_all _ (fun y => show gaussianPDF m v y < ∞ from gaussianPDF_lt_top))).mp hi
  refine ⟨fun y => hd ▸ gaussianPDFReal_nonneg m v y, hd ▸ integrable_gaussianPDFReal m v, ?_⟩
  simpa only [hd, gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m v _),
    smul_eq_mul, mul_comm] using hh

end SAP.P001d.Bridge
