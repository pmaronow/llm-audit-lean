import SAP.P022.WH.W1.Leaves
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T17_L7

open ProbabilityTheory MeasureTheory Set

local instance : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma normalCDF_eq_cdf (x : ℝ) :
    SAP.P022.normalCDF x = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
  calc
    SAP.P022.normalCDF x = AronowAudit.P053.standardNormalCDF x := rfl
    _ = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x :=
      AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf x

lemma strictMono_normalCDF : StrictMono SAP.P022.normalCDF := by
  intro x y hxy
  rw [normalCDF_eq_cdf, normalCDF_eq_cdf]
  exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hxy

lemma normalCDF_zero : SAP.P022.normalCDF 0 = 1 / 2 := by
  rw [normalCDF_eq_cdf]
  exact AronowAudit.P053.NormalCompletion.normal_cdf_zero

lemma normalCritical_facts (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    SAP.P022.NormalCriticalDefined α ∧
      0 < SAP.P022.normalCritical α ∧
      SAP.P022.normalCDF (SAP.P022.normalCritical α) = 1 - α / 2 := by
  let p : ℝ := 1 - α / 2
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  obtain ⟨q, hq⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) hp0 hp1
  have hq' : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) q =
      1 - α / 2 := by simpa [p] using hq
  have hset : {x : ℝ | 1 - α / 2 ≤ SAP.P022.normalCDF x} = Set.Ici q := by
    ext x
    change (1 - α / 2 ≤ SAP.P022.normalCDF x) ↔ q ≤ x
    calc
      1 - α / 2 ≤ SAP.P022.normalCDF x ↔
          ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) q ≤
            ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
        rw [normalCDF_eq_cdf, ← hq']
      _ ↔ q ≤ x :=
        AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.le_iff_le
  have hcrit : SAP.P022.normalCritical α = q := by
    unfold SAP.P022.normalCritical
    rw [hset]
    exact csInf_Ici
  have hdefined : SAP.P022.NormalCriticalDefined α := by
    constructor
    · refine ⟨q, ?_⟩
      change 1 - α / 2 ≤ SAP.P022.normalCDF q
      rw [normalCDF_eq_cdf, ← hq']
    · exact ⟨q, by
        intro x hx
        change x ∈ {y : ℝ | 1 - α / 2 ≤ SAP.P022.normalCDF y} at hx
        rw [hset] at hx
        exact hx⟩
  have hc : SAP.P022.normalCDF (SAP.P022.normalCritical α) = 1 - α / 2 := by
    rw [hcrit, normalCDF_eq_cdf]
    exact hq'
  have hz : 0 < SAP.P022.normalCritical α := by
    apply (strictMono_normalCDF.lt_iff_lt).mp
    rw [normalCDF_zero, hc]
    linarith
  exact ⟨hdefined, hz, hc⟩

end SAP.P022.WH.W1.P.T17_L7

theorem SAP.P022.WH.W1.T17_L7_proof : SAP.P022.WH.W1.T17_L7 := by
  constructor
  · intro α hα hα1
    exact SAP.P022.WH.W1.P.T17_L7.normalCritical_facts α hα hα1
  · intro α v s hα hα1 hv hs
    let z : ℝ := SAP.P022.normalCritical α
    let r : ℝ := Real.sqrt (v / s)
    have hz : 0 < z := by
      dsimp [z]
      exact (SAP.P022.WH.W1.P.T17_L7.normalCritical_facts α hα hα1).2.1
    have hc : SAP.P022.normalCDF z = 1 - α / 2 := by
      dsimp [z]
      exact (SAP.P022.WH.W1.P.T17_L7.normalCritical_facts α hα hα1).2.2
    have hratio : 0 ≤ v / s := div_nonneg hv hs.le
    have hmono := SAP.P022.WH.W1.P.T17_L7.strictMono_normalCDF
    have hcov :
        (1 - α ≤ SAP.P022.gaussianWaldCoverage α v s ↔ s ≤ v) := by
      change (1 - α ≤ 2 * SAP.P022.normalCDF (z * r) - 1 ↔ s ≤ v)
      constructor
      · intro hcoverage
        have hcdf : SAP.P022.normalCDF z ≤ SAP.P022.normalCDF (z * r) := by
          nlinarith [hcoverage, hc]
        have harg : z ≤ z * r := hmono.le_iff_le.mp hcdf
        have hr : 1 ≤ r := by nlinarith [hz, harg]
        have hratio' : 1 ≤ v / s := (Real.one_le_sqrt).mp (by simpa [r] using hr)
        simpa using (le_div_iff₀ hs).mp hratio'
      · intro hvariance
        have hratio' : 1 ≤ v / s := (le_div_iff₀ hs).2 (by nlinarith)
        have hr : 1 ≤ r := by
          dsimp [r]
          exact Real.one_le_sqrt.mpr hratio'
        have harg : z ≤ z * r := by nlinarith [hz, hr]
        have hcdf : SAP.P022.normalCDF z ≤ SAP.P022.normalCDF (z * r) :=
          hmono.monotone harg
        nlinarith [hcdf, hc]
    have hstrict : v < s → SAP.P022.gaussianWaldCoverage α v s < 1 - α := by
      intro hvs
      change 2 * SAP.P022.normalCDF (z * r) - 1 < 1 - α
      have hratio' : v / s < 1 := (div_lt_one hs).2 hvs
      have hr : r < 1 := by
        dsimp [r]
        calc
          Real.sqrt (v / s) < Real.sqrt 1 := Real.sqrt_lt_sqrt hratio hratio'
          _ = 1 := by norm_num
      have harg : z * r < z := by nlinarith [hz, hr]
      have hcdf : SAP.P022.normalCDF (z * r) < SAP.P022.normalCDF z := hmono harg
      nlinarith [hcdf, hc]
    exact ⟨hcov, hstrict⟩
