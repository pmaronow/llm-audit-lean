import SAP.P029b.Defs
import AronowAudit.P029.P029_Audit
import AronowAudit.P029.Wave1.Gap.GP029B1
import AronowAudit.P029.Wave1.Gap.GP029B2b
import AronowAudit.P029.Wave1.Gap.GP029B3b
import AronowAudit.P029.Wave1.Gap.GLP029B1
import AronowAudit.P029.Wave1.Gap.GLP029B2
import AronowAudit.P029.Wave1.IgnorabilityOrdering
import AronowAudit.P029.Wave1.MarginalSufficiency
import AronowAudit.P029.Wave1.ConditionalSufficiency
import AronowAudit.P029.Wave1.Gap.FidP029
import AronowAudit.P029.Wave1.LateIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.Bridge

universe u v

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def toUnit {X : Type*} (u : PotentialUnit X) : AronowAudit.P029.PotentialUnit X :=
  ⟨u.x, u.d0, u.d1, u.y0, u.y1⟩

def fromUnit {X : Type*} (u : AronowAudit.P029.PotentialUnit X) : PotentialUnit X :=
  ⟨u.x, u.d0, u.d1, u.y0, u.y1⟩

theorem to_from {X : Type*} (u : AronowAudit.P029.PotentialUnit X) :
    toUnit (fromUnit u) = u := rfl

theorem from_to {X : Type*} (u : PotentialUnit X) : fromUnit (toUnit u) = u := rfl

theorem iv_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (Z : Ω → Bool) :
    AronowAudit.P029.IVAssumptions μ (fun ω => toUnit (U ω)) Z = IVAssumptions μ U Z := rfl

theorem score_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (c m : X → ℝ) :
    AronowAudit.P029.ScoreVersions μ (fun ω => toUnit (U ω)) c m = ScoreVersions μ U c m := rfl

def toConditions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ) (h : ICSWConditions μ U Z c m s) :
    AronowAudit.P029.ICSWConditions μ (fun i ω => toUnit (U i ω)) Z c m s where
  iv := h.iv
  independent := h.independent
  identical := h.identical
  score := h.score
  overlap := h.overlap
  estimated_measurable := h.estimated_measurable
  estimated_range := h.estimated_range
  uniform_consistency := h.uniform_consistency


theorem one_sided_saturated_unbiasedness_proof (n1 n0 : ℕ) (hn1 : 0 < n1) (hn0 : 0 < n0)
    (p1 : ℝ) (hp1 : p1 ∈ Icc (0 : ℝ) 1) :
    fP (binomialArmLaw n1 n0 p1 0) (fun k => k.2.val = 0) = 1 ∧
    (∀ k : Fin (n1+1) × Fin (n0+1), k.2.val = 0 →
      armRateScore n1 n0 k = (k.1.val : ℝ)/n1) ∧
    fE (binomialArmLaw n1 n0 p1 0) (armRateScore n1 n0) = p1 := by
  apply AronowAudit.P029.Wave1.one_sided_saturated_unbiasedness_proof <;> assumption


theorem saturated_binomial_bias_bound_proof (n1 n0 : ℕ) (hn1 : 0 < n1) (hn0 : 0 < n0)
    (p1 p0 : ℝ) (hp0 : 0 ≤ p0) (horder : p0 ≤ p1) (hp1 : p1 ≤ 1) :
    fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0) =
      fE (binomialArmLaw n1 n0 p1 p0)
        (fun k => positiveScore ((k.2.val : ℝ)/n0) ((k.1.val : ℝ)/n1)) ∧
    0 ≤ fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0) ∧
    (0 < p0 → p1 < 1 → 0 < fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0)) ∧
    (∀ δ : ℝ, 0 < δ →
      fP (binomialArmLaw n1 n0 p1 p0) (fun k => δ < |armRateScore n1 n0 k - (p1-p0)|) ≤
        (p1*(1-p1)/n1 + p0*(1-p0)/n0) / δ^2) := by
  apply AronowAudit.P029.Wave1.saturated_binomial_bias_bound_proof <;> assumption


theorem saturated_score_consistency_proof (n1 n0 : ℕ → ℕ)
    (hn1 : ∀ n, 0 < n1 n) (hn0 : ∀ n, 0 < n0 n)
    (ht1 : Tendsto n1 atTop atTop) (ht0 : Tendsto n0 atTop atTop)
    (p1 p0 : ℝ) (hp0 : 0 ≤ p0) (horder : p0 ≤ p1) (hp1 : p1 ≤ 1) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      fP (binomialArmLaw (n1 n) (n0 n) p1 p0)
        (fun k => δ < |armRateScore (n1 n) (n0 n) k - (p1-p0)|)) atTop (𝓝 0) := by
  apply AronowAudit.P029.Wave1.saturated_score_consistency_proof <;> assumption


theorem positive_part_error_bound (t c : ℝ) (hc : 0 ≤ c) :
    |max t 0 - c| ≤ |t - c| := by
  apply AronowAudit.P029.positive_part_error_bound <;> assumption


theorem constant_quantile {n : ℕ} (a level : ℝ) (hlevel : level ∈ Icc (0 : ℝ) 1) :
    Type7Quantile (fun _ : Fin (n+1) => a) level a ∧
    (∀ c, Type7Quantile (fun _ : Fin (n+1) => a) level c → c = a) := by
  apply AronowAudit.P029.constant_quantile <;> assumption


theorem cutoff_not_zero :
    ¬ Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0) ∧
    (∀ n (level : ℝ), level ∈ Icc (0 : ℝ) 1 →
      Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2)) ∧
    (∀ n, belowCount (fun _ : Fin (n+1) => (1/2 : ℝ)) (1/2) = 0) := by
  apply AronowAudit.P029.cutoff_not_zero <;> assumption


theorem constant_score_counterexample_law :
    FIV sixMass (liftUnit constantUnit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit constantUnit) ∧
    fScore sixMass (liftUnit constantUnit) () = 1/2 ∧
    (1/4 : ℝ) < fScore sixMass (liftUnit constantUnit) () ∧
    fE sixMass (fun i => (constantUnit i.1).tau) = 1 ∧
    fWald sixMass (liftUnit constantUnit) Prod.snd (fun _ => 2) = 1 := by
  apply AronowAudit.P029.constant_score_counterexample_law <;> assumption


theorem winsorization_cutoff_counterexample :
    FIV sixMass (liftUnit constantUnit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit constantUnit) ∧
    fScore sixMass (liftUnit constantUnit) () = 1/2 ∧
    (1/4 : ℝ) < fScore sixMass (liftUnit constantUnit) () ∧
    fE sixMass (fun i => (constantUnit i.1).tau) = 1 ∧
    fWald sixMass (liftUnit constantUnit) Prod.snd (fun _ => 2) = 1 ∧
    Tendsto (fun _ : ℕ => |(1/2 : ℝ)-fScore sixMass (liftUnit constantUnit) ()|)
      atTop (𝓝 0) ∧
    ¬ Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0) ∧
    (∀ n (level : ℝ), level ∈ Icc (0 : ℝ) 1 →
      Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2)) ∧
    (∀ n (Y : Fin (n+1) → ℝ) (D Z : Fin (n+1) → Bool),
      sampleWald (fun _ => 1/max (1/2 : ℝ) (1/2)) Y D Z =
        sampleWald (fun _ => 1/(1/2 : ℝ)) Y D Z) := by
  apply AronowAudit.P029.winsorization_cutoff_counterexample <;> assumption


theorem quantile_count_and_lower_bound {n : ℕ} (s : Fin (n+1) → ℝ) (level c b : ℝ)
    (hlevel : level ∈ Ioo (0 : ℝ) 1) (hq : Type7Quantile s level c) (hb : ∀ i, b ≤ s i) :
    (belowCount s c : ℝ) ≤ 1 + n*level ∧
    (belowCount s c : ℝ)/(n+1) ≤ level + 1/(n+1) ∧ b ≤ c := by
  apply AronowAudit.P029.quantile_count_and_lower_bound <;> assumption


theorem quantile_changed_fraction_tends_zero (s : (n : ℕ) → Fin (n+1) → ℝ)
    (c : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (hq : ∀ n, Type7Quantile (s n) (((n+1 : ℕ) : ℝ)^(-α)) (c n)) :
    Tendsto (fun n => (belowCount (s n) (c n) : ℝ)/(n+1)) atTop (𝓝 0) := by
  apply AronowAudit.P029.quantile_changed_fraction_tends_zero <;> assumption


theorem weight_change_bound (s c b : ℝ) (hb : 0 < b) (hs : b ≤ s) :
    0 ≤ weightChange s c ∧ weightChange s c ≤ (1/b) * (if s < c then 1 else 0) := by
  apply AronowAudit.P029.weight_change_bound <;> assumption


theorem bounded_weighted_mean_change {n : ℕ} (s V : Fin (n+1) → ℝ)
    (c b K : ℝ) (hb : 0 < b) (hs : ∀ i, b ≤ s i) (hK : 0 ≤ K)
    (hV : ∀ i, |V i| ≤ K) :
    |(∑ i, weightChange (s i) c * V i)/(n+1)| ≤
      (K/b) * ((belowCount s c : ℝ)/(n+1)) := by
  apply AronowAudit.P029.bounded_weighted_mean_change <;> assumption


theorem one_sided_unit_likelihood (π : ℝ) (z d : Bool) :
    bernoulliFactor (nestedReceipt π 0 z) d = bernoulliFactor (π * bit z) d := by
  apply AronowAudit.P029.one_sided_unit_likelihood <;> assumption


theorem one_sided_likelihood_reduction {I : Type*} [Fintype I]
    (π : I → ℝ) (Z D : I → Bool) (hside : ∀ i, Z i = false → D i = false) :
    (∏ i, bernoulliFactor (π i * bit (Z i)) (D i)) =
      ∏ i ∈ Finset.univ.filter (fun i => Z i = true), bernoulliFactor (π i) (D i) := by
  apply AronowAudit.P029.one_sided_likelihood_reduction <;> assumption


theorem printed_one_sided_factor_countercheck :
    ((3/4 : ℝ)^1 + (1-3/4)^0 = 7/4) ∧
    ((3/4 : ℝ)^0 + (1-3/4)^1 = 5/4) ∧
    bernoulliFactor (3/4) true = 3/4 ∧ bernoulliFactor (3/4) false = 1/4 := by
  apply AronowAudit.P029.printed_one_sided_factor_countercheck <;> assumption


theorem nested_probability_range (a b : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (z : Bool) :
    nestedReceipt a b z ∈ Ioo (0 : ℝ) 1 ∧
      nestedReceipt a b z = if z then a else a*b := by
  apply AronowAudit.P029.nested_probability_range <;> assumption


theorem corrected_equation_nine_integrand (p μ : ℝ) (hp : 0 < p) :
    (p*μ)/p = μ := by
  apply AronowAudit.P029.corrected_equation_nine_integrand <;> assumption


theorem receipt_conditioning_countercheck :
    let U : Bool × Bool → PotentialUnit Unit := fun i => ⟨(),false,i.1,0,1⟩
    let p := randomized (fun _ : Bool => (1/2 : ℝ)) (1/2)
    fP p (fun i => (U i).receipt i.2 = true) = 1/4 ∧
    fScore p U () = 1/2 ∧
    ((1/2 : ℝ)*bit false = 0) ∧ ((1/2 : ℝ)*bit true = 1/2) := by
  apply AronowAudit.P029.receipt_conditioning_countercheck <;> assumption


theorem corrected_simulation_types (iAC iA : ℝ) (z : Bool) :
    (latentAC iAC = 0 ∨ latentAC iAC = 1) ∧
    (latentA iAC iA = 0 ∨ latentA iAC iA = 1) ∧
    (latentC iAC iA = 0 ∨ latentC iAC iA = 1) ∧
    latentA iAC iA ≤ latentAC iAC ∧ latentA iAC iA * latentC iAC iA = 0 ∧
    (latentD iAC iA z = 0 ∨ latentD iAC iA z = 1) ∧
    latentD iAC iA true - latentD iAC iA false = latentC iAC iA ∧
    0 ≤ latentC iAC iA ∧
    (latentD iAC iA false = 1 ↔ latentA iAC iA = 1) ∧
    (latentD iAC iA false = 0 ∧ latentD iAC iA true = 1 ↔ latentC iAC iA = 1) ∧
    (latentD iAC iA false = 0 ∧ latentD iAC iA true = 0 ↔ latentAC iAC = 0) := by
  apply AronowAudit.P029.corrected_simulation_types <;> assumption


theorem printed_simulation_equation_failure :
    (¬ ∃ D : ℝ, D = D*1 + 1) ∧
    ((0 : ℝ) = 0*1+0 ∧ (1 : ℝ) = 1*1+0) ∧
    (∀ D A : ℝ, D = D*0+A ↔ D = A) := by
  apply AronowAudit.P029.printed_simulation_equation_failure <;> assumption


theorem simulation_outcome_identity (Y0 τ D : ℝ) :
    Y0 + τ*D = Y0 + D*((Y0+τ)-Y0) := by
  apply AronowAudit.P029.simulation_outcome_identity <;> assumption


theorem baseline_selection_counterexample :
    FIV sixMass (liftUnit case2Unit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit case2Unit) ∧
    fCE sixMass (fun i => (case2Unit i.1).y0)
      (fun i => (case2Unit i.1).receipt i.2 = true) = 1/2 ∧
    fCE sixMass (fun i => (case2Unit i.1).y0)
      (fun i => (case2Unit i.1).receipt i.2 = false) = 0 ∧
    fCE sixMass (fun i => (case2Unit i.1).y1)
      (fun i => (case2Unit i.1).receipt i.2 = true) = 3/2 ∧
    fCE sixMass (fun i => (case2Unit i.1).y1)
      (fun i => (case2Unit i.1).receipt i.2 = false) = 1 := by
  apply AronowAudit.P029.baseline_selection_counterexample <;> assumption


theorem sample_wald_bivariate_2sls {n : ℕ} (Y : Fin n → ℝ) (D Z : Fin n → Bool)
    (hn1 : 0 < ∑ i, bit (Z i)) (hn0 : (∑ i, bit (Z i)) < (n : ℝ))
    (hstage : sampleArm (fun _ => 1) (fun i => bit (D i)) Z true -
      sampleArm (fun _ => 1) (fun i => bit (D i)) Z false ≠ 0) :
    sampleWald (fun _ => 1) Y D Z = sampleCross Z Y / sampleCross Z (fun i => bit (D i)) := by
  apply AronowAudit.P029.sample_wald_bivariate_2sls <;> assumption


theorem gender_worked_example :
    ((1/2*0 + 1/2*1)/(1/2+1/2) : ℝ) = 1/2 ∧
    ((1/2*(3/4)*0 + 1/2*(1/10)*1)/(1/2*(3/4)+1/2*(1/10)) : ℝ) = 2/17 ∧
    (115/1000 : ℝ) ≤ 2/17 ∧ (2/17 : ℝ) < 125/1000 ∧
    ((1/2*(3/4)*(1/(3/4))*0 + 1/2*(1/10)*(1/(1/10))*1)/
      (1/2*(3/4)*(1/(3/4)) + 1/2*(1/10)*(1/(1/10))) : ℝ) = 1/2 := by
  apply AronowAudit.P029.gender_worked_example <;> assumption


theorem constant_scores_equal_iv {n : ℕ} (Y : Fin n → ℝ) (D Z : Fin n → Bool)
    (p : ℝ) (hp : 0 < p) :
    sampleWald (fun _ => 1/p) Y D Z = sampleWald (fun _ => 1) Y D Z := by
  apply AronowAudit.P029.constant_scores_equal_iv <;> assumption


theorem compliance_type_partition {X : Type*} (u : PotentialUnit X) (h : ¬ u.defier) :
    ¬ (u.complier ∧ u.d0 = true) ∧
    (u.complier ∨ u.d0 = true ↔ u.d1 = true) := by
  exact AronowAudit.P029.compliance_type_partition (toUnit u) h

end
end SAP.P029b.Bridge
