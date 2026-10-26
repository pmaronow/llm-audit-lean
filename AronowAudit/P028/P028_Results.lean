import Mathlib.Tactic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Bernoulli

namespace AronowAudit.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
open Classical

/-- The CACE τ=(EY₁-EY₀)/P_c, Section 2's LATE display, p. 678. -/
def effect (p e0 e1 : ℝ) : ℝ := (e1 - e0) / p

/-- Proposition 1's control lower endpoint, p. 678:
max{0, -(EY₁-EY₀)/P_c, 1-(1-EY₀)/P_c}. -/
def lowerControl (p e0 e1 : ℝ) : ℝ :=
  max (max 0 (-effect p e0 e1)) (1 - (1 - e0) / p)
/-- Proposition 1's control upper endpoint, p. 678:
“min{1, 1-(EY₁-EY₀)/P_c, EY₀/P_c}”. -/
def upperControl (p e0 e1 : ℝ) : ℝ :=
  min (min 1 (1 - effect p e0 e1)) (e0 / p)
/-- Proposition 1's treated lower endpoint, p. 678:
“max{0, (EY₁-EY₀)/P_c, 1-(1-EY₁)/P_c}”. -/
def lowerTreated (p e0 e1 : ℝ) : ℝ :=
  max (max 0 (effect p e0 e1)) (1 - (1 - e1) / p)
/-- Proposition 1's treated upper endpoint, p. 678:
“min{1, 1+(EY₁-EY₀)/P_c, EY₁/P_c}”. -/
def upperTreated (p e0 e1 : ℝ) : ℝ :=
  min (min 1 (1 + effect p e0 e1)) (e1 / p)

/-- Eqs. (1)-(2) and the three unit-interval restrictions, Proposition 1 proof,
p. 678. `n` is the ordinary noncomplier mean, used only for P_c<1. -/
def mixtureSystem (p e0 e1 x0 x1 : ℝ) : Prop :=
  ∃ n : ℝ, p*x0 + (1-p)*n = e0 ∧ p*x1 + (1-p)*n = e1 ∧
    0 ≤ x0 ∧ x0 ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧ 0 ≤ n ∧ n ≤ 1

/-- The corrected sentence after Eq. (3), p. 678: the noncomplier
contribution is bounded by 1-P_c, rather than the printed 1. -/
def correctedSystem (p e0 e1 x0 x1 : ℝ) : Prop :=
  p*x0 + e1 - p*x1 = e0 ∧ 0 ≤ x0 ∧ x0 ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧
    0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1-p

/-- The system as actually printed after Eq. (3), Proposition 1 proof, p. 678. -/
def printedSystem (p e0 e1 x0 x1 : ℝ) : Prop :=
  p*x0 + e1 - p*x1 = e0 ∧ 0 ≤ x0 ∧ x0 ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧
    0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1

/-- T4(i): for 0<P_c<1 the corrected intermediate system is equivalent to
the original mixture equations with a noncomplier mean in [0,1]. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem corrected_reframing (p e0 e1 x0 x1 : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    mixtureSystem p e0 e1 x0 x1 ↔ correctedSystem p e0 e1 x0 x1 := by
  constructor
  · rintro ⟨n, h0, h1, hx0, hx01, hx1, hx11, hn, hn1⟩
    refine ⟨by linarith, hx0, hx01, hx1, hx11, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h, hx0, hx01, hx1, hx11, hm, hm1⟩
    have hd : 0 < 1-p := by linarith
    have he : (1-p)*((e1-p*x1)/(1-p)) = e1-p*x1 :=
      mul_div_cancel₀ _ (ne_of_gt hd)
    refine ⟨(e1-p*x1)/(1-p), by linarith, by linarith,
      hx0, hx01, hx1, hx11, div_nonneg hm hd.le, ?_⟩
    exact (div_le_one hd).2 hm1

/-- T4(i): when the original system holds, Eq. (2) uniquely determines n
as (EY₁-P_c EY_c(1))/(1-P_c). The denominator condition is explicit. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem noncomplier_mean_from_equation (p e1 x1 n : ℝ) (hp1 : p < 1)
    (h : p*x1 + (1-p)*n = e1) : n = (e1-p*x1)/(1-p) := by
  apply (eq_div_iff (by linarith : 1-p ≠ 0)).2
  linarith

/-- T4(ii): the variable eliminated through Eq. (3) is the control mean x0. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem control_substitution (p e0 e1 x0 x1 : ℝ) (hp : 0 < p) :
    p*x0 + e1 - p*x1 = e0 ↔ x0 = x1 - effect p e0 e1 := by
  unfold effect
  have ht : p*((e1-e0)/p) = e1-e0 := mul_div_cancel₀ _ (ne_of_gt hp)
  constructor <;> intro h <;> nlinarith

/-- T4(ii): substituting x0=x1-τ translates the unit-interval restriction. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem control_unit_interval (x1 t : ℝ) :
    (0 ≤ x1-t ∧ x1-t ≤ 1) ↔ (t ≤ x1 ∧ x1 ≤ 1+t) := by
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

/-- T4(ii): the corrected contribution constraint gives exactly the third line
of the printed three-line display. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem contribution_interval (p e1 x1 : ℝ) (hp : 0 < p) :
    (0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1-p) ↔
    ((e1+p-1)/p ≤ x1 ∧ x1 ≤ e1/p) := by
  rw [div_le_iff₀ hp, le_div_iff₀ hp]
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

/-- Algebraic equality of the two forms of Proposition 1's third lower limit. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem third_lower_identity (p e : ℝ) (hp : 0 < p) :
    (e+p-1)/p = 1-(1-e)/p := by
  field_simp
  <;> ring

/-- T4(iii): the corrected system is exactly the treated interval together with
the implied control mean. This statement permits all real arm means. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem corrected_interval_system (p e0 e1 x0 x1 : ℝ) (hp : 0 < p) :
    correctedSystem p e0 e1 x0 x1 ↔
      x0 = x1 - effect p e0 e1 ∧
      lowerTreated p e0 e1 ≤ x1 ∧ x1 ≤ upperTreated p e0 e1 := by
  unfold correctedSystem lowerTreated upperTreated
  rw [control_substitution p e0 e1 x0 x1 hp]
  constructor
  · rintro ⟨h, hx0, hx01, hx1, hx11, hm, hm1⟩
    have hc := (control_unit_interval x1 (effect p e0 e1)).1
      (by simpa [← h] using And.intro hx0 hx01)
    have hm' := (contribution_interval p e1 x1 hp).1 ⟨hm, hm1⟩
    rw [third_lower_identity p e1 hp] at hm'
    exact ⟨h, max_le (max_le hx1 hc.1) hm'.1,
      le_min (le_min hx11 hc.2) hm'.2⟩
  · rintro ⟨h, hl, hu⟩
    simp only [max_le_iff] at hl
    simp only [le_min_iff] at hu
    have hc := (control_unit_interval x1 (effect p e0 e1)).2 ⟨hl.1.2, hu.1.2⟩
    have hm := (contribution_interval p e1 x1 hp).2
      ⟨by simpa [third_lower_identity p e1 hp] using hl.2, hu.2⟩
    exact ⟨h, by simpa [h] using hc.1, by simpa [h] using hc.2,
      hl.1.1, hu.1.1, hm.1, hm.2⟩

/-- T4(iii): subtracting τ from the treated endpoints yields exactly the
control endpoints printed in Proposition 1. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem endpoint_translation (p e0 e1 : ℝ) (hp : 0 < p) :
    lowerTreated p e0 e1 - effect p e0 e1 = lowerControl p e0 e1 ∧
    upperTreated p e0 e1 - effect p e0 e1 = upperControl p e0 e1 := by
  have hl : (1-(1-e1)/p)-effect p e0 e1 = 1-(1-e0)/p := by
    unfold effect
    field_simp [ne_of_gt hp]
    <;> ring
  have hu : e1/p-effect p e0 e1 = e0/p := by
    unfold effect
    field_simp [ne_of_gt hp]
    <;> ring
  constructor
  · simp only [lowerTreated, lowerControl, ← max_sub_sub_right, sub_self, zero_sub, hl]
    rw [max_comm (-effect p e0 e1) 0]
  · simp only [upperTreated, upperControl, ← min_sub_sub_right, hu]
    simp only [add_sub_cancel_right]
    rw [min_comm (1 - effect p e0 e1) 1]

/-- T4(iv): the weaker printed constraint yields (EY₁-1)/P_c, rather than
(EY₁+P_c-1)/P_c, as its lower restriction. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem printed_contribution_interval (p e1 x1 : ℝ) (hp : 0 < p) :
    (0 ≤ e1-p*x1 ∧ e1-p*x1 ≤ 1) ↔
    ((e1-1)/p ≤ x1 ∧ x1 ≤ e1/p) := by
  rw [div_le_iff₀ hp, le_div_iff₀ hp]
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

/-- T4(iv): for e1≤1 and x1≥0, the printed upper contribution restriction
is redundant; it cannot supply the missing lower limit in general. 
Reference (P028-T4): Corrected Proposition 1 proof after Eq. (3), p. 678. -/
theorem printed_lower_redundant (p e1 x1 : ℝ) (hp : 0 < p)
    (he : e1 ≤ 1) (hx : 0 ≤ x1) : (e1-1)/p ≤ x1 := by
  apply (div_le_iff₀ hp).2
  nlinarith

/-- T5: at (p,e0,e1,x0,x1)=(1/2,3/4,3/4,0,0), the printed system holds
but no noncomplier mean in [0,1] satisfies Eqs. (1)-(2). Its implied mean is
3/2, and the corrected residual restriction fails. This refutes a proof step,
not Proposition 1. 
Reference (P028-T5): Printed Proposition 1 proof after Eq. (3), p. 678. -/
theorem misprinted_constraint_counterexample :
    printedSystem (1/2) (3/4) (3/4) 0 0 ∧
    ¬ mixtureSystem (1/2) (3/4) (3/4) 0 0 ∧
    ¬ correctedSystem (1/2) (3/4) (3/4) 0 0 ∧
    ((3/4-(1/2)*0)/(1-1/2) : ℝ) = 3/2 ∧
    (((3/4)-1)/(1/2) : ℝ) = -1/2 ∧
    (((3/4)+(1/2)-1)/(1/2) : ℝ) = 1/2 ∧
    lowerControl (1/2) (3/4) (3/4) = 1/2 ∧
    upperControl (1/2) (3/4) (3/4) = 1 ∧
    lowerTreated (1/2) (3/4) (3/4) = 1/2 ∧
    upperTreated (1/2) (3/4) (3/4) = 1 := by
  constructor
  · norm_num [printedSystem]
  constructor
  · rintro ⟨n, h0, h1, hx0, hx01, hx1, hx11, hn, hn1⟩
    norm_num at h1
    linarith
  · norm_num [correctedSystem, lowerControl, upperControl,
      lowerTreated, upperTreated, effect]

/-- T6(vii): the two printed intervals at P_c=1 are singletons for every
e0,e1 in [0,1]; there is no division by a noncomplier mass. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem full_compliance_endpoints (e0 e1 : ℝ)
    (he0 : 0 ≤ e0 ∧ e0 ≤ 1) (he1 : 0 ≤ e1 ∧ e1 ≤ 1) :
    lowerControl 1 e0 e1 = e0 ∧ upperControl 1 e0 e1 = e0 ∧
    lowerTreated 1 e0 e1 = e1 ∧ upperTreated 1 e0 e1 = e1 := by
  unfold lowerControl upperControl lowerTreated upperTreated effect
  simp only [div_one]
  have h0 : 1-(1-e0) = e0 := by ring
  have h1 : 1-(1-e1) = e1 := by ring
  rw [h0,h1]
  have h00 : max 0 (-(e1-e0)) ≤ e0 := max_le he0.1 (by linarith [he1.1])
  have h01 : e0 ≤ min 1 (1-(e1-e0)) := le_min he0.2 (by linarith [he1.2])
  have h10 : max 0 (e1-e0) ≤ e1 := max_le he1.1 (by linarith [he0.1])
  have h11 : e1 ≤ min 1 (1+(e1-e0)) := le_min he1.2 (by linarith [he0.2])
  exact ⟨max_eq_right h00, min_eq_right h01, max_eq_right h10, min_eq_right h11⟩


/-- Monotone principal strata (0=A, 1=N, 2=C), Section 2, p. 678.
These encode exactly the three allowed pairs (D(0),D(1))=(1,1),(0,0),(0,1). -/
def treatment (s : Fin 3) (z : Bool) : Bool :=
  if s = 0 then true else if s = 1 then false else z
/-- Real value of a binary variable, 0 or 1. -/
def realBit (b : Bool) : ℝ := if b then 1 else 0

/-- A generic-unit probability model for Section 2, p. 678: “Let Yᵢ(d,z) be the
potential outcome of unit i under treatment d” and “let Dᵢ(z) be the potential
treatment of unit i under assignment z”. The latent stratum
encodes monotonicity exactly; Y(d,z)=Y(d) encodes exclusion. The joint potential
vector (S,Y(0),Y(1)) is independent of Z, which has two positive-probability arms.
Potential outcomes are integrable, with boundedness supplied separately only
where the paper needs it. There is no finite-support or sampling assumption. -/
structure CausalModel (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  S : Ω → Fin 3
  Y : Bool → Ω → ℝ
  Z : Ω → Bool
  measurableS : Measurable S
  measurableY : ∀ d, Measurable (Y d)
  integrableY : ∀ d, Integrable (Y d) μ
  measurableZ : Measurable Z
  randomAssignment : IndepFun (fun ω => (S ω, Y false ω, Y true ω)) Z μ
  armPositive : ∀ z, 0 < μ.real {ω | Z ω = z}
  nonzeroFirstStage : (∫ ω, realBit (treatment (S ω) true) -
    realBit (treatment (S ω) false) ∂μ) ≠ 0

attribute [instance] CausalModel.probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Compliers C={D(1)>D(0)}, Section 2, p. 678. -/
def complierEvent (M : CausalModel Ω) : Set Ω := {ω | M.S ω = 2}
/-- Always-takers A={D(0)=D(1)=1}, principal-stratum decomposition in the
derivation of Proposition 1 and Corollary 1. -/
def alwaysEvent (M : CausalModel Ω) : Set Ω := {ω | M.S ω = 0}
/-- Never-takers N={D(0)=D(1)=0}, same principal-stratum decomposition. -/
def neverEvent (M : CausalModel Ω) : Set Ω := {ω | M.S ω = 1}
/-- Noncompliers {D(1)=D(0)}, Proposition 1 proof, p. 678. -/
def noncomplierEvent (M : CausalModel Ω) : Set Ω := (complierEvent M)ᶜ
/-- Assignment arm {Z=z}, Section 2, p. 678. -/
def armEvent (M : CausalModel Ω) (z : Bool) : Set Ω := {ω | M.Z ω = z}
/-- Observed D=D(Z), the implicit observation rule. -/
def observedD (M : CausalModel Ω) (ω : Ω) : Bool := treatment (M.S ω) (M.Z ω)
/-- Observed Y=Y(D(Z)), the same observation rule; exclusion is built into Y. -/
def observedY (M : CausalModel Ω) (ω : Ω) : ℝ := M.Y (observedD M ω) ω
/-- Elementary conditional mean on an event: integral divided by its probability,
as in Section 2, p. 678.
An ordinary conditional mean exists only on a positive-probability event; every
statement using it as a mean includes that side condition or derives it. -/
def eventMean (μ : Measure Ω) (f : Ω → ℝ) (E : Set Ω) : ℝ :=
  (∫ ω in E, f ω ∂μ) / μ.real E
/-- P_c ≡ Pr[D(1)>D(0)], Section 2, p. 678. -/
def complierProbability (M : CausalModel Ω) : ℝ := M.μ.real (complierEvent M)
/-- EY_z ≡ E[Y|Z=z], Section 2, p. 678. -/
def armMean (M : CausalModel Ω) (z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (armEvent M z)
/-- EY_c(d) ≡ E[Y(d)|D(1)>D(0)], Proposition 1 proof, p. 678. -/
def complierMean (M : CausalModel Ω) (d : Bool) : ℝ :=
  eventMean M.μ (M.Y d) (complierEvent M)
/-- E[Y|D(1)=D(0)], Proposition 1 proof, p. 678, used only with
positive noncomplier mass. -/
def noncomplierMean (M : CausalModel Ω) : ℝ :=
  eventMean M.μ (observedY M) (noncomplierEvent M)
/-- E[Y(1)-Y(0)|D(1)>D(0)], the CACE in the Section 2 display. -/
def cace (M : CausalModel Ω) : ℝ :=
  eventMean M.μ (fun ω => M.Y true ω - M.Y false ω) (complierEvent M)
/-- Bounded potential outcomes “fix Y∈[0,1]”, Section 2, p. 678, with both
potential outcomes bounded. -/
def boundedOutcomes (M : CausalModel Ω) : Prop :=
  ∀ d ω, 0 ≤ M.Y d ω ∧ M.Y d ω ≤ 1
/-- The noncomplier contribution m=E[1_A Y(1)]+E[1_N Y(0)].
This is a moment, not a mean over a possibly null group. -/
def noncomplierContribution (M : CausalModel Ω) : ℝ :=
  (∫ ω in alwaysEvent M, M.Y true ω ∂M.μ) +
  (∫ ω in neverEvent M, M.Y false ω ∂M.μ)
/-- Treatment-assignment cell {D=d,Z=z}, Corollary 1, pp. 678-679. -/
def cellEvent (M : CausalModel Ω) (d z : Bool) : Set Ω :=
  {ω | observedD M ω = d ∧ M.Z ω = z}
/-- Pr[D=d|Z=z], Corollary 1, p. 678. -/
def cellProbability (M : CausalModel Ω) (d z : Bool) : ℝ :=
  M.μ.real (cellEvent M d z) / M.μ.real (armEvent M z)
/-- E[Y|D=d,Z=z], Corollary 1, p. 678; its premise requires positive cells. -/
def cellMean (M : CausalModel Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (cellEvent M d z)
/-- Assignment-conditional product moment E[Y·1{D=d}|Z=z],
which remains defined with empty treatment-assignment cells. -/
def jointOutcomeMoment (M : CausalModel Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (fun ω => if observedD M ω = d then observedY M ω else 0)
    (armEvent M z)

/-- The three possible indices of the monotone binary treatment strata. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem stratum_cases (s : Fin 3) : s = 0 ∨ s = 1 ∨ s = 2 := by omega

/-- All stratum events are measurable; this is needed for ordinary conditioning. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem stratum_measurable (M : CausalModel Ω) (s : Fin 3) :
    MeasurableSet {ω | M.S ω = s} := M.measurableS (measurableSet_singleton s)

/-- The two positive-probability assignment-arm events are measurable. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem arm_measurable (M : CausalModel Ω) (z : Bool) :
    MeasurableSet (armEvent M z) := M.measurableZ (measurableSet_singleton z)

/-- First-stage population identity: D(1)-D(0)=1_C for every allowed type;
its expectation is P_c>0, including full compliance. 
Reference (P028-T10): Section 2 LATE display, p. 678, and Section 1 identification claim, p. 677. -/
theorem first_stage_population (M : CausalModel Ω) :
    (∫ ω, realBit (treatment (M.S ω) true) -
      realBit (treatment (M.S ω) false) ∂M.μ) = complierProbability M ∧
    0 < complierProbability M := by
  have h : (∫ ω, realBit (treatment (M.S ω) true) -
      realBit (treatment (M.S ω) false) ∂M.μ) = complierProbability M := by
    unfold complierProbability complierEvent
    rw [← integral_indicator_one (stratum_measurable M 2)]
    apply integral_congr_ae
    filter_upwards [] with ω
    rcases stratum_cases (M.S ω) with hs | hs | hs <;>
      simp [Set.indicator, treatment, realBit, hs]
  refine ⟨h, lt_of_le_of_ne (measureReal_nonneg) ?_⟩
  intro he
  exact M.nonzeroFirstStage (h.trans he.symm)

/-- Random assignment equates an arm-conditional potential-vector moment with
its population moment. This is the finite/integrable form of Section 2 (i). 
Reference (P028-T10): Section 2 LATE display, p. 678, and Section 1 identification claim, p. 677. -/
theorem random_assignment_moment (M : CausalModel Ω)
    (f : Fin 3 × ℝ × ℝ → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun ω => f (M.S ω, M.Y false ω, M.Y true ω)) M.μ)
    (z : Bool) :
    eventMean M.μ (fun ω => f (M.S ω, M.Y false ω, M.Y true ω)) (armEvent M z) =
      ∫ ω, f (M.S ω, M.Y false ω, M.Y true ω) ∂M.μ := by
  let g : Bool → ℝ := fun b => if b = z then 1 else 0
  have hg : Measurable g := Measurable.of_discrete
  have hvec : Measurable (fun ω => (M.S ω, M.Y false ω, M.Y true ω)) :=
    M.measurableS.prodMk ((M.measurableY false).prodMk (M.measurableY true))
  have hi := M.randomAssignment.integral_fun_comp_mul_comp
    hvec.aemeasurable M.measurableZ.aemeasurable
    hf.aestronglyMeasurable hg.aestronglyMeasurable
  have he : (∫ ω, g (M.Z ω) ∂M.μ) = M.μ.real (armEvent M z) := by
    convert integral_indicator_one (arm_measurable M z) using 1
    congr 1
    funext ω
    simp [g, armEvent, Set.indicator]
    split_ifs <;> simp_all
  have hn : (∫ ω, f (M.S ω, M.Y false ω, M.Y true ω) * g (M.Z ω) ∂M.μ) =
      ∫ ω in armEvent M z, f (M.S ω, M.Y false ω, M.Y true ω) ∂M.μ := by
    rw [← integral_indicator (arm_measurable M z)]
    congr 1
    funext ω
    simp [g, armEvent, Set.indicator]
    split_ifs <;> simp_all
  unfold eventMean
  rw [← hn, hi, he]
  exact mul_div_cancel_right₀ _ (ne_of_gt (M.armPositive z))


/-- A potential-vector expression for the outcome in assignment arm z. -/
def potentialArmOutcome (z : Bool) (v : Fin 3 × ℝ × ℝ) : ℝ :=
  if v.1 = 0 then v.2.2 else if v.1 = 1 then v.2.1 else if z then v.2.2 else v.2.1

/-- The arm-outcome expression is measurable in the joint potential vector. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem potential_arm_measurable (z : Bool) : Measurable (potentialArmOutcome z) := by
  unfold potentialArmOutcome
  apply Measurable.ite (measurable_fst (measurableSet_singleton 0))
  · exact measurable_snd.snd
  · apply Measurable.ite (measurable_fst (measurableSet_singleton 1))
    · exact measurable_snd.fst
    · cases z <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- The arm-outcome expression is integrable because it is a sum of the three
stratum-restricted integrable potential outcomes. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem potential_arm_integrable (M : CausalModel Ω) (z : Bool) :
    Integrable (fun ω => potentialArmOutcome z (M.S ω,M.Y false ω,M.Y true ω)) M.μ := by
  have hC := (M.integrableY z).indicator (stratum_measurable M 2)
  have hA := (M.integrableY true).indicator (stratum_measurable M 0)
  have hN := (M.integrableY false).indicator (stratum_measurable M 1)
  apply ((hC.add hA).add hN).congr
  filter_upwards [] with ω
  rcases stratum_cases (M.S ω) with hs | hs | hs <;> cases z <;>
    simp [potentialArmOutcome, Set.indicator, hs]

/-- Under random assignment, EY_z is the population integral of the fixed-arm
outcome expression. The observation rule is used on the positive arm event. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem arm_mean_population (M : CausalModel Ω) (z : Bool) :
    armMean M z = ∫ ω, potentialArmOutcome z (M.S ω,M.Y false ω,M.Y true ω) ∂M.μ := by
  rw [← random_assignment_moment M (potentialArmOutcome z)
    (potential_arm_measurable z) (potential_arm_integrable M z) z]
  unfold armMean eventMean
  congr 1
  apply setIntegral_congr_fun (arm_measurable M z)
  intro ω hω
  change M.Z ω = z at hω
  rcases stratum_cases (M.S ω) with hs | hs | hs <;> cases z <;>
    simp [observedY, observedD, treatment, potentialArmOutcome, hs, hω]

/-- The exact population mixture equations in the corrected Proposition 1 proof,
with an unnormalized noncomplier contribution. No boundedness is required. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem population_mixture (M : CausalModel Ω) (z : Bool) :
    armMean M z = complierProbability M*complierMean M z + noncomplierContribution M := by
  have hC := (M.integrableY z).indicator (stratum_measurable M 2)
  have hA := (M.integrableY true).indicator (stratum_measurable M 0)
  have hN := (M.integrableY false).indicator (stratum_measurable M 1)
  have he : (fun ω => potentialArmOutcome z (M.S ω,M.Y false ω,M.Y true ω)) =
      (fun ω => (complierEvent M).indicator (M.Y z) ω +
        (alwaysEvent M).indicator (M.Y true) ω + (neverEvent M).indicator (M.Y false) ω) := by
    funext ω
    rcases stratum_cases (M.S ω) with hs | hs | hs <;> cases z <;>
      simp [potentialArmOutcome, complierEvent, alwaysEvent, neverEvent, Set.indicator, hs]
  rw [arm_mean_population, he]
  change (∫ ω, ({ω | M.S ω = 2}.indicator (M.Y z) ω +
    {ω | M.S ω = 0}.indicator (M.Y true) ω) +
    {ω | M.S ω = 1}.indicator (M.Y false) ω ∂M.μ) = _
  have hi := integral_add (hC.add hA) hN
  simp only [Pi.add_apply] at hi
  rw [hi, integral_add hC hA]
  rw [integral_indicator (stratum_measurable M 2), integral_indicator (stratum_measurable M 0),
    integral_indicator (stratum_measurable M 1)]
  have hpne : M.μ.real (complierEvent M) ≠ 0 := ne_of_gt (first_stage_population M).2
  unfold complierMean eventMean noncomplierContribution complierProbability
  rw [mul_div_cancel₀ _ hpne]
  unfold complierEvent alwaysEvent neverEvent
  ring

/-- Noncomplier stratum probabilities add to 1-P_c. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem noncomplier_probability_partition (M : CausalModel Ω) :
    M.μ.real (alwaysEvent M)+M.μ.real (neverEvent M) = 1-complierProbability M := by
  have hs : noncomplierEvent M = alwaysEvent M ∪ neverEvent M := by
    ext ω
    rcases stratum_cases (M.S ω) with h | h | h <;>
      simp [noncomplierEvent, complierEvent, alwaysEvent, neverEvent, h]
  have hd : Disjoint (alwaysEvent M) (neverEvent M) := by
    apply Set.disjoint_left.2
    intro ω hA hN
    change M.S ω = 0 at hA
    change M.S ω = 1 at hN
    omega
  have hp : M.μ.real (noncomplierEvent M) = 1-complierProbability M := by
    exact probReal_compl_eq_one_sub (stratum_measurable M 2)
  rw [hs, measureReal_union hd (stratum_measurable M 1)] at hp
  exact hp

/-- Integral of a unit-interval outcome over any event is between zero and the
probability of that event; the event may have zero probability. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem bounded_set_moment (M : CausalModel Ω) (hb : boundedOutcomes M)
    (d : Bool) (E : Set Ω) :
    0 ≤ (∫ ω in E, M.Y d ω ∂M.μ) ∧ (∫ ω in E, M.Y d ω ∂M.μ) ≤ M.μ.real E := by
  constructor
  · exact integral_nonneg (fun ω => (hb d ω).1)
  · calc
      (∫ ω in E, M.Y d ω ∂M.μ) ≤ ∫ _ in E, (1:ℝ) ∂M.μ :=
        integral_mono (M.integrableY d).restrict (integrable_const 1) (fun ω => (hb d ω).2)
      _ = M.μ.real E := by simp [setIntegral_const]

/-- The bounded noncomplier contribution obeys 0≤m≤1-P_c at every compliance
rate; it is zero at full compliance without defining a null-group mean. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem noncomplier_contribution_bounds (M : CausalModel Ω) (hb : boundedOutcomes M) :
    0 ≤ noncomplierContribution M ∧ noncomplierContribution M ≤ 1-complierProbability M := by
  have ha := bounded_set_moment M hb true (alwaysEvent M)
  have hn := bounded_set_moment M hb false (neverEvent M)
  unfold noncomplierContribution
  have hp := noncomplier_probability_partition M
  constructor <;> linarith

/-- The two complier conditional means are in [0,1], with positive conditioning
probability obtained from nonzero first stage and monotonicity. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem complier_mean_bounds (M : CausalModel Ω) (hb : boundedOutcomes M) (d : Bool) :
    0 ≤ complierMean M d ∧ complierMean M d ≤ 1 := by
  have hp := (first_stage_population M).2
  have h := bounded_set_moment M hb d (complierEvent M)
  unfold complierMean eventMean
  exact ⟨div_nonneg h.1 hp.le, (div_le_one hp).2 h.2⟩

/-- CACE is the treated complier mean minus the control complier mean. 
Reference (P028-T10): Section 2 LATE display, p. 678, and Section 1 identification claim, p. 677. -/
theorem cace_difference (M : CausalModel Ω) :
    cace M = complierMean M true-complierMean M false := by
  unfold cace complierMean eventMean
  rw [integral_sub (M.integrableY true).restrict (M.integrableY false).restrict, sub_div]

/-- The reduced form divided by P_c equals CACE; this proves the population
part of the Section 2 LATE display without any outcome boundedness premise. 
Reference (P028-T10): Section 2 LATE display, p. 678, and Section 1 identification claim, p. 677. -/
theorem late_population_ratio (M : CausalModel Ω) :
    cace M = (armMean M true-armMean M false)/complierProbability M := by
  rw [cace_difference, population_mixture M true, population_mixture M false]
  field_simp [ne_of_gt (first_stage_population M).2]
  <;> ring


/-- Outcome potential multiplied by the indicator of the fixed-arm treatment cell. -/
def potentialCellOutcome (d z : Bool) (v : Fin 3 × ℝ × ℝ) : ℝ :=
  if treatment v.1 z = d then (if d then v.2.2 else v.2.1) else 0

/-- The fixed-arm cell-outcome test is measurable. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem potential_cell_measurable (d z : Bool) : Measurable (potentialCellOutcome d z) := by
  have hs : MeasurableSet {v : Fin 3 × ℝ × ℝ | treatment v.1 z = d} :=
    ((Measurable.of_discrete : Measurable (fun s : Fin 3 => treatment s z)).comp measurable_fst)
      (measurableSet_singleton d)
  unfold potentialCellOutcome
  apply Measurable.ite hs
  · cases d <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  · exact measurable_const

/-- Fixed-arm cell-outcome moments are integrable even when a cell is null. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem potential_cell_integrable (M : CausalModel Ω) (d z : Bool) :
    Integrable (fun ω => potentialCellOutcome d z (M.S ω,M.Y false ω,M.Y true ω)) M.μ := by
  have hs : MeasurableSet {ω | treatment (M.S ω) z = d} :=
    ((Measurable.of_discrete : Measurable (fun s : Fin 3 => treatment s z)).comp M.measurableS)
      (measurableSet_singleton d)
  apply ((M.integrableY d).indicator hs).congr
  filter_upwards [] with ω
  cases d <;> simp [potentialCellOutcome, Set.indicator]

/-- Random assignment identifies the assignment-conditional joint outcome moment
with a stratum-restricted population outcome moment. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem joint_outcome_population (M : CausalModel Ω) (d z : Bool) :
    jointOutcomeMoment M d z =
      ∫ ω, potentialCellOutcome d z (M.S ω,M.Y false ω,M.Y true ω) ∂M.μ := by
  rw [← random_assignment_moment M (potentialCellOutcome d z)
    (potential_cell_measurable d z) (potential_cell_integrable M d z) z]
  unfold jointOutcomeMoment eventMean
  congr 1
  apply setIntegral_congr_fun (arm_measurable M z)
  intro ω hω
  change M.Z ω = z at hω
  rcases stratum_cases (M.S ω) with hs | hs | hs <;> cases d <;> cases z <;>
    simp [potentialCellOutcome, observedD, observedY, treatment, hs, hω]

/-- The two pure noncomplier product moments equal their unnormalized population
stratum outcome moments. This has no positive-cell hypothesis. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem pure_cell_product_moments (M : CausalModel Ω) :
    jointOutcomeMoment M true false = (∫ ω in alwaysEvent M, M.Y true ω ∂M.μ) ∧
    jointOutcomeMoment M false true = (∫ ω in neverEvent M, M.Y false ω ∂M.μ) := by
  constructor
  · have hsA : MeasurableSet (alwaysEvent M) := stratum_measurable M 0
    rw [joint_outcome_population, ← integral_indicator hsA]
    apply integral_congr_ae
    filter_upwards [] with ω
    rcases stratum_cases (M.S ω) with hs | hs | hs <;>
      simp [potentialCellOutcome, treatment, alwaysEvent, Set.indicator, hs]
  · have hsN : MeasurableSet (neverEvent M) := stratum_measurable M 1
    rw [joint_outcome_population, ← integral_indicator hsN]
    apply integral_congr_ae
    filter_upwards [] with ω
    rcases stratum_cases (M.S ω) with hs | hs | hs <;>
      simp [potentialCellOutcome, treatment, neverEvent, Set.indicator, hs]

/-- The two treatment-cell joint outcome moments add to EY_z in each arm. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem arm_joint_moment_partition (M : CausalModel Ω) (z : Bool) :
    jointOutcomeMoment M false z+jointOutcomeMoment M true z = armMean M z := by
  rw [joint_outcome_population, joint_outcome_population, arm_mean_population,
    ← integral_add (potential_cell_integrable M false z) (potential_cell_integrable M true z)]
  apply integral_congr_ae
  filter_upwards [] with ω
  rcases stratum_cases (M.S ω) with hs | hs | hs <;> cases z <;>
    simp [potentialCellOutcome, potentialArmOutcome, treatment, hs]

/-- m equals the two observable product moments (the optional empty-cell extension
of Corollary 1). 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem noncomplier_contribution_observable (M : CausalModel Ω) :
    noncomplierContribution M = jointOutcomeMoment M true false+jointOutcomeMoment M false true := by
  rw [(pure_cell_product_moments M).1, (pure_cell_product_moments M).2]
  rfl

/-- The probability of the noncomplier event is 1-P_c, including P_c=1. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem noncomplier_event_probability (M : CausalModel Ω) :
    M.μ.real (noncomplierEvent M) = 1-complierProbability M :=
  probReal_compl_eq_one_sub (stratum_measurable M 2)

/-- The unnormalized observed-outcome moment on noncompliers is m. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem noncomplier_outcome_moment (M : CausalModel Ω) :
    (∫ ω in noncomplierEvent M, observedY M ω ∂M.μ) = noncomplierContribution M := by
  have hs : MeasurableSet (noncomplierEvent M) := (stratum_measurable M 2).compl
  rw [← integral_indicator hs]
  have he : (noncomplierEvent M).indicator (observedY M) =
      fun ω => (alwaysEvent M).indicator (M.Y true) ω +
        (neverEvent M).indicator (M.Y false) ω := by
    funext ω
    rcases stratum_cases (M.S ω) with hs | hs | hs <;> cases hz : M.Z ω <;>
      simp [noncomplierEvent, complierEvent, alwaysEvent, neverEvent,
        observedY, observedD, treatment, Set.indicator, hs, hz]
  rw [he]
  change (∫ ω, {ω | M.S ω = 0}.indicator (M.Y true) ω +
    {ω | M.S ω = 1}.indicator (M.Y false) ω ∂M.μ) = _
  rw [integral_add ((M.integrableY true).indicator (stratum_measurable M 0))
      ((M.integrableY false).indicator (stratum_measurable M 1)),
    integral_indicator (stratum_measurable M 0), integral_indicator (stratum_measurable M 1)]
  rfl

/-- The noncomplier-mean formula on a positive event; no value at a null event
is interpreted as an ordinary conditional mean. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem noncomplier_mean_positive_formula (M : CausalModel Ω) (hp : complierProbability M < 1) :
    0 < M.μ.real (noncomplierEvent M) ∧
    noncomplierMean M = noncomplierContribution M/(1-complierProbability M) := by
  refine ⟨by rw [noncomplier_event_probability]; linarith,?_⟩
  unfold noncomplierMean eventMean
  rw [noncomplier_outcome_moment, noncomplier_event_probability]

/-- Probability implies P_c≤1; first stage supplies strict positivity separately. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem complier_probability_le_one (M : CausalModel Ω) : complierProbability M ≤ 1 := by
  have h := measureReal_add_measureReal_compl (μ := M.μ) (stratum_measurable M 2)
  have hn : 0 ≤ M.μ.real (complierEvent M)ᶜ := measureReal_nonneg
  simp only [probReal_univ] at h
  unfold complierProbability complierEvent at *
  linarith

/-- The corrected full-compliance branch gives m=0 and c_d=EY_d directly. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem full_compliance_population (M : CausalModel Ω) (hb : boundedOutcomes M)
    (hp : complierProbability M = 1) : noncomplierContribution M = 0 ∧
    complierMean M false = armMean M false ∧ complierMean M true = armMean M true := by
  have h := noncomplier_contribution_bounds M hb
  have hm : noncomplierContribution M = 0 := by rw [hp] at h; linarith
  have h0 := population_mixture M false
  have h1 := population_mixture M true
  rw [hp,hm] at h0 h1
  exact ⟨hm,by linarith,by linarith⟩


/-- The implicit observed treatment is measurable, since the treatment map on
stratum and assignment is a function on a finite measurable space. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem observed_d_measurable (M : CausalModel Ω) : Measurable (observedD M) :=
  (Measurable.of_discrete : Measurable (fun v : Fin 3 × Bool => treatment v.1 v.2)).comp
    (M.measurableS.prodMk M.measurableZ)

/-- All treatment-assignment cells are measurable. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem cell_measurable (M : CausalModel Ω) (d z : Bool) : MeasurableSet (cellEvent M d z) :=
  ((observed_d_measurable M) (measurableSet_singleton d)).inter (arm_measurable M z)

/-- A product moment is the unnormalized cell outcome integral divided only by
the positive assignment-arm probability. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem joint_moment_cell_integral (M : CausalModel Ω) (d z : Bool) :
    jointOutcomeMoment M d z = (∫ ω in cellEvent M d z, observedY M ω ∂M.μ)/M.μ.real (armEvent M z) := by
  unfold jointOutcomeMoment eventMean
  congr 1
  rw [← integral_indicator (arm_measurable M z), ← integral_indicator (cell_measurable M d z)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hz : M.Z ω = z <;> by_cases hd : observedD M ω = d <;>
    simp [Set.indicator, armEvent, cellEvent, hz, hd]

/-- Cell probability is an arm-conditional binary-indicator expectation. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem cell_probability_as_mean (M : CausalModel Ω) (d z : Bool) :
    cellProbability M d z = eventMean M.μ (fun ω => if observedD M ω = d then 1 else 0) (armEvent M z) := by
  unfold cellProbability eventMean
  congr 1
  rw [← integral_indicator_one (cell_measurable M d z), ← integral_indicator (arm_measurable M z)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hz : M.Z ω = z <;> by_cases hd : observedD M ω = d <;>
    simp [Set.indicator, armEvent, cellEvent, hz, hd]

/-- Random assignment identifies treatment-cell probabilities with the
corresponding potential-treatment probabilities. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem cell_probability_population (M : CausalModel Ω) (d z : Bool) :
    cellProbability M d z = M.μ.real {ω | treatment (M.S ω) z = d} := by
  let f : Fin 3 × ℝ × ℝ → ℝ := fun v => if treatment v.1 z = d then 1 else 0
  have hf : Measurable f :=
    (Measurable.of_discrete : Measurable (fun s : Fin 3 => if treatment s z = d then (1:ℝ) else 0)).comp measurable_fst
  have hvec : Measurable (fun ω => (M.S ω,M.Y false ω,M.Y true ω)) :=
    M.measurableS.prodMk ((M.measurableY false).prodMk (M.measurableY true))
  have hfi : Integrable (fun ω => f (M.S ω,M.Y false ω,M.Y true ω)) M.μ :=
    Integrable.of_mem_Icc 0 1 (hf.comp hvec).aemeasurable (by
      filter_upwards [] with ω
      dsimp [f]
      split_ifs <;> norm_num)
  rw [cell_probability_as_mean]
  calc
    eventMean M.μ (fun ω => if observedD M ω = d then 1 else 0) (armEvent M z) =
      eventMean M.μ (fun ω => f (M.S ω,M.Y false ω,M.Y true ω)) (armEvent M z) := by
      unfold eventMean
      congr 1
      apply setIntegral_congr_fun (arm_measurable M z)
      intro ω hω
      change M.Z ω = z at hω
      simp [observedD, f, hω]
    _ = ∫ ω, f (M.S ω,M.Y false ω,M.Y true ω) ∂M.μ :=
      random_assignment_moment M f hf hfi z
    _ = M.μ.real {ω | treatment (M.S ω) z = d} := by
      have hs : MeasurableSet {ω | treatment (M.S ω) z = d} :=
        ((Measurable.of_discrete : Measurable (fun s : Fin 3 => treatment s z)).comp M.measurableS)
          (measurableSet_singleton d)
      rw [← integral_indicator_one hs]
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [f, Set.indicator]

/-- The two pure-cell treatment probabilities are the always- and never-taker
masses, and sum to 1-P_c. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem pure_cell_probabilities (M : CausalModel Ω) :
    cellProbability M true false = M.μ.real (alwaysEvent M) ∧
    cellProbability M false true = M.μ.real (neverEvent M) ∧
    cellProbability M true false+cellProbability M false true = 1-complierProbability M := by
  have ha : cellProbability M true false = M.μ.real (alwaysEvent M) := by
    rw [cell_probability_population]
    congr 1
    ext ω
    rcases stratum_cases (M.S ω) with hs | hs | hs <;> simp [treatment, alwaysEvent, hs]
  have hn : cellProbability M false true = M.μ.real (neverEvent M) := by
    rw [cell_probability_population]
    congr 1
    ext ω
    rcases stratum_cases (M.S ω) with hs | hs | hs <;> simp [treatment, neverEvent, hs]
  refine ⟨ha,hn,?_⟩
  rw [ha,hn]
  exact noncomplier_probability_partition M

/-- On a positive cell, probability times its ordinary conditional mean equals
the joint outcome moment. This explicitly avoids a mean on a null cell. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem weighted_cell_mean (M : CausalModel Ω) (d z : Bool)
    (hc : 0 < M.μ.real (cellEvent M d z)) :
    cellProbability M d z*cellMean M d z = jointOutcomeMoment M d z := by
  rw [joint_moment_cell_integral]
  unfold cellProbability cellMean eventMean
  field_simp [ne_of_gt hc, ne_of_gt (M.armPositive z)]
  <;> ring


/-- Each arm's two treatment probabilities add to one. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem cell_probability_partition (M : CausalModel Ω) (z : Bool) :
    cellProbability M false z+cellProbability M true z = 1 := by
  have hs : MeasurableSet {ω | treatment (M.S ω) z = false} :=
    ((Measurable.of_discrete : Measurable (fun s : Fin 3 => treatment s z)).comp M.measurableS)
      (measurableSet_singleton false)
  have he : {ω | treatment (M.S ω) z = true} = {ω | treatment (M.S ω) z = false}ᶜ := by
    ext ω
    cases ht : treatment (M.S ω) z <;> simp [ht]
  rw [cell_probability_population,cell_probability_population,he,probReal_compl_eq_one_sub hs]
  ring

/-- Positive conditional treatment probability implies positive joint cell mass,
since both assignment arms have positive probability. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem positive_cell_mass (M : CausalModel Ω) (d z : Bool)
    (hp : 0 < cellProbability M d z) : 0 < M.μ.real (cellEvent M d z) := by
  have he : M.μ.real (armEvent M z)*cellProbability M d z = M.μ.real (cellEvent M d z) := by
    unfold cellProbability
    exact mul_div_cancel₀ _ (ne_of_gt (M.armPositive z))
  have h := mul_pos (M.armPositive z) hp
  change 0 < M.μ.real (armEvent M z)*cellProbability M d z at h
  rwa [he] at h

/-- Two-sided noncompliance plus the standing nonzero first stage makes all four
ordinary cell means well-defined, as required by Corollary 1. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem two_sided_cells_positive (M : CausalModel Ω)
    (hq : 0 < cellProbability M true false) (hr : 0 < cellProbability M false true) :
    ∀ d z, 0 < M.μ.real (cellEvent M d z) := by
  have hs := (pure_cell_probabilities M).2.2
  have hp := (first_stage_population M).2
  have h0 := cell_probability_partition M false
  have h1 := cell_probability_partition M true
  intro d z
  apply positive_cell_mass
  cases d <;> cases z <;> linarith

/-- The exact observed first-stage identity, Section 2: E[D|Z=1]-E[D|Z=0]=P_c. 
Reference (P028-T10): Section 2 LATE display, p. 678, and Section 1 identification claim, p. 677. -/
theorem observed_first_stage (M : CausalModel Ω) :
    eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M true) -
      eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M false) = complierProbability M := by
  have he : ∀ z, eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M z) =
      cellProbability M true z := by
    intro z
    rw [cell_probability_as_mean]
    unfold realBit
    rfl
  have h0 := cell_probability_partition M true
  have hs := (pure_cell_probabilities M).2.2
  rw [he,he]
  linarith

/-- T8 finite algebra: every value in the printed treated interval supplies an
actual feasible pair of complier means and a contribution m in [0,1-p]. This
is the numerical certificate used by the attaining-population construction. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem sharpness_moment_certificate (p e0 e1 x1 : ℝ) (hp : 0 < p)
    (hx : lowerTreated p e0 e1 ≤ x1 ∧ x1 ≤ upperTreated p e0 e1) :
    let x0 := x1-effect p e0 e1
    let m := e1-p*x1
    0 ≤ x0 ∧ x0 ≤ 1 ∧ 0 ≤ x1 ∧ x1 ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1-p ∧
    e0 = p*x0+m ∧ e1 = p*x1+m := by
  have h := (corrected_interval_system p e0 e1 (x1-effect p e0 e1) x1 hp).2
    ⟨rfl,hx.1,hx.2⟩
  rcases h with ⟨he,h0,h01,h1,h11,hm,hm1⟩
  dsimp
  exact ⟨h0,h01,h1,h11,hm,hm1,by linarith,by ring⟩

/-- T8 finite algebra: the compatibility restriction |e1-e0|≤p is
necessary and sufficient for feasible bounded mixture moments. It is not a
replacement for the separate theorem asserting existence of a probability model. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem compatible_mixture_moments (p e0 e1 : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    (0 ≤ e0 ∧ e0 ≤ 1 ∧ 0 ≤ e1 ∧ e1 ≤ 1 ∧ |e1-e0| ≤ p) ↔
    ∃ c0 c1 m : ℝ, 0 ≤ c0 ∧ c0 ≤ 1 ∧ 0 ≤ c1 ∧ c1 ≤ 1 ∧
      0 ≤ m ∧ m ≤ 1-p ∧ e0 = p*c0+m ∧ e1 = p*c1+m := by
  constructor
  · rintro ⟨h0,h01,h1,h11,he⟩
    rw [abs_le] at he
    let m := max (max 0 (e0-p)) (e1-p)
    have hm : 0 ≤ m := le_trans (le_max_left 0 (e0-p)) (le_max_left _ _)
    have hm0 : m ≤ e0 := max_le (max_le h0 (by linarith [hp.1])) (by linarith [he.2])
    have hm1 : m ≤ e1 := max_le (max_le h1 (by linarith [he.1])) (by linarith [hp.1])
    have hmp : m ≤ 1-p := max_le
      (max_le (by linarith [hp.2]) (by linarith)) (by linarith)
    have hmc0 : e0-p ≤ m := le_trans (le_max_right 0 (e0-p)) (le_max_left _ _)
    have hmc1 : e1-p ≤ m := le_max_right _ _
    refine ⟨(e0-m)/p,(e1-m)/p,m,div_nonneg (by linarith) hp.1.le,
      (div_le_one hp.1).2 (by linarith),div_nonneg (by linarith) hp.1.le,
      (div_le_one hp.1).2 (by linarith),hm,hmp,?_,?_⟩
    · rw [mul_div_cancel₀ _ (ne_of_gt hp.1)]; ring
    · rw [mul_div_cancel₀ _ (ne_of_gt hp.1)]; ring
  · rintro ⟨c0,c1,m,h0,h01,h1,h11,hm,hmp,he0,he1⟩
    refine ⟨by nlinarith [hp.1],by nlinarith [hp.1],
      by nlinarith [hp.1],by nlinarith [hp.1],?_⟩
    rw [abs_le]
    constructor <;> nlinarith [hp.1]

/-- T9 finite algebra: substituting the identified noncomplier contribution
q·a+r·n in Eqs. (1)-(2) gives both expressions of Corollary 1. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem corollary_moment_identity (p q r e0 e1 c0 c1 a n : ℝ) (hp : 0 < p)
    (h0 : e0 = p*c0+q*a+r*n) (h1 : e1 = p*c1+q*a+r*n) :
    c0 = (e0-q*a-r*n)/p ∧ c1 = c0+(e1-e0)/p ∧
    c1 = (e1-q*a-r*n)/p := by
  have hc0 : c0 = (e0-q*a-r*n)/p := by
    apply (eq_div_iff (ne_of_gt hp)).2; linarith
  have hc1 : c1 = (e1-q*a-r*n)/p := by
    apply (eq_div_iff (ne_of_gt hp)).2; linarith
  refine ⟨hc0,?_,hc1⟩
  have ht : p*((e1-e0)/p) = e1-e0 := mul_div_cancel₀ _ (ne_of_gt hp)
  nlinarith

/-- T2(v) finite lemma: a full outcome moment lies between its recorded moment
and the recorded moment plus missing-cell probability. Differences of two such
moments give the sensitivity bounds after division by P_c>0. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem missing_moment_difference_bounds
    (p c full0 full1 recorded0 recorded1 missing0 missing1 : ℝ) (hp : 0 < p)
    (he : p*c = full0-full1)
    (h0 : recorded0 ≤ full0 ∧ full0 ≤ recorded0+missing0)
    (h1 : recorded1 ≤ full1 ∧ full1 ≤ recorded1+missing1) :
    (recorded0-recorded1-missing1)/p ≤ c ∧
    c ≤ (recorded0+missing0-recorded1)/p := by
  rw [div_le_iff₀ hp, le_div_iff₀ hp]
  constructor <;> linarith

/-- T7(F6): the printed intervals in the two-atom full-compliance witness are
[0,0] and [1,1]; the witness refutes only the unqualified proof expressions. 
Reference (P028-T7): Proposition 1 proof, p. 678. -/
theorem full_compliance_witness_intervals :
    lowerControl 1 0 1 = 0 ∧ upperControl 1 0 1 = 0 ∧
    lowerTreated 1 0 1 = 1 ∧ upperTreated 1 0 1 = 1 := by
  norm_num [lowerControl, upperControl, lowerTreated, upperTreated, effect]


/-- The independent fair assignment coin used in the attaining models. -/
def fairUnitProbability : Set.Icc (0:ℝ) 1 := ⟨1/2,by constructor <;> norm_num⟩
/-- Genuine four-atom probability measure: complier indicator with probability p,
times an independent fair assignment coin. The never-taker mass may be zero. -/
def attainingMeasure (p : Set.Icc (0:ℝ) 1) : Measure (Bool × Bool) :=
  (bernoulliMeasure true false p).prod (bernoulliMeasure true false fairUnitProbability)
instance attainingMeasure_probability (p : Set.Icc (0:ℝ) 1) :
    IsProbabilityMeasure (attainingMeasure p) := by unfold attainingMeasure; infer_instance

/-- Exact weighted-sum formula for the four-atom attaining measure. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem attaining_integral (p : Set.Icc (0:ℝ) 1) (f : Bool × Bool → ℝ) :
    (∫ ω, f ω ∂attainingMeasure p) =
      (p:ℝ)*((1/2)*f (true,true)+(1/2)*f (true,false)) +
      (1-(p:ℝ))*((1/2)*f (false,true)+(1/2)*f (false,false)) := by
  unfold attainingMeasure
  rw [integral_prod f Integrable.of_finite, integral_bernoulliMeasure]
  simp only [integral_bernoulliMeasure, smul_eq_mul, fairUnitProbability]
  ring

/-- Both assignment arms have probability 1/2 in the attaining model. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem attaining_arm_probability (p : Set.Icc (0:ℝ) 1) (z : Bool) :
    (attainingMeasure p).real {ω | ω.2 = z} = 1/2 := by
  rw [← integral_indicator_one (MeasurableSet.of_discrete), attaining_integral]
  cases z <;> simp [Set.indicator] <;> ring

/-- Attaining population: compliers have constant (c0,c1),
never-takers have both potential outcomes n, and Z is an independent fair coin.
Sharpness construction for Proposition 1. -/
def attainingModel (p : Set.Icc (0:ℝ) 1) (hp : 0 < (p:ℝ)) (c0 c1 n : ℝ) :
    CausalModel (Bool × Bool) where
  μ := attainingMeasure p
  probability := inferInstance
  S := fun ω => if ω.1 then 2 else 1
  Y := fun d ω => if ω.1 then (if d then c1 else c0) else n
  Z := fun ω => ω.2
  measurableS := Measurable.of_discrete
  measurableY := fun _ => Measurable.of_discrete
  integrableY := fun _ => Integrable.of_finite
  measurableZ := measurable_snd
  randomAssignment := indepFun_prod
    (X := fun b : Bool => ((if b then 2 else 1 : Fin 3),
      (if b then c0 else n),(if b then c1 else n)))
    (Y := id) Measurable.of_discrete measurable_id
  armPositive := fun z => by rw [attaining_arm_probability]; norm_num
  nonzeroFirstStage := by
    rw [attaining_integral]
    simp only [treatment, realBit]
    norm_num
    have he : (p:ℝ)*(1/2+1/2) + (1-(p:ℝ))*(0+0) = (p:ℝ) := by ring
    exact ne_of_gt hp

/-- The attaining model has bounded potential outcomes whenever its three
constant outcomes lie in [0,1]; the model's measure is never identically zero. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem attaining_model_bounded (p : Set.Icc (0:ℝ) 1) (hp : 0 < (p:ℝ))
    (c0 c1 n : ℝ) (h0 : 0 ≤ c0 ∧ c0 ≤ 1) (h1 : 0 ≤ c1 ∧ c1 ≤ 1)
    (hn : 0 ≤ n ∧ n ≤ 1) : boundedOutcomes (attainingModel p hp c0 c1 n) := by
  intro d ω
  cases hd : d <;> cases hb : ω.1 <;>
    simp [attainingModel, hd, hb] <;> assumption

/-- Exact population moments of the attaining model, valid also at p=1. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem attaining_model_moments (p : Set.Icc (0:ℝ) 1) (hp : 0 < (p:ℝ)) (c0 c1 n : ℝ) :
    complierProbability (attainingModel p hp c0 c1 n) = (p:ℝ) ∧
    armMean (attainingModel p hp c0 c1 n) false = (p:ℝ)*c0+(1-(p:ℝ))*n ∧
    armMean (attainingModel p hp c0 c1 n) true = (p:ℝ)*c1+(1-(p:ℝ))*n ∧
    complierMean (attainingModel p hp c0 c1 n) false = c0 ∧
    complierMean (attainingModel p hp c0 c1 n) true = c1 := by
  have hc : complierProbability (attainingModel p hp c0 c1 n) = (p:ℝ) := by
    unfold complierProbability complierEvent
    simp only [attainingModel]
    rw [← integral_indicator_one (MeasurableSet.of_discrete), attaining_integral]
    simp [Set.indicator]
    <;> ring
  refine ⟨hc,?_,?_,?_,?_⟩
  · rw [arm_mean_population]
    simp only [attainingModel]
    rw [attaining_integral]
    simp [potentialArmOutcome]
    <;> ring
  · rw [arm_mean_population]
    simp only [attainingModel]
    rw [attaining_integral]
    simp [potentialArmOutcome]
    <;> ring
  · unfold complierMean eventMean
    change (∫ ω in complierEvent (attainingModel p hp c0 c1 n),
      (attainingModel p hp c0 c1 n).Y false ω ∂attainingMeasure p) /
      complierProbability (attainingModel p hp c0 c1 n) = c0
    rw [hc, ← integral_indicator (MeasurableSet.of_discrete), attaining_integral]
    simp [Set.indicator, complierEvent, attainingModel]
    field_simp [ne_of_gt hp]
    <;> ring
  · unfold complierMean eventMean
    change (∫ ω in complierEvent (attainingModel p hp c0 c1 n),
      (attainingModel p hp c0 c1 n).Y true ω ∂attainingMeasure p) /
      complierProbability (attainingModel p hp c0 c1 n) = c1
    rw [hc, ← integral_indicator (MeasurableSet.of_discrete), attaining_integral]
    simp [Set.indicator, complierEvent, attainingModel]
    field_simp [ne_of_gt hp]
    <;> ring


/-- Every feasible mixture certificate is realized by an actual probability
model. The noncomplier outcome is chosen only when 1-p>0; at p=1 it is 0. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem realize_mixture_moments (p e0 e1 c0 c1 m : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (h0 : 0 ≤ c0 ∧ c0 ≤ 1) (h1 : 0 ≤ c1 ∧ c1 ≤ 1)
    (hm : 0 ≤ m ∧ m ≤ 1-p) (he0 : e0 = p*c0+m) (he1 : e1 = p*c1+m) :
    ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧
      complierProbability M = p ∧ armMean M false = e0 ∧ armMean M true = e1 ∧
      complierMean M false = c0 ∧ complierMean M true = c1 := by
  obtain ⟨n,hn,hen⟩ : ∃ n : ℝ, (0 ≤ n ∧ n ≤ 1) ∧ (1-p)*n = m := by
    by_cases hlt : p < 1
    · have hd : 0 < 1-p := by linarith
      exact ⟨m/(1-p),⟨div_nonneg hm.1 hd.le,(div_le_one hd).2 hm.2⟩,
        mul_div_cancel₀ _ (ne_of_gt hd)⟩
    · have hp1 : p = 1 := le_antisymm hp.2 (le_of_not_gt hlt)
      have hm0 : m = 0 := by rw [hp1] at hm; linarith
      exact ⟨0,by norm_num,by rw [hm0]; ring⟩
  let u : Set.Icc (0:ℝ) 1 := ⟨p,hp.1.le,hp.2⟩
  let M := attainingModel u hp.1 c0 c1 n
  have h := attaining_model_moments u hp.1 c0 c1 n
  refine ⟨M,attaining_model_bounded u hp.1 c0 c1 n h0 h1 hn,h.1,?_,?_,h.2.2.2.1,h.2.2.2.2⟩
  · change armMean (attainingModel u hp.1 c0 c1 n) false = e0
    rw [h.2.1]
    change p*c0+(1-p)*n = e0
    rw [hen]
    exact he0.symm
  · change armMean (attainingModel u hp.1 c0 c1 n) true = e1
    rw [h.2.2.1]
    change p*c1+(1-p)*n = e1
    rw [hen]
    exact he1.symm

/-- T6 finite algebra: the mixture equations with 0≤m≤1-p imply both printed
intervals for every p>0, including p=1, without dividing by 1-p. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem bounds_from_mixture_moments (p e0 e1 c0 c1 m : ℝ) (hp : 0 < p)
    (h0 : e0 = p*c0+m) (h1 : e1 = p*c1+m)
    (hc0 : 0 ≤ c0 ∧ c0 ≤ 1) (hc1 : 0 ≤ c1 ∧ c1 ≤ 1)
    (hm : 0 ≤ m ∧ m ≤ 1-p) :
    c1 = c0+effect p e0 e1 ∧
    lowerControl p e0 e1 ≤ c0 ∧ c0 ≤ upperControl p e0 e1 ∧
    lowerTreated p e0 e1 ≤ c1 ∧ c1 ≤ upperTreated p e0 e1 := by
  have hs : correctedSystem p e0 e1 c0 c1 :=
    ⟨by linarith, hc0.1, hc0.2, hc1.1, hc1.2, by linarith [hm.1], by linarith [hm.2]⟩
  rcases (corrected_interval_system p e0 e1 c0 c1 hp).1 hs with ⟨he,hl,hu⟩
  rcases endpoint_translation p e0 e1 hp with ⟨hel,heu⟩
  exact ⟨by linarith, by linarith, by linarith, hl, hu⟩

/-- T6(i)-(v): the corrected proof works at every 0<P_c≤1 using the noncomplier
contribution. It supplies the ordinary noncomplier mean only for P_c<1, gives
c_d=EY_d at full compliance, and gives the product-moment extension of Corollary 1
without any positive-cell premise. 
Reference (P028-T6): Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679. -/
theorem boundary_proof_repair (M : CausalModel Ω) (hb : boundedOutcomes M) :
    0 < complierProbability M ∧ complierProbability M ≤ 1 ∧
    (0 ≤ noncomplierContribution M ∧ noncomplierContribution M ≤ 1-complierProbability M) ∧
    (∀ z, armMean M z = complierProbability M*complierMean M z + noncomplierContribution M) ∧
    noncomplierContribution M = jointOutcomeMoment M true false + jointOutcomeMoment M false true ∧
    (complierProbability M < 1 →
      M.μ.real (noncomplierEvent M) = 1-complierProbability M ∧
      0 < M.μ.real (noncomplierEvent M) ∧
      noncomplierContribution M = (1-complierProbability M)*noncomplierMean M ∧
      0 ≤ noncomplierMean M ∧ noncomplierMean M ≤ 1) ∧
    (complierProbability M = 1 → noncomplierContribution M = 0 ∧
      complierMean M false = armMean M false ∧ complierMean M true = armMean M true) ∧
    (∀ z, complierMean M z = (armMean M z-noncomplierContribution M)/complierProbability M) := by
  have hp := (first_stage_population M).2
  have hm := noncomplier_contribution_bounds M hb
  refine ⟨hp,complier_probability_le_one M,hm,population_mixture M,
    noncomplier_contribution_observable M,?_,full_compliance_population M hb,?_⟩
  · intro hlt
    have hn := noncomplier_mean_positive_formula M hlt
    have hd : 0 < 1-complierProbability M := by linarith
    refine ⟨noncomplier_event_probability M,hn.1,?_,?_,?_⟩
    · rw [hn.2]; exact (mul_div_cancel₀ _ (ne_of_gt hd)).symm
    · rw [hn.2]; exact div_nonneg hm.1 hd.le
    · rw [hn.2]; exact (div_le_one hd).2 hm.2
  · intro z
    apply (eq_div_iff (ne_of_gt hp)).2
    have h := population_mixture M z
    linarith

/-- T8, validity and translated intervals: Proposition 1 under the full standing
assumptions. Its sharpness is stated separately, so validity cannot be confused
with attainment of every bound. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem proposition1_valid (M : CausalModel Ω) (hb : boundedOutcomes M) :
    lowerControl (complierProbability M) (armMean M false) (armMean M true) ≤ complierMean M false ∧
    complierMean M false ≤ upperControl (complierProbability M) (armMean M false) (armMean M true) ∧
    lowerTreated (complierProbability M) (armMean M false) (armMean M true) ≤ complierMean M true ∧
    complierMean M true ≤ upperTreated (complierProbability M) (armMean M false) (armMean M true) ∧
    complierMean M true = complierMean M false + effect (complierProbability M) (armMean M false) (armMean M true) := by
  have h := bounds_from_mixture_moments
    (complierProbability M) (armMean M false) (armMean M true)
    (complierMean M false) (complierMean M true) (noncomplierContribution M)
    (first_stage_population M).2 (population_mixture M false) (population_mixture M true)
    (complier_mean_bounds M hb false) (complier_mean_bounds M hb true)
    (noncomplier_contribution_bounds M hb)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h.1⟩

/-- T8, sharpness (“when only EY₁,EY₀,P_c are known”, Proposition 1, p. 678):
for every admissible triple and every treated mean in the displayed interval,
a genuine randomized bounded-outcome probability model attains that mean and the
implied control mean. The explicit four-atom sample space is sufficient for
attainment; validity is universal over arbitrary probability spaces. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem proposition1_sharp (p e0 e1 : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (he0 : 0 ≤ e0 ∧ e0 ≤ 1) (he1 : 0 ≤ e1 ∧ e1 ≤ 1) (hcompat : |e1-e0| ≤ p)
    (x1 : ℝ) (hx : lowerTreated p e0 e1 ≤ x1 ∧ x1 ≤ upperTreated p e0 e1) :
    ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧
      complierProbability M = p ∧ armMean M false = e0 ∧ armMean M true = e1 ∧
      complierMean M true = x1 ∧ complierMean M false = x1-effect p e0 e1 := by
  have h := sharpness_moment_certificate p e0 e1 x1 hp.1 hx
  dsimp at h
  rcases h with ⟨h0,h01,h1,h11,hm,hm1,he0,he1⟩
  obtain ⟨M,hb,hpc,he0',he1',hc0,hc1⟩ :=
    realize_mixture_moments p e0 e1 (x1-effect p e0 e1) x1 (e1-p*x1)
      hp ⟨h0,h01⟩ ⟨h1,h11⟩ ⟨hm,hm1⟩ he0 he1
  exact ⟨M,hb,hpc,he0',he1',hc1,hc0⟩

/-- T8, admissible-input characterization: exactly the triples in [0,1]²,
0<p≤1 with |e1-e0|≤p arise from bounded randomized monotone models. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem proposition1_compatible_triples (p e0 e1 : ℝ) :
    (0 < p ∧ p ≤ 1 ∧ 0 ≤ e0 ∧ e0 ≤ 1 ∧ 0 ≤ e1 ∧ e1 ≤ 1 ∧ |e1-e0| ≤ p) ↔
    ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧
      complierProbability M = p ∧ armMean M false = e0 ∧ armMean M true = e1 := by
  constructor
  · rintro ⟨hp,hp1,h0,h01,h1,h11,he⟩
    obtain ⟨c0,c1,m,hc0,hc01,hc1,hc11,hm,hm1,he0,he1⟩ :=
      (compatible_mixture_moments p e0 e1 ⟨hp,hp1⟩).1 ⟨h0,h01,h1,h11,he⟩
    obtain ⟨M,hb,hpc,hey0,hey1,_⟩ := realize_mixture_moments p e0 e1 c0 c1 m
      ⟨hp,hp1⟩ ⟨hc0,hc01⟩ ⟨hc1,hc11⟩ ⟨hm,hm1⟩ he0 he1
    exact ⟨M,hb,hpc,hey0,hey1⟩
  · rintro ⟨M,hb,hpc,hey0,hey1⟩
    have h := (compatible_mixture_moments (complierProbability M) (armMean M false)
      (armMean M true) ⟨(first_stage_population M).2,complier_probability_le_one M⟩).2
      ⟨complierMean M false,complierMean M true,noncomplierContribution M,
        (complier_mean_bounds M hb false).1,(complier_mean_bounds M hb false).2,
        (complier_mean_bounds M hb true).1,(complier_mean_bounds M hb true).2,
        (noncomplier_contribution_bounds M hb).1,(noncomplier_contribution_bounds M hb).2,
        population_mixture M false,population_mixture M true⟩
    rw [hpc,hey0,hey1] at h
    refine ⟨?_,?_,h⟩
    · rw [← hpc]; exact (first_stage_population M).2
    · rw [← hpc]; exact complier_probability_le_one M

/-- T9: Corollary 1 and the intermediate noncomplier-mean ratio, pp. 678-679.
The ordinary “four cell means are known” premise includes positive probability
of all four treatment-assignment cells. No boundedness premise is needed. 
Reference (P028-T9): Corollary 1, pp. 678-679, under Section 2's standing assumptions. -/
theorem corollary1 (M : CausalModel Ω)
    (hcell : ∀ d z, 0 < M.μ.real (cellEvent M d z)) :
    cellProbability M true false = M.μ.real (alwaysEvent M) ∧
    cellProbability M false true = M.μ.real (neverEvent M) ∧
    complierProbability M = 1-cellProbability M true false-cellProbability M false true ∧
    cellMean M true false = eventMean M.μ (M.Y true) (alwaysEvent M) ∧
    cellMean M false true = eventMean M.μ (M.Y false) (neverEvent M) ∧
    noncomplierMean M =
      (cellProbability M true false*cellMean M true false +
       cellProbability M false true*cellMean M false true) /
      (cellProbability M true false+cellProbability M false true) ∧
    complierMean M false =
      (armMean M false-cellProbability M true false*cellMean M true false-
       cellProbability M false true*cellMean M false true)/complierProbability M ∧
    complierMean M true = complierMean M false +
      (armMean M true-armMean M false)/complierProbability M ∧
    complierMean M true =
      (armMean M true-cellProbability M true false*cellMean M true false-
       cellProbability M false true*cellMean M false true)/complierProbability M := by
  rcases pure_cell_probabilities M with ⟨ha,hn,hs⟩
  have hq : 0 < cellProbability M true false :=
    div_pos (hcell true false) (M.armPositive false)
  have hr : 0 < cellProbability M false true :=
    div_pos (hcell false true) (M.armPositive true)
  have hqa : 0 < M.μ.real (alwaysEvent M) := by rw [← ha]; exact hq
  have hrn : 0 < M.μ.real (neverEvent M) := by rw [← hn]; exact hr
  have hwa := (weighted_cell_mean M true false (hcell true false)).trans (pure_cell_product_moments M).1
  have hwn := (weighted_cell_mean M false true (hcell false true)).trans (pure_cell_product_moments M).2
  have hma : cellMean M true false = eventMean M.μ (M.Y true) (alwaysEvent M) := by
    unfold eventMean
    apply (eq_div_iff (ne_of_gt hqa)).2
    rw [← ha]
    nlinarith
  have hmn : cellMean M false true = eventMean M.μ (M.Y false) (neverEvent M) := by
    unfold eventMean
    apply (eq_div_iff (ne_of_gt hrn)).2
    rw [← hn]
    nlinarith
  have hm : noncomplierContribution M = cellProbability M true false*cellMean M true false+
      cellProbability M false true*cellMean M false true := by
    rw [noncomplier_contribution_observable,
      ← weighted_cell_mean M true false (hcell true false),
      ← weighted_cell_mean M false true (hcell false true)]
  have hlt : complierProbability M < 1 := by linarith
  have hnm : noncomplierMean M =
      (cellProbability M true false*cellMean M true false+
       cellProbability M false true*cellMean M false true) /
      (cellProbability M true false+cellProbability M false true) := by
    rw [(noncomplier_mean_positive_formula M hlt).2,hm,← hs]
  have h0 : armMean M false = complierProbability M*complierMean M false+
      cellProbability M true false*cellMean M true false+
      cellProbability M false true*cellMean M false true := by
    rw [population_mixture,hm]; ring
  have h1 : armMean M true = complierProbability M*complierMean M true+
      cellProbability M true false*cellMean M true false+
      cellProbability M false true*cellMean M false true := by
    rw [population_mixture,hm]; ring
  have hc := corollary_moment_identity (complierProbability M) (cellProbability M true false)
    (cellProbability M false true) (armMean M false) (armMean M true)
    (complierMean M false) (complierMean M true) (cellMean M true false)
    (cellMean M false true) (first_stage_population M).2 h0 h1
  exact ⟨ha,hn,by linarith,hma,hmn,hnm,hc.1,hc.2.1,hc.2.2⟩

/-- T10(a)-(c): the LATE display, Section 2, p. 678. The observed first stage
is P_c>0, the reduced form is P_c times CACE, and both Wald ratios equal CACE.
Only integrability, rather than bounded outcomes, is required. 
Reference (P028-T10): Section 2 LATE display, p. 678, and Section 1 identification claim, p. 677. -/
theorem late_identity (M : CausalModel Ω) :
    eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M true) -
      eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M false) = complierProbability M ∧
    0 < complierProbability M ∧
    armMean M true-armMean M false = complierProbability M*cace M ∧
    cace M = (armMean M true-armMean M false)/complierProbability M ∧
    cace M = (armMean M true-armMean M false) /
      (eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M true) -
       eventMean M.μ (fun ω => realBit (observedD M ω)) (armEvent M false)) := by
  have hf := observed_first_stage M
  have hp := (first_stage_population M).2
  have hr := late_population_ratio M
  have he := (eq_div_iff (ne_of_gt hp)).1 hr
  refine ⟨hf,hp,by nlinarith,hr,?_⟩
  rw [hf]
  exact hr

/-- T10(d): the introduction's non-identification claim is existential, not
universal over triples. The two bounded randomized models have (P_c,EY₀,EY₁)
=(1/2,3/4,3/4), CACE=0, and complier means (1/2,1/2) versus (1,1). 
Reference (P028-T10): Section 2 LATE display, p. 678, and Section 1 identification claim, p. 677. -/
theorem three_figures_do_not_identify_levels :
    ∃ M₀ M₁ : CausalModel (Bool × Bool), boundedOutcomes M₀ ∧ boundedOutcomes M₁ ∧
      complierProbability M₀ = 1/2 ∧ complierProbability M₁ = 1/2 ∧
      armMean M₀ false = 3/4 ∧ armMean M₀ true = 3/4 ∧
      armMean M₁ false = 3/4 ∧ armMean M₁ true = 3/4 ∧
      cace M₀ = 0 ∧ cace M₁ = 0 ∧
      complierMean M₀ false = 1/2 ∧ complierMean M₀ true = 1/2 ∧
      complierMean M₁ false = 1 ∧ complierMean M₁ true = 1 := by
  obtain ⟨M₀,hb0,hp0,he00,he01,hc00,hc01⟩ :=
    realize_mixture_moments (1/2) (3/4) (3/4) (1/2) (1/2) (1/2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨M₁,hb1,hp1,he10,he11,hc10,hc11⟩ :=
    realize_mixture_moments (1/2) (3/4) (3/4) 1 1 (1/4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨M₀,M₁,hb0,hb1,hp0,hp1,he00,he01,he10,he11,?_,?_,hc00,hc01,hc10,hc11⟩
  · rw [cace_difference,hc00,hc01]; ring
  · rw [cace_difference,hc10,hc11]; ring

/-- Response R on the same probability space is otherwise unrestricted;
no independence of response is built into the causal model. -/
structure Response (Ω : Type*) [MeasurableSpace Ω] where
  R : Ω → Bool
  measurableR : Measurable R
/-- Respondents {R=1}. -/
def responseEvent (T : Response Ω) : Set Ω := {ω | T.R ω = true}
/-- Respondent arm outcome mean E[Y|Z=z,R=1], corrected application (T2). -/
def responseArmMean (M : CausalModel Ω) (T : Response Ω) (z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (armEvent M z ∩ responseEvent T)
/-- Respondent cell outcome mean E[Y|D=d,Z=z,R=1], corrected application. -/
def responseCellMean (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (observedY M) (cellEvent M d z ∩ responseEvent T)
/-- The mean equalities (M1) and (M2) required by the mixed available-case repair.
They are extra hypotheses, not consequences of the Section 2 assumptions. -/
def mixedMeanEqualities (M : CausalModel Ω) (T : Response Ω) : Prop :=
  (∀ z, responseArmMean M T z = armMean M z) ∧
  responseCellMean M T true false = cellMean M true false ∧
  responseCellMean M T false true = cellMean M false true
/-- Response positivity required by the mixed version, stated as positive joint
masses. Under positive arms/cells this is equivalent to positive
conditional response probabilities. -/
def mixedResponsePositive (M : CausalModel Ω) (T : Response Ω) : Prop :=
  (∀ z, 0 < M.μ.real (armEvent M z ∩ responseEvent T)) ∧
  0 < M.μ.real (cellEvent M true false ∩ responseEvent T) ∧
  0 < M.μ.real (cellEvent M false true ∩ responseEvent T)
/-- Correctly normalized assignment-conditional law, for conditional independence
of response and (Y,D), T2(iii). -/
def assignmentConditionalLaw (M : CausalModel Ω) (z : Bool) : Measure Ω :=
  (M.μ (armEvent M z))⁻¹ • M.μ.restrict (armEvent M z)

/-- T2(i): joint-moment Corollary 1, without any assumption on response or
positive treatment-assignment cells. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem response_joint_moment_identity (M : CausalModel Ω) :
    complierProbability M*complierMean M false = jointOutcomeMoment M false false-jointOutcomeMoment M false true ∧
    complierProbability M*complierMean M true = jointOutcomeMoment M true true-jointOutcomeMoment M true false := by
  have h0 := population_mixture M false
  have h1 := population_mixture M true
  have h0' := arm_joint_moment_partition M false
  have h1' := arm_joint_moment_partition M true
  have hm := noncomplier_contribution_observable M
  constructor <;> linarith

/-- T2(ii): the mixed available-case plug-in identifies the population complier
means under precisely the stated respondent/full-population mean equalities,
positive response events, and positive pure noncomplier cells. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem response_mixed_identification (M : CausalModel Ω) (T : Response Ω)
    (hb : boundedOutcomes M) (hq : 0 < cellProbability M true false)
    (hr : 0 < cellProbability M false true) (hp : mixedResponsePositive M T)
    (hm : mixedMeanEqualities M T) :
    complierMean M false =
      (responseArmMean M T false-cellProbability M true false*responseCellMean M T true false-
       cellProbability M false true*responseCellMean M T false true)/complierProbability M ∧
    complierMean M true = complierMean M false +
      (responseArmMean M T true-responseArmMean M T false)/complierProbability M := by
  rcases corollary1 M (two_sided_cells_positive M hq hr) with
    ⟨ha,hn,hpc,hma,hmn,hnm,hc0,hc1,hc1'⟩
  rcases hm with ⟨hmarm,hmar,hmnr⟩
  constructor
  · rw [hmarm false,hmar,hmnr]
    exact hc0
  · rw [hmarm true,hmarm false]
    exact hc1

/-- Full-sample cell probability times respondent cell mean; an empty cell is
explicitly omitted rather than treated as an ordinary conditional mean. -/
def reweightedCellMoment (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  if 0 < cellProbability M d z then cellProbability M d z*responseCellMean M T d z else 0

/-- E[R Y·1{D=d}|Z=z], an observed-data moment in the T2 sensitivity repair. -/
def recordedOutcomeMoment (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  eventMean M.μ (fun ω => realBit (T.R ω) *
    (if observedD M ω = d then observedY M ω else 0)) (armEvent M z)
/-- Pr[R=0,D=d|Z=z], an observed-data missing-outcome probability. -/
def missingOutcomeProbability (M : CausalModel Ω) (T : Response Ω) (d z : Bool) : ℝ :=
  M.μ.real {ω | T.R ω = false ∧ observedD M ω = d ∧ M.Z ω = z} / M.μ.real (armEvent M z)

/-- The implicit observed outcome is a measurable selection of the two potential
outcomes; Section 2's observation rule adds no response assumption. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem observed_y_measurable (M : CausalModel Ω) : Measurable (observedY M) := by
  have he : observedY M = fun ω => if observedD M ω = true then M.Y true ω else M.Y false ω := by
    funext ω
    cases hd : observedD M ω <;> simp [observedY,hd]
  rw [he]
  exact Measurable.ite ((observed_d_measurable M) (measurableSet_singleton true))
    (M.measurableY true) (M.measurableY false)

/-- The observed outcome is integrable, without requiring bounded potentials. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem observed_y_integrable (M : CausalModel Ω) : Integrable (observedY M) M.μ := by
  have ht := (M.integrableY true).indicator ((observed_d_measurable M) (measurableSet_singleton true))
  have hf := (M.integrableY false).indicator ((observed_d_measurable M) (measurableSet_singleton false))
  apply (ht.add hf).congr
  filter_upwards [] with ω
  cases hd : observedD M ω <;> simp [Set.indicator,observedY,hd]

/-- A null treatment-assignment cell contributes zero product moment, without
claiming that its ordinary conditional mean is defined. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem null_cell_joint_moment (M : CausalModel Ω) (d z : Bool)
    (hz : cellProbability M d z = 0) : jointOutcomeMoment M d z = 0 := by
  change M.μ.real (cellEvent M d z)/M.μ.real (armEvent M z) = 0 at hz
  have hr := (div_eq_zero_iff).1 hz
  have he : M.μ.real (cellEvent M d z) = 0 := hr.resolve_right (ne_of_gt (M.armPositive z))
  have hμ : M.μ (cellEvent M d z) = 0 := (measureReal_eq_zero_iff (μ := M.μ) (s := cellEvent M d z) (by finiteness)).1 he
  rw [joint_moment_cell_integral]
  simp [Measure.restrict_eq_zero.mpr hμ]

/-- The conditional missing-cell probability is the expectation of its binary
indicator in the assignment arm. This quantity is fully observed. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem missing_probability_as_mean (M : CausalModel Ω) (T : Response Ω) (d z : Bool) :
    missingOutcomeProbability M T d z =
      eventMean M.μ (fun ω => if T.R ω = false ∧ observedD M ω = d then 1 else 0) (armEvent M z) := by
  have hs : MeasurableSet {ω | T.R ω = false ∧ observedD M ω = d ∧ M.Z ω = z} :=
    (T.measurableR (measurableSet_singleton false)).inter
      (((observed_d_measurable M) (measurableSet_singleton d)).inter (arm_measurable M z))
  unfold missingOutcomeProbability eventMean
  congr 1
  rw [← integral_indicator_one hs, ← integral_indicator (arm_measurable M z)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hz : M.Z ω = z <;> by_cases hr : T.R ω = false <;>
    by_cases hd : observedD M ω = d <;> simp [Set.indicator,armEvent,hz,hr,hd]

/-- T2(v)'s finite population inequality: the full joint outcome moment lies
between its recorded moment and that moment plus missing-cell probability.
It uses only bounded outcomes, not response ignorability or independence. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem recorded_joint_moment_bounds (M : CausalModel Ω) (T : Response Ω)
    (hb : boundedOutcomes M) (d z : Bool) :
    recordedOutcomeMoment M T d z ≤ jointOutcomeMoment M d z ∧
    jointOutcomeMoment M d z ≤ recordedOutcomeMoment M T d z+missingOutcomeProbability M T d z := by
  let f : Ω → ℝ := fun ω => if observedD M ω = d then observedY M ω else 0
  let g : Ω → ℝ := fun ω => realBit (T.R ω)*f ω
  let h : Ω → ℝ := fun ω => if T.R ω = false ∧ observedD M ω = d then 1 else 0
  have hD := (observed_d_measurable M) (measurableSet_singleton d)
  have hR := T.measurableR (measurableSet_singleton false)
  have hfm : Measurable f := Measurable.ite hD (observed_y_measurable M) measurable_const
  have hgm : Measurable g := ((Measurable.of_discrete : Measurable realBit).comp T.measurableR).mul hfm
  have hhm : Measurable h := Measurable.ite (hR.inter hD) measurable_const measurable_const
  have hfb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1 := by
    intro ω
    dsimp [f]
    split_ifs
    · exact hb (observedD M ω) ω
    · norm_num
  have hgb : ∀ ω, 0 ≤ g ω ∧ g ω ≤ 1 := by
    intro ω
    cases hr : T.R ω <;> simp [g,realBit,hr,hfb ω]
  have hhb : ∀ ω, 0 ≤ h ω ∧ h ω ≤ 1 := by
    intro ω
    dsimp [h]
    split_ifs <;> norm_num
  have hfi : Integrable f M.μ := Integrable.of_mem_Icc 0 1 hfm.aemeasurable (Filter.Eventually.of_forall hfb)
  have hgi : Integrable g M.μ := Integrable.of_mem_Icc 0 1 hgm.aemeasurable (Filter.Eventually.of_forall hgb)
  have hhi : Integrable h M.μ := Integrable.of_mem_Icc 0 1 hhm.aemeasurable (Filter.Eventually.of_forall hhb)
  have hgf : ∀ ω, g ω ≤ f ω := by
    intro ω
    cases hr : T.R ω <;> simp [g,realBit,hr,(hfb ω).1]
  have hfgh : ∀ ω, f ω ≤ g ω+h ω := by
    intro ω
    cases hr : T.R ω <;> by_cases hd : observedD M ω = d <;>
      simp [f,g,h,realBit,hr,hd] <;> exact (hb (observedD M ω) ω).2
  have hgmean : eventMean M.μ g (armEvent M z) = recordedOutcomeMoment M T d z := rfl
  have hfmean : eventMean M.μ f (armEvent M z) = jointOutcomeMoment M d z := rfl
  have hhmean : eventMean M.μ h (armEvent M z) = missingOutcomeProbability M T d z :=
    (missing_probability_as_mean M T d z).symm
  constructor
  · rw [← hgmean,← hfmean]
    unfold eventMean
    exact div_le_div_of_nonneg_right
      (integral_mono hgi.restrict hfi.restrict hgf) (M.armPositive z).le
  · rw [← hgmean,← hfmean,← hhmean]
    unfold eventMean
    rw [← add_div,← integral_add hgi.restrict hhi.restrict]
    exact div_le_div_of_nonneg_right
      (integral_mono hfi.restrict (hgi.add hhi).restrict hfgh) (M.armPositive z).le


/-- Integral under the normalized arm law, including a further measurable event. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem normalized_arm_set_integral (M : CausalModel Ω) (z : Bool) (f : Ω → ℝ)
    (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω in E, f ω ∂assignmentConditionalLaw M z) =
      (∫ ω in armEvent M z ∩ E, f ω ∂M.μ)/M.μ.real (armEvent M z) := by
  unfold assignmentConditionalLaw
  rw [Measure.restrict_smul,Measure.restrict_restrict hE,integral_smul_measure]
  simp only [smul_eq_mul,ENNReal.toReal_inv,← measureReal_def,div_eq_mul_inv]
  rw [Set.inter_comm E (armEvent M z),mul_comm]

/-- The normalized arm law's event probabilities are ordinary conditional probabilities. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem normalized_arm_real (M : CausalModel Ω) (z : Bool) (E : Set Ω) (hE : MeasurableSet E) :
    (assignmentConditionalLaw M z).real E = M.μ.real (armEvent M z ∩ E)/M.μ.real (armEvent M z) := by
  have h := normalized_arm_set_integral M z (fun _ => 1) E hE
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using h

/-- Integral under the normalized arm law is the ordinary arm conditional mean. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem normalized_arm_integral (M : CausalModel Ω) (z : Bool) (f : Ω → ℝ) :
    (∫ ω, f ω ∂assignmentConditionalLaw M z) =
      (∫ ω in armEvent M z, f ω ∂M.μ)/M.μ.real (armEvent M z) := by
  simpa using normalized_arm_set_integral M z f Set.univ MeasurableSet.univ

/-- Independence of response and (Y,D) factorizes every integrable outcome/cell
moment restricted to respondents. This is a probability lemma, not an assumption. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem independent_response_factor (ν : Measure Ω) (R : Ω → Bool) (V : Ω → ℝ × Bool)
    (hR : Measurable R) (hV : Measurable V) (hi : IndepFun R V ν)
    (f : ℝ × Bool → ℝ) (hf : Measurable f) :
    (∫ ω in {ω | R ω = true}, f (V ω) ∂ν) =
      ν.real {ω | R ω = true}*(∫ ω, f (V ω) ∂ν) := by
  have hp := hi.integral_fun_comp_mul_comp hR.aemeasurable hV.aemeasurable
    (Measurable.of_discrete : Measurable realBit).aestronglyMeasurable hf.aestronglyMeasurable
  have hRE : MeasurableSet {ω | R ω = true} := hR (measurableSet_singleton true)
  have hr : (∫ ω, realBit (R ω) ∂ν) = ν.real {ω | R ω = true} := by
    rw [← integral_indicator_one hRE]
    apply integral_congr_ae
    filter_upwards [] with ω
    cases h : R ω <;> simp [Set.indicator,realBit,h]
  have he : (∫ ω in {ω | R ω = true}, f (V ω) ∂ν) =
      ∫ ω, realBit (R ω)*f (V ω) ∂ν := by
    rw [← integral_indicator hRE]
    apply integral_congr_ae
    filter_upwards [] with ω
    cases h : R ω <;> simp [Set.indicator,realBit,h]
  rw [he,hp,hr]

/-- Conditional response independence yields the arm-restricted moment factorization. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem independent_arm_response_factor (M : CausalModel Ω) (T : Response Ω) (z : Bool)
    (hi : IndepFun T.R (fun ω => (observedY M ω,observedD M ω)) (assignmentConditionalLaw M z))
    (f : ℝ × Bool → ℝ) (hf : Measurable f) :
    (∫ ω in armEvent M z ∩ responseEvent T, f (observedY M ω,observedD M ω) ∂M.μ) =
      (M.μ.real (armEvent M z ∩ responseEvent T)/M.μ.real (armEvent M z))*
      (∫ ω in armEvent M z, f (observedY M ω,observedD M ω) ∂M.μ) := by
  have h := independent_response_factor (assignmentConditionalLaw M z) T.R
    (fun ω => (observedY M ω,observedD M ω)) T.measurableR
    ((observed_y_measurable M).prodMk (observed_d_measurable M)) hi f hf
  have hR : MeasurableSet (responseEvent T) := T.measurableR (measurableSet_singleton true)
  change (∫ ω in responseEvent T, f (observedY M ω,observedD M ω) ∂assignmentConditionalLaw M z) =
    (assignmentConditionalLaw M z).real (responseEvent T)*
      (∫ ω, f (observedY M ω,observedD M ω) ∂assignmentConditionalLaw M z) at h
  rw [normalized_arm_set_integral M z _ _ hR,normalized_arm_real M z _ hR,normalized_arm_integral] at h
  have ha : M.μ.real (armEvent M z) ≠ 0 := ne_of_gt (M.armPositive z)
  field_simp [ha] at h ⊢
  nlinarith

/-- A treatment indicator integrated over an arm and another event is their
joint cell probability. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem arm_event_cell_indicator (M : CausalModel Ω) (d z : Bool) (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω in armEvent M z ∩ E, if observedD M ω = d then (1:ℝ) else 0 ∂M.μ) =
      M.μ.real (cellEvent M d z ∩ E) := by
  rw [← integral_indicator ((arm_measurable M z).inter hE),
    ← integral_indicator_one ((cell_measurable M d z).inter hE)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hz : M.Z ω = z <;> by_cases hd : observedD M ω = d <;>
    by_cases he : ω ∈ E <;> simp [Set.indicator,armEvent,cellEvent,hz,hd,he]

/-- A cell-restricted outcome product integrated over an arm and another event
is the unnormalized outcome moment on that treatment-assignment cell. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem arm_event_cell_outcome (M : CausalModel Ω) (d z : Bool) (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω in armEvent M z ∩ E, if observedD M ω = d then observedY M ω else 0 ∂M.μ) =
      (∫ ω in cellEvent M d z ∩ E, observedY M ω ∂M.μ) := by
  rw [← integral_indicator ((arm_measurable M z).inter hE),
    ← integral_indicator ((cell_measurable M d z).inter hE)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hz : M.Z ω = z <;> by_cases hd : observedD M ω = d <;>
    by_cases he : ω ∈ E <;> simp [Set.indicator,armEvent,cellEvent,hz,hd,he]

/-- Positive arm response and conditional response independence imply (M1). 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem independent_response_arm_mean (M : CausalModel Ω) (T : Response Ω) (z : Bool)
    (hr : 0 < M.μ.real (armEvent M z ∩ responseEvent T))
    (hi : IndepFun T.R (fun ω => (observedY M ω,observedD M ω)) (assignmentConditionalLaw M z)) :
    responseArmMean M T z = armMean M z := by
  have h := independent_arm_response_factor M T z hi Prod.fst measurable_fst
  unfold responseArmMean armMean eventMean
  have ha : M.μ.real (armEvent M z) ≠ 0 := ne_of_gt (M.armPositive z)
  have hrn : M.μ.real (armEvent M z ∩ responseEvent T) ≠ 0 := ne_of_gt hr
  dsimp only at h
  field_simp [ha,hrn] at h ⊢
  nlinarith

/-- Positive cell and arm response, with conditional response independence,
imply positive cell response and equality of its respondent and population means. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem independent_response_cell_mean (M : CausalModel Ω) (T : Response Ω) (d z : Bool)
    (hc : 0 < M.μ.real (cellEvent M d z))
    (hr : 0 < M.μ.real (armEvent M z ∩ responseEvent T))
    (hi : IndepFun T.R (fun ω => (observedY M ω,observedD M ω)) (assignmentConditionalLaw M z)) :
    0 < M.μ.real (cellEvent M d z ∩ responseEvent T) ∧
    responseCellMean M T d z = cellMean M d z := by
  have hR : MeasurableSet (responseEvent T) := T.measurableR (measurableSet_singleton true)
  let g : ℝ × Bool → ℝ := fun v => if v.2 = d then 1 else 0
  let f : ℝ × Bool → ℝ := fun v => if v.2 = d then v.1 else 0
  have hg : Measurable g :=
    (Measurable.of_discrete : Measurable (fun b : Bool => if b = d then (1:ℝ) else 0)).comp measurable_snd
  have hf : Measurable f := Measurable.ite (measurable_snd (measurableSet_singleton d)) measurable_fst measurable_const
  have hP := independent_arm_response_factor M T z hi g hg
  have hY := independent_arm_response_factor M T z hi f hf
  dsimp only [g] at hP
  dsimp only [f] at hY
  rw [arm_event_cell_indicator M d z _ hR] at hP
  rw [arm_event_cell_outcome M d z _ hR] at hY
  have hP0 : (∫ ω in armEvent M z, if observedD M ω = d then (1:ℝ) else 0 ∂M.μ) =
      M.μ.real (cellEvent M d z) := by
    simpa using arm_event_cell_indicator M d z Set.univ MeasurableSet.univ
  have hY0 : (∫ ω in armEvent M z, if observedD M ω = d then observedY M ω else 0 ∂M.μ) =
      ∫ ω in cellEvent M d z, observedY M ω ∂M.μ := by
    simpa using arm_event_cell_outcome M d z Set.univ MeasurableSet.univ
  rw [hP0] at hP
  rw [hY0] at hY
  have hρ : 0 < M.μ.real (armEvent M z ∩ responseEvent T)/M.μ.real (armEvent M z) :=
    div_pos hr (M.armPositive z)
  refine ⟨by rw [hP]; exact mul_pos hρ hc,?_⟩
  unfold responseCellMean cellMean eventMean
  rw [hP,hY]
  exact mul_div_mul_left _ _ (ne_of_gt hρ)

/-- T2(iii): conditional independence R ⟂ (Y,D) in each assignment arm, with
positive arm response, is a sufficient stronger condition for the four mean
equalities and required response positivity when q,r>0. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem response_independence_sufficient (M : CausalModel Ω) (T : Response Ω)
    (hb : boundedOutcomes M) (hq : 0 < cellProbability M true false)
    (hr : 0 < cellProbability M false true)
    (hp : ∀ z, 0 < M.μ.real (armEvent M z ∩ responseEvent T))
    (hi : ∀ z, IndepFun T.R (fun ω => (observedY M ω,observedD M ω)) (assignmentConditionalLaw M z)) :
    mixedMeanEqualities M T ∧ mixedResponsePositive M T := by
  have ha := independent_response_cell_mean M T true false
    (positive_cell_mass M true false hq) (hp false) (hi false)
  have hn := independent_response_cell_mean M T false true
    (positive_cell_mass M false true hr) (hp true) (hi true)
  exact ⟨⟨fun z => independent_response_arm_mean M T z (hp z) (hi z),ha.2,hn.2⟩,
    ⟨hp,ha.1,hn.1⟩⟩

/-- T2(iv): cell mean ignorability identifies arm means after reweighting by
full-sample cell probabilities and identifies both complier means by differences
of reweighted cell moments. No unweighted respondent-arm equality is assumed. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem response_cell_reweighting (M : CausalModel Ω) (T : Response Ω)
    (hb : boundedOutcomes M)
    (hc : ∀ d z, 0 < cellProbability M d z →
      0 < M.μ.real (cellEvent M d z ∩ responseEvent T) ∧
      responseCellMean M T d z = cellMean M d z) :
    (∀ z, armMean M z = ∑ d : Bool, reweightedCellMoment M T d z) ∧
    complierMean M false =
      (reweightedCellMoment M T false false-reweightedCellMoment M T false true)/complierProbability M ∧
    complierMean M true =
      (reweightedCellMoment M T true true-reweightedCellMoment M T true false)/complierProbability M := by
  have hJ : ∀ d z, reweightedCellMoment M T d z = jointOutcomeMoment M d z := by
    intro d z
    unfold reweightedCellMoment
    by_cases hp : 0 < cellProbability M d z
    · rw [if_pos hp,(hc d z hp).2]
      exact weighted_cell_mean M d z (positive_cell_mass M d z hp)
    · have hz : cellProbability M d z = 0 :=
        le_antisymm (le_of_not_gt hp) (div_nonneg measureReal_nonneg (M.armPositive z).le)
      rw [if_neg hp,null_cell_joint_moment M d z hz]
  have h := response_joint_moment_identity M
  have hp := (first_stage_population M).2
  refine ⟨?_,?_,?_⟩
  · intro z
    simp only [Fintype.sum_bool]
    rw [hJ,hJ]
    linarith [arm_joint_moment_partition M z]
  · rw [hJ,hJ]
    apply (eq_div_iff (ne_of_gt hp)).2
    nlinarith [h.1]
  · rw [hJ,hJ]
    apply (eq_div_iff (ne_of_gt hp)).2
    nlinarith [h.2]

/-- T2(v): without any response restriction, bounded outcomes imply the two
missing-outcome sensitivity intervals. These are population identification
bounds, not sampling confidence intervals. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem response_sensitivity_bounds (M : CausalModel Ω) (T : Response Ω)
    (hb : boundedOutcomes M) :
    (recordedOutcomeMoment M T false false-recordedOutcomeMoment M T false true-
      missingOutcomeProbability M T false true)/complierProbability M ≤ complierMean M false ∧
    complierMean M false ≤
      (recordedOutcomeMoment M T false false+missingOutcomeProbability M T false false-
       recordedOutcomeMoment M T false true)/complierProbability M ∧
    (recordedOutcomeMoment M T true true-recordedOutcomeMoment M T true false-
      missingOutcomeProbability M T true false)/complierProbability M ≤ complierMean M true ∧
    complierMean M true ≤
      (recordedOutcomeMoment M T true true+missingOutcomeProbability M T true true-
       recordedOutcomeMoment M T true false)/complierProbability M := by
  have h := response_joint_moment_identity M
  have hp := (first_stage_population M).2
  have h0 := missing_moment_difference_bounds (complierProbability M) (complierMean M false)
    (jointOutcomeMoment M false false) (jointOutcomeMoment M false true)
    (recordedOutcomeMoment M T false false) (recordedOutcomeMoment M T false true)
    (missingOutcomeProbability M T false false) (missingOutcomeProbability M T false true)
    hp h.1 (recorded_joint_moment_bounds M T hb false false)
    (recorded_joint_moment_bounds M T hb false true)
  have h1 := missing_moment_difference_bounds (complierProbability M) (complierMean M true)
    (jointOutcomeMoment M true true) (jointOutcomeMoment M true false)
    (recordedOutcomeMoment M T true true) (recordedOutcomeMoment M T true false)
    (missingOutcomeProbability M T true true) (missingOutcomeProbability M T true false)
    hp h.2 (recorded_joint_moment_bounds M T hb true true)
    (recorded_joint_moment_bounds M T hb true false)
  exact ⟨h0.1,h0.2,h1.1,h1.2⟩

/-- T2 worked instance: all exact sensitivity endpoints and both conditional
plug-in calculations from the source table. The point values are justified only
under their respective response assumptions; T1 proves endpoint attainment. 
Reference (P028-T2): Corrected Section 4 identification claim, p. 679. -/
theorem response_source_table_calculations :
    ((167/495-130/505-26/505)/(2047/9999) : ℝ) = 1423/10235 ∧
    ((167/495+36/495-130/505)/(2047/9999) : ℝ) = 7633/10235 ∧
    ((110/505-40/495-1/495)/(2047/9999) : ℝ) = 6749/10235 ∧
    ((110/505+8/505-40/495)/(2047/9999) : ℝ) = 7642/10235 ∧
    ((207/458-(16/99)*(40/79)-(64/101)*(130/294))/(2047/9999) : ℝ) = 1594452863/3629163146 ∧
    ((207/458-(16/99)*(40/79)-(64/101)*(130/294))/(2047/9999)+(240/471-207/458)/(2047/9999) : ℝ) = 896530960/1244058109 ∧
    (((415/495)*(167/379)-(320/505)*(130/294))/(2047/9999) : ℝ) = 16568969/38014837 ∧
    (((185/505)*(110/177)-(80/495)*(40/79))/(2047/9999) : ℝ) = 295510/414829 := by
  norm_num

/-- T8: for bounded arm means and 0<p≤1, the printed intervals are nonempty
exactly when |e1-e0|≤p. The control interval is its translated counterpart. 
Reference (P028-T8): Proposition 1, p. 678, including the sharpness interpretation. -/
theorem proposition1_interval_nonempty (p e0 e1 : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (he0 : 0 ≤ e0 ∧ e0 ≤ 1) (he1 : 0 ≤ e1 ∧ e1 ≤ 1) :
    lowerTreated p e0 e1 ≤ upperTreated p e0 e1 ↔ |e1-e0| ≤ p := by
  constructor
  · intro hx
    have h := sharpness_moment_certificate p e0 e1 (lowerTreated p e0 e1) hp.1 ⟨le_rfl,hx⟩
    dsimp at h
    rcases h with ⟨h0,h01,h1,h11,hm,hm1,he0',he1'⟩
    have hc := (compatible_mixture_moments p e0 e1 hp).2
      ⟨lowerTreated p e0 e1-effect p e0 e1,lowerTreated p e0 e1,
        e1-p*lowerTreated p e0 e1,h0,h01,h1,h11,hm,hm1,he0',he1'⟩
    exact hc.2.2.2.2
  · intro he
    obtain ⟨c0,c1,m,h0,h01,h1,h11,hm,hm1,he0',he1'⟩ :=
      (compatible_mixture_moments p e0 e1 hp).1 ⟨he0.1,he0.2,he1.1,he1.2,he⟩
    have h := bounds_from_mixture_moments p e0 e1 c0 c1 m hp.1 he0' he1'
      ⟨h0,h01⟩ ⟨h1,h11⟩ ⟨hm,hm1⟩
    exact le_trans h.2.2.2.1 h.2.2.2.2

/-- T5(E6): the counterexample's input triple (1/2,3/4,3/4) really is generated
by an admissible randomized bounded-outcome population. A half-complier, half-
never-taker law has complier means 1 and noncomplier outcome 1/2. 
Reference (P028-T5): Printed Proposition 1 proof after Eq. (3), p. 678. -/
theorem misprinted_witness_admissible_inputs :
    ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧
      complierProbability M = 1/2 ∧ armMean M false = 3/4 ∧ armMean M true = 3/4 ∧
      complierMean M false = 1 ∧ complierMean M true = 1 := by
  exact realize_mixture_moments (1/2) (3/4) (3/4) 1 1 (1/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
end AronowAudit.P028



