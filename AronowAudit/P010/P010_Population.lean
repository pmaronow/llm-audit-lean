import Mathlib

namespace AronowAudit.P010

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical

/-- Section 2, pp. 573–574: “Y denotes the subject's response, S ... (1 if ...
passed, 0 if ... failed), and Z ... treatment assignment.” A state contains the
whole vector of real potential outcomes, binary potential passing indicators,
assignment, and a finite real covariate vector (Section 2.3, p. 576).
`Fin K` is the paper's {1,...,K}, with labels shifted down by one. Arbitrary
Borel probability measures on this space represent arbitrary population laws;
no finite-support or joint-vector randomization restriction is imposed. -/
abbrev State (K d : ℕ) := (Fin K → ℝ) × (Fin K → Bool) × Fin K × (Fin d → ℝ)

/-- Assumption 1, p. 573: “Y = sum Y(z) I(Z=z) and S = sum S(z) I(Z=z).”
Selection of exactly one arm implements both consistency equations. -/
def potentialY {K d} (a : Fin K) (ω : State K d) : ℝ := ω.1 a
/-- Assumption 1, p. 573: “potential results from the manipulation check”
S(z), represented by a binary coordinate for each arm. -/
def potentialS {K d} (a : Fin K) (ω : State K d) : Bool := ω.2.1 a
/-- Section 2, p. 573: “Z denotes the subject's treatment assignment”. -/
def assignment {K d} (ω : State K d) : Fin K := ω.2.2.1
/-- Section 2.3, p. 576: “a vector of covariates X associated with each unit”. -/
def covariates {K d} (ω : State K d) : Fin d → ℝ := ω.2.2.2
/-- Assumption 1, p. 573: “Y = sum Y(z) I(Z=z)”, implemented as Y(Z). -/
def observedY {K d} (ω : State K d) : ℝ := potentialY (assignment ω) ω
/-- Assumption 1, p. 573: “S = sum S(z) I(Z=z)”, implemented as S(Z). -/
def observedS {K d} (ω : State K d) : Bool := potentialS (assignment ω) ω

/-- Section 2.1, p. 574: “subjects who would pass under all treatment
conditions.” A is the all-pass event; C says potential passing status is
unaffected by treatment, without asserting anything about joint outcomes. -/
def alwaysPass {K d} : Set (State K d) := {ω | ∀ a, potentialS a ω = true}
/-- Corollary 1, p. 574: “S(1)=S(2)=...=S(K)”, the common-status event. -/
def commonStatus {K d} : Set (State K d) := {ω | ∀ a b, potentialS a ω = potentialS b ω}
/-- Assumption 2, p. 574: the assignment event “Z=z”. -/
def armEvent {K d} (a : Fin K) : Set (State K d) := {ω | assignment ω = a}
/-- Section 2, p. 573: “1 if the subject passed”, namely observed S=1. -/
def passEvent {K d} : Set (State K d) := {ω | observedS ω = true}
/-- Proposition 1 proof, p. 580: potential passing event “S(1)=1”, with
the focal arm generalized to any a. -/
def potentialPass {K d} (a : Fin K) : Set (State K d) := {ω | potentialS a ω = true}

/-- Population conditional expectations in Section 2, pp. 574–576:
E[f|E] is the event-restricted integral divided by Pr(E). Results attach
positive conditioning mass and integrability where needed; the totalized
zero-event convention is never used to manufacture an identification result. -/
noncomputable def eventMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (E : Set Ω) : ℝ := (∫ ω in E, f ω ∂μ) / (μ E).toReal

/-- Conditional outcome law, Proposition 1, p. 575: “conditional ... Y given
Z=z and S=1.” Normalization is by the full mass of the conditioning event. -/
noncomputable def eventLaw {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (μ : Measure Ω) (f : Ω → B) (E : Set Ω) : Measure B :=
  (μ E)⁻¹ • (μ.restrict E).map f

/-- Assumption 2 (Ignorability), p. 574: for every arm, “(Y(z), S(z)) ... Z,
with Pr(Z=z)>0.” This is per-arm pair independence, exactly as printed. -/
def Ignorability {K d} (μ : Measure (State K d)) : Prop :=
  (∀ a, IndepFun (fun ω => (potentialY a ω, potentialS a ω)) assignment μ) ∧
  (∀ a, 0 < μ (armEvent a))

/-- Corrected Assumption 3, p. 574 (T17): “at least some subjects pass ... in
every treatment arm”; the event missing in print is explicitly S=1. -/
noncomputable def passingRate {K d} (μ : Measure (State K d)) (a : Fin K) : ℝ :=
  (μ (passEvent ∩ armEvent a)).toReal / (μ (armEvent a)).toReal
/-- Corrected Assumption 3, p. 574, T17: “Pr[S=1|Z=z]>0” for every arm. -/
def NonzeroPassing {K d} (μ : Measure (State K d)) : Prop := ∀ a, 0 < passingRate μ a

/-- Section 2, pp. 573–574: “We make three assumptions to proceed.” SUTVA
is built into the coordinates; the other two assumptions and a probability
population law are collected here. -/
def Assumptions {K d} (μ : Measure (State K d)) : Prop :=
  IsProbabilityMeasure μ ∧ Ignorability μ ∧ NonzeroPassing μ

/-- Assumption 4, p. 576: “(Y(z), S(z), X) ... Z, with Pr(Z=z)>0.” -/
def CovariateIgnorability {K d} (μ : Measure (State K d)) : Prop :=
  (∀ a, IndepFun (fun ω => (potentialY a ω, potentialS a ω, covariates ω)) assignment μ) ∧
  (∀ a, 0 < μ (armEvent a))

/-- Corollaries 4–5, p. 576: X independent of Z given S. Because S is binary,
this means independence under each normalized S=b law with positive mass;
X remains a general real vector, and is not discretized. -/
def CovariateBalance {K d} (μ : Measure (State K d)) : Prop :=
  ∀ b : Bool, 0 < μ {ω | observedS ω = b} →
    IndepFun covariates assignment ((μ {ω | observedS ω = b})⁻¹ •
      μ.restrict {ω | observedS ω = b})

/-- Proposition 1, p. 575: the trimming proportion sums each other arm's
failure probability and divides by the focal arm's passing probability. -/
noncomputable def trimRatio {K d} (μ : Measure (State K d)) (a : Fin K) : ℝ :=
  (∑ b : Fin K, if b ≠ a then 1 - passingRate μ b else 0) / passingRate μ a
/-- Proposition 1, p. 575: the “conditional” distribution of Y given
“Z=z and S=1”, represented as a normalized restricted image measure. -/
noncomputable def passerLaw {K d} (μ : Measure (State K d)) (a : Fin K) : Measure ℝ :=
  eventLaw μ observedY (passEvent ∩ armEvent a)

/-- Proposition 1: “Let Q ... denote the conditional quantile function.”
The left quantile is an infimum in the extended reals. This represents
endpoint quantiles ±infinity without inventing a finite cutoff at 0 or 1. -/
noncomputable def quantile (ν : Measure ℝ) (u : ℝ) : EReal :=
  sInf {x : EReal | u ≤ (ν {y : ℝ | (y : EReal) ≤ x}).toReal}

/-- The real quantile on (0,1), for the equivalent quantile-integral form
of corrected Proposition 1, p. 575 (T4). Extended endpoint values are mapped
to zero only inside Lebesgue integrals, where the two endpoints are null. -/
noncomputable def quantileReal (ν : Measure ℝ) (u : ℝ) : ℝ := (quantile ν u).toReal

/-- Proposition 1, p. 575: “Y is continuous”; the targets spell out the
needed mathematical content as zero probability for every singleton. -/
def Atomless (ν : Measure ℝ) : Prop := ∀ x : ℝ, ν {x} = 0

/-- Proposition 1, p. 575: “unbounded support”; the concrete witnesses
have the stronger explicit full support R in their specified targets. -/
def FullRealSupport {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ l u : ℝ, l < u → 0 < μ {ω | l < f ω ∧ f ω < u}

/-- Section 2.1, p. 574: “finite third moments” as a regularity example;
T3's specified exponential/Laplace witness has all absolute moments finite. -/
def AllMoments {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ n : ℕ, Integrable (fun ω => |f ω| ^ n) μ

/-- Corrected Proposition 1 (T4): both tail means condition on passers.
With r=0 the endpoint quantiles retain the whole distribution. -/
noncomputable def lowerBound {K d} (μ : Measure (State K d)) (a : Fin K) : ℝ :=
  eventMean μ observedY ((passEvent ∩ armEvent a) ∩
    {ω | (observedY ω : EReal) ≤ quantile (passerLaw μ a) (1 - trimRatio μ a)})
/-- Corrected Proposition 1, p. 575, T4: upper-tail “Y >= Q(r)” mean,
with “S=1” restored to the outer conditioning event. -/
noncomputable def upperBound {K d} (μ : Measure (State K d)) (a : Fin K) : ℝ :=
  eventMean μ observedY ((passEvent ∩ armEvent a) ∩
    {ω | quantile (passerLaw μ a) (trimRatio μ a) ≤ (observedY ω : EReal)})

/-- “Sharp bounds” (Proposition 1, p. 575), interpreted over all joint laws
satisfying Assumptions 1–3, positive all-pass mass, and the given complete law
of the observables (Y,S,Z). Failers' outcome laws
are preserved as well. No independence of the whole potential vector is added. -/
def Compatible {K d} (μ ν : Measure (State K d)) : Prop :=
  Assumptions ν ∧ 0 < ν alwaysPass ∧
  ν.map (fun ω => (observedY ω, observedS ω, assignment ω)) =
    μ.map (fun ω => (observedY ω, observedS ω, assignment ω))
/-- Proposition 1's “sharp bounds”, p. 575: attainable always-passer
means over all compatible full population laws, as fixed in T4/T6. -/
noncomputable def identifiedMeans {K d} (μ : Measure (State K d)) (a : Fin K) : Set ℝ :=
  {m | ∃ ν : Measure (State K d), Compatible μ ν ∧ eventMean ν (potentialY a) alwaysPass = m}
/-- Proposition 1's “sharp bounds”, p. 575, T6: the same set of attainable
real means embedded in the extended reals for infinite endpoints. -/
noncomputable def extendedMeans {K d} (μ : Measure (State K d)) (a : Fin K) : Set EReal :=
  {m | ∃ x ∈ identifiedMeans μ a, (x : EReal) = m}

/-- Corrected else-branch (T6): essential support endpoints of the *passer*
outcome law, in extended reals; these differ from support of observed Y. -/
noncomputable def passerInf {K d} (μ : Measure (State K d)) (a : Fin K) : EReal :=
  essInf (fun y : ℝ => (y : EReal)) (passerLaw μ a)
/-- Corrected else-branch, p. 575, T6: “ess sup” of the focal passer
outcome law, with +infinity allowed. -/
noncomputable def passerSup {K d} (μ : Measure (State K d)) (a : Fin K) : EReal :=
  essSup (fun y : ℝ => (y : EReal)) (passerLaw μ a)

/-- Measurability of the paper's coordinate potential variables (p. 573). -/
@[fun_prop] theorem measurable_potentialY {K d} (a : Fin K) : Measurable (potentialY (d := d) a) := by
  unfold potentialY
  fun_prop
/-- Binary potential manipulation response S(z) is measurable (Section 2, p. 573). -/
@[fun_prop] theorem measurable_potentialS {K d} (a : Fin K) : Measurable (potentialS (d := d) a) := by
  unfold potentialS
  fun_prop
/-- Finite treatment assignment Z is measurable (Section 2, p. 573). -/
@[fun_prop] theorem measurable_assignment {K d} : Measurable (assignment (K := K) (d := d)) := by
  unfold assignment
  fun_prop
/-- The covariate vector X is measurable (Section 2.3, p. 576). -/
@[fun_prop] theorem measurable_covariates {K d} : Measurable (covariates (K := K) (d := d)) := by
  unfold covariates
  fun_prop
/-- Observed Y=Y(Z) is measurable by the SUTVA construction (p. 573). -/
@[fun_prop] theorem measurable_observedY {K d} : Measurable (observedY (K := K) (d := d)) :=
  (measurable_from_prod_countable_left
    (f := fun p : State K d × Fin K => potentialY p.2 p.1)
    (fun a : Fin K => measurable_potentialY (d := d) a)).comp
    (measurable_id.prodMk measurable_assignment)
/-- Observed S=S(Z) is measurable by the SUTVA construction (p. 573). -/
@[fun_prop] theorem measurable_observedS {K d} : Measurable (observedS (K := K) (d := d)) :=
  (measurable_from_prod_countable_left
    (f := fun p : State K d × Fin K => potentialS p.2 p.1)
    (fun a : Fin K => measurable_potentialS (d := d) a)).comp
    (measurable_id.prodMk measurable_assignment)

/-- The event Z=z is measurable (Assumption 2, p. 574). -/
theorem measurableSet_arm {K d} (a : Fin K) : MeasurableSet (armEvent (d := d) a) :=
  measurable_assignment (measurableSet_singleton a)
/-- The event S=1 is measurable (corrected Assumption 3, p. 574). -/
theorem measurableSet_pass {K d} : MeasurableSet (passEvent (K := K) (d := d)) :=
  measurable_observedS (measurableSet_singleton true)
/-- The potential event S(z)=1 is measurable (Section 2.1, p. 574). -/
theorem measurableSet_potentialPass {K d} (a : Fin K) : MeasurableSet (potentialPass (d := d) a) :=
  (measurable_potentialS a) (measurableSet_singleton true)
/-- The event that all potential passing results coincide is measurable (Corollary 1, p. 574). -/
theorem measurableSet_common {K d} : MeasurableSet (commonStatus (K := K) (d := d)) := by
  have he : (commonStatus : Set (State K d)) =
      ⋂ a : Fin K, ⋂ b : Fin K, {ω | potentialS a ω = potentialS b ω} := by
    ext ω
    simp [commonStatus]
  rw [he]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_eq_fun (measurable_potentialS a) (measurable_potentialS b)
/-- The always-passer event is measurable (target parameter, p. 574). -/
theorem measurableSet_always {K d} : MeasurableSet (alwaysPass (K := K) (d := d)) := by
  have he : (alwaysPass : Set (State K d)) = ⋂ a : Fin K, potentialPass a := by
    ext ω
    simp [alwaysPass,potentialPass]
  rw [he]
  exact MeasurableSet.iInter fun a => measurableSet_potentialPass a

/-- Assumption 1, p. 573, identifies observed and arm potential passing on
that assignment event; this equality is pointwise, not a design assumption. -/
theorem pass_inter_arm {K d} (a : Fin K) :
    (passEvent (d := d) ∩ armEvent a) = potentialPass a ∩ armEvent a := by
  ext ω
  simp only [mem_inter_iff, passEvent, potentialPass, armEvent, mem_setOf_eq, observedS]
  constructor <;> rintro ⟨hs,hz⟩ <;> exact ⟨by simpa [hz] using hs,hz⟩

/-- Common potential passing status, p. 574, implies each potential indicator
and the observed indicator are equal almost surely. -/
theorem common_status_ae {K d} (μ : Measure (State K d)) [IsProbabilityMeasure μ]
    (hC : μ commonStatus = 1) (a : Fin K) : observedS =ᵐ[μ] potentialS a := by
  have hc : ∀ᵐ ω ∂μ, ω ∈ commonStatus := (mem_ae_iff_prob_eq_one measurableSet_common).mpr hC
  filter_upwards [hc] with ω hω
  exact hω (assignment ω) a

/-- E[f|E] is unchanged by replacing E with an a.e.-equal event. -/
theorem eventMean_congr_set {Ω} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) {E F : Set Ω} (hEF : E =ᵐ[μ] F) : eventMean μ f E = eventMean μ f F := by
  unfold eventMean
  rw [setIntegral_congr_set hEF, measure_congr hEF]

/-- Event means are linear for integrable potential outcomes (Section 2.1,
p. 574); this lemma does not replace population means by a finite sample. -/
theorem eventMean_sub {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (E : Set Ω) (hf : Integrable f μ) (hg : Integrable g μ) :
    eventMean μ (fun ω => f ω-g ω) E = eventMean μ f E-eventMean μ g E := by
  unfold eventMean
  rw [integral_sub hf.integrableOn hg.integrableOn, sub_div]


/-- Conditional-law and nested-event means are identical (the conditional
outcome-law interpretation in Proposition 1, p. 575). This lemma proves the
normalization explicitly, even if the inner B event has zero mass. The outer
conditioning event E has positive mass in a probability population. -/
theorem eventMean_eventLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (E : Set Ω) (hE : MeasurableSet E) (hpos : 0 < μ E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    eventMean (eventLaw μ f E) id B = eventMean μ f (E ∩ f ⁻¹' B) := by
  have hc : 0 < ((μ E)⁻¹).toReal := by
    rw [ENNReal.toReal_inv]
    exact inv_pos.mpr (ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top μ E))
  have hn : (∫ ω in E, B.indicator id (f ω) ∂μ) = ∫ ω in E ∩ f ⁻¹' B, f ω ∂μ := by
    rw [← integral_indicator hE,← integral_indicator (hE.inter (hf hB))]
    congr 1
    ext ω
    by_cases he : ω ∈ E <;> by_cases hb : f ω ∈ B <;> simp [indicator,he,hb]
  unfold eventMean eventLaw
  rw [← integral_indicator hB,integral_smul_measure,
    integral_map hf.aemeasurable ((measurable_id.indicator hB).aestronglyMeasurable),
    Measure.smul_apply,Measure.map_apply hf hB,Measure.restrict_apply (hf hB)]
  simp only [smul_eq_mul,ENNReal.toReal_mul]
  rw [hn,inter_comm (f ⁻¹' B) E]
  exact mul_div_mul_left _ _ (ne_of_gt hc)

/-- Independence identifies an arm-restricted mean with its unconditional
mean, the component identity behind Lemma 1, p. 574. -/
theorem independent_arm_mean {K d} (μ : Measure (State K d)) [IsProbabilityMeasure μ]
    (a : Fin K) (hZ : 0 < μ (armEvent a))
    (hI : IndepFun (potentialY a) assignment μ) :
    eventMean μ (potentialY a) (armEvent a) = ∫ ω, potentialY a ω ∂μ := by
  have hpos : 0 < (μ (armEvent a)).toReal := ENNReal.toReal_pos (ne_of_gt hZ) (measure_ne_top μ _)
  have hInd : IndepFun (potentialY a)
      (fun ω => (armEvent a).indicator (fun _ => (1 : ℝ)) ω) μ := by
    have he : (({a} : Set (Fin K)).indicator (fun _ => (1:ℝ))) ∘ assignment =
        (armEvent (d := d) a).indicator (fun _ => (1:ℝ)) := by
      funext ω
      by_cases hω : assignment ω = a <;>
        simp [Function.comp_def, Set.indicator, armEvent, hω]
    have hc := hI.comp measurable_id
      ((show Measurable (fun _ : Fin K => (1:ℝ)) from measurable_const).indicator
        (measurableSet_singleton a))
    change IndepFun (potentialY a)
      ((({a} : Set (Fin K)).indicator (fun _ => (1:ℝ))) ∘ assignment) μ at hc
    rw [he] at hc
    exact hc
  have hnum : (∫ ω in armEvent a, potentialY a ω ∂μ) =
      (∫ ω, potentialY a ω ∂μ)*(μ (armEvent a)).toReal := by
    rw [← integral_indicator (measurableSet_arm a)]
    calc
      (∫ ω, (armEvent a).indicator (potentialY a) ω ∂μ) =
          ∫ ω, potentialY a ω * (armEvent a).indicator (fun _ => (1:ℝ)) ω ∂μ := by
        congr 1
        ext ω
        by_cases hω : ω ∈ armEvent a <;> simp [hω]
      _ = (∫ ω, potentialY a ω ∂μ)*(∫ ω, (armEvent a).indicator (fun _ => (1:ℝ)) ω ∂μ) :=
        hInd.integral_fun_mul_eq_mul_integral (measurable_potentialY a).aestronglyMeasurable
          (measurable_const.indicator (measurableSet_arm a)).aestronglyMeasurable
      _ = _ := by
        simp only [integral_indicator_const (1:ℝ) (measurableSet_arm a),
          smul_eq_mul, mul_one, measureReal_def]
  unfold eventMean
  rw [hnum, mul_div_cancel_right₀ _ (ne_of_gt hpos)]

/-- Arm-by-arm conditional mean identity used in the corrected proof of
Corollary 1 (Appendix A, pp. 579–580). Independence of (Y(a),S) from Z
factorizes both the restricted integral and its positive event mass. -/
theorem pair_independent_selected_mean {K d} (μ : Measure (State K d)) [IsProbabilityMeasure μ]
    (a t : Fin K) (hS : 0 < μ passEvent) (hZ : 0 < μ (armEvent t))
    (hI : IndepFun (fun ω => (potentialY a ω, observedS ω)) assignment μ) :
    eventMean μ (potentialY a) (passEvent ∩ armEvent t) = eventMean μ (potentialY a) passEvent := by
  let mask : ℝ × Bool → ℝ := fun p => if p.2 then p.1 else 0
  have hm : Measurable mask := by
    exact Measurable.ite
      (show MeasurableSet {p : ℝ × Bool | p.2 = true} from
        measurable_snd (measurableSet_singleton true)) measurable_fst measurable_const
  have hI' : IndepFun ((passEvent (K := K) (d := d)).indicator (potentialY a))
      ((armEvent (d := d) t).indicator (fun _ => (1:ℝ))) μ := by
    have heM : mask ∘ (fun ω => (potentialY a ω,observedS ω)) =
        (passEvent (K := K) (d := d)).indicator (potentialY a) := by
      funext ω
      by_cases hω : observedS ω = true <;>
        simp [mask,Function.comp_def,Set.indicator,passEvent,hω]
    have heZ : (({t} : Set (Fin K)).indicator (fun _ => (1:ℝ))) ∘ assignment =
        (armEvent (d := d) t).indicator (fun _ => (1:ℝ)) := by
      funext ω
      by_cases hω : assignment ω = t <;>
        simp [Function.comp_def,Set.indicator,armEvent,hω]
    have hc := hI.comp hm
      ((show Measurable (fun _ : Fin K => (1:ℝ)) from measurable_const).indicator
        (measurableSet_singleton t))
    rw [heM,heZ] at hc
    exact hc
  have hnum : (∫ ω in passEvent ∩ armEvent t, potentialY a ω ∂μ) =
      (∫ ω in passEvent, potentialY a ω ∂μ)*(μ (armEvent t)).toReal := by
    rw [← integral_indicator (measurableSet_pass.inter (measurableSet_arm t))]
    calc
      (∫ ω, (passEvent ∩ armEvent t).indicator (potentialY a) ω ∂μ) =
          ∫ ω, passEvent.indicator (potentialY a) ω * (armEvent t).indicator (fun _ => (1:ℝ)) ω ∂μ := by
        congr 1
        ext ω
        by_cases hs : ω ∈ passEvent <;> by_cases hz : ω ∈ armEvent t <;> simp [hs,hz]
      _ = (∫ ω, passEvent.indicator (potentialY a) ω ∂μ)*
          (∫ ω, (armEvent t).indicator (fun _ => (1:ℝ)) ω ∂μ) :=
        hI'.integral_fun_mul_eq_mul_integral
          ((measurable_potentialY a).indicator measurableSet_pass).aestronglyMeasurable
          (measurable_const.indicator (measurableSet_arm t)).aestronglyMeasurable
      _ = _ := by
        rw [integral_indicator measurableSet_pass]
        simp only [integral_indicator_const (1:ℝ) (measurableSet_arm t),
          smul_eq_mul, mul_one, measureReal_def]
  have hIS : IndepFun observedS assignment μ := hI.comp measurable_snd measurable_id
  have hden := hIS.measure_inter_preimage_eq_mul {true} {t}
    (measurableSet_singleton true) (measurableSet_singleton t)
  change μ (passEvent ∩ armEvent t) = μ passEvent * μ (armEvent t) at hden
  have hs : (μ passEvent).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos (ne_of_gt hS) (measure_ne_top μ _))
  have hz : (μ (armEvent t)).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos (ne_of_gt hZ) (measure_ne_top μ _))
  unfold eventMean
  rw [hnum,hden,ENNReal.toReal_mul]
  field_simp

/-- Binary-stratum conditional independence follows by factorizing joint
(X,S) probabilities with Z and normalizing within S=b (Corollary 4, p. 576). -/
theorem pair_covariate_balance {K d} (μ : Measure (State K d)) [IsProbabilityMeasure μ]
    (hI : IndepFun (fun ω => (covariates ω,observedS ω)) assignment μ) : CovariateBalance μ := by
  intro b hb
  let E : Set (State K d) := {ω | observedS ω = b}
  have hE : MeasurableSet E := measurable_observedS (measurableSet_singleton b)
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hx : MeasurableSet (covariates (K := K) (d := d) ⁻¹' s) := measurable_covariates hs
  have hz : MeasurableSet (assignment (K := K) (d := d) ⁻¹' t) := measurable_assignment ht
  have hj := hI.measure_inter_preimage_eq_mul (s ×ˢ {b}) t (hs.prod (measurableSet_singleton b)) ht
  change μ ((covariates ⁻¹' s ∩ E) ∩ assignment ⁻¹' t) =
      μ (covariates ⁻¹' s ∩ E)*μ (assignment ⁻¹' t) at hj
  have hi : IndepFun observedS assignment μ := hI.comp measurable_snd measurable_id
  have hzE := hi.measure_inter_preimage_eq_mul {b} t (measurableSet_singleton b) ht
  change μ (E ∩ assignment ⁻¹' t) = μ E*μ (assignment ⁻¹' t) at hzE
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hx.inter hz), Measure.restrict_apply hx, Measure.restrict_apply hz]
  change (μ E)⁻¹*μ ((covariates ⁻¹' s ∩ assignment ⁻¹' t) ∩ E) =
    ((μ E)⁻¹*μ (covariates ⁻¹' s ∩ E))*((μ E)⁻¹*μ (assignment ⁻¹' t ∩ E))
  rw [inter_right_comm, hj, inter_comm (assignment ⁻¹' t) E, hzE]
  rw [← mul_assoc ((μ E)⁻¹) (μ E) _, ENNReal.inv_mul_cancel (ne_of_gt hb) (measure_ne_top μ E), one_mul]
  exact (mul_assoc _ _ _).symm


/-- T17, corrected Assumption 3, p. 574: under consistency and the printed
per-arm ignorability, positive observed passing is equivalent to positive
potential passing; in particular each bound denominator is positive. -/
theorem nonzero_passing_corrected {K d : ℕ} (μ : Measure (State K d))
    (hp : IsProbabilityMeasure μ) (h : Ignorability μ) :
    (∀ a, passingRate μ a = (μ (potentialPass a)).toReal) ∧
    (NonzeroPassing μ ↔ ∀ a, 0 < μ (potentialPass a)) := by
  letI := hp
  have heq (a : Fin K) : passingRate μ a = (μ (potentialPass a)).toReal := by
    have hi : IndepFun (potentialS a) assignment μ := (h.1 a).comp measurable_snd measurable_id
    have he := hi.measure_inter_preimage_eq_mul {true} {a} (measurableSet_singleton true) (measurableSet_singleton a)
    change μ (potentialPass a ∩ armEvent a) = μ (potentialPass a)*μ (armEvent a) at he
    have hpos := ENNReal.toReal_pos (ne_of_gt (h.2 a)) (measure_ne_top μ (armEvent a))
    unfold passingRate
    rw [pass_inter_arm, he, ENNReal.toReal_mul, mul_div_cancel_right₀ _ (ne_of_gt hpos)]
  refine ⟨heq, ?_⟩
  simp only [NonzeroPassing, heq, ENNReal.toReal_pos_iff, measure_lt_top, and_true]


/-- Finite-arm union bound behind corrected Proposition 1, p. 575 and
Appendix A, p. 580: all-pass mass is at least 1 minus the sum of the observed
failure rates. No sharpness or limiting construction is assumed. -/
theorem always_passer_union_bound {K d} (μ : Measure (State K d)) (h : Assumptions μ) :
    1-(∑ b : Fin K, (1-passingRate μ b)) ≤ (μ alwaysPass).toReal := by
  letI := h.1
  have hc : (alwaysPass (K := K) (d := d))ᶜ = ⋃ b : Fin K, (potentialPass b)ᶜ := by
    ext ω
    simp [alwaysPass,potentialPass]
  have hu := measureReal_iUnion_fintype_le (μ := μ) (fun b : Fin K => (potentialPass b)ᶜ)
  rw [← hc, measureReal_compl measurableSet_always] at hu
  have hr := (nonzero_passing_corrected μ h.1 h.2.1).1
  have hf (b : Fin K) : μ.real (potentialPass b)ᶜ = 1-passingRate μ b := by
    rw [measureReal_compl (measurableSet_potentialPass b)]
    simp only [hr b,measureReal_def,measure_univ,ENNReal.toReal_one]
  simp only [hf,measureReal_def,measure_univ,ENNReal.toReal_one] at hu
  linarith

/-- Corrected Proposition 1 (T4), p. 575: p_z(1-r_z)=L exactly, where
L=1-sum failure rates; r_z<1 iff L>0. This algebra uses only finite K and
positive passing, not a stronger joint-independence assumption. -/
theorem trimming_mass_identity {K d} (μ : Measure (State K d)) (h : NonzeroPassing μ)
    (a : Fin K) :
    passingRate μ a*(1-trimRatio μ a) = 1-∑ b : Fin K, (1-passingRate μ b) ∧
    (trimRatio μ a < 1 ↔ 0 < 1-∑ b : Fin K, (1-passingRate μ b)) := by
  have hs : (∑ b : Fin K, (1-passingRate μ b)) =
      (∑ b : Fin K, if b ≠ a then 1-passingRate μ b else 0)+(1-passingRate μ a) := by
    have hf : (∑ b : Fin K, (1-passingRate μ b)) =
        ∑ b : Fin K, ((if b ≠ a then 1-passingRate μ b else 0)+(if b=a then 1-passingRate μ b else 0)) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases he : b=a <;> simp [he]
    rw [hf,Finset.sum_add_distrib]
    simp
  have hi : passingRate μ a*(1-trimRatio μ a) = 1-∑ b : Fin K, (1-passingRate μ b) := by
    rw [hs]
    unfold trimRatio
    field_simp [ne_of_gt (h a)]
    <;> ring
  refine ⟨hi,?_⟩
  constructor
  · intro hr
    rw [← hi]
    exact mul_pos (h a) (sub_pos.mpr hr)
  · intro hl
    rw [← hi] at hl
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (h a)).mp hl)

/-- Corrected Proposition 1's else-branch criterion, p. 575 (T6):
r_z≥1 is equivalent to the sum of all arm passing rates being at most K−1.
This is an exact finite-arm identity, with positive focal passing. -/
theorem else_branch_criterion {K d} (μ : Measure (State K d))
    (h : NonzeroPassing μ) (a : Fin K) :
    (1 ≤ trimRatio μ a ↔ (∑ b : Fin K, passingRate μ b) ≤ (K:ℝ)-1) := by
  have hs : (∑ b : Fin K, (1-passingRate μ b)) =
      (K:ℝ)-∑ b : Fin K, passingRate μ b := by
    rw [Finset.sum_sub_distrib]
    simp
  have hi := (trimming_mass_identity μ h a).1
  rw [hs] at hi
  constructor
  · intro hr
    have hh := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (h a)) (sub_nonpos.mpr hr)
    linarith
  · intro hr
    by_contra hn
    have hlt : trimRatio μ a < 1 := lt_of_not_ge hn
    have hh := mul_pos (h a) (sub_pos.mpr hlt)
    linarith

/-- T19, Lemma 1, p. 574: observed arm means identify mean potential outcomes,
and differences identify the intent-to-treat effect, under Assumptions 1–2. -/
theorem lemma_one {K d : ℕ} (μ : Measure (State K d))
    (hp : IsProbabilityMeasure μ) (h : Ignorability μ)
    (a b : Fin K) (ha : Integrable (potentialY a) μ) (hb : Integrable (potentialY b) μ) :
    eventMean μ observedY (armEvent a) = ∫ ω, potentialY a ω ∂μ ∧
    eventMean μ observedY (armEvent b) = ∫ ω, potentialY b ω ∂μ ∧
    eventMean μ observedY (armEvent a) - eventMean μ observedY (armEvent b) =
      ∫ ω, (potentialY a ω - potentialY b ω) ∂μ := by
  letI := hp
  have hid (c : Fin K) : eventMean μ observedY (armEvent c) = ∫ ω, potentialY c ω ∂μ := by
    have he : eventMean μ observedY (armEvent c) = eventMean μ (potentialY c) (armEvent c) := by
      unfold eventMean
      congr 1
      apply setIntegral_congr_fun (measurableSet_arm c)
      intro ω hω
      simp only [armEvent, mem_setOf_eq] at hω
      simp [observedY, hω]
    rw [he]
    exact independent_arm_mean μ c (h.2 c) ((h.1 c).comp measurable_fst measurable_id)
  refine ⟨hid a, hid b, ?_⟩
  rw [hid a, hid b, integral_sub ha hb]


/-- T20, Corollary 2, p. 574: treatment-invariant passing status almost surely
implies independence of observed passing and assignment. -/
theorem corollary_two {K d : ℕ} (μ : Measure (State K d))
    (hp : IsProbabilityMeasure μ) (h : Ignorability μ) (hC : μ commonStatus = 1) :
    IndepFun observedS assignment μ := by
  letI := hp
  by_cases hK : Nonempty (Fin K)
  · let a : Fin K := Classical.choice hK
    exact ((h.1 a).comp measurable_snd measurable_id).congr
      (common_status_ae μ hC a).symm (Filter.EventuallyEq.refl _ _)
  · have hzero : μ univ = 0 := by
      have hu : (univ : Set (State K d)) = ∅ := by
        ext ω
        exact False.elim (hK ⟨assignment ω⟩)
      simp [hu]
    have hne : μ univ = 1 := measure_univ
    exact False.elim (by rw [hzero] at hne; exact zero_ne_one hne)


/-- T8, corrected arm-by-arm proof of Corollary 1, pp. 579–580: common status,
per-arm pair independence, positive passing, equal conditioning events and all
four conditional means. No joint potential-vector independence is asserted. -/
theorem corollary_one_corrected_proof {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (hC : μ commonStatus = 1)
    (a : Fin K) (ha : Integrable (potentialY a) μ) :
    (observedS =ᵐ[μ] potentialS a) ∧
    IndepFun (fun ω => (potentialY a ω, observedS ω)) assignment μ ∧
    (∀ t, passingRate μ t = (μ passEvent).toReal ∧ 0 < passingRate μ t) ∧
    (passEvent =ᵐ[μ] alwaysPass) ∧
    eventMean μ observedY (passEvent ∩ armEvent a) =
      eventMean μ (potentialY a) (passEvent ∩ armEvent a) ∧
    eventMean μ (potentialY a) (passEvent ∩ armEvent a) = eventMean μ (potentialY a) passEvent ∧
    eventMean μ (potentialY a) passEvent = eventMean μ (potentialY a) alwaysPass := by
  letI := h.1
  have hSa : observedS =ᵐ[μ] potentialS a := common_status_ae μ hC a
  have hPair : IndepFun (fun ω => (potentialY a ω, observedS ω)) assignment μ := by
    apply (h.2.1.1 a).congr _ (Filter.EventuallyEq.refl _ _)
    filter_upwards [hSa] with ω hω
    simp [hω]
  have hE (t : Fin K) : passEvent =ᵐ[μ] potentialPass t := by
    filter_upwards [common_status_ae μ hC t] with ω hω
    simp [passEvent, potentialPass, hω]
  have hR := nonzero_passing_corrected μ h.1 h.2.1
  have hRate (t : Fin K) : passingRate μ t = (μ passEvent).toReal ∧ 0 < passingRate μ t := by
    exact ⟨(hR.1 t).trans (congrArg ENNReal.toReal (measure_congr (hE t)).symm), h.2.2 t⟩
  have hS : 0 < μ passEvent := (ENNReal.toReal_pos_iff.mp (by rw [← (hRate a).1]; exact (hRate a).2)).1
  have hAlways : passEvent =ᵐ[μ] alwaysPass := by
    have hCom : ∀ᵐ ω ∂μ, ω ∈ commonStatus := (mem_ae_iff_prob_eq_one measurableSet_common).mpr hC
    filter_upwards [hCom] with ω hω
    apply propext
    constructor
    · intro hs b
      change potentialS b ω = true
      change potentialS (assignment ω) ω = true at hs
      rw [hω b (assignment ω)]
      exact hs
    · intro hs
      exact hs (assignment ω)
  have hobs : eventMean μ observedY (passEvent ∩ armEvent a) =
      eventMean μ (potentialY a) (passEvent ∩ armEvent a) := by
    unfold eventMean
    congr 1
    apply setIntegral_congr_fun (measurableSet_pass.inter (measurableSet_arm a))
    intro ω hω
    have hz := hω.2
    simp only [armEvent, mem_setOf_eq] at hz
    simp [observedY, hz]
  exact ⟨hSa,hPair,hRate,hAlways,hobs,
    pair_independent_selected_mean μ a a hS (h.2.1.2 a) hPair,
    eventMean_congr_set μ (potentialY a) hAlways⟩

/-- T18, corrected Corollary 1, p. 574: under almost-sure treatment-invariant
passing status, the contrast after dropping equals the average effect among
always-passers. The printed stray bracket is removed. -/
theorem corollary_one {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (hC : μ commonStatus = 1) (a b : Fin K)
    (ha : Integrable (potentialY a) μ)
    (hb : Integrable (potentialY b) μ) :
    eventMean μ observedY (passEvent ∩ armEvent a) -
      eventMean μ observedY (passEvent ∩ armEvent b) =
    eventMean μ (fun ω => potentialY a ω - potentialY b ω) alwaysPass := by
  have hA := corollary_one_corrected_proof μ h hC a ha
  have hB := corollary_one_corrected_proof μ h hC b hb
  have ea := hA.2.2.2.2.1.trans (hA.2.2.2.2.2.1.trans hA.2.2.2.2.2.2)
  have eb := hB.2.2.2.2.1.trans (hB.2.2.2.2.2.1.trans hB.2.2.2.2.2.2)
  rw [ea,eb,eventMean_sub μ (potentialY a) (potentialY b) alwaysPass ha hb]

/-- T22, Corollary 4, p. 576: treatment-invariant passing status implies
conditional covariate balance, under Assumptions 1 and 4. -/
theorem corollary_four {K d : ℕ} (μ : Measure (State K d))
    (hp : IsProbabilityMeasure μ) (h : CovariateIgnorability μ) (hC : μ commonStatus = 1) :
    CovariateBalance μ := by
  letI := hp
  by_cases hK : Nonempty (Fin K)
  · let a : Fin K := Classical.choice hK
    have hi : IndepFun (fun ω => (covariates ω,potentialS a ω)) assignment μ := by
      simpa [Function.comp_def] using (h.1 a).comp
        (show Measurable (fun p : ℝ × Bool × (Fin d → ℝ) => (p.2.2,p.2.1)) by fun_prop) measurable_id
    have hi' : IndepFun (fun ω => (covariates ω,observedS ω)) assignment μ := by
      apply hi.congr _ (Filter.EventuallyEq.refl _ _)
      filter_upwards [common_status_ae μ hC a] with ω hω
      simp [hω]
    exact pair_covariate_balance μ hi'
  · have hu : (univ : Set (State K d)) = ∅ := by
      ext ω
      exact False.elim (hK ⟨assignment ω⟩)
    have hz : μ univ = 0 := by simp [hu]
    exact False.elim (by simpa using hz)

/-- Appendix A, p. 580: “Define U=1 if S(2)=...=S(K)=1, else ... U=0.”
For a general focal arm, U means that every *other* arm passes. -/
def otherPass {K d} (a : Fin K) : Set (State K d) := {ω | ∀ b, b ≠ a → potentialS b ω = true}
/-- Appendix A, p. 580: “sum Pr[S(k)=0] / Pr[S(1)=1]”, generalized
to a focal arm a; its denominator is the focal potential passing mass. -/
noncomputable def potentialTrim {K d} (μ : Measure (State K d)) (a : Fin K) : ℝ :=
  (∑ b : Fin K, if b ≠ a then (μ {ω | potentialS b ω = false}).toReal else 0) /
    (μ (potentialPass a)).toReal

/-- Exact conditional union bound in corrected Appendix A, p. 580 (T14(ii)):
among focal passers, the probability that some other arm fails is bounded by
the sum of the other potential failure probabilities divided by focal passing
probability. This uses no assignment or full-vector independence assumption. -/
theorem other_arm_conditional_union_bound {K d} (μ : Measure (State K d))
    (hp : IsProbabilityMeasure μ) (a : Fin K) (hpass : 0 < μ (potentialPass a)) :
    (μ ((otherPass a)ᶜ ∩ potentialPass a)).toReal / (μ (potentialPass a)).toReal ≤
      potentialTrim μ a := by
  letI := hp
  let F : Fin K → Set (State K d) := fun b => if b ≠ a then (potentialPass b)ᶜ else ∅
  have hsub : (otherPass a)ᶜ ∩ potentialPass a ⊆ ⋃ b : Fin K, F b := by
    intro ω hω
    have hn := hω.1
    change ¬ (∀ b, b ≠ a → potentialS b ω = true) at hn
    push_neg at hn
    rcases hn with ⟨b,hb,hs⟩
    apply Set.mem_iUnion.mpr
    refine ⟨b,?_⟩
    simp [F,hb,potentialPass,hs]
  have hf (b : Fin K) : (potentialPass (d := d) b)ᶜ =
      {ω | potentialS b ω = false} := by
    ext ω
    cases hs : potentialS b ω <;> simp [potentialPass,hs]
  have hbound : (μ ((otherPass a)ᶜ ∩ potentialPass a)).toReal ≤
      ∑ b : Fin K, if b ≠ a then (μ {ω | potentialS b ω = false}).toReal else 0 := by
    calc
      _ ≤ μ.real (⋃ b : Fin K, F b) := measureReal_mono hsub
      _ ≤ ∑ b : Fin K, μ.real (F b) := measureReal_iUnion_fintype_le F
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hba : b = a <;> simp [F,hba,hf,measureReal_def]
  unfold potentialTrim
  exact div_le_div_of_nonneg_right hbound ENNReal.toReal_nonneg

/-- The all-pass event equals U=1 intersect S(a)=1 for any focal arm,
Appendix A, p. 580; this is a pointwise set identity. -/
theorem always_pass_focal {K d} (a : Fin K) :
    (alwaysPass : Set (State K d)) = otherPass a ∩ potentialPass a := by
  ext ω
  constructor
  · intro hω
    exact ⟨fun b _ => hω b,hω a⟩
  · rintro ⟨hU,ha⟩ b
    by_cases hb : b=a
    · simpa [potentialPass,hb] using ha
    · exact hU b hb

/-- Corrected final display of Proposition 1's proof, Appendix A, p. 580:
the potential failure-probability sum over the focal passing probability
is exactly the observable trimming ratio, with the focal denominator. -/
theorem potential_trim_consistency {K d} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) : potentialTrim μ a = trimRatio μ a := by
  letI := h.1
  have hr := (nonzero_passing_corrected μ h.1 h.2.1).1
  have hf (b : Fin K) : (μ {ω | potentialS b ω = false}).toReal = 1-passingRate μ b := by
    have he : {ω : State K d | potentialS b ω = false} = (potentialPass b)ᶜ := by
      ext ω
      cases hs : potentialS b ω <;> simp [potentialPass,hs]
    rw [he, ← measureReal_def,measureReal_compl (measurableSet_potentialPass b),
      probReal_univ,measureReal_def,← hr b]
  simp only [potentialTrim,hf,← hr a,trimRatio]

/-- Fixed passer distribution and nonpassing proportion p, Appendix A, p. 580:
all joint laws of (Y(1),U) with this Y marginal and Pr(U=0)=p. -/
def TailCoupling (F : Measure ℝ) (p : ℝ) (γ : Measure (ℝ × Bool)) : Prop :=
  IsProbabilityMeasure γ ∧ γ.map Prod.fst = F ∧ (γ {ω | ω.2 = false}).toReal = p
/-- Corrected Appendix A, p. 580, T14: mean conditional on the upper
tail “Y(1) >= Q(p)” of the specified potential passer law. -/
noncomputable def tailUpper (F : Measure ℝ) (p : ℝ) : ℝ :=
  eventMean F id {y | quantile F p ≤ (y : EReal)}

/-- Fixed-mass rearrangement behind corrected Appendix A, p. 580 (T14):
an upper threshold event maximizes the integral and conditional mean among
all measurable selection events of its probability. This proves the exact
inequality independently of the quantile mass and sharpness constructions. -/
theorem upper_tail_fixed_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hi : Integrable f μ) (E : Set Ω)
    (hE : MeasurableSet E) (q : ℝ)
    (hmass : μ E = μ {ω | q ≤ f ω}) (hpos : 0 < μ E) :
    (∫ ω in E, f ω ∂μ) ≤ ∫ ω in {ω | q ≤ f ω}, f ω ∂μ ∧
    eventMean μ f E ≤ eventMean μ f {ω | q ≤ f ω} := by
  have hg : Integrable (fun ω => f ω-q) μ := hi.sub (integrable_const q)
  have hgm : StronglyMeasurable (fun ω => f ω-q) :=
    (hf.sub measurable_const).stronglyMeasurable
  have hcut : {ω | 0 ≤ f ω-q} = {ω | q ≤ f ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq,sub_nonneg]
  have hbound := setIntegral_le_nonneg hE hgm hg
  rw [hcut,integral_sub hi.integrableOn (integrable_const q),
    integral_sub hi.integrableOn (integrable_const q),
    setIntegral_const,setIntegral_const] at hbound
  simp only [smul_eq_mul,measureReal_def,hmass] at hbound
  have hIntegral : (∫ ω in E, f ω ∂μ) ≤ ∫ ω in {ω | q ≤ f ω}, f ω ∂μ := by
    linarith
  refine ⟨hIntegral,?_⟩
  unfold eventMean
  rw [← hmass]
  exact div_le_div_of_nonneg_right hIntegral ENNReal.toReal_nonneg


/-- Corrected Proposition 1 proof, Appendix A, p. 580: the conditional
potential outcome law given its own passing event equals the observed
outcome law given passing and focal assignment. Only per-arm pair
ignorability is used, and the equality is of actual probability measures. -/
theorem conditional_law_consistency {K d} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) :
    eventLaw μ (potentialY a) (potentialPass a) = passerLaw μ a := by
  letI := h.1
  have hI : IndepFun (potentialS a) assignment μ :=
    (h.2.1.1 a).comp measurable_snd measurable_id
  have hden := hI.measure_inter_preimage_eq_mul {true} {a}
    (measurableSet_singleton true) (measurableSet_singleton a)
  change μ (potentialPass a ∩ armEvent a) = μ (potentialPass a)*μ (armEvent a) at hden
  have hmap : (μ.restrict (passEvent ∩ armEvent a)).map observedY =
      (μ.restrict (passEvent ∩ armEvent a)).map (potentialY a) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (measurableSet_pass.inter (measurableSet_arm a))] with ω hω
    have hz := hω.2
    change assignment ω = a at hz
    simp [observedY,hz]
  unfold passerLaw eventLaw
  rw [hmap,pass_inter_arm,hden]
  ext s hs
  have hy := measurable_potentialY (d := d) a
  rw [Measure.smul_apply,Measure.smul_apply,smul_eq_mul,smul_eq_mul,
    Measure.map_apply hy hs,Measure.map_apply hy hs,
    Measure.restrict_apply (hy hs),Measure.restrict_apply (hy hs)]
  have hn := (h.2.1.1 a).measure_inter_preimage_eq_mul (s ×ˢ {true}) {a}
    (hs.prod (measurableSet_singleton true)) (measurableSet_singleton a)
  change μ ((potentialY a ⁻¹' s ∩ potentialPass a) ∩ armEvent a) =
    μ (potentialY a ⁻¹' s ∩ potentialPass a)*μ (armEvent a) at hn
  rw [← inter_assoc,hn,
    ENNReal.mul_inv (Or.inr (measure_ne_top μ _)) (Or.inl (measure_ne_top μ _))]
  calc
    (μ (potentialPass a))⁻¹*μ (potentialY a ⁻¹' s ∩ potentialPass a) =
        ((μ (potentialPass a))⁻¹*μ (potentialY a ⁻¹' s ∩ potentialPass a))*
          ((μ (armEvent a))⁻¹*μ (armEvent a)) := by
      rw [ENNReal.inv_mul_cancel (ne_of_gt (h.2.1.2 a)) (measure_ne_top μ _),mul_one]
    _ = _ := by ring

/-- Assumption 3, p. 574, gives positive mass to the actual selected
arm event, so its conditional-law normalization is nondegenerate. -/
theorem passing_event_positive {K d} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) : 0 < μ (passEvent ∩ armEvent a) := by
  letI := h.1
  have hz : 0 < (μ (armEvent a)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (h.2.1.2 a)) (measure_ne_top μ _)
  have hn : 0 < (μ (passEvent ∩ armEvent a)).toReal := by
    exact (div_pos_iff_of_pos_right hz).mp (h.2.2 a)
  exact (ENNReal.toReal_pos_iff.mp hn).1

/-- Atomlessness of observed Y, Proposition 1, p. 575, passes to its
conditional outcome distribution among focal-arm passers. -/
theorem passer_atomless {K d} (μ : Measure (State K d)) (a : Fin K)
    (hc : Atomless (μ.map observedY)) : Atomless (passerLaw μ a) := by
  intro x
  have hy : MeasurableSet (observedY (K := K) (d := d) ⁻¹' {x}) :=
    measurable_observedY (measurableSet_singleton x)
  have hz : μ (observedY ⁻¹' {x}) = 0 := by
    rw [← Measure.map_apply measurable_observedY (measurableSet_singleton x)]
    exact hc x
  have hzr : μ (observedY ⁻¹' {x} ∩ (passEvent ∩ armEvent a)) = 0 :=
    measure_mono_null inter_subset_left hz
  unfold passerLaw eventLaw
  rw [Measure.smul_apply,Measure.map_apply measurable_observedY (measurableSet_singleton x),
    Measure.restrict_apply hy,hzr]
  simp

/-- Corrected Proposition 1, p. 575: its population tail means are the
same tail means computed from the conditional passer outcome law. This
normalization identity is independent of the validity/sharpness proof. -/
theorem passer_tail_mean_formula {K d} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) :
    lowerBound μ a = eventMean (passerLaw μ a) id
      {y | (y : EReal) ≤ quantile (passerLaw μ a) (1-trimRatio μ a)} ∧
    upperBound μ a = tailUpper (passerLaw μ a) (trimRatio μ a) := by
  letI := h.1
  constructor
  · exact (eventMean_eventLaw μ observedY measurable_observedY (passEvent ∩ armEvent a)
      (measurableSet_pass.inter (measurableSet_arm a)) (passing_event_positive μ h a)
      {y | (y : EReal) ≤ quantile (passerLaw μ a) (1-trimRatio μ a)}
      (measurableSet_le measurable_coe_real_ereal measurable_const)).symm
  · exact (eventMean_eventLaw μ observedY measurable_observedY (passEvent ∩ armEvent a)
      (measurableSet_pass.inter (measurableSet_arm a)) (passing_event_positive μ h a)
      {y | quantile (passerLaw μ a) (trimRatio μ a) ≤ (y : EReal)}
      (measurableSet_le measurable_const measurable_coe_real_ereal)).symm


/-- Finite laws used for the paper's Appendix A witnesses (p. 580) and the
T7 proof-step counterexample. This is an actual finite weighted probability
measure when the displayed masses are nonnegative and sum to one. -/
noncomputable def finiteLaw {n K d : ℕ} (atoms : Fin n → State K d)
    (mass : Fin n → ℝ≥0∞) : Measure (State K d) :=
  Measure.sum (fun i => mass i • Measure.dirac (atoms i))

/-- Finite probability of an event is the sum of its atom masses, for the
Appendix A finite witnesses (p. 580); no atom is replaced by a zero measure. -/
theorem finiteLaw_apply {n K d} (atoms : Fin n → State K d) (mass : Fin n → ℝ≥0∞)
    (E : Set (State K d)) :
    finiteLaw atoms mass E = ∑ i : Fin n, if atoms i ∈ E then mass i else 0 := by
  simp [finiteLaw, Measure.sum_apply_of_countable, tsum_fintype, Measure.smul_apply, indicator]

/-- Finite-law expectation is the weighted sum of the potential responses,
Appendix A, p. 580. Every displayed atom mass is finite. -/
theorem finiteLaw_integral {n K d} (atoms : Fin n → State K d) (mass : Fin n → ℝ≥0∞)
    (hf : ∀ i, mass i ≠ ⊤) (f : State K d → ℝ) :
    (∫ ω, f ω ∂finiteLaw atoms mass) = ∑ i : Fin n, (mass i).toReal*f (atoms i) := by
  simpa [finiteLaw, tsum_fintype, smul_eq_mul] using integral_sum_dirac (x := atoms) (c := mass) (f := f) hf


/-- Any property holding on all displayed atoms holds a.s. in their finite
law, including zero unit effects and a constant covariate (Appendix A). -/
theorem finiteLaw_ae {n K d} (atoms : Fin n → State K d) (mass : Fin n → ℝ≥0∞)
    (P : State K d → Prop) (hP : ∀ i, P (atoms i)) : ∀ᵐ ω ∂finiteLaw atoms mass, P ω := by
  apply Measure.ae_sum_iff.mpr
  intro i
  by_cases hm : mass i = 0
  · simp [hm]
  · simpa [Measure.ae_ennreal_smul_measure_iff hm, ae_dirac_eq] using hP i

/-- Finite laws with nonnegative real masses summing to one are probability
measures; used for every randomization probability in corrected T16. -/
theorem finiteLaw_probability {n K d} (atoms : Fin n → State K d) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∑ i, r i = 1) :
    IsProbabilityMeasure (finiteLaw atoms (fun i => ENNReal.ofReal (r i))) := by
  constructor
  rw [finiteLaw_apply]
  simp only [mem_univ, if_true]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i), hs, ENNReal.ofReal_one]

/-- The real event mass of a finite law is the sum of the given real atom
weights in the event, with no hidden denominator or normalization. -/
theorem finiteLaw_apply_real {n K d} (atoms : Fin n → State K d) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (E : Set (State K d)) :
    (finiteLaw atoms (fun i => ENNReal.ofReal (r i)) E).toReal =
      ∑ i : Fin n, if atoms i ∈ E then r i else 0 := by
  rw [finiteLaw_apply, ENNReal.toReal_sum (by intro i _; split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases he : atoms i ∈ E <;> simp [he,ENNReal.toReal_ofReal (hr i)]

/-- Exact finite conditional means with real nonnegative atom masses,
Appendix A, p. 580; this version is useful for symbolic assignment q. -/
theorem finiteLaw_mean_real {n K d} (atoms : Fin n → State K d) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (f : State K d → ℝ) (E : Set (State K d))
    (hE : MeasurableSet E) :
    eventMean (finiteLaw atoms (fun i => ENNReal.ofReal (r i))) f E =
      (∑ i : Fin n, if atoms i ∈ E then r i*f (atoms i) else 0) /
        (∑ i : Fin n, if atoms i ∈ E then r i else 0) := by
  unfold eventMean
  rw [← integral_indicator hE,finiteLaw_integral atoms _ (by intro i; exact ENNReal.ofReal_ne_top),
    finiteLaw_apply_real atoms r hr E]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases he : atoms i ∈ E <;> simp [he,indicator,ENNReal.toReal_ofReal (hr i)]

/-- T7 witness, P010-E009: the four equiprobable primitive states
are (Z,Y1,Y2,S1,S2)=(1,0,0,1,1),(1,1,1,1,1),(2,0,1,1,1),(2,1,0,1,1).
The covariate vector is empty. -/
def jointStepAtoms : Fin 4 → State 2 0 :=
  ![(![0,0], ![true,true], 0, fun _ => 0),
    (![1,1], ![true,true], 0, fun _ => 0),
    (![0,1], ![true,true], 1, fun _ => 0),
    (![1,0], ![true,true], 1, fun _ => 0)]
/-- T7, P010-E009: four states, each of probability 1/4,
refuting the joint-independence step on pp. 579–580. -/
noncomputable def jointStepLaw : Measure (State 2 0) := finiteLaw jointStepAtoms (fun _ => ENNReal.ofReal (1/4:ℝ))

/-- T7, counterexample to the joint-independence inference in the proof of
Corollary 1, pp. 579–580: all standing assumptions and common status hold,
but joint-vector independence fails with masses 1/4 versus 1/8.
The corollary itself continues to hold, with both arm means 1/2 and effect 0. -/
theorem joint_independence_step_counterexample :
    Assumptions jointStepLaw ∧ jointStepLaw commonStatus = 1 ∧
    jointStepLaw alwaysPass = 1 ∧
    ¬ IndepFun (fun ω : State 2 0 => (ω.1, observedS ω)) assignment jointStepLaw ∧
    jointStepLaw {ω | potentialY 0 ω = 0 ∧ potentialY 1 ω = 0 ∧
      observedS ω = true ∧ assignment ω = 0} = 1/4 ∧
    jointStepLaw {ω | potentialY 0 ω = 0 ∧ potentialY 1 ω = 0 ∧ observedS ω = true} *
      jointStepLaw (armEvent 0) = 1/8 ∧
    eventMean jointStepLaw observedY (passEvent ∩ armEvent 0) = 1/2 ∧
    eventMean jointStepLaw observedY (passEvent ∩ armEvent 1) = 1/2 ∧
    eventMean jointStepLaw (fun ω => potentialY 0 ω - potentialY 1 ω) alwaysPass = 0 := by
  let r : Fin 4 → ℝ := fun _ => 1/4
  have hr : ∀ i, 0 ≤ r i := by intro i; norm_num [r]
  have hp : IsProbabilityMeasure jointStepLaw :=
    finiteLaw_probability jointStepAtoms r hr (by norm_num [r,Fin.sum_univ_succ])
  letI := hp
  have hevent (E : Set (State 2 0)) : (jointStepLaw E).toReal =
      ∑ i : Fin 4, if jointStepAtoms i ∈ E then r i else 0 := by
    exact finiteLaw_apply_real jointStepAtoms r hr E
  have hi : Ignorability jointStepLaw := by
    constructor
    · intro a
      rw [indepFun_iff_measure_inter_preimage_eq_mul]
      intro s t hs ht
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
        (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
      rw [ENNReal.toReal_mul]
      simp only [hevent]
      fin_cases a
      all_goals
        by_cases h0 : ((0:ℝ),true) ∈ s <;>
        by_cases h1 : ((1:ℝ),true) ∈ s <;>
        by_cases ht0 : (0:Fin 2) ∈ t <;>
        by_cases ht1 : (1:Fin 2) ∈ t <;>
        norm_num [jointStepAtoms, potentialY, potentialS, assignment,r,
          Fin.sum_univ_succ,h0,h1,ht0,ht1]
    · intro a
      apply (ENNReal.toReal_pos_iff.mp ?_).1
      rw [hevent]
      fin_cases a <;> norm_num [jointStepAtoms,armEvent,assignment,r,Fin.sum_univ_succ]
  have hn : NonzeroPassing jointStepLaw := by
    intro a
    rw [(nonzero_passing_corrected jointStepLaw hp hi).1 a,hevent]
    fin_cases a <;> norm_num [jointStepAtoms,potentialPass,potentialS,r,Fin.sum_univ_succ]
  have hc : jointStepLaw commonStatus = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    rw [hevent]
    norm_num [jointStepAtoms,commonStatus,potentialS,r,Fin.sum_univ_succ,Fin.forall_fin_succ]
  have ha : jointStepLaw alwaysPass = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    rw [hevent]
    norm_num [jointStepAtoms,alwaysPass,potentialS,r,Fin.sum_univ_succ,Fin.forall_fin_succ]
  have hbad : ¬ IndepFun (fun ω : State 2 0 => (ω.1, observedS ω)) assignment jointStepLaw := by
    intro hh
    have he := hh.measure_inter_preimage_eq_mul
      {((![0,0] : Fin 2 → ℝ),true)} {(0:Fin 2)}
      (measurableSet_singleton ((![0,0] : Fin 2 → ℝ),true)) (measurableSet_singleton (0:Fin 2))
    have heR := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_mul] at heR
    simp only [hevent] at heR
    norm_num [jointStepAtoms,observedS,potentialS,assignment,r,Fin.sum_univ_succ,
      funext_iff,Fin.forall_fin_succ] at heR
  refine ⟨⟨hp,hi,hn⟩,hc,ha,hbad,?_,?_,?_,?_,?_⟩
  · apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    rw [hevent]
    norm_num [jointStepAtoms,potentialY,observedS,potentialS,assignment,r,
      Fin.sum_univ_succ,ENNReal.toReal_div]
  · apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) (by norm_num)).mp
    rw [ENNReal.toReal_mul]
    simp only [hevent]
    norm_num [jointStepAtoms,potentialY,observedS,potentialS,assignment,armEvent,r,
      Fin.sum_univ_succ,ENNReal.toReal_div]
  · change eventMean (finiteLaw jointStepAtoms (fun i => ENNReal.ofReal (r i))) _ _ = _
    rw [finiteLaw_mean_real _ r hr _ _ (measurableSet_pass.inter (measurableSet_arm 0))]
    norm_num [jointStepAtoms,potentialY,observedY,observedS,potentialS,assignment,
      armEvent,passEvent,r,Fin.sum_univ_succ]
  · change eventMean (finiteLaw jointStepAtoms (fun i => ENNReal.ofReal (r i))) _ _ = _
    rw [finiteLaw_mean_real _ r hr _ _ (measurableSet_pass.inter (measurableSet_arm 1))]
    norm_num [jointStepAtoms,potentialY,observedY,observedS,potentialS,assignment,
      armEvent,passEvent,r,Fin.sum_univ_succ]
  · change eventMean (finiteLaw jointStepAtoms (fun i => ENNReal.ofReal (r i))) _ _ = _
    rw [finiteLaw_mean_real _ r hr _ _ measurableSet_always]
    norm_num [jointStepAtoms,potentialY,potentialS,alwaysPass,r,
      Fin.forall_fin_succ,Fin.sum_univ_succ]

/-- Appendix A, p. 580, proof of Corollary 3: “f ... 1/3” on each of
(Y1,Y2,S1,S2)=(1,1,0,1),(0,0,1,0),(0,0,1,1). Independent assignment has
Pr(Z=1)=q, for arbitrary 0<q<1, as required by corrected T16. -/
def selectionAtoms : Fin 6 → State 2 1 :=
  ![(![1,1], ![false,true], 0, fun _ => 0),
    (![0,0], ![true,false], 0, fun _ => 0),
    (![0,0], ![true,true], 0, fun _ => 0),
    (![1,1], ![false,true], 1, fun _ => 0),
    (![0,0], ![true,false], 1, fun _ => 0),
    (![0,0], ![true,true], 1, fun _ => 0)]
/-- Appendix A, p. 580: “f ... 1/3” on each of the three principal
strata, with independent assignment having probability q for paper arm 1. -/
noncomputable def selectionLaw (q : ℝ) : Measure (State 2 1) :=
  finiteLaw selectionAtoms (fun i => ENNReal.ofReal (if i.val < 3 then q/3 else (1-q)/3))

/-- The three principal strata in Corollary 3's printed witness are sampled
independently of treatment, for every 0<q<1 (Appendix A, p. 580). Any variable
having the same values in the two assignment copies of each stratum is
independent of assignment. This proves full Borel independence, not just means. -/
theorem selection_independent {B : Type*} [MeasurableSpace B] (q : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (f : State 2 1 → B) (v₀ v₁ v₂ : B)
    (hv : ∀ i : Fin 6, f (selectionAtoms i) = (![v₀,v₁,v₂,v₀,v₁,v₂] : Fin 6 → B) i) :
    IndepFun f assignment (selectionLaw q) := by
  have hqc : 0 < 1-q := sub_pos.mpr hq1
  have hm (i : Fin 6) : 0 ≤ (if i.val < 3 then q/3 else (1-q)/3) := by
    split_ifs <;> positivity
  have hp : IsProbabilityMeasure (selectionLaw q) := finiteLaw_probability selectionAtoms _ hm (by
    norm_num [Fin.sum_univ_succ]
    ring)
  letI := hp
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  simp only [selectionLaw, finiteLaw_apply_real _ _ hm]
  simp only [mem_inter_iff, mem_preimage, hv]
  by_cases h₀ : v₀ ∈ s <;> by_cases h₁ : v₁ ∈ s <;> by_cases h₂ : v₂ ∈ s <;>
    by_cases ht₀ : (0:Fin 2) ∈ t <;> by_cases ht₁ : (1:Fin 2) ∈ t <;>
    norm_num [selectionAtoms, assignment, Fin.sum_univ_succ, h₀,h₁,h₂,ht₀,ht₁] <;> ring

/-- A constant pre-treatment covariate is balanced within every positive
passing/failing stratum, as used in the proof of Corollary 5, p. 576. -/
theorem constant_covariate_balance {K d} (μ : Measure (State K d)) [IsProbabilityMeasure μ]
    (x : Fin d → ℝ) (hx : covariates =ᵐ[μ] fun _ => x) : CovariateBalance μ := by
  intro b hb
  letI : IsProbabilityMeasure ((μ {ω | observedS ω = b})⁻¹ • μ.restrict {ω | observedS ω = b}) :=
    cond_isProbabilityMeasure (ne_of_gt hb)
  have hc : covariates =ᵐ[(μ {ω | observedS ω = b})⁻¹ • μ.restrict {ω | observedS ω = b}] fun _ => x :=
    Measure.ae_smul_measure hx.restrict _
  exact (indepFun_const_left x assignment).congr hc.symm (Filter.EventuallyEq.refl _ _)

/-- T16, corrected closing calculation of Corollary 3's proof, Appendix A,
p. 580: all standing assumptions hold for every 0<q<1; passing rates are 2/3
and S independent of Z; every unit has zero effect and every named stratum
has effect mean zero; selected means are 0 and 1/2, so the contrast is +1/2. -/
theorem selection_counterexample_corrected (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    Assumptions (selectionLaw q) ∧
    CovariateIgnorability (selectionLaw q) ∧ CovariateBalance (selectionLaw q) ∧
    selectionLaw q alwaysPass = 1/3 ∧
    (∀ a, passingRate (selectionLaw q) a = 2/3) ∧
    IndepFun observedS assignment (selectionLaw q) ∧
    (∀ᵐ ω ∂selectionLaw q, potentialY 1 ω - potentialY 0 ω = 0) ∧
    (∫ ω, (if potentialS 1 ω then (1:ℝ) else 0) -
      (if potentialS 0 ω then (1:ℝ) else 0) ∂selectionLaw q) = 0 ∧
    eventMean (selectionLaw q) (fun ω => potentialY 1 ω - potentialY 0 ω) alwaysPass = 0 ∧
    eventMean (selectionLaw q) (fun ω => potentialY 1 ω - potentialY 0 ω)
      {ω | potentialS 0 ω = true ∧ potentialS 1 ω = false} = 0 ∧
    eventMean (selectionLaw q) (fun ω => potentialY 1 ω - potentialY 0 ω)
      {ω | potentialS 0 ω = false ∧ potentialS 1 ω = true} = 0 ∧
    eventMean (selectionLaw q) observedY (passEvent ∩ armEvent 0) = 0 ∧
    eventMean (selectionLaw q) observedY (passEvent ∩ armEvent 1) = 1/2 ∧
    eventMean (selectionLaw q) observedY (passEvent ∩ armEvent 1) -
      eventMean (selectionLaw q) observedY (passEvent ∩ armEvent 0) = 1/2 ∧
    (1/2 : ℝ) ≠ 0 := by
  have hqc : 0 < 1-q := sub_pos.mpr hq1
  let r : Fin 6 → ℝ := fun i => if i.val < 3 then q/3 else (1-q)/3
  have hr : ∀ i, 0 ≤ r i := by intro i; dsimp [r]; split_ifs <;> positivity
  have hp : IsProbabilityMeasure (selectionLaw q) := finiteLaw_probability selectionAtoms r hr (by
    norm_num [r,Fin.sum_univ_succ]
    ring)
  letI := hp
  have hPair (a : Fin 2) : IndepFun (fun ω => (potentialY a ω,potentialS a ω)) assignment (selectionLaw q) := by
    fin_cases a
    · apply selection_independent q hq hq1 _ (1,false) (0,true) (0,true)
      intro i; fin_cases i <;> norm_num [selectionAtoms,potentialY,potentialS]
    · apply selection_independent q hq hq1 _ (1,true) (0,false) (0,true)
      intro i; fin_cases i <;> norm_num [selectionAtoms,potentialY,potentialS]
  have hTriple (a : Fin 2) :
      IndepFun (fun ω => (potentialY a ω,potentialS a ω,covariates ω)) assignment (selectionLaw q) := by
    fin_cases a
    · apply selection_independent q hq hq1 _ (1,false,fun _ => 0) (0,true,fun _ => 0) (0,true,fun _ => 0)
      intro i; fin_cases i <;> norm_num [selectionAtoms,potentialY,potentialS,covariates]
    · apply selection_independent q hq hq1 _ (1,true,fun _ => 0) (0,false,fun _ => 0) (0,true,fun _ => 0)
      intro i; fin_cases i <;> norm_num [selectionAtoms,potentialY,potentialS,covariates]
  have hAssign (a : Fin 2) : 0 < selectionLaw q (armEvent a) := by
    apply (ENNReal.toReal_pos_iff.mp ?_).1
    change 0 < (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i)) (armEvent a)).toReal
    rw [finiteLaw_apply_real _ r hr]
    fin_cases a <;> norm_num [selectionAtoms,armEvent,assignment,r,Fin.sum_univ_succ] <;> linarith
  have hRate (a : Fin 2) : passingRate (selectionLaw q) a = 2/3 := by
    rw [(nonzero_passing_corrected (selectionLaw q) hp ⟨hPair,hAssign⟩).1 a]
    change (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i)) (potentialPass a)).toReal = 2/3
    rw [finiteLaw_apply_real _ r hr]
    fin_cases a <;> norm_num [selectionAtoms,potentialPass,potentialS,r,Fin.sum_univ_succ] <;> ring
  have hn : NonzeroPassing (selectionLaw q) := by intro a; rw [hRate a]; norm_num
  have hA : selectionLaw q alwaysPass = 1/3 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    change (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i)) alwaysPass).toReal = (1/3:ℝ≥0∞).toReal
    rw [finiteLaw_apply_real _ r hr]
    norm_num [selectionAtoms,alwaysPass,potentialS,r,Fin.sum_univ_succ,Fin.forall_fin_succ]
    ring
  have hX : covariates =ᵐ[selectionLaw q] fun _ => (fun _ => (0:ℝ)) := by
    apply finiteLaw_ae
    intro i; fin_cases i <;> rfl
  have hBal := constant_covariate_balance (selectionLaw q) (fun _ => 0) hX
  have hIS : IndepFun observedS assignment (selectionLaw q) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
    rw [ENNReal.toReal_mul]
    change (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i)) _).toReal =
      (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i)) _).toReal *
      (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i)) _).toReal
    simp only [finiteLaw_apply_real _ r hr]
    by_cases hs₀ : false ∈ s <;> by_cases hs₁ : true ∈ s <;>
      by_cases ht₀ : (0:Fin 2) ∈ t <;> by_cases ht₁ : (1:Fin 2) ∈ t <;>
      norm_num [selectionAtoms,observedS,potentialS,assignment,r,Fin.sum_univ_succ,hs₀,hs₁,ht₀,ht₁] <;> ring
  have hEffect : ∀ᵐ ω ∂selectionLaw q, potentialY 1 ω-potentialY 0 ω=0 := by
    apply finiteLaw_ae
    intro i; fin_cases i <;> norm_num [selectionAtoms,potentialY]
  have hEffectMean (E : Set (State 2 1)) :
      eventMean (selectionLaw q) (fun ω => potentialY 1 ω-potentialY 0 ω) E = 0 := by
    unfold eventMean
    rw [integral_congr_ae (ae_restrict_of_ae hEffect)]
    simp
  have hDiffS : (∫ ω, (if potentialS 1 ω then (1:ℝ) else 0)-(if potentialS 0 ω then (1:ℝ) else 0)
      ∂selectionLaw q) = 0 := by
    rw [selectionLaw, finiteLaw_integral _ _ (by intro i; exact ENNReal.ofReal_ne_top)]
    norm_num [selectionAtoms,potentialS,Fin.sum_univ_succ,ENNReal.toReal_ofReal,show 0 ≤ q/3 by positivity,
      show 0 ≤ (1-q)/3 by positivity]
  have hMean0 : eventMean (selectionLaw q) observedY (passEvent ∩ armEvent 0) = 0 := by
    change eventMean (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i))) _ _ = 0
    rw [finiteLaw_mean_real _ r hr _ _ (measurableSet_pass.inter (measurableSet_arm 0))]
    norm_num [selectionAtoms,potentialY,observedY,observedS,potentialS,assignment,passEvent,armEvent,r,Fin.sum_univ_succ]
  have hMean1 : eventMean (selectionLaw q) observedY (passEvent ∩ armEvent 1) = 1/2 := by
    change eventMean (finiteLaw selectionAtoms (fun i => ENNReal.ofReal (r i))) _ _ = 1/2
    rw [finiteLaw_mean_real _ r hr _ _ (measurableSet_pass.inter (measurableSet_arm 1))]
    norm_num [selectionAtoms,potentialY,observedY,observedS,potentialS,assignment,passEvent,armEvent,r,Fin.sum_univ_succ]
    field_simp
    <;> nlinarith
  refine ⟨⟨hp,⟨hPair,hAssign⟩,hn⟩,⟨hTriple,hAssign⟩,hBal,hA,hRate,hIS,hEffect,hDiffS,
    hEffectMean _,hEffectMean _,hEffectMean _,hMean0,hMean1,?_,by norm_num⟩
  rw [hMean0,hMean1]
  ring

/-- T21, Corollary 3, p. 575: independence S from Z does not justify dropping.
An existential law satisfies every assumption and positive all-pass mass,
yet the selected contrast differs from the always-passer average effect. -/
theorem corollary_three : ∃ μ : Measure (State 2 1), Assumptions μ ∧
    IndepFun observedS assignment μ ∧ 0 < μ alwaysPass ∧
    eventMean μ observedY (passEvent ∩ armEvent 1) - eventMean μ observedY (passEvent ∩ armEvent 0) ≠
      eventMean μ (fun ω => potentialY 1 ω - potentialY 0 ω) alwaysPass := by
  have h := selection_counterexample_corrected (1/2) (by norm_num) (by norm_num)
  rcases h with ⟨hAss,hCovI,hCovB,hA,hRate,hIS,hEff,hS,hEA,hE10,hE01,hM0,hM1,hContrast,hne⟩
  refine ⟨selectionLaw (1/2),hAss,hIS,?_,?_⟩
  · rw [hA]; norm_num
  · rw [hContrast,hEA]; norm_num

/-- T23, Corollary 5, p. 576: conditional covariate balance does not justify
dropping, even under Assumptions 1,3,4. A one-dimensional constant covariate
in the Appendix A law supplies positive conditioning mass and a failed contrast. -/
theorem corollary_five : ∃ μ : Measure (State 2 1),
    IsProbabilityMeasure μ ∧ NonzeroPassing μ ∧ CovariateIgnorability μ ∧
    CovariateBalance μ ∧ 0 < μ (alwaysPass ∩ {ω | covariates ω = fun _ => 0}) ∧
    eventMean μ observedY ((passEvent ∩ armEvent 1) ∩ {ω | covariates ω = fun _ => 0}) -
      eventMean μ observedY ((passEvent ∩ armEvent 0) ∩ {ω | covariates ω = fun _ => 0}) ≠
      eventMean μ (fun ω => potentialY 1 ω - potentialY 0 ω)
        (alwaysPass ∩ {ω | covariates ω = fun _ => 0}) := by
  have h := selection_counterexample_corrected (1/2) (by norm_num) (by norm_num)
  rcases h with ⟨hAss,hCovI,hCovB,hA,hRate,hIS,hEff,hS,hEA,hE10,hE01,hM0,hM1,hContrast,hne⟩
  have hX : covariates =ᵐ[selectionLaw (1/2)] fun _ => (fun _ => (0:ℝ)) := by
    apply finiteLaw_ae
    intro i; fin_cases i <;> rfl
  have hE (E : Set (State 2 1)) : (E ∩ {ω | covariates ω = fun _ => 0}) =ᵐ[selectionLaw (1/2)] E := by
    filter_upwards [hX] with ω hω
    simp [hω]
  refine ⟨selectionLaw (1/2),hAss.1,hAss.2.2,hCovI,hCovB,?_,?_⟩
  · rw [measure_congr (hE alwaysPass),hA]; norm_num
  · rw [eventMean_congr_set _ _ (hE (passEvent ∩ armEvent 1)),
      eventMean_congr_set _ _ (hE (passEvent ∩ armEvent 0)),
      eventMean_congr_set _ _ (hE alwaysPass),hContrast,hEA]
    norm_num

/-- T3: W is exponential of rate 1 and V has density exp(-2|v|).
Both are represented by densities with respect to Lebesgue measure. -/
noncomputable def exponentialOne : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x) else 0))
/-- T3, P010-E001: “V” has density exp(-2|v|); this rate
parameterization also specifies the rate-one passer Laplace distribution. -/
noncomputable def laplaceRate (r : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (r/2 * Real.exp (-r * |x|)))
/-- Appendix C, p. 581: “Pr(Z=1)=1/2”, used as independent uniform
assignment in the explicit two-arm continuous witnesses. -/
noncomputable def fairAssignment : Measure (Fin 2) :=
  (1/2 : ℝ≥0∞) • Measure.dirac 0 + (1/2 : ℝ≥0∞) • Measure.dirac 1

/-- Product-stratum law used in T3 and in T5’s endpoint-approaching families:
potential outcomes are independent conditional on the stratum, followed by
independent uniform treatment assignment. T5’s baseline uses `diagonalLaw` instead. -/
noncomputable def stratumLaw (s₁ s₂ : Bool) (F₁ F₂ : Measure ℝ) : Measure (State 2 0) :=
  ((F₁.prod F₂).prod fairAssignment).map
    (fun ω => (![ω.1.1,ω.1.2], ![s₁,s₂], ω.2, fun _ => 0))

/-- T3, P010-E001 witness: strata 11 and 10 each have mass 1/4;
stratum 01 has mass 1/2. Arm-1 outcomes are ±W, swapped between the first
strata by `upper`; failures have V of Laplace rate 2. Arm-2 is Laplace rate 1. -/
noncomputable def missingPassLaw (upper : Bool) : Measure (State 2 0) :=
  (1/4 : ℝ≥0∞) • stratumLaw true true
    (if upper then exponentialOne else exponentialOne.map (fun x => -x)) (laplaceRate 1) +
  (1/4 : ℝ≥0∞) • stratumLaw true false
    (if upper then exponentialOne.map (fun x => -x) else exponentialOne) (laplaceRate 1) +
  (1/2 : ℝ≥0∞) • stratumLaw false true (laplaceRate 2) (laplaceRate 1)


/-- T5 witness: beta(3,3) density b=30x²(1-x)² on (0,1),
and heavy-tailed density h=5/(2(1+|v|)^6) on R. -/
noncomputable def beta33 : Measure ℝ := volume.withDensity
  (fun x => ENNReal.ofReal (if 0 < x ∧ x < 1 then 30*x^2*(1-x)^2 else 0))
/-- T5, P010-E002: “h(v)=5/[2(1+|v|)^6]”,
the full-support failer density used to test Proposition 1 on p. 575. -/
noncomputable def heavySix : Measure ℝ := volume.withDensity
  (fun x => ENNReal.ofReal (5 / (2*(1+|x|)^6)))

/-- A common-status stratum: both passing indicators equal `s` and both
potential outcomes equal one draw from `F`, with independent fair assignment.
The T5 baseline mixes these strata in `boundedPassLaw` below. -/
noncomputable def diagonalLaw (s : Bool) (F : Measure ℝ) : Measure (State 2 0) :=
  (F.prod fairAssignment).map (fun ω => (![ω.1,ω.1], ![s,s], ω.2, fun _ => 0))
/-- T5, P010-E002 witness: common passers of mass “1/3”
have the beta outcome; common failers of mass “2/3” have the heavy outcome. -/
noncomputable def boundedPassLaw : Measure (State 2 0) :=
  (1/3 : ℝ≥0∞) • diagonalLaw true beta33 + (2/3 : ℝ≥0∞) • diagonalLaw false heavySix

/-- T5 endpoint-approaching construction: q=F_beta(t),
stratum masses q/3,(1-q)/3,(1-q)/3,(1+q)/3, and beta outcomes conditioned on
(0,t) (or (1-t,1)) in always-passers and its complement in one-arm passers.
Each failing potential response retains the heavySix law. -/
noncomputable def betaEndpointLaw (t : ℝ) (upper : Bool) : Measure (State 2 0) :=
  let E := if upper then Ioo (1-t) 1 else Ioo 0 t
  let q := (beta33 E).toReal
  let F := eventLaw beta33 id E
  let G := eventLaw beta33 id (Ioo 0 1 \ E)
  ENNReal.ofReal (q/3) • stratumLaw true true F F +
  ENNReal.ofReal ((1-q)/3) • stratumLaw true false G heavySix +
  ENNReal.ofReal ((1-q)/3) • stratumLaw false true heavySix G +
  ENNReal.ofReal ((1+q)/3) • stratumLaw false false heavySix heavySix


/-- T13 normal witness (P010-B02): independent Bernoulli(4/5)
common passing and N(0,1) common potential outcome, with fair assignment. -/
noncomputable def normalCommonLaw : Measure (State 2 0) :=
  (4/5 : ℝ≥0∞) • diagonalLaw true (gaussianReal 0 1) +
  (1/5 : ℝ≥0∞) • diagonalLaw false (gaussianReal 0 1)


/-- Appendix C, p. 581: “Y(1)=Y(2)=lambda[S(2)-S(1)]+N(0,sigma).”
The normal term and assignment are independent of the principal stratum.
The parameter sigma is standard deviation (the deposited code's convention). -/
noncomputable def simulationState (s₁ s₂ : Bool) (lam : ℝ) (ω : ℝ × Fin 2) : State 2 0 :=
  let y := lam*((if s₂ then (1:ℝ) else 0)-(if s₁ then (1:ℝ) else 0)) + ω.1
  (![y,y], ![s₁,s₂], ω.2, fun _ => 0)
/-- Appendix C, p. 581: vary “lambda, sigma, and the joint distribution
of (S(1),S(2))”; the four stratum masses are parameterized by their passing
marginals and correlation, with independent normal noise and assignment. -/
noncomputable def simulationLaw (p₁ p₂ ρ lam σ : ℝ) : Measure (State 2 0) :=
  let a := p₁*p₂ + ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂))
  let base := (gaussianReal 0 ⟨σ^2, sq_nonneg σ⟩).prod fairAssignment
  ENNReal.ofReal (1-p₁-p₂+a) • base.map (simulationState false false lam) +
  ENNReal.ofReal (p₁-a) • base.map (simulationState true false lam) +
  ENNReal.ofReal (p₂-a) • base.map (simulationState false true lam) +
  ENNReal.ofReal a • base.map (simulationState true true lam)

/-- Correlation between binary potential manipulation responses, Appendix C,
p. 581: covariance divided by product of standard deviations. -/
noncomputable def checkCorrelation {K d} (μ : Measure (State K d)) (a b : Fin K) : ℝ :=
  let p := (μ (potentialPass a)).toReal
  let q := (μ (potentialPass b)).toReal
  ((μ (potentialPass a ∩ potentialPass b)).toReal - p*q) /
    Real.sqrt (p*(1-p)*q*(1-q))

/-- Appendix C/Table 1 (p. 582): effect interval width computed as the upper
endpoint of one arm minus the lower endpoint of the other, minus the reverse
endpoint. This is the target's deposited-code definition of Bound Width. -/
noncomputable def effectBoundWidth (μ : Measure (State 2 0)) : ℝ :=
  (upperBound μ 1 - lowerBound μ 0) - (lowerBound μ 1 - upperBound μ 0)

/-- Observable normal mixture (P010-E011): F_w is the law
of noise with mass 1-w and noise minus one with mass w. -/
noncomputable def normalMixture (w : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1-w) • gaussianReal 0 1 + ENNReal.ofReal w • gaussianReal (-1) 1
/-- T9, P010-E011: “L_w”, the mean of the lower three
quarters of the observable passer mixture in the p. 581 simulation. -/
noncomputable def mixtureLower (w : ℝ) : ℝ :=
  eventMean (normalMixture w) id {y | (y : EReal) ≤ quantile (normalMixture w) (3/4)}
/-- T9, P010-E011: “U_w”, the mean of the upper three
quarters of the observable passer mixture in the p. 581 simulation. -/
noncomputable def mixtureUpper (w : ℝ) : ℝ := tailUpper (normalMixture w) (1/4)


/-- Corrected Proposition 1's endpoints as a function of observable inputs,
Appendix C, p. 581, corrected T10(i). Finite branch uses the quantile tail
means, else branch uses essential endpoints of the specified passer law. -/
noncomputable def observableBoundPair {K : ℕ} (p : Fin K → ℝ) (F : Measure ℝ) (a : Fin K) : EReal × EReal :=
  let r := (∑ b : Fin K, if b ≠ a then 1 - p b else 0) / p a
  if r < 1 then
    ((eventMean F id {y | (y : EReal) ≤ quantile F (1-r)} : ℝ), (tailUpper F r : ℝ))
  else (essInf (fun y : ℝ => (y : EReal)) F, essSup (fun y : ℝ => (y : EReal)) F)

/-- Corrected Proposition 1's two branches (p. 575, T4/T6) evaluated in
an actual population law: passer-conditioned event means for r<1 and
essential passer support endpoints otherwise. -/
noncomputable def correctedBoundPair {K d} (μ : Measure (State K d)) (a : Fin K) : EReal × EReal :=
  if trimRatio μ a < 1 then ((lowerBound μ a : EReal),(upperBound μ a : EReal))
  else (passerInf μ a,passerSup μ a)

/-- T10(i), corrected Appendix C, p. 581: holding observed passing rates and
the focal passer outcome law fixed holds both bound endpoints fixed, including
the else branch. This is a function-of-observables fact, not a sharpness proof. -/
theorem bounds_fixed_observables {K d : ℕ} (μ ν : Measure (State K d))
    (a : Fin K) (hp : passingRate μ = passingRate ν) (hF : passerLaw μ a = passerLaw ν a) :
    observableBoundPair (passingRate μ) (passerLaw μ a) a =
      observableBoundPair (passingRate ν) (passerLaw ν a) a := by
  rw [hp, hF]

/-- T10(i), corrected Appendix C, p. 581: both actual tail means and both
essential-support endpoints remain fixed when the observed passing rates
and focal passer distribution are fixed. This proves the population-law
invariance, in addition to the separate formula-input identity. -/
theorem bounds_fixed_observables_actual {K d} (μ ν : Measure (State K d))
    (hμ : Assumptions μ) (hν : Assumptions ν) (a : Fin K)
    (hp : passingRate μ = passingRate ν) (hF : passerLaw μ a = passerLaw ν a) :
    correctedBoundPair μ a = correctedBoundPair ν a := by
  have hr : trimRatio μ a = trimRatio ν a := by unfold trimRatio; rw [hp]
  have hl : lowerBound μ a = lowerBound ν a := by
    rw [(passer_tail_mean_formula μ hμ a).1,(passer_tail_mean_formula ν hν a).1,hr,hF]
  have hu : upperBound μ a = upperBound ν a := by
    rw [(passer_tail_mean_formula μ hμ a).2,(passer_tail_mean_formula ν hν a).2,hr,hF]
  simp only [correctedBoundPair,hr,hl,hu,passerInf,passerSup,hF]

/-- Exact simulation-formula component of corrected Appendix C, p. 581
(T10): interior passing marginals and nonzero lambda make each displayed
observable mean formula injective in rho. This does not assume the law
calculation or the Gaussian quantile certificates. -/
theorem simulation_mean_formula_injective (p₁ p₂ ρ ρ' lam : ℝ)
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hlam : lam ≠ 0) (hρ : ρ' ≠ ρ) :
    -lam*(1-(p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁) ≠
      -lam*(1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁) ∧
    lam*(1-(p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂) ≠
      lam*(1-(p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂) := by
  have hpc₁ : 0 < 1-p₁ := sub_pos.mpr hp₁'
  have hpc₂ : 0 < 1-p₂ := sub_pos.mpr hp₂'
  have hD : 0 < Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) := by
    apply Real.sqrt_pos.mpr
    positivity
  constructor
  · intro he
    have hi := mul_left_cancel₀ (neg_ne_zero.mpr hlam) he
    have hdiv : (p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁ =
        (p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₁ := by linarith
    have hn := congrArg (fun x => x*p₁) hdiv
    simp only [div_mul_cancel₀ _ (ne_of_gt hp₁)] at hn
    have hc : ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) =
        ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) := by linarith
    exact hρ (mul_right_cancel₀ (ne_of_gt hD) hc)
  · intro he
    have hi := mul_left_cancel₀ hlam he
    have hdiv : (p₁*p₂+ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂ =
        (p₁*p₂+ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)))/p₂ := by linarith
    have hn := congrArg (fun x => x*p₂) hdiv
    simp only [div_mul_cancel₀ _ (ne_of_gt hp₂)] at hn
    have hc : ρ'*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) =
        ρ*Real.sqrt (p₁*(1-p₁)*p₂*(1-p₂)) := by linarith
    exact hρ (mul_right_cancel₀ (ne_of_gt hD) hc)


end AronowAudit.P010
