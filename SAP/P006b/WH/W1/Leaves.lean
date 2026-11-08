import SAP.P006b.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.WH.W1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- T17, actual finite-stratum selection moments, with noisy outcomes.
Apply RepairT6T7_unit_outcome_moments, subtract the treated moment from
the total moment, and integrate conditional expectations. Push the covariate
integrals through covariate_law and integral_fintype. Consistency replaces Y
by Y0 on the untreated event. The observed outcome is integrable by its
two measurable indicator pieces. About 120--200 lines. -/
def T17_L1 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {K n : ℕ}
    (E : Experiment Ω (Fin K) n), OutcomeStanding E →
    ∀ (p : Fin K → ℝ), (∀ u, 0 < p u) → (∑ u, p u) = 1 →
    (∀ u, (E.PX {u}).toReal = p u) →
    ∀ π, Admissible π → ∀ i,
      Integrable (fun ω => E.observed π ω i) (E.law π) ∧
      (E.law π {ω | E.T π i ω = false}).toReal = finiteMass p (fun u => 1-π u) ∧
      (∫ ω in {ω | E.T π i ω = false}, E.observed π ω i ∂E.law π) =
        finiteA p E.μ0 (fun u => 1-π u)

/-- T17, finite conditional convexity and its integrated form.
For each x use sum p=1 and abs_sum_le_sum_abs to bound the deviation of
the weighted mean by the weighted sum of deviations, then by their finite
maximum. maximumDeviation is a supremum of a nonempty finite range whenever
the premises hold. The joint finiteConditionalLaw is a probability measure:
sum the density masses, using sum p=1. The marginal deviation is measurable
by finite sums and is dominated by the integrable maximum deviation; apply
Integrable.mono' and integral_mono. Both expectations are actual integrals
under the joint law with conditional type probabilities p(x), with no
disintegration assumption for an arbitrary private space. About 150--250 lines. -/
def T17_L2 : Prop := T17ComparisonStatement

/-- T17, fixed-heterogeneity endogenous-baseline counterexample family.
Expand the four atoms of binaryPopulationLaw. For each of the two feasible
policies, integral_fintype gives its actual untreated conditional mean,
score and welfare. The masses are nonnegative and sum to one. With
p=1/(2L), the public baseline is zero, heterogeneity is exactly one,
the score at (1,0) is positive and that at (0,1) negative. Compare the
two policies and use bestValue_at for regret L/2+3/4. All denominators
are positive for L>1. About 150--250 lines of finite probability and field algebra. -/
def T17_L3 : Prop := ∀ L : ℝ, 1 < L → T17BadFamily L

/-- T17, general companion comparison for conditional probability kernels.
There is no finite-private-type or positive-atom hypothesis. For fixed (x,u),
the attained maximum makes the range of |m(x,u)-m(x,v)| bounded, so le_csSup
bounds every difference by maximumDeviation m (x,u). The measurable difference
v ↦ m(x,v)-m(x,u) is bounded on the probability space κ x, hence integrable.
Its integral is kernelMarginalBaseline κ m x-m(x,u); apply
abs_integral_le_integral_abs and integral_mono to obtain the bound (in fact
pointwise). StronglyMeasurable.integral_kernel_prod_right' gives measurable
baseline and deviation. Domination by the integrable maximum gives deviation
integrability, then integral_mono_ae gives the expectation comparison.
The joint law is a probability by the Markov-kernel instance. No extrema for m
itself, uniform bound in x, or extra independence premise is needed.
About 100--180 lines; the same-constant implication is proved in the assembly. -/
def T17_L4 : Prop := T17KernelComparisonStatement

/-- T25, integration and endpoints for arbitrary public covariates.
Use boundedness of admissible policies to obtain integrability of both
sections. Fubini and the two atoms of fairPrivateLaw give the reward,
welfare and heterogeneity formulas. Constant-in-X policies realize every
point of the square. For the endpoint equivalences apply
integral_eq_zero_iff_of_nonneg to 1-pi(.,false) and pi(.,true).
The integral guards follow from boundedness and the probability law;
there is no atom or finiteness assumption on X. About 120--220 lines. -/
def T25_L1 : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (Q : Measure X), IsProbabilityMeasure Q →
    (∀ ρ, binaryFeasible ρ →
      Admissible (fun c : X × Bool => binaryRule ρ c.2) ∧
      policyCoordinates Q (fun c : X × Bool => binaryRule ρ c.2) = ρ) ∧
    (∀ α : ℝ,
      (∫ c : X × Bool, |(0 : ℝ)-lowerBoundY0 α c.2| ∂Q.prod fairPrivateLaw) = |α| ∧
      ∀ _x : X, (∫ u, lowerBoundY0 α u ∂fairPrivateLaw) = 0) ∧
    (∀ π : X × Bool → ℝ, Admissible π →
      binaryFeasible (policyCoordinates Q π) ∧
      (∀ β η : ℝ,
        (∫ c, π c*lowerBoundY1 β η c.2 ∂Q.prod fairPrivateLaw) =
          lowerBoundReward β η (policyCoordinates Q π)) ∧
      (∀ α β η : ℝ,
        (∫ c, π c*(lowerBoundY1 β η c.2-lowerBoundY0 α c.2) ∂Q.prod fairPrivateLaw) =
          lowerBoundWelfare α β η (policyCoordinates Q π)) ∧
      ((policyCoordinates Q π).1 = 1 ↔ ∀ᵐ x ∂Q, π (x,false) = 1) ∧
      ((policyCoordinates Q π).2 = 0 ↔ ∀ᵐ x ∂Q, π (x,true) = 0))

/-- T29, estimator-free noisy-outcome ATO identity.
Apply T2_marked_average to the independent pairs (Y1_i,T_i). Obtain their
common Bernoulli and treated-outcome moments from the standing conditional
moments and RepairT6T7_unit_outcome_moments. T2_total_moment and covariate_law
identify q=int pi and A=int pi*mu1. On the event of no treatment all terms
are zero, so the q=0 case requires no quotient. Consistency replaces observed
outcomes by Y1 in the average. Integrability follows by domination by the
finite sum of |Y1_i|. No estimator assumption is made. About 100--180 lines. -/
def T29_L1 : Prop :=
  ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), OutcomeStanding E → ∀ π, Admissible π →
    E.expectedATO π = emptyFactor n (∫ x, π x ∂E.PX) *
      (∫ x, π x * E.μ1 x ∂E.PX)

theorem T17_assembly (h1 : T17_L1) (h2 : T17_L2) (h3 : T17_L3) (h4 : T17_L4) :
    T17WholeStatement := by
  refine ⟨?_, @AronowAudit.P006.T17_selected_type,
    AronowAudit.P006.T17_three_type_example, h2, ?_, h4, ?_, ?_⟩
  · intro Ω mΩ K n E hE p hp hsum hmass π hπ hq i
    obtain ⟨hi,hm,hy⟩ := h1 E hE p hp hsum hmass π hπ i
    refine ⟨hi,hm,by simpa only [hm] using hq,?_⟩
    simp only [eventMean,hm,hy,finiteSelectedBaseline]
  · intro X mX K Q hQ p m hpmeas hm hp hsum hint γ hγ
    exact (h2 Q hQ p m hpmeas hm hp hsum hint).2.2.2.trans hγ
  · intro X U mX mU hU Q hQ κ hκ m hm hmi hmax hint γ hγ
    exact (h4 Q hQ κ hκ m hm hmi hmax hint).2.2.2.trans hγ
  · intro M hM
    let L : ℝ := 2*(M+1)
    have hL : 1 < L := by dsimp [L]; linarith
    have hf := h3 L hL
    refine ⟨L,hL,hf,?_⟩
    have hr : regret T17BadPolicies
        (binaryActualWelfare (T17BadProbability L) (T17BadY0 L) (T17BadY1 L)) (1,0) =
        L/2+3/4 := hf.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [hr]
    dsimp [L]
    linarith

theorem T18_assembly : T18WholeStatement := by
  have hold : T18Statement := AronowAudit.P006.T18_regret_sign_counterexample
  have hp (π : BinaryPolicy) : rewardP1 (1/2) π = π.2*(4-π.1-π.2)/4 := by
    change AronowAudit.P006.rewardP1 (1/2) π = _
    unfold AronowAudit.P006.rewardP1 AronowAudit.P006.outcomeP1
    rw [AronowAudit.P006.twoATO_formula]
    ring
  refine ⟨hold,?_,?_,hp,?_,?_,?_,?_,?_,by norm_num,?_⟩
  · intro x0 x1 t0 t1
    change AronowAudit.P006.wATO _ _ ≤ _
    rw [AronowAudit.P006.wATO_two]
    cases x0 <;> cases x1 <;> cases t0 <;> cases t1 <;> norm_num [outcomeP1]
  · intro x0 x1
    change AronowAudit.P006.wATO _ _ = _
    rw [AronowAudit.P006.wATO_two]
    cases x0 <;> cases x1 <;> norm_num [outcomeP1]
  · intro π
    constructor
    · intro h
      obtain ⟨ha0,ha1,hb0,hb1⟩ := h.1
      have hv := h.2 (0,1) (by norm_num [binaryPolicies,binaryFeasible])
      rw [hp π,hp (0,1)] at hv
      have hn := mul_nonneg ha0 hb0
      have hg := mul_nonneg (sub_nonneg.mpr hb1) (show 0 < 3-π.2 by linarith).le
      have hb : π.2 = 1 := by dsimp at hv; nlinarith
      have ha : π.1 = 0 := by dsimp at hv; rw [hb] at hv; nlinarith
      exact Prod.ext ha hb
    · rintro rfl
      exact hold.1
  · intro π
    dsimp [binaryWelfare,effectP1]
    ring
  · rw [bestValue_at hold.2.2.1]
    norm_num [binaryWelfare,effectP1]
  · norm_num [binaryWelfare,effectP1]
  · norm_num [binaryWelfare,effectP1]
  · intro P S V s π hs hπ
    rw [regret,bestValue_at hs]
    exact sub_nonneg.mpr (hs.2 π hπ)

theorem coordinates_best (h1 : T25_L1) {X : Type} [MeasurableSpace X]
    (Q : Measure X) (hQ : IsProbabilityMeasure Q)
    (f : BinaryPolicy → ℝ) (g : (X × Bool → ℝ) → ℝ)
    (hfg : ∀ π, Admissible π → g π = f (policyCoordinates Q π)) (π : X × Bool → ℝ) :
    IsBest {ρ | Admissible ρ} g π ↔
      Admissible π ∧ IsBest binaryPolicies f (policyCoordinates Q π) := by
  obtain ⟨hlift,_,hcoords⟩ := h1 Q hQ
  constructor
  · intro h
    refine ⟨h.1,(hcoords π h.1).1,?_⟩
    intro ρ hρ
    have hh := h.2 (fun c => binaryRule ρ c.2) (hlift ρ hρ).1
    rwa [hfg _ (hlift ρ hρ).1,hfg π h.1,(hlift ρ hρ).2] at hh
  · rintro ⟨hπ,hbest⟩
    refine ⟨hπ,?_⟩
    intro ρ hρ
    rw [hfg ρ hρ,hfg π hπ]
    exact hbest.2 _ (hcoords ρ hρ).1

theorem T25_general (h1 : T25_L1) : T25GeneralStatement := by
  intro Ω X mΩ mX n E Q α β η hm hβ hβα hη hηα
  obtain ⟨hS,hQ,hPX,hμ0,hμ1,_hpublic,hU⟩ := hm
  obtain ⟨hlift,hmean,hcoords⟩ := h1 Q hQ
  have hα : 0 < α := hβ.trans hβα
  have hnr : (0 : ℝ) < n := by exact_mod_cast E.hn
  have hscore (π : X × Bool → ℝ) (hπ : Admissible π) :
      E.expectedTT π = (n : ℝ)*lowerBoundReward β η (policyCoordinates Q π) := by
    rw [actual_TT E hS (fun _ => 0) measurable_const (integrable_zero _ _ _) hU hπ]
    simp only [sub_zero,hPX,hμ1]
    rw [(hcoords π hπ).2.1 β η]
  have hV (π : X × Bool → ℝ) (hπ : Admissible π) :
      E.V π = lowerBoundWelfare α β η (policyCoordinates Q π) := by
    rw [actual_welfare E hS hπ]
    simpa only [hPX,hμ0,hμ1,Experiment.τ] using (hcoords π hπ).2.2.1 α β η
  have hR (π : X × Bool → ℝ) : IsBest {ρ | Admissible ρ} E.expectedTT π ↔
      Admissible π ∧ IsBest binaryPolicies (lowerBoundReward β η) (policyCoordinates Q π) := by
    rw [coordinates_best h1 Q hQ (fun ρ => (n : ℝ)*lowerBoundReward β η ρ) E.expectedTT hscore π]
    exact and_congr_right fun _ => scale_best _ _ _ hnr _
  have hg : Admissible (privateGoodRule : X × Bool → ℝ) :=
    (hlift (0,1) (by norm_num [binaryFeasible])).1
  have hb : Admissible (privateBadRule : X × Bool → ℝ) :=
    (hlift (1,0) (by norm_num [binaryFeasible])).1
  have hgc : policyCoordinates Q (privateGoodRule : X × Bool → ℝ) = (0,1) :=
    (hlift (0,1) (by norm_num [binaryFeasible])).2
  have hbc : policyCoordinates Q (privateBadRule : X × Bool → ℝ) = (1,0) :=
    (hlift (1,0) (by norm_num [binaryFeasible])).2
  have hgood : IsBest {ρ | Admissible ρ} E.V privateGoodRule := by
    apply (coordinates_best h1 Q hQ _ _ hV _).mpr
    refine ⟨hg,?_⟩
    rw [hgc]
    exact (lowerBound_welfare_optimum α β η hβα hηα).1
  have hvmax : bestValue {ρ | Admissible ρ} E.V = (α-η)/2 := by
    rw [bestValue_at hgood,hV _ hg,hgc,
      (lowerBound_formulas α β η (0,1)).2.1]
    ring
  have hbad : IsBest {ρ | Admissible ρ} E.expectedTT privateBadRule := by
    apply (hR _).mpr
    refine ⟨hb,?_⟩
    rw [hbc]
    by_cases hzero : η = 0
    · subst η
      exact (lowerBound_best_response β hβ (1,0)).mpr
        ⟨by norm_num [binaryFeasible],rfl⟩
    · exact (lowerBound_perturbed_best β η hβ
        (lt_of_le_of_ne hη (Ne.symm hzero)) (1,0)).mpr rfl
  have hstat (π : X × Bool → ℝ) (hπ : Admissible π) :
      binaryFeasible (policyCoordinates Q π) ∧
      E.expectedTT π = (n : ℝ)*(∫ c, π c*(E.μ1 c-0) ∂E.PX) ∧
      E.expectedTT π = (n : ℝ)*(β*(policyCoordinates Q π).1-η*(policyCoordinates Q π).2)/2 ∧
      E.V π = ((β-α)*(policyCoordinates Q π).1+(α-η)*(policyCoordinates Q π).2)/2 := by
    refine ⟨(hcoords π hπ).1,
      actual_TT E hS (fun _ => 0) measurable_const (integrable_zero _ _ _) hU hπ,?_,?_⟩
    · rw [hscore π hπ,(lowerBound_formulas α β η _).1]
      ring
    · rw [hV π hπ]
      exact (lowerBound_formulas α β η _).2.1
  have hhet : (∫ c, |(0 : ℝ)-E.μ0 c| ∂E.PX) = α := by
    rw [hPX,hμ0,(hmean α).1,abs_of_pos hα]
  refine ⟨hstat,?_,hhet,?_,hgood,hvmax,hbad,?_,?_⟩
  · intro x
    simpa only [hμ0] using (hmean α).2 x
  · intro γ
    rw [hhet]
  · intro hzero
    have hresp (π : X × Bool → ℝ) : IsBest {ρ | Admissible ρ} E.expectedTT π ↔
        Admissible π ∧ (policyCoordinates Q π).1 = 1 := by
      rw [hR π,hzero,lowerBound_best_response β hβ]
      constructor
      · exact fun h => ⟨h.1,h.2.2⟩
      · exact fun h => ⟨h.1,(hcoords π h.1).1,h.2⟩
    refine ⟨hresp,fun π hπ => (hcoords π hπ).2.2.2.1,?_,?_⟩
    · intro π hπ
      have hp0 := (hresp π).mp hπ
      rw [regret,hvmax,(hstat π hp0.1).2.2.2,hzero,hp0.2]
      ring
    · rw [regret,hvmax,(hstat _ hb).2.2.2,hbc,hzero]
      ring
  · intro hpos
    have hresp (π : X × Bool → ℝ) : IsBest {ρ | Admissible ρ} E.expectedTT π ↔
        Admissible π ∧ policyCoordinates Q π = (1,0) := by
      rw [hR π,lowerBound_perturbed_best β η hβ hpos]
    refine ⟨?_,?_⟩
    · intro π
      rw [hresp π]
      constructor
      · rintro ⟨hπ,hc⟩
        refine ⟨hπ,(hcoords π hπ).2.2.2.1.mp ?_,(hcoords π hπ).2.2.2.2.mp ?_⟩ <;>
          simp [hc]
      · rintro ⟨hπ,hp0,hp1⟩
        exact ⟨hπ,Prod.ext ((hcoords π hπ).2.2.2.1.mpr hp0)
          ((hcoords π hπ).2.2.2.2.mpr hp1)⟩
    · intro π hπ
      have hc := (hresp π).mp hπ
      rw [regret,hvmax,(hstat π hc.1).2.2.2,hc.2]
      ring

theorem T25_assembly (h1 : T25_L1) : T25WholeStatement := by
  refine ⟨T25_general h1,retained_T25,?_⟩
  intro α ε hα hε
  let δ := min ε (α/2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδα : δ < α := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨hδ,hδα,hδε,?_,?_,?_⟩
  · intro Ω X mΩ mX n E Q hm
    obtain ⟨_,_,_,_,_,_,hb,hzero,_⟩ := T25_general h1 E Q α δ 0 hm hδ hδα (by norm_num) hα
    have hr := (hzero rfl).2.2.2
    exact ⟨hb,hr,by rw [hr]; linarith⟩
  · intro Ω X mΩ mX n E Q hm π hπ
    obtain ⟨_,_,_,_,_,_,_,_,hpos⟩ := T25_general h1 E Q α δ δ hm hδ hδα hδ.le hδα
    have hr := (hpos hδ).2 π hπ
    exact ⟨hr,by rw [hr]; linarith⟩
  · intro n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hf := retained_T25.1 n hn α δ hα hδ hδα
    have hb : IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward δ 0 π) (1,0) :=
      (hf.2.1 (1,0)).mpr ⟨by norm_num [binaryFeasible],rfl⟩
    have hr : regret binaryPolicies (lowerBoundWelfare α δ 0) (1,0) = α-δ/2 :=
      hf.2.2.2.2.2.1
    have hb' : IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward δ δ π) (1,0) :=
      (scale_best _ _ _ hnr _).mpr
        ((lowerBound_perturbed_best δ δ hδ hδ (1,0)).mpr rfl)
    have hr' : regret binaryPolicies (lowerBoundWelfare α δ δ) (1,0) = α-(δ+δ)/2 := by
      rw [regret,(lowerBound_welfare_optimum α δ δ hδα hδα).2,
        (lowerBound_formulas α δ δ (1,0)).2.1]
      ring
    exact ⟨hb,hr,by rw [hr]; linarith,hb',hr',by rw [hr']; linarith⟩

theorem T29_family (h1 : T29_L1) {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (E : Experiment Ω Bool n) (p α β : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hm : T29Model E p α β) : T29FamilyConclusion E p α β := by
  obtain ⟨hS,hmass,hμ0,hμ1⟩ := hm
  let : IsProbabilityMeasure E.PX := hS.px_probability
  have hf (π : BinaryPolicy) (hπ : π ∈ binaryPolicies) :
      E.expectedATO (binaryRule π) = emptyFactor n ((1-p)*π.1+p*π.2)*(p*π.2) ∧
      E.V (binaryRule π) = (1-p)*π.1*(-α)+p*π.2*(1-β) := by
    have hadm := binary_admissible π hπ
    constructor
    · rw [h1 E hS _ hadm,integral_bool E.PX p hmass (binaryRule π),
        integral_bool E.PX p hmass (fun u => binaryRule π u*E.μ1 u)]
      simp [binaryRule,hμ1,outcomeP1]
    · rw [actual_welfare E hS hadm,integral_bool E.PX p hmass]
      simp only [Experiment.τ,hμ0,hμ1,binaryRule,outcomeP1,Bool.false_eq_true,
        ite_false,ite_true]
      ring
  have heq (π : BinaryPolicy) (hπ : π ∈ binaryPolicies) :
      E.expectedATO (binaryRule π) = finiteIIDAverage n p outcomeP1 π := by
    exact (hf π hπ).1.trans
      (AronowAudit.P006.Wave1.T29_finite_iid_formula n p ⟨hp,hp1⟩ π hπ).symm
  refine ⟨hf,?_,?_,?_⟩
  · intro hn π
    rw [best_congr binaryPolicies _ _ heq π]
    exact AronowAudit.P006.Wave1.T29_unique n hn p ⟨hp,hp1⟩ π
  · intro hn π
    rw [best_congr binaryPolicies _ _ heq π]
    have hone : IsBest binaryPolicies (finiteIIDAverage 1 p outcomeP1) π ↔
        binaryFeasible π ∧ π.2 = 1 := AronowAudit.P006.Wave1.T29_one p ⟨hp,hp1⟩ π
    simpa only [hn] using hone
  · intro hα hβ
    let V0 := binaryWelfare p (fun u => if u then 1 else -α)
    have hV (π : BinaryPolicy) (hπ : π ∈ binaryPolicies) : E.V (binaryRule π) = V0 π := by
      rw [(hf π hπ).2,hβ]
      dsimp [V0,binaryWelfare]
      ring
    have hold := AronowAudit.P006.T29_first_mode_welfare p α ⟨hp,hp1⟩ hα
    have hvbest : IsBest binaryPolicies (fun ρ => E.V (binaryRule ρ)) (1,1) :=
      (best_congr binaryPolicies _ V0 hV (1,1)).mpr hold.1
    refine ⟨?_,?_,?_,hvbest,?_,?_,?_⟩
    · simp [Experiment.τ,hμ0,hμ1,outcomeP1]
    · simpa [Experiment.τ,hμ0,hμ1,outcomeP1] using neg_pos.mpr hα
    · simp [Experiment.τ,hμ0,hμ1,hβ,outcomeP1]
    · rw [bestValue_congr binaryPolicies _ V0 hV]
      exact hold.2.1
    · rw [hV (0,1) (by norm_num [binaryPolicies,binaryFeasible])]
      simp [V0,binaryWelfare]
    · change bestValue binaryPolicies (fun ρ => E.V (binaryRule ρ))-E.V (binaryRule (0,1)) = _
      rw [bestValue_congr binaryPolicies _ V0 hV,
        hV (0,1) (by norm_num [binaryPolicies,binaryFeasible])]
      exact hold.2.2

theorem T29_assembly (h1 : T29_L1) : T29WholeStatement := by
  refine ⟨retained_T29,?_,?_⟩
  · intro Ω mΩ n E p α β hp hp1 hm
    exact T29_family h1 E p α β hp hp1 hm
  · intro Ω mΩ n F p hp hp1 hm
    apply (AronowAudit.P006.T29_first_mode_tendsto p hp1).congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with α hα
    obtain ⟨_,_,_,_,_,_,hr⟩ :=
      (T29_family h1 (F α) p α 0 hp hp1 (hm α hα)).2.2.2 hα rfl
    exact hr.symm

theorem T30_maximum : T30MaximumStatement := by
  intro Ω C mΩ mC n E hS hU
  have ht : Measurable E.τ := hS.means_measurable.2.sub hS.means_measurable.1
  have hti : Integrable E.τ E.PX := hS.means_integrable.2.sub hS.means_integrable.1
  have hp : Admissible (positiveRule E.τ) ∧ ∀ π : C → ℝ, Admissible π →
      (∫ x, π x*E.τ x ∂E.PX) ≤ (∫ x, positiveRule E.τ x*E.τ x ∂E.PX) :=
    AronowAudit.P006.Wave1.RepairT6T7_positive_rule_integral_maximum ht hti
  have hf (π : C → ℝ) (hπ : Admissible π) :
      E.expectedTT π = (n : ℝ)*(∫ x, π x*E.τ x ∂E.PX) :=
    actual_TT E hS E.μ0 hS.means_measurable.1 hS.means_integrable.1 hU hπ
  have hb : IsBest {π | Admissible π} E.expectedTT (positiveRule E.τ) := by
    refine ⟨hp.1,?_⟩
    intro π hπ
    rw [hf π hπ,hf _ hp.1]
    exact mul_le_mul_of_nonneg_left (hp.2 π hπ) (Nat.cast_nonneg n)
  refine ⟨hb,?_⟩
  rw [bestValue_at hb,hf _ hp.1]
  unfold positiveEffectMean
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => mul_comm _ _

theorem T30_pair (hmax : T30MaximumStatement) : T30PairStatement := by
  intro Ωj Ωk C mΩj mΩk mC nj nk Ej Ek hj hk huj huk _ hPX hdom hAk
  have htj : Measurable Ej.τ := hj.means_measurable.2.sub hj.means_measurable.1
  have htk : Measurable Ek.τ := hk.means_measurable.2.sub hk.means_measurable.1
  have hij : Integrable Ej.τ Ej.PX := hj.means_integrable.2.sub hj.means_integrable.1
  have hik : Integrable Ek.τ Ek.PX := hk.means_integrable.2.sub hk.means_integrable.1
  have pp (t : ℝ) : t*(if 0 < t then 1 else 0) = max t 0 := by
    by_cases h : 0 < t
    · simp [h,max_eq_left h.le]
    · simp [h,max_eq_right (le_of_not_gt h)]
  have hpi {t : C → ℝ} {P : Measure C} (ht : Measurable t) (hi : Integrable t P) :
      Integrable (fun x => t x*positiveRule t x) P := by
    have hp : Admissible (positiveRule t) :=
      (AronowAudit.P006.Wave1.RepairT6T7_positive_rule_integral_maximum ht hi).1
    simpa only [mul_comm] using
      AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hp.1
        (AronowAudit.P006.Wave1.RepairT6T7_admissible_norm hp) hi
  have hle : positiveEffectMean Ek ≤ positiveEffectMean Ej := by
    unfold positiveEffectMean
    rw [← hPX]
    apply integral_mono (by simpa only [hPX] using hpi htk hik) (hpi htj hij)
    intro x
    simp only [positiveRule,pp]
    exact max_le_max (hdom x) le_rfl
  have hAj : 0 < positiveEffectMean Ej := hAk.trans_le hle
  refine ⟨hle,hAj,(lt_div_iff₀ hAj).symm,?_⟩
  intro hsize
  have hjmax := (hmax Ej hj huj).2
  have hkmax := (hmax Ek hk huk).2
  have hscore : bestValue {π | Admissible π} Ej.expectedTT <
      bestValue {π | Admissible π} Ek.expectedTT := by rw [hjmax,hkmax]; exact hsize
  refine ⟨hscore,?_,?_⟩
  · exact fun h => (not_le_of_gt hscore) (h hdom)
  · intro Q _ hijQ hikQ
    have hmean := integral_mono hikQ hijQ hdom
    exact ⟨hmean, fun h => (not_le_of_gt hscore) (h hmean)⟩

theorem T30_existence (hmax : T30MaximumStatement) : T30ExistenceStatement := by
  have hA (n : ℕ) (hn : 0 < n) : positiveEffectMean (constantEffectExperiment n hn) = 1 := by
    let : IsProbabilityMeasure AronowAudit.P006.Wave1.BinaryExperiment.fairLaw :=
      AronowAudit.P006.Wave1.BinaryExperiment.fairLaw_probability
    simp only [positiveEffectMean,Experiment.τ,constantEffectExperiment,Bridge.fromProject,
      AronowAudit.P006.Wave1.BinaryExperiment.binExp,sub_zero,positiveRule,
      zero_lt_one,ite_true,mul_one]
    rw [integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
  have hj := constantEffect_standing 1 (by decide)
  have hk := constantEffect_standing 2 (by decide)
  have huj := constantEffect_moment 1 (by decide)
  have huk := constantEffect_moment 2 (by decide)
  have hvj := (hmax _ hj huj).2
  have hvk := (hmax _ hk huk).2
  rw [hA] at hvj hvk
  refine ⟨constantEffectExperiment 1 (by decide),constantEffectExperiment 2 (by decide),
    hj,hk,huj,huk,?_,?_,rfl,rfl,rfl,rfl,by simpa using hvj,by simpa using hvk,?_,?_⟩
  · exact fairPrivateLaw_eq.symm
  · exact fairPrivateLaw_eq.symm
  · intro h
    have hh := h (fun _ => le_rfl)
    norm_num at hh
  · intro h
    let := fairPrivateLaw_probability
    have hm : (∫ x, (constantEffectExperiment 2 (by decide)).τ x ∂fairPrivateLaw) ≤
        (∫ x, (constantEffectExperiment 1 (by decide)).τ x ∂fairPrivateLaw) := by
      simp [constantEffectExperiment,Bridge.fromProject,
        AronowAudit.P006.Wave1.BinaryExperiment.binExp,Experiment.τ]
    have hh := h hm
    norm_num at hh

theorem T30_assembly : T30WholeStatement :=
  ⟨T30_maximum,T30_pair T30_maximum,T30_existence T30_maximum⟩

end
end SAP.P006b.WH.W1
