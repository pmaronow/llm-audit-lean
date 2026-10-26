import Mathlib

namespace AronowAudit.P010

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal

/-- Footnote 7, p. 578: “R_i=1 ... replication ... p_i=Pr[R_i=1|X_i].”
With replication sampling share pi and conditional covariate densities fR,fO,
Bayes' formula defines the true propensity. These are true probabilities,
not an assertion of exact balance from an estimated logistic regression. -/
noncomputable def studyPropensity (π fR fO : ℝ) : ℝ := π*fR / (π*fR+(1-π)*fO)

/-- Footnote 7: printed weight “p_i/(1-p_i)” under replication=1; the
correction T12 reverses the coding or, equivalently, uses its reciprocal. -/
noncomputable def printedOdds (p : ℝ) : ℝ := p/(1-p)
/-- Corrected footnote 7, p. 578, T12: with “R_i=1” for replication,
the odds of original membership are (1-p)/p. -/
noncomputable def correctedOdds (p : ℝ) : ℝ := (1-p)/p

/-- T11/T12, P010-E007 derivation: normalized reweighting of the replication
covariate distribution by w. Finite support uses sums exactly. -/
noncomputable def reweighted {n : ℕ} (f w : Fin n → ℝ) (x : Fin n) : ℝ :=
  f x*w x / ∑ u : Fin n, f u*w u

/-- T11's eight-subject population: original X=(0,0,0,1), replication
X=(0,1,1,1). The two conditional covariate distributions on {0,1} are
(3/4,1/4) and (1/4,3/4); study sizes are equal. -/
noncomputable def originalMass : Fin 2 → ℝ := ![3/4,1/4]
/-- T11 replication sample “X=(0,1,1,1)”, giving these two
cell masses; it instantiates the footnote 7 claim on p. 578. -/
noncomputable def replicationMass : Fin 2 → ℝ := ![1/4,3/4]
/-- Footnote 7, p. 578: “p_i=Pr[R_i=1|X_i]”, evaluated with the true
Bayes propensity in the eight-subject T11 witness. -/
noncomputable def examplePropensity (x : Fin 2) : ℝ :=
  studyPropensity (1/2) (replicationMass x) (originalMass x)

/-- T11, counterexample to the reweighting claim in footnote 7, p. 578:
all cells have overlap and the true propensities are 1/4 and 3/4. Printed
odds return 27/28 at X=1 instead of the original 1/4. Reciprocal odds return
the original distribution at both cells. The input cell counts encode the
eight-subject population. -/
theorem transport_odds_counterexample :
    (∀ x : Fin 2, 0 < originalMass x ∧ 0 < replicationMass x ∧
      0 < examplePropensity x ∧ examplePropensity x < 1) ∧
    examplePropensity 0 = 1/4 ∧ examplePropensity 1 = 3/4 ∧
    printedOdds (examplePropensity 0) = 1/3 ∧ printedOdds (examplePropensity 1) = 3 ∧
    replicationMass 0*printedOdds (examplePropensity 0) = 1/12 ∧
    replicationMass 1*printedOdds (examplePropensity 1) = 9/4 ∧
    (∑ x : Fin 2, replicationMass x*printedOdds (examplePropensity x)) = 7/3 ∧
    reweighted replicationMass (fun x => printedOdds (examplePropensity x)) 1 = 27/28 ∧
    reweighted replicationMass (fun x => printedOdds (examplePropensity x)) 1 ≠ originalMass 1 ∧
    (∀ x : Fin 2, reweighted replicationMass (fun x => correctedOdds (examplePropensity x)) x = originalMass x) := by
  norm_num [Fin.forall_fin_succ, originalMass, replicationMass, examplePropensity,
    studyPropensity, printedOdds, correctedOdds, reweighted, Fin.sum_univ_succ]

/-- Saturated binary logistic fitting in T11: each cell's
binomial log likelihood has its unique maximum at the observed cell share.
The statement is for interior probabilities, so neither separation nor a
boundary supremum substitutes for the finite fitted probabilities. -/
theorem bernoulli_cell_mle (p q : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    p*Real.log q+(1-p)*Real.log (1-q) ≤ p*Real.log p+(1-p)*Real.log (1-p) ∧
    (p*Real.log q+(1-p)*Real.log (1-q) = p*Real.log p+(1-p)*Real.log (1-p) ↔ q=p) := by
  have hp' : 0 < 1-p := sub_pos.mpr hp1
  have hq' : 0 < 1-q := sub_pos.mpr hq1
  by_cases he : q=p
  · subst q; exact ⟨le_rfl,by simp⟩
  · have hdiv : q/p ≠ 1 := by intro h; apply he; exact (div_eq_one_iff_eq (ne_of_gt hp)).mp h
    have h₁ := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hq hp) hdiv) hp
    have h₂ := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq' hp')) (le_of_lt hp')
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at h₁
    rw [Real.log_div (ne_of_gt hq') (ne_of_gt hp')] at h₂
    have hz : p*(q/p-1)+(1-p)*((1-q)/(1-p)-1)=0 := by
      field_simp
      <;> ring
    have hlt : p*Real.log q+(1-p)*Real.log (1-q) < p*Real.log p+(1-p)*Real.log (1-p) := by
      nlinarith
    exact ⟨le_of_lt hlt,⟨fun h => False.elim (ne_of_lt hlt h),fun h => False.elim (he h)⟩⟩

/-- Logistic link used in footnote 7, p. 578. -/
noncomputable def logisticProbability (η : ℝ) : ℝ := Real.exp η/(1+Real.exp η)

/-- T11's finite saturated logistic fit: intercept log(1/3), slope log 9
produce the true two cell propensities 1/4 and 3/4. In probability coordinates
the pooled eight subjects' likelihood has this unique maximizer. The affine
map from the two cell logits to intercept/slope is bijective. -/
theorem transport_logistic_certificate :
    logisticProbability (Real.log (1/3)) = (1/4:ℝ) ∧
    logisticProbability (Real.log (1/3)+Real.log 9) = (3/4:ℝ) ∧
    (∀ q₀ q₁ : ℝ, 0 < q₀ → q₀ < 1 → 0 < q₁ → q₁ < 1 →
      Real.log q₀+3*Real.log (1-q₀)+3*Real.log q₁+Real.log (1-q₁) ≤
        Real.log (1/4)+3*Real.log (3/4)+3*Real.log (3/4)+Real.log (1/4) ∧
      (Real.log q₀+3*Real.log (1-q₀)+3*Real.log q₁+Real.log (1-q₁) =
        Real.log (1/4)+3*Real.log (3/4)+3*Real.log (3/4)+Real.log (1/4) ↔
        q₀=1/4 ∧ q₁=3/4)) := by
  refine ⟨?_,?_,?_⟩
  · norm_num [logisticProbability,Real.exp_log (by norm_num : (0:ℝ)<1/3)]
  · rw [logisticProbability,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<1/3),
      Real.exp_log (by norm_num : (0:ℝ)<9)]
    norm_num
  · intro q₀ q₁ h₀ h₀' h₁ h₁'
    have he₀ := bernoulli_cell_mle (1/4) q₀ (by norm_num) (by norm_num) h₀ h₀'
    have he₁ := bernoulli_cell_mle (3/4) q₁ (by norm_num) (by norm_num) h₁ h₁'
    constructor
    · linarith [he₀.1,he₁.1]
    · constructor
      · intro he
        have heq₀ : (1/4)*Real.log q₀+(1-1/4)*Real.log (1-q₀) =
            (1/4)*Real.log (1/4)+(1-1/4)*Real.log (1-1/4) := by linarith [he₀.1,he₁.1]
        have heq₁ : (3/4)*Real.log q₁+(1-3/4)*Real.log (1-q₁) =
            (3/4)*Real.log (3/4)+(1-3/4)*Real.log (1-3/4) := by linarith [he₀.1,he₁.1]
        exact ⟨he₀.2.mp heq₀,he₁.2.mp heq₁⟩
      · rintro ⟨rfl,rfl⟩
        ring

/-- T12(i), corrected footnote 7, p. 578: Bayes' rule includes the sampling
fraction and gives both equivalent density/odds ratios and overlap. -/
theorem transport_bayes (π fR fO : ℝ) (hπ : 0 < π) (hπ1 : π < 1)
    (hR : 0 < fR) (hO : 0 < fO) :
    0 < studyPropensity π fR fO ∧ studyPropensity π fR fO < 1 ∧
    printedOdds (studyPropensity π fR fO) = π/(1-π)*(fR/fO) ∧
    fO/fR = π/(1-π)*correctedOdds (studyPropensity π fR fO) := by
  have hπc : 0 < 1-π := sub_pos.mpr hπ1
  have hm : 0 < π*fR+(1-π)*fO := add_pos (mul_pos hπ hR) (mul_pos hπc hO)
  have hcomp : 1-studyPropensity π fR fO = (1-π)*fO/(π*fR+(1-π)*fO) := by
    unfold studyPropensity
    field_simp [ne_of_gt hm]
    <;> ring
  refine ⟨div_pos (mul_pos hπ hR) hm, ?_, ?_, ?_⟩
  · unfold studyPropensity
    apply (div_lt_one hm).mpr
    nlinarith [mul_pos hπc hO]
  · unfold printedOdds
    rw [hcomp]
    unfold studyPropensity
    field_simp [ne_of_gt hm,ne_of_gt hπc,ne_of_gt hO]
    <;> ring
  · unfold correctedOdds
    rw [hcomp]
    unfold studyPropensity
    field_simp [ne_of_gt hm,ne_of_gt hπ,ne_of_gt hR,ne_of_gt hπc]
    <;> ring

/-- Multiplying either study-odds weight by the replication density gives
the exact mass factors used in corrected footnote 7, p. 578. -/
theorem transport_mass_factors (π R O : ℝ) (hπ : 0 < π) (hπ1 : π < 1)
    (hR : 0 < R) (hO : 0 < O) :
    R*correctedOdds (studyPropensity π R O) = ((1-π)/π)*O ∧
    R*printedOdds (studyPropensity π R O) = (π/(1-π))*(R^2/O) := by
  have hb := transport_bayes π R O hπ hπ1 hR hO
  have hc : 0 < π/(1-π) := div_pos hπ (sub_pos.mpr hπ1)
  have hcorr : correctedOdds (studyPropensity π R O) = (O/R)/(π/(1-π)) := by
    apply (eq_div_iff (ne_of_gt hc)).mpr
    nlinarith [hb.2.2.2]
  constructor
  · rw [hcorr]
    field_simp [ne_of_gt hR,ne_of_gt hπ,ne_of_gt (sub_pos.mpr hπ1)]
    <;> ring
  · rw [hb.2.2.1]
    ring

/-- T12(ii), discrete form, corrected footnote 7: reciprocal odds transport
any positive common-support finite covariate distribution exactly; a positive
constant in all weights cancels. -/
theorem transport_corrected_finite {n : ℕ} (π : ℝ) (fR fO : Fin n → ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hR : ∀ x, 0 < fR x) (hO : ∀ x, 0 < fO x)
    (hsR : ∑ x, fR x = 1) (hsO : ∑ x, fO x = 1) :
    (∀ x, reweighted fR (fun u => correctedOdds (studyPropensity π (fR u) (fO u))) x = fO x) ∧
    (∀ c : ℝ, 0 < c → ∀ x,
      reweighted fR (fun u => c*correctedOdds (studyPropensity π (fR u) (fO u))) x = fO x) := by
  have hc : 0 < (1-π)/π := div_pos (sub_pos.mpr hπ1) hπ
  have hm (x : Fin n) :
      fR x * correctedOdds (studyPropensity π (fR x) (fO x)) = ((1-π)/π)*fO x := by
    exact (transport_mass_factors π (fR x) (fO x) hπ hπ1 (hR x) (hO x)).1
  constructor
  · intro x
    unfold reweighted
    simp_rw [hm]
    rw [← Finset.mul_sum, hsO, mul_one]
    exact mul_div_cancel_left₀ _ (ne_of_gt hc)
  · intro c hc' x
    have hm' (u : Fin n) : fR u*(c*correctedOdds (studyPropensity π (fR u) (fO u))) =
        (c*((1-π)/π))*fO u := by rw [← mul_assoc, mul_comm (fR u) c, mul_assoc, hm, mul_assoc]
    unfold reweighted
    simp_rw [hm']
    rw [← Finset.mul_sum, hsO, mul_one]
    exact mul_div_cancel_left₀ _ (ne_of_gt (mul_pos hc' hc))

/-- T12(iii), discrete form, corrected footnote 7: printed odds give density
proportional to fR²/fO, and this equals fO exactly when the two study
covariate distributions agree everywhere on their common positive support. -/
theorem transport_printed_finite {n : ℕ} (π : ℝ) (fR fO : Fin n → ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hR : ∀ x, 0 < fR x) (hO : ∀ x, 0 < fO x)
    (hsR : ∑ x, fR x = 1) (hsO : ∑ x, fO x = 1) :
    (∀ x, reweighted fR (fun u => printedOdds (studyPropensity π (fR u) (fO u))) x =
      (fR x)^2/(fO x) / ∑ u, (fR u)^2/(fO u)) ∧
    ((∀ x, reweighted fR (fun u => printedOdds (studyPropensity π (fR u) (fO u))) x = fO x) ↔ fR = fO) := by
  let D := ∑ u : Fin n, (fR u)^2/fO u
  have hD : 0 < D := by
    have hx : ∃ u ∈ (Finset.univ : Finset (Fin n)), fR u ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsR]; norm_num)
    obtain ⟨x,hx,hx'⟩ := hx
    apply Finset.sum_pos' (fun u _ => le_of_lt (div_pos (sq_pos_of_pos (hR u)) (hO u)))
    exact ⟨x,hx,div_pos (sq_pos_of_pos (hR x)) (hO x)⟩
  have hC : 0 < π/(1-π) := div_pos hπ (sub_pos.mpr hπ1)
  have hm (x : Fin n) : fR x*printedOdds (studyPropensity π (fR x) (fO x)) =
      (π/(1-π))*((fR x)^2/fO x) := by
    rw [(transport_bayes π (fR x) (fO x) hπ hπ1 (hR x) (hO x)).2.2.1]
    ring
  have hform (x : Fin n) : reweighted fR (fun u => printedOdds (studyPropensity π (fR u) (fO u))) x =
      (fR x)^2/fO x / D := by
    unfold reweighted
    simp_rw [hm]
    rw [← Finset.mul_sum]
    change ((π/(1-π))*((fR x)^2/fO x))/((π/(1-π))*D) = _
    field_simp [ne_of_gt hC,ne_of_gt hD,ne_of_gt (sub_pos.mpr hπ1),ne_of_gt (hO x)]
    <;> ring
  refine ⟨hform,?_⟩
  constructor
  · intro he
    have hc : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    have hsq : (Real.sqrt D)^2=D := Real.sq_sqrt (le_of_lt hD)
    have hratio (x : Fin n) : fR x = Real.sqrt D*fO x := by
      have hx := he x
      rw [hform x] at hx
      have hneq : fO x ≠ 0 := ne_of_gt (hO x)
      have hx' : (fR x)^2 = D*(fO x)^2 := by
        field_simp [hneq,ne_of_gt hD] at hx
        nlinarith
      have hnon : 0 ≤ Real.sqrt D*fO x := mul_nonneg hc (le_of_lt (hO x))
      apply (sq_eq_sq₀ (le_of_lt (hR x)) hnon).mp
      rw [mul_pow,hsq]
      exact hx'
    have hconst : Real.sqrt D = 1 := by
      have heq : (∑ x : Fin n, fR x) = Real.sqrt D*∑ x : Fin n, fO x := by
        simp_rw [hratio]
        rw [Finset.mul_sum]
      rw [hsR,hsO,mul_one] at heq
      exact heq.symm
    funext x
    rw [hratio x,hconst,one_mul]
  · intro he
    subst fO
    intro x
    rw [hform x]
    have hd' : D=1 := by
      have hs (u : Fin n) : (fR u)^2/fR u = fR u := by
        rw [sq,mul_div_cancel_right₀ _ (ne_of_gt (hR u))]
      dsimp [D]
      simp_rw [hs]
      exact hsR
    rw [hd']
    simp [sq,ne_of_gt (hR x)]

/-- Continuous counterpart of T12, using densities with respect to an
arbitrary dominating measure. Sums are replaced by integrals; positive
common support is required almost everywhere, not at irrelevant null points. -/
noncomputable def reweightedDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f w : Ω → ℝ) (x : Ω) : ℝ :=
  f x*w x / ∫ u, f u*w u ∂ν

/-- On positive common support, normalizing fR²/fO reproduces fO exactly
when fR=fO a.e.; the density normalizer is positive when finite. This is the
continuous counterpart of the last assertion in corrected footnote 7. -/
theorem square_density_normalization {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f g : Ω → ℝ)
    (hf : ∀ᵐ x ∂ν, 0 < f x) (hg : ∀ᵐ x ∂ν, 0 < g x)
    (hif : Integrable f ν) (hig : Integrable g ν)
    (hsf : ∫ x, f x ∂ν = 1) (hsg : ∫ x, g x ∂ν = 1)
    (his : Integrable (fun x => (f x)^2/g x) ν) :
    0 < (∫ x, (f x)^2/g x ∂ν) ∧
    (((fun x => (f x)^2/g x / ∫ u, (f u)^2/g u ∂ν) =ᵐ[ν] g) ↔ f =ᵐ[ν] g) := by
  let D := ∫ x, (f x)^2/g x ∂ν
  have hnon : 0 ≤ᵐ[ν] fun x => (f x)^2/g x := by
    filter_upwards [hf,hg] with x hx hy
    exact le_of_lt (div_pos (sq_pos_of_pos hx) hy)
  have hD0 : D ≠ 0 := by
    intro he
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnon his).mp he
    have hf0 : f =ᵐ[ν] fun _ => 0 := by
      filter_upwards [hf,hg,hz] with x hx hy hxy
      exact False.elim ((ne_of_gt (div_pos (sq_pos_of_pos hx) hy)) hxy)
    have hi := integral_congr_ae hf0
    rw [hsf] at hi
    simpa using hi
  have hD : 0 < D := lt_of_le_of_ne (integral_nonneg_of_ae hnon) (Ne.symm hD0)
  refine ⟨hD,?_⟩
  constructor
  · intro he
    have hsqrt : (Real.sqrt D)^2=D := Real.sq_sqrt (le_of_lt hD)
    have hratio : f =ᵐ[ν] fun x => Real.sqrt D*g x := by
      filter_upwards [hf,hg,he] with x hx hy hxy
      have hxy' : (f x)^2 = D*(g x)^2 := by
        change (f x)^2/g x / D = g x at hxy
        field_simp [ne_of_gt hy,hD0] at hxy
        nlinarith
      apply (sq_eq_sq₀ (le_of_lt hx) (mul_nonneg (Real.sqrt_nonneg D) (le_of_lt hy))).mp
      rw [mul_pow,hsqrt]
      exact hxy'
    have hc : Real.sqrt D=1 := by
      have hi := integral_congr_ae hratio
      rw [hsf,integral_const_mul,hsg,mul_one] at hi
      exact hi.symm
    filter_upwards [hratio] with x hx
    simpa [hc] using hx
  · intro he
    have hsq : (fun x => (f x)^2/g x) =ᵐ[ν] g := by
      filter_upwards [he,hg] with x hx hy
      simp [hx,sq,ne_of_gt hy]
    have hd' : D=1 := (integral_congr_ae hsq).trans hsg
    filter_upwards [hsq] with x hx
    change (f x)^2/g x / D = g x
    simpa [hd'] using hx

/-- T12(ii–iii), general density form: reciprocal odds reproduce the original
density and printed odds reproduce normalized fR²/fO. For printed odds the
normalizer must be finite (otherwise the weighted distribution is undefined).
Equality with the original is exactly equality of the original densities a.e. -/
theorem transport_corrected_density {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (π : ℝ) (fR fO : Ω → ℝ)
    (hπ : 0 < π) (hπ1 : π < 1)
    (hR : ∀ᵐ x ∂ν, 0 < fR x) (hO : ∀ᵐ x ∂ν, 0 < fO x)
    (hiR : Integrable fR ν) (hiO : Integrable fO ν)
    (hsR : ∫ x, fR x ∂ν = 1) (hsO : ∫ x, fO x ∂ν = 1) :
    (fun x => reweightedDensity ν fR (fun u => correctedOdds (studyPropensity π (fR u) (fO u))) x) =ᵐ[ν] fO ∧
    (∀ c : ℝ, 0 < c →
      (fun x => reweightedDensity ν fR (fun u => c*correctedOdds (studyPropensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ∧
    (Integrable (fun x => (fR x)^2/fO x) ν →
      (fun x => reweightedDensity ν fR (fun u => printedOdds (studyPropensity π (fR u) (fO u))) x) =ᵐ[ν]
        (fun x => (fR x)^2/fO x / ∫ u, (fR u)^2/fO u ∂ν) ∧
      (((fun x => reweightedDensity ν fR (fun u => printedOdds (studyPropensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ↔
        fR =ᵐ[ν] fO)) := by
  let c := (1-π)/π
  let C := π/(1-π)
  have hc : 0 < c := div_pos (sub_pos.mpr hπ1) hπ
  have hC : 0 < C := div_pos hπ (sub_pos.mpr hπ1)
  have hm : (fun x => fR x*correctedOdds (studyPropensity π (fR x) (fO x))) =ᵐ[ν] fun x => c*fO x := by
    filter_upwards [hR,hO] with x hx hy
    exact (transport_mass_factors π (fR x) (fO x) hπ hπ1 hx hy).1
  have hmass : (∫ x, fR x*correctedOdds (studyPropensity π (fR x) (fO x)) ∂ν) = c := by
    rw [integral_congr_ae hm,integral_const_mul,hsO,mul_one]
  have hcorrect : (fun x => reweightedDensity ν fR (fun u => correctedOdds (studyPropensity π (fR u) (fO u))) x) =ᵐ[ν] fO := by
    filter_upwards [hm] with x hx
    unfold reweightedDensity
    rw [hmass,hx,mul_div_cancel_left₀ _ (ne_of_gt hc)]
  refine ⟨hcorrect,?_,?_⟩
  · intro k hk
    have hmk : (fun x => fR x*(k*correctedOdds (studyPropensity π (fR x) (fO x)))) =ᵐ[ν]
        fun x => (k*c)*fO x := by
      filter_upwards [hm] with x hx
      calc
        fR x*(k*correctedOdds (studyPropensity π (fR x) (fO x))) =
            k*(fR x*correctedOdds (studyPropensity π (fR x) (fO x))) := by ring
        _ = _ := by rw [hx]; ring
    have hmkint : (∫ x, fR x*(k*correctedOdds (studyPropensity π (fR x) (fO x))) ∂ν) = k*c := by
      rw [integral_congr_ae hmk,integral_const_mul,hsO,mul_one]
    filter_upwards [hmk] with x hx
    unfold reweightedDensity
    rw [hmkint,hx,mul_div_cancel_left₀ _ (ne_of_gt (mul_pos hk hc))]
  · intro hiSq
    let D := ∫ x, (fR x)^2/fO x ∂ν
    have hnorm := square_density_normalization ν fR fO hR hO hiR hiO hsR hsO hiSq
    have hD : 0 < D := hnorm.1
    have hmp : (fun x => fR x*printedOdds (studyPropensity π (fR x) (fO x))) =ᵐ[ν]
        fun x => C*((fR x)^2/fO x) := by
      filter_upwards [hR,hO] with x hx hy
      exact (transport_mass_factors π (fR x) (fO x) hπ hπ1 hx hy).2
    have hmpint : (∫ x, fR x*printedOdds (studyPropensity π (fR x) (fO x)) ∂ν) = C*D := by
      rw [integral_congr_ae hmp,integral_const_mul]
    have hform : (fun x => reweightedDensity ν fR (fun u => printedOdds (studyPropensity π (fR u) (fO u))) x) =ᵐ[ν]
        (fun x => (fR x)^2/fO x / D) := by
      filter_upwards [hmp] with x hx
      unfold reweightedDensity
      rw [hmpint,hx]
      field_simp [ne_of_gt hC,ne_of_gt hD]
    refine ⟨hform,?_⟩
    constructor
    · intro he
      exact hnorm.2.mp (hform.symm.trans he)
    · intro he
      exact hform.trans (hnorm.2.mpr he)

end AronowAudit.P010
