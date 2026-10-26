import AronowAudit.P002.Wave1.Gap.GLP0022B2
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
P002-T5, corrected Remark 3. Constant effects reduce coverage to the finite
quantile of a fixed baseline. The finite-population CLT, relative variance
consistency, and continuous Gaussian bracketing give nominal sequence coverage.
The proved corrected Theorem 1 supplies the lower bound on the full-class
liminf; the admissible increasing sequence supplies its matching upper bound.
-/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

local instance GP0022B2b_normalNullSingleton :
    NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

/-! ## Constant effects and limits inferior on a restricted set of sizes -/

/-- A constant treatment-receipt effect is the complier average treatment-receipt effect. -/
theorem GP0022B2b_SH_late_constant {n} (P : Population n) (β : ℝ)
    (hc : (compliers P).Nonempty) (hy : ∀ i, P.y i true = P.y i false + β) :
    late P = β := by
  have hcard : ((compliers P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hc)
  simp [late, groupMean, hy, hcard]

/-- Under constant effects, adjustment at the LATE gives the fixed baseline response. -/
theorem GP0022B2b_SH_observedW_baseline {n} (P : Population n)
    (hc : (compliers P).Nonempty)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β)
    (S : Finset (Fin n)) : observedW P (late P) S = fun i => P.y i false := by
  rcases hy with ⟨β, hβ⟩
  rw [GP0022B2b_SH_late_constant P β hc hβ]
  exact constant_effect_adjusted_outcomes P β hβ S

/-- The same baseline is the potential adjusted response in both assignment arms. -/
theorem GP0022B2b_SH_w_baseline {n} (P : Population n)
    (hc : (compliers P).Nonempty)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β) (a : Bool) :
    w P a (late P) = fun i => P.y i false := by
  rcases hy with ⟨β, hβ⟩
  rw [GP0022B2b_SH_late_constant P β hc hβ]
  funext i
  unfold w
  cases hdi : P.d i a <;> simp [hdi, binary, hβ]

/-- Retain the actual attainable finite quantile in the fixed-baseline reduction. -/
theorem GP0022B2b_SH_coverage_baseline {n} (P : Population n)
    (hc : (compliers P).Nonempty)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β) (α : ℝ) :
    coverage P (late P) α = probability P (fun S =>
      rawAR P (fun i => P.y i false) S ≤
        quantile P (rawAR P (fun i => P.y i false)) α) := by
  unfold coverage accepted
  simp_rw [GP0022B2b_SH_observedW_baseline P hc hy]

/-- Transfer the actual Theta moment premise to the fixed baseline vector. -/
theorem GP0022B2b_SH_baseline_moment_bound {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β) :
    fourthNorm (fun i => P.y i false - mean (fun j => P.y j false)) ≤
      A * Real.sqrt (popVar (fun i => P.y i false)) := by
  rcases hP with ⟨hv, hm, hc, hlo, hhi, hcov, hfourth⟩
  have hh := hfourth true
  unfold v at hh
  rw [GP0022B2b_SH_w_baseline P hc hy true] at hh
  exact hh

private theorem GP0022B2b_SH_probability_congr {n} (P : Population n)
    {E F : Finset (Fin n) → Prop}
    (hEF : ∀ S ∈ assignments P, E S ↔ F S) : probability P E = probability P F := by
  unfold probability
  have he : (assignments P).filter E = (assignments P).filter F := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hS, hE⟩
      exact ⟨hS, (hEF S hS).mp hE⟩
    · rintro ⟨hS, hF⟩
      exact ⟨hS, (hEF S hS).mpr hF⟩
  rw [he]

private theorem GP0022B2b_SH_probability_mono {n} (P : Population n)
    {E F : Finset (Fin n) → Prop}
    (hEF : ∀ S ∈ assignments P, E S → F S) : probability P E ≤ probability P F := by
  unfold probability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (assignments P).filter E ⊆
      (assignments P).filter F from by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hS, hE⟩
    exact Finset.mem_filter.mpr ⟨hS, hEF S hS hE⟩)

/-- Finite-support quantile bracket, including an upper endpoint not itself attained.
This uses precisely the attainable-minimum quantile in P002, with no change to ties. -/
theorem GP0022B2b_SH_quantile_bracket {n} (P : Population n) (hP : ValidDesign P)
    (g : Finset (Fin n) → ℝ≥0∞) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (a b : ℝ≥0∞)
    (ha : probability P (fun S => g S ≤ a) < 1 - α)
    (hb : 1 - α ≤ probability P (fun S => g S ≤ b)) :
    a < quantile P g α ∧ quantile P g α ≤ b := by
  have hlower : a < quantile P g α := by
    by_contra hnot
    have hqa : quantile P g α ≤ a := le_of_not_gt hnot
    have hm : probability P (fun S => g S ≤ quantile P g α) ≤
        probability P (fun S => g S ≤ a) := by
      apply GP0022B2b_SH_probability_mono
      intro S hS hSq
      exact hSq.trans hqa
    have hv := quantile_valid P hP g α hα
    linarith
  let B := (assignments P).filter (fun S => g S ≤ b)
  have hB : B.Nonempty := by
    by_contra hnot
    have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hpzero : probability P (fun S => g S ≤ b) = 0 := by
      unfold probability
      change (B.card : ℝ) / ((assignments P).card : ℝ) = 0
      rw [he]
      simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    rw [hpzero] at hb
    linarith [hα.2]
  let L := B.image g
  have hL : L.Nonempty := hB.image g
  let t := L.max' hL
  have htL : t ∈ L := Finset.max'_mem L hL
  have htb : t ≤ b := by
    rcases Finset.mem_image.mp htL with ⟨S, hS, hgt⟩
    rw [← hgt]
    exact (Finset.mem_filter.mp hS).2
  have hCDF : probability P (fun S => g S ≤ t) =
      probability P (fun S => g S ≤ b) := by
    apply GP0022B2b_SH_probability_congr
    intro S hS
    constructor
    · exact fun hSt => hSt.trans htb
    · intro hSb
      have hSB : S ∈ B := Finset.mem_filter.mpr ⟨hS, hSb⟩
      exact Finset.le_max' L (g S) (Finset.mem_image.mpr ⟨S, hSB, rfl⟩)
  let C := ((assignments P).image g).filter (fun z =>
    1 - α ≤ probability P (fun S => g S ≤ z))
  have htC : t ∈ C := by
    apply Finset.mem_filter.mpr
    constructor
    · rcases Finset.mem_image.mp htL with ⟨S, hS, hgt⟩
      exact Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, hgt⟩
    · rw [hCDF]
      exact hb
  have hC : C.Nonempty := ⟨t, htC⟩
  have hqt : quantile P g α ≤ t := by
    change (if h : C.Nonempty then C.min' h else ⊤) ≤ t
    rw [dite_eq_left hC]
    exact Finset.min'_le C t htC
  exact ⟨hlower, hqt.trans htb⟩

/-- Continuous-law CDF bracketing gives nominal probability at the actual
finite quantile. This is a generic analytic lemma, not an assumption that the
constant-effect population sequence has the required CDF limit. -/
theorem GP0022B2b_SH_nominal_of_cdf_limits (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (g : ∀ j, Finset (Fin (sizes j)) → ℝ≥0∞)
    (hP : ∀ j, ValidDesign (P j)) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (H : ℝ → ℝ)
    (hCDF : ∀ t : ℝ, 0 < t → Tendsto (fun j =>
      probability (P j) (fun S => g j S ≤ ENNReal.ofReal t)) atTop (nhds (H t)))
    (hbracket : ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ,
      0 < a ∧ 0 < b ∧ H a < 1 - α ∧ 1 - α < H b ∧ H b < 1 - α + ε) :
    Tendsto (fun j => probability (P j) (fun S =>
      g j S ≤ quantile (P j) (g j) α)) atTop (nhds (1 - α)) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    exact Eventually.of_forall (fun j =>
      hx.trans_le (quantile_valid (P j) (hP j) (g j) α hα))
  · intro x hx
    rcases hbracket (x - (1 - α)) (sub_pos.mpr hx) with
      ⟨a, b, ha, hb, hHa, hHb, hHbx⟩
    have hl : ∀ᶠ j in atTop,
        probability (P j) (fun S => g j S ≤ ENNReal.ofReal a) < 1 - α :=
      (tendsto_order.1 (hCDF a ha)).2 _ hHa
    have hu : ∀ᶠ j in atTop,
        1 - α < probability (P j) (fun S => g j S ≤ ENNReal.ofReal b) :=
      (tendsto_order.1 (hCDF b hb)).1 _ hHb
    have hHx : H b < x := by linarith only [hHbx]
    have hxevent : ∀ᶠ j in atTop,
        probability (P j) (fun S => g j S ≤ ENNReal.ofReal b) < x :=
      (tendsto_order.1 (hCDF b hb)).2 _ hHx
    filter_upwards [hl, hu, hxevent] with j hlj huj hxj
    have hq : quantile (P j) (g j) α ≤ ENNReal.ofReal b :=
      (GP0022B2b_SH_quantile_bracket (P j) (hP j) (g j) α hα
        (ENNReal.ofReal a) (ENNReal.ofReal b) hlj huj.le).2
    have hp : probability (P j) (fun S => g j S ≤ quantile (P j) (g j) α) ≤
        probability (P j) (fun S => g j S ≤ ENNReal.ofReal b) := by
      apply GP0022B2b_SH_probability_mono
      intro S hS hg
      exact hg.trans hq
    exact hp.trans_lt hxj

/-- The absolute-standard-normal CDF at positive arguments. -/
def GP0022B2b_SH_absNormalCDF (t : ℝ) : ℝ :=
  2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t - 1

/-- The CDF bracketing premise for the absolute normal law.
Surjectivity of the normal CDF avoids a separate epsilon/delta cutoff argument. -/
theorem GP0022B2b_SH_normal_bracket (α : ℝ) (hα : 0 < α ∧ α < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ GP0022B2b_SH_absNormalCDF a < 1 - α ∧
      1 - α < GP0022B2b_SH_absNormalCDF b ∧ GP0022B2b_SH_absNormalCDF b < 1 - α + ε := by
  let d : ℝ := min (α / 4) (ε / 4)
  have hd0 : 0 < d := lt_min (by linarith [hα.1]) (by linarith)
  have hdα : d ≤ α / 4 := min_le_left _ _
  have hdε : d ≤ ε / 4 := min_le_right _ _
  obtain ⟨a, ha⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := (3 : ℝ) / 4 - α / 4)
    (by linarith [hα.2]) (by linarith [hα.1])
  obtain ⟨b, hb⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := 1 - α / 2 + d)
    (by linarith [hα.2]) (by linarith [hα.1])
  have ha0 : 0 < a := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero, ha]
    linarith [hα.2]
  have hb0 : 0 < b := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero, hb]
    linarith [hα.2]
  refine ⟨a, b, ha0, hb0, ?_, ?_, ?_⟩
  · unfold GP0022B2b_SH_absNormalCDF
    rw [ha]
    linarith [hα.2]
  · unfold GP0022B2b_SH_absNormalCDF
    rw [hb]
    linarith
  · unfold GP0022B2b_SH_absNormalCDF
    rw [hb]
    linarith

/-- Nominal constant-effect coverage and conversion to `ENNReal`, conditional on the
studentized CDF limit. -/
theorem GP0022B2b_SH_constant_nominal_of_cdf (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (δ r A α : ℝ) (hα : 0 < α ∧ α < 1) (hP : ∀ j, Theta (P j) δ r A)
    (hconstant : ∀ j, ∃ β, ∀ i, (P j).y i true = (P j).y i false + β)
    (hCDF : ∀ t : ℝ, 0 < t → Tendsto (fun j => probability (P j)
      (fun S => rawAR (P j) (fun i => (P j).y i false) S ≤ ENNReal.ofReal t))
      atTop (nhds (GP0022B2b_SH_absNormalCDF t))) :
    Tendsto (fun j => ENNReal.ofReal (coverage (P j) (late (P j)) α))
      atTop (nhds (ENNReal.ofReal (1 - α))) := by
  have hnom := GP0022B2b_SH_nominal_of_cdf_limits sizes P
    (fun j => rawAR (P j) (fun i => (P j).y i false))
    (fun j => (hP j).1) α hα GP0022B2b_SH_absNormalCDF hCDF
    (fun ε hε => GP0022B2b_SH_normal_bracket α hα ε hε)
  have hfun : (fun j => coverage (P j) (late (P j)) α) =
      (fun j => probability (P j) (fun S =>
        rawAR (P j) (fun i => (P j).y i false) S ≤
          quantile (P j) (rawAR (P j) (fun i => (P j).y i false)) α)) := by
    funext j
    exact GP0022B2b_SH_coverage_baseline (P j) (hP j).2.2.1 (hconstant j) α
  apply ENNReal.tendsto_ofReal
  rw [hfun]
  exact hnom

/-- The lower bound uses the same `q` as the sequential upper limit.
In particular, mere boundedness below of the full liminf is not a premise here. -/
theorem GP0022B2b_SH_sparse_liminf (E : Set ℕ) (a : ℕ → ℝ≥0∞) (q : ℝ≥0∞)
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (hE : ∀ j, sizes j ∈ E)
    (b : ℕ → ℝ≥0∞)
    (hlower : q ≤ Filter.liminf a (atTop ⊓ Filter.principal E))
    (hab : ∀ j, a (sizes j) ≤ b j) (hb : Tendsto b atTop (nhds q)) :
    Filter.liminf a (atTop ⊓ Filter.principal E) = q := by
  have hs : Tendsto sizes atTop (atTop ⊓ Filter.principal E) := by
    apply tendsto_inf.2
    refine ⟨hsizes.tendsto_atTop, ?_⟩
    exact tendsto_principal.2 (Eventually.of_forall hE)
  have hsub : Filter.liminf a (atTop ⊓ Filter.principal E) ≤
      Filter.liminf (a ∘ sizes) atTop := hs.liminf_le_liminf_comp
  have hbound : Filter.liminf (a ∘ sizes) atTop ≤ Filter.liminf b atTop := by
    exact Filter.liminf_le_liminf (Eventually.of_forall hab)
  apply le_antisymm
  · exact hsub.trans (hbound.trans_eq hb.liminf_eq)
  · exact hlower

/-- The nested beta/model infimum is bounded above by any admissible model. -/
theorem GP0022B2b_SH_infCoverage_le {n} (P : Population n) (δ r A α : ℝ)
    (hP : Theta P δ r A) :
    infCoverageTheta n δ r A α ≤ ENNReal.ofReal (coverage P (late P) α) := by
  unfold infCoverageTheta
  exact (iInf_le_of_le (late P)
    (iInf_le_of_le (⟨P, hP, rfl⟩ : {Q : Population n // Theta Q δ r A ∧ late Q = late P})
      le_rfl))

/-- The worst-case coverage liminf equals nominal coverage, conditional on a
full-class lower bound and an admissible sequence with nominal limiting coverage. -/
theorem GP0022B2b_SH_liminf_from_coverage (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (δ r A α : ℝ)
    (hP : ∀ j, Theta (P j) δ r A)
    (hlower : ENNReal.ofReal (1 - α) ≤ Filter.liminf
      (fun N => infCoverageTheta N δ r A α)
      (atTop ⊓ Filter.principal {N | ∃ Q : Population N, Theta Q δ r A}))
    (hseq : Tendsto (fun j => ENNReal.ofReal (coverage (P j) (late (P j)) α))
      atTop (nhds (ENNReal.ofReal (1 - α)))) :
    Filter.liminf (fun N => infCoverageTheta N δ r A α)
      (atTop ⊓ Filter.principal {N | ∃ Q : Population N, Theta Q δ r A}) =
        ENNReal.ofReal (1 - α) := by
  apply GP0022B2b_SH_sparse_liminf _ _ _ sizes hsizes
    (fun j => (show ∃ Q : Population (sizes j), Theta Q δ r A from ⟨P j, hP j⟩))
    (fun j => ENNReal.ofReal (coverage (P j) (late (P j)) α)) hlower
  · intro j
    exact GP0022B2b_SH_infCoverage_le (P j) δ r A α (hP j)
  · exact hseq


/-! The variance and CLT lemmas below are adapted from the fixed-response
lemmas of `GLP0022B2.lean`. They use the finite-population CLT and finite
variance-ratio bound without an extra statistical premise. -/

private lemma GP0022B2b_probability_union {n} (P : Population n)
    (E F : Finset (Fin n) → Prop) :
    probability P (fun S => E S ∨ F S) ≤ probability P E + probability P F := by
  simp only [DecisionLemma12_probability_eq_expectation]
  rw [← DecisionLemma12_expectation_add]
  apply DecisionLemma12_expectation_mono
  intro S hS
  by_cases hE : E S <;> by_cases hF : F S <;> simp [hE, hF]

private lemma GP0022B2b_rawTau_mean {n} (P : Population n) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P q S = fraction P * (groupMean S q - mean q) := by
  have hcard := (Finset.mem_powersetCard.mp hS).2
  rw [rawTau_sum]
  simp only [fraction, groupMean, mean, hcard]
  by_cases hm : (P.n1 : ℝ) = 0
  · have hmN : P.n1 = 0 := by exact_mod_cast hm
    have hsz : S = ∅ := Finset.card_eq_zero.mp (hcard.trans hmN)
    simp [hsz, hm]
  · field_simp
    <;> ring

private lemma GP0022B2b_rawTau_variance {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) :
    designVariance P (rawTau P q) =
      (fraction P)^2 * (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
  calc
    _ = designVariance P (fun S => fraction P * groupMean S q - fraction P * mean q) := by
      apply NDS_variance_congr
      intro S hS
      rw [GP0022B2b_rawTau_mean P q S hS]
      ring
    _ = _ := by rw [NDS_variance_affine P hP, NDS_groupMean_variance P hP]; ring

private lemma GP0022B2b_rawTau_variance_pos {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (hq : 0 < popVar q) :
    0 < designVariance P (rawTau P q) := by
  rw [GP0022B2b_rawTau_variance P hP]
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hn := hm.trans hmn
  apply mul_pos (mul_pos (sq_pos_of_pos (div_pos hm hn)) _) hq
  exact sub_pos.mpr ((one_div_lt_one_div hn hm).mpr hmn)

private lemma GP0022B2b_standardize {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (hq : 0 < popVar q)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P q S / Real.sqrt (designVariance P (rawTau P q)) =
      (groupMean S q - mean q) /
        Real.sqrt ((1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q) := by
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hp : 0 < fraction P := div_pos hm (hm.trans hmn)
  rw [GP0022B2b_rawTau_mean P q S hS, GP0022B2b_rawTau_variance P hP]
  rw [mul_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp.le]
  exact mul_div_mul_left _ _ hp.ne'

/-- A fourth-moment condition implies the Hájek maximal-entry condition. -/
private lemma GP0022B2b_maximum_bound {n} (P : Population n) (q : Fin n → ℝ)
    (hn : 2 ≤ n) (hv : 0 < popVar q) (r K : ℝ) (hr : 0 < r)
    (hK : 0 ≤ K) (hmin : r * n ≤ ((min P.n1 (n-P.n1) : ℕ) : ℝ))
    (hq : ∑ i, (q i-mean q)^4 ≤ K * n * (popVar q)^2) :
    maximum (fun i => (q i-mean q)^2) /
      (((min P.n1 (n-P.n1) : ℕ) : ℝ) * popVar q) ≤
        Real.sqrt K / (r * Real.sqrt n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hminpos : (0 : ℝ) < ((min P.n1 (n-P.n1) : ℕ) : ℝ) :=
    (mul_pos hr hnR).trans_le hmin
  have hpoint (i : Fin n) : (q i-mean q)^2 ≤ Real.sqrt K * Real.sqrt n * popVar q := by
    have hi : (q i-mean q)^4 ≤ ∑ j, (q j-mean q)^4 :=
      Finset.single_le_sum (f := fun j => (q j-mean q)^4)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hs : (Real.sqrt K * Real.sqrt n * popVar q)^2 = K*n*(popVar q)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hnR.le]
    nlinarith [sq_nonneg (q i-mean q), Real.sqrt_nonneg K,
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg K) hroot.le) hv.le]
  have hmax : maximum (fun i => (q i-mean q)^2) ≤ Real.sqrt K * Real.sqrt n * popVar q := by
    exact maximum_le _ _ (by positivity) hpoint
  calc
    _ ≤ (Real.sqrt K * Real.sqrt n * popVar q) /
        (((min P.n1 (n-P.n1) : ℕ) : ℝ) * popVar q) :=
      div_le_div_of_nonneg_right hmax (by positivity)
    _ = (Real.sqrt K * Real.sqrt n) / ((min P.n1 (n-P.n1) : ℕ) : ℝ) := by field_simp
    _ ≤ (Real.sqrt K * Real.sqrt n) / (r*n) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hr hnR) hmin
    _ = (Real.sqrt K * Real.sqrt n) / (r*(Real.sqrt n)^2) := by
      rw [Real.sq_sqrt hnR.le]
    _ = _ := by field_simp; <;> ring

private lemma GP0022B2b_rawCLT (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (q : ∀ j, Fin (sizes j) → ℝ)
    (hP : ∀ j, ValidDesign (P j)) (hq : ∀ j, 0 < popVar (q j))
    (r K : ℝ) (hr : 0 < r) (hK : 0 ≤ K)
    (hl : ∀ j, r*sizes j ≤ ((P j).n1 : ℝ))
    (hu : ∀ j, ((P j).n1 : ℝ) ≤ (1-r)*sizes j)
    (hfour : ∀ j, ∑ i, (q j i-mean (q j))^4 ≤ K*sizes j*(popVar (q j))^2) :
    ∀ t : ℝ, Tendsto (fun j => probability (P j) (fun S =>
      rawTau (P j) (q j) S / Real.sqrt (designVariance (P j) (rawTau (P j) (q j))) ≤ t))
      atTop (nhds (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t)) := by
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hroot : Tendsto (fun j => Real.sqrt (sizes j : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have hb : Tendsto (fun j => Real.sqrt K / (r*Real.sqrt (sizes j : ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (hroot.const_mul_atTop hr)
  have hmin (j) : r*sizes j ≤ ((min (P j).n1 (sizes j-(P j).n1) : ℕ) : ℝ) := by
    rw [Nat.cast_min, Nat.cast_sub (hP j).2.2.le]
    exact le_min (hl j) (by linarith [hu j])
  have hmax := squeeze_zero (fun j => div_nonneg (by
      unfold maximum
      exact Finset.le_max' _ _ (Finset.mem_insert_self _ _))
        (mul_nonneg (Nat.cast_nonneg _) (hq j).le))
    (fun j => GP0022B2b_maximum_bound (P j) (q j) (hP j).1 (hq j) r K hr hK (hmin j) (hfour j)) hb
  intro t
  have h := finitePopulationCLT sizes hsizes P q hP hq hmax t
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  convert h using 1
  funext j
  exact GP0022B2b_SH_probability_congr (P j) (fun S hS => by
    rw [GP0022B2b_standardize (P j) (hP j) (q j) (hq j) S hS])


private lemma GP0022B2b_cdf_lt (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (x : ∀ j, Finset (Fin (sizes j)) → ℝ)
    (hseq : ∀ t, Tendsto (fun j => probability (P j) (fun S => x j S ≤ t))
      atTop (nhds (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t)))
    (t : ℝ) :
    Tendsto (fun j => probability (P j) (fun S => x j S < t))
      atTop (nhds (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t)) := by
  apply tendsto_order.2
  constructor
  · intro z hz
    have hcont := AronowAudit.P053.NormalCompletion.cdf_continuousAt
      (ProbabilityTheory.gaussianReal 0 1) t
    have he : ∀ᶠ a in nhdsWithin t (Set.Iio t),
        z < ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a :=
      (hcont.tendsto.mono_left inf_le_left).eventually (eventually_gt_nhds hz)
    obtain ⟨a, hFa, ha⟩ := (he.and self_mem_nhdsWithin).exists
    filter_upwards [(tendsto_order.1 (hseq a)).1 z hFa] with j hj
    exact hj.trans_le (GP0022B2b_SH_probability_mono (P j) (fun S hS hx => hx.trans_lt ha))
  · intro z hz
    filter_upwards [(tendsto_order.1 (hseq t)).2 z hz] with j hj
    exact (GP0022B2b_SH_probability_mono (P j) (fun S hS hx => hx.le)).trans_lt hj

private lemma GP0022B2b_abs_cdf (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (x : ∀ j, Finset (Fin (sizes j)) → ℝ)
    (hseq : ∀ t, Tendsto (fun j => probability (P j) (fun S => x j S ≤ t))
      atTop (nhds (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t)))
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun j => probability (P j) (fun S => |x j S| ≤ t))
      atTop (nhds (GP0022B2b_SH_absNormalCDF t)) := by
  have he (j) : probability (P j) (fun S => |x j S| ≤ t) =
      probability (P j) (fun S => x j S ≤ t) -
        probability (P j) (fun S => x j S < -t) := by
    simp only [DecisionLemma12_probability_eq_expectation]
    rw [← expectation_sub]
    apply DecisionLemma12_expectation_congr
    intro S hS
    by_cases h1 : x j S ≤ t <;> by_cases h0 : x j S < -t
    · have ha : ¬ |x j S| ≤ t := by rw [abs_le]; intro h; linarith
      simp [h1, h0, ha]
    · have ha : |x j S| ≤ t := abs_le.mpr ⟨by linarith, h1⟩
      simp [h1, h0, ha]
    · linarith
    · have ha : ¬ |x j S| ≤ t := fun h => h1 (abs_le.mp h).2
      simp [h1, h0, ha]
  simp_rw [he]
  have h := (hseq t).sub (GP0022B2b_cdf_lt sizes P x hseq (-t))
  rw [AronowAudit.P053.NormalCompletion.normal_cdf_neg] at h
  convert h using 1 <;> simp only [GP0022B2b_SH_absNormalCDF] <;> ring

private lemma GP0022B2b_absStudent_sq (x s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) :
    absStudent x s ≤ ENNReal.ofReal a ↔ x^2 ≤ a^2*s := by
  by_cases hs0 : s = 0
  · subst s
    by_cases hx : x = 0
    · simp [absStudent, hx]
    · have hx2 := sq_pos_of_ne_zero hx
      simp [absStudent, hx, not_le_of_gt hx2, ENNReal.ofReal_ne_top]
  · have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr (lt_of_le_of_ne hs (Ne.symm hs0))
    rw [absStudent, if_neg hs0, ENNReal.ofReal_le_ofReal_iff ha, div_le_iff₀ hsp]
    have hsq := Real.sq_sqrt hs
    constructor
    · intro h
      have h' := (sq_le_sq₀ (abs_nonneg x) (mul_nonneg ha hsp.le)).mpr h
      nlinarith [sq_abs x]
    · intro h
      apply (sq_le_sq₀ (abs_nonneg x) (mul_nonneg ha hsp.le)).mp
      nlinarith [sq_abs x]

private lemma GP0022B2b_standard_sq (x V a : ℝ) (hV : 0 < V) (ha : 0 ≤ a) :
    |x / Real.sqrt V| ≤ a ↔ x^2 ≤ a^2*V := by
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have hsq := Real.sq_sqrt hV.le
  constructor
  · intro h
    have h' := (sq_le_sq₀ (abs_nonneg x) (mul_nonneg ha hs.le)).mpr h
    nlinarith [sq_abs x]
  · intro h
    apply (sq_le_sq₀ (abs_nonneg x) (mul_nonneg ha hs.le)).mp
    nlinarith [sq_abs x]

private lemma GP0022B2b_student_upper (x s V a b : ℝ) (hs : 0 ≤ s)
    (hV : 0 < V) (ha : 0 < a) (hab : a < b)
    (hstudent : absStudent x s ≤ ENNReal.ofReal a)
    (hgood : |s/V-1| < (b^2-a^2)/a^2) :
    |x / Real.sqrt V| ≤ b := by
  apply (GP0022B2b_standard_sq x V b hV (ha.trans hab).le).mpr
  have h := (GP0022B2b_absStudent_sq x s a hs ha.le).mp hstudent
  have hratio := (abs_lt.mp hgood).2
  have hscale : a^2*s ≤ b^2*V := by
    have hh := (lt_div_iff₀ (sq_pos_of_pos ha)).mp hratio
    have he : (s/V-1)*a^2*V = a^2*s-a^2*V := by field_simp; <;> ring
    have hh' := mul_lt_mul_of_pos_right hh hV
    rw [he] at hh'
    nlinarith
  exact h.trans hscale

private lemma GP0022B2b_student_lower (x s V B a c : ℝ)
    (hs : 0 ≤ s) (hV : 0 < V) (hB : 0 < B) (hVB : V ≤ B)
    (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (hraw : |x / Real.sqrt V| ≤ c)
    (hgood : |s/B-1| < (a^2-c^2)/a^2) :
    absStudent x s ≤ ENNReal.ofReal a := by
  apply (GP0022B2b_absStudent_sq x s a hs ha.le).mpr
  have h := (GP0022B2b_standard_sq x V c hV hc).mp hraw
  have hratio := (abs_lt.mp hgood).1
  rw [← neg_div] at hratio
  have hh := (div_lt_iff₀ (sq_pos_of_pos ha)).mp hratio
  have he : (s/B-1)*a^2*B = a^2*s-a^2*B := by field_simp; <;> ring
  have hh' := mul_lt_mul_of_pos_right hh hB
  rw [he] at hh'
  have hcb := mul_le_mul_of_nonneg_left hVB (sq_nonneg c)
  nlinarith

private lemma GP0022B2b_sigma_nonneg {n} (P : Population n) (q : Fin n → ℝ)
    (S : Finset (Fin n)) : 0 ≤ rawSigma2 P q S := by
  unfold rawSigma2
  positivity

private lemma GP0022B2b_variance_ratio_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (q : ∀ j, Fin (sizes j) → ℝ)
    (hP : ∀ j, ValidDesign (P j)) (hq : ∀ j, 0 < popVar (q j))
    (r K : ℝ) (hr : 0 < r) (hK : 0 ≤ K)
    (hl : ∀ j, r*sizes j ≤ ((P j).n1 : ℝ))
    (hu : ∀ j, ((P j).n1 : ℝ) ≤ (1-r)*sizes j)
    (hfour : ∀ j, ∑ i, (q j i-mean (q j))^4 ≤ K*sizes j*(popVar (q j))^2)
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun j => probability (P j) (fun S =>
      |rawSigma2 (P j) (q j) S / designVariance (P j) (rawTau (P j) (q j))-1| ≥ κ))
      atTop (nhds 0) := by
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hi : Tendsto (fun j => 1/(sizes j : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hlin : Tendsto (fun j => 2*K/(r*(sizes j : ℝ))) atTop (nhds 0) := by
    convert hi.const_mul (2*K/r) using 1 <;> first | funext j; ring | simp
  have hroot : Tendsto (fun j => Real.sqrt (2*K/(r*(sizes j : ℝ)))) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hlin
  have hlin' : Tendsto (fun j => 2/(r*(sizes j : ℝ))) atTop (nhds 0) := by
    convert hi.const_mul (2/r) using 1 <;> first | funext j; ring | simp
  have hb : Tendsto (fun j =>
      (2*Real.sqrt (2*K/(r*(sizes j : ℝ))) + 2/(r*(sizes j : ℝ)) +
        1/(sizes j : ℝ))/κ) atTop (nhds 0) := by
    simpa using (((hroot.const_mul 2).add hlin').add hi).div_const κ
  apply squeeze_zero' (Eventually.of_forall (fun _ => DecisionLemma12_probability_nonneg _ _)) _ hb
  filter_upwards [(hN.const_mul_atTop hr).eventually_ge_atTop 2] with j hj
  have hm : 2 ≤ (P j).n1 := by exact_mod_cast hj.trans (hl j)
  have hc : 2 ≤ sizes j-(P j).n1 := by
    have hh : (2 : ℝ) ≤ ((sizes j-(P j).n1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hP j).2.2.le]
      linarith [hu j]
    exact_mod_cast hh
  exact DecisionLemma12_conditional_bound (P j) (hP j) hm hc (q j) (hq j)
    r K κ hr hK hκ (hl j) (hu j) (hfour j)

/-- Studentization preserves the absolute-normal limit, including the defined
zero-denominator branches. Both CDF bounds use the relative variance error. -/
theorem GP0022B2b_studentized_cdf (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (q : ∀ j, Fin (sizes j) → ℝ)
    (hP : ∀ j, ValidDesign (P j)) (hq : ∀ j, 0 < popVar (q j))
    (r K : ℝ) (hr : 0 < r) (hK : 0 ≤ K)
    (hl : ∀ j, r*sizes j ≤ ((P j).n1 : ℝ))
    (hu : ∀ j, ((P j).n1 : ℝ) ≤ (1-r)*sizes j)
    (hfour : ∀ j, ∑ i, (q j i-mean (q j))^4 ≤ K*sizes j*(popVar (q j))^2)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun j => probability (P j) (fun S =>
      rawAR (P j) (q j) S ≤ ENNReal.ofReal t)) atTop
      (nhds (GP0022B2b_SH_absNormalCDF t)) := by
  have hraw := GP0022B2b_rawCLT sizes hsizes P q hP hq r K hr hK hl hu hfour
  have habs := GP0022B2b_abs_cdf sizes P _ hraw
  have herr := GP0022B2b_variance_ratio_limit sizes hsizes P q hP hq r K hr hK hl hu hfour
  have hcont : ContinuousAt GP0022B2b_SH_absNormalCDF t := by
    unfold GP0022B2b_SH_absNormalCDF
    exact (continuousAt_const.mul
      (AronowAudit.P053.NormalCompletion.cdf_continuousAt
        (ProbabilityTheory.gaussianReal 0 1) t)).sub continuousAt_const
  apply tendsto_order.2
  constructor
  · intro z hz
    have he : ∀ᶠ a in nhdsWithin t (Set.Iio t),
        z < GP0022B2b_SH_absNormalCDF a :=
      (hcont.tendsto.mono_left inf_le_left).eventually (eventually_gt_nhds hz)
    have hepos : ∀ᶠ a in nhdsWithin t (Set.Iio t), 0 < a :=
      (eventually_gt_nhds ht).filter_mono inf_le_left
    obtain ⟨a, ⟨hFa, ha0⟩, hat⟩ := ((he.and hepos).and self_mem_nhdsWithin).exists
    have hκ : 0 < (t^2-a^2)/t^2 := by
      apply div_pos _ (sq_pos_of_pos ht)
      nlinarith
    have hlim := (habs a ha0.le).sub (herr _ hκ)
    simp only [sub_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).1 z hFa] with j hj
    apply hj.trans_le
    have hle : probability (P j) (fun S =>
        |rawTau (P j) (q j) S / Real.sqrt (designVariance (P j) (rawTau (P j) (q j)))| ≤ a) ≤
        probability (P j) (fun S => rawAR (P j) (q j) S ≤ ENNReal.ofReal t) +
          probability (P j) (fun S =>
            |rawSigma2 (P j) (q j) S / designVariance (P j) (rawTau (P j) (q j))-1| ≥
              (t^2-a^2)/t^2) := by
      apply le_trans (GP0022B2b_SH_probability_mono (P j) (fun S hS hstandard => ?_))
        (GP0022B2b_probability_union (P j) _ _)
      by_cases he : |rawSigma2 (P j) (q j) S / designVariance (P j) (rawTau (P j) (q j))-1| ≥
          (t^2-a^2)/t^2
      · exact Or.inr he
      · have hV := GP0022B2b_rawTau_variance_pos (P j) (hP j) (q j) (hq j)
        exact Or.inl (GP0022B2b_student_lower _ _ _ _ t a
          (GP0022B2b_sigma_nonneg _ _ _) hV hV le_rfl ht ha0.le hat hstandard
          (lt_of_not_ge he))
    linarith only [hle]
  · intro z hz
    have he : ∀ᶠ b in nhdsWithin t (Set.Ioi t),
        GP0022B2b_SH_absNormalCDF b < z :=
      (hcont.tendsto.mono_left inf_le_left).eventually (eventually_lt_nhds hz)
    obtain ⟨b, hFb, htb⟩ := (he.and self_mem_nhdsWithin).exists
    have hκ : 0 < (b^2-t^2)/t^2 := by
      apply div_pos _ (sq_pos_of_pos ht)
      nlinarith
    have hlim := (habs b (ht.trans htb).le).add (herr _ hκ)
    simp only [add_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).2 z hFb] with j hj
    apply lt_of_le_of_lt _ hj
    apply le_trans (GP0022B2b_SH_probability_mono (P j) (fun S hS hstudent => ?_))
      (GP0022B2b_probability_union (P j) _ _)
    by_cases he : |rawSigma2 (P j) (q j) S / designVariance (P j) (rawTau (P j) (q j))-1| ≥
        (b^2-t^2)/t^2
    · exact Or.inr he
    · exact Or.inl (GP0022B2b_student_upper _ _ _ t b (GP0022B2b_sigma_nonneg _ _ _)
        (GP0022B2b_rawTau_variance_pos (P j) (hP j) _ (hq j)) ht htb hstudent
        (lt_of_not_ge he))

/-- The baseline Theta moment bound has exactly the scale-relative fourth-moment
form required by the finite-population CLT and variance-ratio estimate. -/
theorem GP0022B2b_baseline_fourth {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β)
    (hv : 0 < popVar (fun i => P.y i false)) :
    ∑ i, (P.y i false - mean (fun i => P.y i false))^4 ≤
      A^4*n*(popVar (fun i => P.y i false))^2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1.1; omega)
  have hf := GP0022B2b_SH_baseline_moment_bound P δ r A hP hy
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hf 4
  have hm : 0 ≤ mean (fun i => (P.y i false - mean (fun i => P.y i false))^4) := by
    exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hn.le
  have he : (fourthNorm (fun i => P.y i false - mean (fun i => P.y i false)))^4 =
      mean (fun i => (P.y i false - mean (fun i => P.y i false))^4) := by
    unfold fourthNorm
    calc
      _ = ((Real.sqrt (Real.sqrt (mean (fun i =>
          (P.y i false - mean (fun i => P.y i false))^4))))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hm]
  change (fourthNorm (fun i => P.y i false - mean (fun i => P.y i false)))^4 ≤
    (A*Real.sqrt (popVar (fun i => P.y i false)))^4 at hp
  rw [he, mul_pow, show (Real.sqrt (popVar (fun i => P.y i false)))^4 =
      ((Real.sqrt (popVar (fun i => P.y i false)))^2)^2 by ring,
    Real.sq_sqrt hv.le] at hp
  nlinarith only [(div_le_iff₀ hn).mp hp]

/-- Exact corrected Remark 3: constant-effect sequence coverage and the
full-class worst-case liminf are both nominal. -/
theorem corrected_remark3_sharpness_proof (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ n, Population (sizes n)) (δ r A α : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hα : 0 < α ∧ α < 1) (hP : ∀ n, Theta (P n) δ r A)
    (hconstant : ∀ n, ∃ β, ∀ i, (P n).y i true=(P n).y i false+β)
    (hnondegenerate : ∀ n, 0 < popVar (fun i => (P n).y i false)) :
    Tendsto (fun n => ENNReal.ofReal (coverage (P n) (late (P n)) α))
      atTop (nhds (ENNReal.ofReal (1-α))) ∧
    Filter.liminf (fun N => infCoverageTheta N δ r A α)
      (atTop ⊓ Filter.principal {N | ∃ Q : Population N, Theta Q δ r A}) =
        ENNReal.ofReal (1-α) := by
  have hCDF := GP0022B2b_studentized_cdf sizes hsizes P
    (fun j i => (P j).y i false) (fun j => (hP j).1) hnondegenerate r (A^4)
    hr.1 (by positivity) (fun j => (hP j).2.2.2.1) (fun j => (hP j).2.2.2.2.1)
    (fun j => GP0022B2b_baseline_fourth (P j) δ r A (hP j) (hconstant j) (hnondegenerate j))
  have hseq := GP0022B2b_SH_constant_nominal_of_cdf sizes P δ r A α hα hP hconstant hCDF
  exact ⟨hseq, GP0022B2b_SH_liminf_from_coverage sizes hsizes P δ r A α hP
    (corrected_theorem1_proof δ r A α hδ hr hA hα) hseq⟩

end
end AronowAudit.P002.Wave1

