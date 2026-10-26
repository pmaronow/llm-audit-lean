import AronowAudit.P002.Wave1.Gap.GLP0021B1
import AronowAudit.P002.Wave1.Gap.GP0022B2
import AronowAudit.P002.Wave1.Gap.DecisionLemma12
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT

/-!
P002-T5: uniform coverage for the unadjusted Anderson--Rubin randomization interval.

The finite-population CLT is applied to the fixed mixture of adjusted potential
responses. Finite second moments control observed studentization. A normalized
fourth-moment tail estimate controls the fixed response's first two moments,
and then the same CLT controls its reassignment cutoff. Sequential uniformization
passes from increasing arrays to the nested class infimum. Zero-variance rows
have coverage one and are retained throughout.

The normalization and fixed-response calculations adapt the helpers in
`DecisionLemma12.lean`; the contrast variance bound is reused from `GLP0021B1.lean`.
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

local instance CT1_normalNullSingleton : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

private lemma CT1_popVar_nonneg {n} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    0 ≤ popVar q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by linarith)

private lemma CT1_probability_mono {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S → F S) :
    probability P E ≤ probability P F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (assignments P).filter E ⊆
    (assignments P).filter F from fun S hS =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1,
        h S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2⟩)

private lemma CT1_probability_congr {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S ↔ F S) :
    probability P E = probability P F := by
  apply le_antisymm
  · exact CT1_probability_mono P (fun S hS => (h S hS).mp)
  · exact CT1_probability_mono P (fun S hS => (h S hS).mpr)

private lemma CT1_probability_union {n} (P : Population n)
    (E F : Finset (Fin n) → Prop) :
    probability P (fun S => E S ∨ F S) ≤ probability P E + probability P F := by
  simp only [DecisionLemma12_probability_eq_expectation]
  rw [← DecisionLemma12_expectation_add]
  apply DecisionLemma12_expectation_mono
  intro S hS
  by_cases hE : E S <;> by_cases hF : F S <;> simp [hE, hF]

private lemma CT1_rawTau_mean {n} (P : Population n) (q : Fin n → ℝ)
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

private lemma CT1_rawTau_variance {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) :
    designVariance P (rawTau P q) =
      (fraction P)^2 * (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
  calc
    _ = designVariance P (fun S => fraction P * groupMean S q - fraction P * mean q) := by
      apply NDS_variance_congr
      intro S hS
      rw [CT1_rawTau_mean P q S hS]
      ring
    _ = _ := by rw [NDS_variance_affine P hP, NDS_groupMean_variance P hP]; ring

private lemma CT1_rawTau_variance_pos {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (hq : 0 < popVar q) :
    0 < designVariance P (rawTau P q) := by
  rw [CT1_rawTau_variance P hP]
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hn := hm.trans hmn
  apply mul_pos (mul_pos (sq_pos_of_pos (div_pos hm hn)) _) hq
  exact sub_pos.mpr ((one_div_lt_one_div hn hm).mpr hmn)

private lemma CT1_standardize {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (hq : 0 < popVar q)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P q S / Real.sqrt (designVariance P (rawTau P q)) =
      (groupMean S q - mean q) /
        Real.sqrt ((1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q) := by
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hp : 0 < fraction P := div_pos hm (hm.trans hmn)
  rw [CT1_rawTau_mean P q S hS, CT1_rawTau_variance P hP]
  rw [mul_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp.le]
  exact mul_div_mul_left _ _ hp.ne'

/-- A fourth-moment condition implies the Hájek maximal-entry condition. -/
private lemma CT1_maximum_bound {n} (P : Population n) (q : Fin n → ℝ)
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

private lemma CT1_rawCLT (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
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
    (fun j => CT1_maximum_bound (P j) (q j) (hP j).1 (hq j) r K hr hK (hmin j) (hfour j)) hb
  intro t
  have h := finitePopulationCLT sizes hsizes P q hP hq hmax t
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  convert h using 1
  funext j
  exact CT1_probability_congr (P j) (fun S hS => by
    rw [CT1_standardize (P j) (hP j) (q j) (hq j) S hS])

private lemma CT1_uniform_eventual {X : ℕ → Type*} (H G : ∀ n, X n → Prop)
    (hseq : ∀ (sizes : ℕ → ℕ), StrictMono sizes → ∀ (x : ∀ j, X (sizes j)),
      (∀ j, H (sizes j) (x j)) → ∀ᶠ j in atTop, G (sizes j) (x j)) :
    ∀ᶠ n in atTop, ∀ x, H n x → G n x := by
  by_contra hn
  have hh : ∃ᶠ n in atTop, ∃ x, H n x ∧ ¬ G n x := by
    apply (not_eventually.mp hn).mono
    intro n hn
    by_contra hh
    apply hn
    intro x hx
    by_contra hg
    exact hh ⟨x,hx,hg⟩
  obtain ⟨sizes, hsizes, hbad⟩ := extraction_of_frequently_atTop hh
  choose x hx hfx using hbad
  obtain ⟨j, hj⟩ := (hseq sizes hsizes x hx).exists
  exact hfx j hj

private lemma CT1_cdf_lt (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
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
    exact hj.trans_le (CT1_probability_mono (P j) (fun S hS hx => hx.trans_lt ha))
  · intro z hz
    filter_upwards [(tendsto_order.1 (hseq t)).2 z hz] with j hj
    exact (CT1_probability_mono (P j) (fun S hS hx => hx.le)).trans_lt hj

private lemma CT1_abs_cdf (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (x : ∀ j, Finset (Fin (sizes j)) → ℝ)
    (hseq : ∀ t, Tendsto (fun j => probability (P j) (fun S => x j S ≤ t))
      atTop (nhds (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t)))
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun j => probability (P j) (fun S => |x j S| ≤ t))
      atTop (nhds (SH_absNormalCDF t)) := by
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
  have h := (hseq t).sub (CT1_cdf_lt sizes P x hseq (-t))
  rw [AronowAudit.P053.NormalCompletion.normal_cdf_neg] at h
  convert h using 1 <;> simp only [SH_absNormalCDF] <;> ring

private lemma CT1_absStudent_sq (x s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) :
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

private lemma CT1_standard_sq (x V a : ℝ) (hV : 0 < V) (ha : 0 ≤ a) :
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

private lemma CT1_student_upper (x s V a b : ℝ) (hs : 0 ≤ s)
    (hV : 0 < V) (ha : 0 < a) (hab : a < b)
    (hstudent : absStudent x s ≤ ENNReal.ofReal a)
    (hgood : |s/V-1| < (b^2-a^2)/a^2) :
    |x / Real.sqrt V| ≤ b := by
  apply (CT1_standard_sq x V b hV (ha.trans hab).le).mpr
  have h := (CT1_absStudent_sq x s a hs ha.le).mp hstudent
  have hratio := (abs_lt.mp hgood).2
  have hscale : a^2*s ≤ b^2*V := by
    have hh := (lt_div_iff₀ (sq_pos_of_pos ha)).mp hratio
    have he : (s/V-1)*a^2*V = a^2*s-a^2*V := by field_simp; <;> ring
    have hh' := mul_lt_mul_of_pos_right hh hV
    rw [he] at hh'
    nlinarith
  exact h.trans hscale

private lemma CT1_student_lower (x s V B a c : ℝ)
    (hs : 0 ≤ s) (hV : 0 < V) (hB : 0 < B) (hVB : V ≤ B)
    (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (hraw : |x / Real.sqrt V| ≤ c)
    (hgood : |s/B-1| < (a^2-c^2)/a^2) :
    absStudent x s ≤ ENNReal.ofReal a := by
  apply (CT1_absStudent_sq x s a hs ha.le).mpr
  have h := (CT1_standard_sq x V c hV hc).mp hraw
  have hratio := (abs_lt.mp hgood).1
  rw [← neg_div] at hratio
  have hh := (div_lt_iff₀ (sq_pos_of_pos ha)).mp hratio
  have he : (s/B-1)*a^2*B = a^2*s-a^2*B := by field_simp; <;> ring
  have hh' := mul_lt_mul_of_pos_right hh hB
  rw [he] at hh'
  have hcb := mul_le_mul_of_nonneg_left hVB (sq_nonneg c)
  nlinarith

private lemma CT1_sigma_nonneg {n} (P : Population n) (q : Fin n → ℝ)
    (S : Finset (Fin n)) : 0 ≤ rawSigma2 P q S := by
  unfold rawSigma2
  positivity

private lemma CT1_variance_ratio_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
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

/-- Only the upper CDF comparison is needed for the lower bound on the cutoff. -/
private lemma CT1_fixed_cdf_upper (r K a b p : ℝ) (hr : 0 < r) (hK : 0 ≤ K)
    (ha : 0 < a) (hab : a < b) (hp : SH_absNormalCDF b < p) :
    ∀ᶠ n in atTop, ∀ (P : Population n) (q : Fin n → ℝ),
      ValidDesign P → 0 < popVar q →
      r*n ≤ (P.n1 : ℝ) → (P.n1 : ℝ) ≤ (1-r)*n →
      (∑ i, (q i-mean q)^4 ≤ K*n*(popVar q)^2) →
      probability P (fun S => rawAR P q S ≤ ENNReal.ofReal a) < p := by
  let H : ∀ n, (Population n × (Fin n → ℝ)) → Prop := fun n x =>
    ValidDesign x.1 ∧ 0 < popVar x.2 ∧ r*n ≤ (x.1.n1 : ℝ) ∧
      (x.1.n1 : ℝ) ≤ (1-r)*n ∧ (∑ i, (x.2 i-mean x.2)^4 ≤ K*n*(popVar x.2)^2)
  have he := CT1_uniform_eventual H
    (fun n x => probability x.1 (fun S => rawAR x.1 x.2 S ≤ ENNReal.ofReal a) < p) (by
      intro sizes hsizes x hx
      let P := fun j => (x j).1
      let q := fun j => (x j).2
      have hraw := CT1_rawCLT sizes hsizes P q (fun j => (hx j).1)
        (fun j => (hx j).2.1) r K hr hK (fun j => (hx j).2.2.1)
        (fun j => (hx j).2.2.2.1) (fun j => (hx j).2.2.2.2)
      have habs := CT1_abs_cdf sizes P _ hraw b (ha.trans hab).le
      have hκ : 0 < (b^2-a^2)/a^2 := by
        apply div_pos _ (sq_pos_of_pos ha)
        nlinarith
      have herr := CT1_variance_ratio_limit sizes hsizes P q (fun j => (hx j).1)
        (fun j => (hx j).2.1) r K hr hK (fun j => (hx j).2.2.1)
        (fun j => (hx j).2.2.2.1) (fun j => (hx j).2.2.2.2) _ hκ
      have hsum := habs.add herr
      simp only [add_zero] at hsum
      filter_upwards [(tendsto_order.1 hsum).2 p hp] with j hj
      apply lt_of_le_of_lt _ hj
      apply le_trans (CT1_probability_mono (P j) (fun S hS hstudent => ?_))
        (CT1_probability_union (P j) _ _)
      by_cases he : |rawSigma2 (P j) (q j) S / designVariance (P j) (rawTau (P j) (q j))-1| ≥
          (b^2-a^2)/a^2
      · exact Or.inr he
      · exact Or.inl (CT1_student_upper _ _ _ a b (CT1_sigma_nonneg _ _ _)
          (CT1_rawTau_variance_pos (P j) (hx j).1 _ (hx j).2.1) ha hab hstudent (lt_of_not_ge he)))
  filter_upwards [he] with n hn P q hP hq hl hu hf
  exact hn (P,q) ⟨hP,hq,hl,hu,hf⟩

private def CT1_total {n} (P : Population n) : ℝ :=
  popVar (w P true (late P)) + popVar (w P false (late P))

private def CT1_B {n} (P : Population n) : ℝ :=
  S2 P (late P) true / (P.n1 : ℝ) + S2 P (late P) false / controlSize P

private def CT1_mix {n} (P : Population n) (i : Fin n) : ℝ :=
  (1-fraction P)*w P true (late P) i + fraction P*w P false (late P) i

private lemma CT1_sizes {n} (P : Population n) (hP : ValidDesign P) :
    0 < (n : ℝ) ∧ 0 < (P.n1 : ℝ) ∧ 0 < controlSize P ∧
      0 < fraction P ∧ fraction P < 1 := by
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hn := hm.trans hmn
  exact ⟨hn,hm,sub_pos.mpr hmn,div_pos hm hn,(div_lt_one hn).mpr hmn⟩

private lemma CT1_fourth {n} (P : Population n) (δ r A : ℝ) (hP : Theta P δ r A)
    (a : Bool) :
    ∑ i, v P a (late P) i^4 ≤ A^4*n*(popVar (w P a (late P)))^2 := by
  have hn : (0 : ℝ) < n := (CT1_sizes P hP.1).1
  have hv := CT1_popVar_nonneg hP.1.1 (w P a (late P))
  have hf := hP.2.2.2.2.2.2 a
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hf 4
  have hmean4 : 0 ≤ mean (fun i => v P a (late P) i^4) := by
    exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hn.le
  have hroot : (fourthNorm (v P a (late P)))^4 = mean (fun i => v P a (late P) i^4) := by
    unfold fourthNorm
    calc
      _ = ((Real.sqrt (Real.sqrt (mean (fun i => v P a (late P) i^4))))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hmean4]
  change (fourthNorm (v P a (late P)))^4 ≤ (A*Real.sqrt (popVar (w P a (late P))))^4 at hp
  rw [hroot, mul_pow, show (Real.sqrt (popVar (w P a (late P))))^4 =
      ((Real.sqrt (popVar (w P a (late P))))^2)^2 by ring, Real.sq_sqrt hv] at hp
  nlinarith only [(div_le_iff₀ hn).mp hp]

private lemma CT1_normalized {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A) (hT : 0 < CT1_total P) :
    let x := fun a i => v P a (late P) i / Real.sqrt (CT1_total P)
    (∀ a, ∑ i, x a i = 0) ∧
    (∑ i, x true i^2) + (∑ i, x false i^2) = (n : ℝ)-1 ∧
    (∑ i, x true i^4) + (∑ i, x false i^4) ≤ (2*A^4)*n := by
  let T := CT1_total P
  let x := fun a i => v P a (late P) i / Real.sqrt T
  change (∀ a, ∑ i, x a i = 0) ∧ _ ∧ _
  have hn : 0 < n := by have := hP.1.1; omega
  have hs := (Real.sqrt_pos.mpr hT).ne'
  have hv (a) := CT1_popVar_nonneg hP.1.1 (w P a (late P))
  have hx0 (a) : ∑ i, x a i = 0 := by
    simp only [x, ← Finset.sum_div]
    change (∑ i, (w P a (late P) i - mean (w P a (late P)))) / Real.sqrt T = 0
    rw [DecisionLemma12_sum_centered hn]
    simp
  have hx2 (a) : ∑ i, x a i^2 = ((n : ℝ)-1)*popVar (w P a (late P))/T := by
    have hn1 : (n : ℝ)-1 ≠ 0 := by
      have hh : (2 : ℝ) ≤ n := by exact_mod_cast hP.1.1
      linarith
    simp only [x, div_pow, ← Finset.sum_div,
      Real.sq_sqrt (show 0 ≤ T from hT.le), popVar, v]
    field_simp [hn1]
    <;> ring
  have hx4 (a) : ∑ i, x a i^4 ≤ A^4*n := by
    have ht : popVar (w P a (late P)) ≤ T := by
      cases a <;> dsimp [T, CT1_total] <;> linarith [hv true,hv false]
    have hf := (CT1_fourth P δ r A hP a).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hv a) ht 2)
        (show 0 ≤ A^4*n by positivity))
    simp only [x, div_pow, ← Finset.sum_div]
    apply (div_le_iff₀ (pow_pos (Real.sqrt_pos.mpr hT) 4)).mpr
    rw [show (Real.sqrt T)^4 = ((Real.sqrt T)^2)^2 by ring, Real.sq_sqrt hT.le]
    exact hf
  refine ⟨hx0, ?_, by linarith [hx4 true,hx4 false]⟩
  rw [hx2, hx2]
  dsimp [T, CT1_total] at *
  field_simp
  <;> ring

private lemma CT1_mix_center {n} (P : Population n) :
    ∀ i, CT1_mix P i - mean (CT1_mix P) =
      (1-fraction P)*v P true (late P) i + fraction P*v P false (late P) i := by
  intro i
  simp only [CT1_mix, mean, Finset.sum_add_distrib, ← Finset.mul_sum, v]
  ring

private lemma CT1_mix_tau {n} (P : Population n) (hP : ValidDesign P)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P (CT1_mix P) S = tau P (late P) S := by
  have hn := (CT1_sizes P hP).1.ne'
  have hmt := (CT1_sizes P hP).2.1.ne'
  have hct := (CT1_sizes P hP).2.2.1.ne'
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have hccard : (Sᶜ.card : ℝ) = controlSize P := by
    rw [Finset.card_compl, Fintype.card_fin, hcard, Nat.cast_sub hP.2.2.le]
    rfl
  have he := mean_w_equal_at_late P hm hc
  have hes : ∑ i, w P true (late P) i = ∑ i, w P false (late P) i := by
    exact (div_left_inj' hn).mp he
  have hsplit := Finset.sum_add_sum_compl S (w P false (late P))
  have hcomp : (∑ i ∈ Sᶜ, w P false (late P) i) =
      (∑ i, w P false (late P) i) - ∑ i ∈ S, w P false (late P) i := by linarith
  rw [NDS_tau_as_contrast P hP (late P) S hS, rawTau_sum]
  simp only [CT1_mix, Finset.sum_add_distrib, ← Finset.mul_sum, groupMean,
    hcard, hccard, hes, hcomp]
  dsimp [fraction, controlSize] at *
  field_simp [hn,hmt,hct]
  <;> ring

private lemma CT1_mix_variance {n} (P : Population n) (hP : ValidDesign P)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty) :
    designVariance P (tau P (late P)) =
      fraction P*(1-fraction P)/(n : ℝ)*popVar (CT1_mix P) := by
  calc
    _ = designVariance P (rawTau P (CT1_mix P)) :=
      NDS_variance_congr P (fun S hS => (CT1_mix_tau P hP hm hc S hS).symm)
    _ = _ := by
      rw [CT1_rawTau_variance P hP]
      have hm := (CT1_sizes P hP).2.1.ne'
      have hn := (CT1_sizes P hP).1.ne'
      dsimp [fraction]
      field_simp
      <;> ring

private lemma CT1_mix_lower {n} (P : Population n) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hP : Theta P δ r A) :
    ((1-max δ 0)*r^2)*CT1_total P ≤ popVar (CT1_mix P) := by
  have hs := CT1_sizes P hP.1
  have hp : r ≤ fraction P := (le_div_iff₀ hs.1).mpr hP.2.2.2.1
  have hpc : r ≤ 1-fraction P := by
    have h := (div_le_iff₀ hs.1).mpr hP.2.2.2.2.1
    change fraction P ≤ 1-r at h
    linarith
  have hfac : 0 < fraction P*(1-fraction P)/(n : ℝ) := by
    exact div_pos (mul_pos hs.2.2.2.1 (sub_pos.mpr hs.2.2.2.2)) hs.1
  have hb := corrected_lemma5_proof P δ r A hδ hr hA hP
  rw [CT1_mix_variance P hP.1 hP.2.1 hP.2.2.1] at hb
  have he : (1-max δ 0) * (controlSize P/((n : ℝ)*(P.n1 : ℝ))*S2 P (late P) true +
      (P.n1 : ℝ)/((n : ℝ)*controlSize P)*S2 P (late P) false) =
      (fraction P*(1-fraction P)/(n : ℝ))*((1-max δ 0)*
        ((1-fraction P)^2*popVar (w P true (late P)) +
          (fraction P)^2*popVar (w P false (late P)))) := by
    dsimp [S2,fraction,controlSize]
    have hn := hs.1.ne'
    have hm := hs.2.1.ne'
    have hc := hs.2.2.1.ne'
    dsimp [controlSize] at hc
    field_simp
    <;> ring
  rw [he] at hb
  have hb := (mul_le_mul_iff_right₀ hfac).mp hb
  have hd : 0 ≤ 1-max δ 0 := by exact sub_nonneg.mpr (max_le hδ.le (by norm_num))
  have hv1 := CT1_popVar_nonneg hP.1.1 (w P true (late P))
  have hv0 := CT1_popVar_nonneg hP.1.1 (w P false (late P))
  have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hpc 2) hv1
  have h0 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hp 2) hv0
  apply le_trans _ hb
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h0) hd
  simpa only [CT1_total, mul_add, mul_assoc] using h

private lemma CT1_mix_fourth {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A) :
    ∑ i, (CT1_mix P i-mean (CT1_mix P))^4 ≤ 8*A^4*n*(CT1_total P)^2 := by
  have hs := CT1_sizes P hP.1
  have hp4 : (fraction P)^4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hs.2.2.2.1.le hs.2.2.2.2.le 4
  have hc4 : (1-fraction P)^4 ≤ 1 := by
    have hc : 0 ≤ 1-fraction P := by linarith [hs.2.2.2.2]
    simpa using pow_le_pow_left₀ hc (show 1-fraction P ≤ 1 by linarith [hs.2.2.2.1]) 4
  have hpoint (i) : (CT1_mix P i-mean (CT1_mix P))^4 ≤
      8*(v P true (late P) i^4+v P false (late P) i^4) := by
    rw [CT1_mix_center]
    have hf (a b : ℝ) : (a+b)^4 ≤ 8*a^4+8*b^4 := by
      nlinarith [sq_nonneg (a^2-b^2),sq_nonneg ((a-b)^2)]
    have h := hf ((1-fraction P)*v P true (late P) i) (fraction P*v P false (late P) i)
    simp only [mul_pow] at h
    have h1 := mul_le_mul_of_nonneg_right hc4 (show 0 ≤ v P true (late P) i^4 by positivity)
    have h0 := mul_le_mul_of_nonneg_right hp4 (show 0 ≤ v P false (late P) i^4 by positivity)
    nlinarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hv1 := CT1_popVar_nonneg hP.1.1 (w P true (late P))
  have hv0 := CT1_popVar_nonneg hP.1.1 (w P false (late P))
  have hf1 := CT1_fourth P δ r A hP true
  have hf0 := CT1_fourth P δ r A hP false
  have hvar : (popVar (w P true (late P)))^2 + (popVar (w P false (late P)))^2 ≤
      (CT1_total P)^2 := by dsimp [CT1_total]; nlinarith
  have hmul := mul_le_mul_of_nonneg_left hvar (show 0 ≤ 8*A^4*n by positivity)
  nlinarith

private lemma CT1_observed_affine {n} (P : Population n)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty)
    (hT : 0 < CT1_total P) (S : Finset (Fin n)) :
    observedW P (late P) S = fun i => mean (w P false (late P)) +
      Real.sqrt (CT1_total P) * (if i ∈ S then
        v P true (late P) i / Real.sqrt (CT1_total P) else
        v P false (late P) i / Real.sqrt (CT1_total P)) := by
  have hs := (Real.sqrt_pos.mpr hT).ne'
  have he := mean_w_equal_at_late P hm hc
  funext i
  by_cases hi : i ∈ S
  · rw [observedW_treated P _ S i hi, if_pos hi]
    dsimp [v]
    rw [he]
    field_simp
    <;> ring
  · rw [observedW_control P _ S i (Finset.mem_compl.mpr hi), if_neg hi]
    dsimp [v]
    field_simp
    <;> ring

private lemma CT1_frozen_lower {n} (P : Population n) (hP : ValidDesign P)
    (r : ℝ) (hr : 0 < r) (hl : r*n ≤ (P.n1 : ℝ))
    (hu : (P.n1 : ℝ) ≤ (1-r)*n) (x : Bool → Fin n → ℝ)
    (hx0 : ∑ i, x false i = 0)
    (hx2 : (∑ i, x true i^2)+(∑ i, x false i^2) = (n : ℝ)-1)
    (S : Finset (Fin n)) (hS : S ∈ assignments P)
    (ha : |(∑ i ∈ S, (x true i-x false i))/(n : ℝ)| < min 1 (r/8))
    (hb : |(∑ i ∈ S, (x true i^2-x false i^2-
      mean (fun i => x true i^2-x false i^2)))/(n : ℝ)| < r/8) :
    let y := fun i => if i ∈ S then x true i else x false i
    r/4 ≤ popVar y ∧ |mean y| ≤ 1 := by
  let y := fun i => if i ∈ S then x true i else x false i
  change r/4 ≤ popVar y ∧ |mean y| ≤ 1
  have hn := (CT1_sizes P hP).1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
  have hym : |mean y| < min 1 (r/8) := by
    simpa only [y,DecisionLemma12_observed_mean P x hx0] using ha
  have hym1 := (hym.trans_le (min_le_left _ _)).le
  have hym2 : (mean y)^2 ≤ r/8 := by
    have hh := hym.trans_le (min_le_right _ _)
    nlinarith [sq_abs (mean y),abs_nonneg (mean y)]
  have hp : r ≤ fraction P := (le_div_iff₀ hn).mpr hl
  have hp' : fraction P ≤ 1-r := (div_le_iff₀ hn).mpr hu
  have hs1 : 0 ≤ ∑ i, x true i^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs0 : 0 ≤ ∑ i, x false i^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : r/2 ≤ (fraction P*(∑ i, x true i^2)+
      (1-fraction P)*(∑ i, x false i^2))/(n : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    have h1 := mul_le_mul_of_nonneg_right hp hs1
    have h0 := mul_le_mul_of_nonneg_right (show r ≤ 1-fraction P by linarith) hs0
    nlinarith
  have hsecond := DecisionLemma12_observed_second P x S hS
  have herr := (abs_lt.mp hb).1
  have hgap : r/4 ≤ mean (fun i => y i^2)-(mean y)^2 := by
    change r/4 ≤ mean (fun i => (if i ∈ S then x true i else x false i)^2)-_
    rw [hsecond]
    linarith
  refine ⟨?_,hym1⟩
  unfold popVar
  rw [DecisionLemma12_sum_centered_sq (by have := hP.1; omega)]
  apply (le_div_iff₀ (by linarith : 0 < (n : ℝ)-1)).mpr
  have hsum : (∑ i, y i^2) = (n : ℝ)*mean (fun i => y i^2) := by
    dsimp [mean]
    field_simp [hn.ne']
  rw [hsum]
  nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hgap)]

private def CT1_frozenK (r A : ℝ) : ℝ := 8*(2*A^4+1)/(r/4)^2

private def CT1_frozenGood {n} (P : Population n) (r A : ℝ)
    (S : Finset (Fin n)) : Prop :=
  let q := observedW P (late P) S
  0 < popVar q ∧ (∑ i, (q i-mean q)^4) ≤ CT1_frozenK r A*n*(popVar q)^2

private lemma CT1_frozen_bad_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (δ r A : ℝ) (hr : 0 < r)
    (hP : ∀ j, Theta (P j) δ r A) (hT : ∀ j, 0 < CT1_total (P j)) :
    Tendsto (fun j => probability (P j) (fun S => ¬ CT1_frozenGood (P j) r A S))
      atTop (nhds 0) := by
  let x := fun j a i => v (P j) a (late (P j)) i / Real.sqrt (CT1_total (P j))
  have hnormal (j) : (∀ a, ∑ i, x j a i = 0) ∧
      (∑ i, x j true i^2)+(∑ i, x j false i^2) = (sizes j : ℝ)-1 ∧
      (∑ i, x j true i^4)+(∑ i, x j false i^4) ≤ (2*A^4)*sizes j :=
    CT1_normalized (P j) δ r A (hP j) (hT j)
  let C : ℝ := 2*A^4
  let a := fun j i => x j true i-x j false i
  let b := fun j i => x j true i^2-x j false i^2-
    mean (fun i => x j true i^2-x j false i^2)
  have ha (j) : ∑ i, a j i = 0 := by simp [a,Finset.sum_sub_distrib,(hnormal j).1]
  have hb (j) : ∑ i, b j i = 0 :=
    DecisionLemma12_sum_centered (by have := (hP j).1.1; omega) _
  have ha2 (j) : ∑ i, a j i^2 ≤ 2*sizes j := by
    calc
      _ ≤ ∑ i, (2*x j true i^2+2*x j false i^2) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [a]
        nlinarith [sq_nonneg (x j true i+x j false i)]
      _ = 2*((sizes j : ℝ)-1) := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,← mul_add,(hnormal j).2.1]
      _ ≤ _ := by linarith
  have hb2 (j) : ∑ i, b j i^2 ≤ (2*C)*sizes j := by
    change (∑ i, ((x j true i^2-x j false i^2)-mean _)^2) ≤ _
    rw [DecisionLemma12_sum_centered_sq (by have := (hP j).1.1; omega)]
    calc
      _ ≤ ∑ i, (x j true i^2-x j false i^2)^2 := by
        have hh := mul_nonneg (Nat.cast_nonneg (α := ℝ) (sizes j))
          (sq_nonneg (mean (fun i => x j true i^2-x j false i^2)))
        linarith
      _ ≤ ∑ i, (2*x j true i^4+2*x j false i^4) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (x j true i^2+x j false i^2)]
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,← mul_add]
        have hh := mul_le_mul_of_nonneg_left (hnormal j).2.2 (by norm_num : (0 : ℝ) ≤ 2)
        dsimp [C]
        nlinarith only [hh]
  have hgood (j) (S : Finset (Fin (sizes j))) (hS : S ∈ assignments (P j))
      (haS : |(∑ i ∈ S, a j i)/(sizes j : ℝ)| < min 1 (r/8))
      (hbS : |(∑ i ∈ S, b j i)/(sizes j : ℝ)| < r/8) : CT1_frozenGood (P j) r A S := by
    let y := fun i => if i ∈ S then x j true i else x j false i
    have hy := CT1_frozen_lower (P j) (hP j).1 r hr (hP j).2.2.2.1
      (hP j).2.2.2.2.1 (x j) ((hnormal j).1 false) (hnormal j).2.1 S hS haS hbS
    have hy4 : ∑ i, y i^4 ≤ C*sizes j := by
      calc
        _ ≤ ∑ i, (x j true i^4+x j false i^4) := by
          apply Finset.sum_le_sum
          intro i _
          dsimp [y]
          by_cases hi : i ∈ S <;> simp only [hi,ite_true,ite_false] <;>
            linarith [show 0 ≤ x j true i^4 by positivity,show 0 ≤ x j false i^4 by positivity]
        _ ≤ _ := by rw [Finset.sum_add_distrib]; exact (hnormal j).2.2
    have hh := DecisionLemma12_relative_fourth
      (show 0 < sizes j by have := (hP j).1.1; omega)
      y (r/4) C (mean (w (P j) false (late (P j)))) (Real.sqrt (CT1_total (P j)))
      (by positivity) (by dsimp [C]; positivity) (Real.sqrt_pos.mpr (hT j)).ne'
      hy.1 hy.2 hy4
    change CT1_frozenGood (P j) r A S
    dsimp only [CT1_frozenGood]
    rw [CT1_observed_affine (P j) (hP j).2.1 (hP j).2.2.1 (hT j) S]
    exact hh
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hi : Tendsto (fun j => 1/(sizes j : ℝ)^2) atTop (nhds 0) := by
    simpa [one_div,Function.comp_def,inv_pow] using
      (tendsto_inv_atTop_zero.comp hN).pow 2
  have hbound : Tendsto (fun j =>
      (19*(2 : ℝ)^2/(min 1 (r/8))^4)*(1/(sizes j : ℝ)^2)+
        (19*(2*C)^2/(r/8)^4)*(1/(sizes j : ℝ)^2)) atTop (nhds 0) := by
    simpa using (hi.const_mul _).add (hi.const_mul _)
  apply squeeze_zero' (Eventually.of_forall (fun _ => DecisionLemma12_probability_nonneg _ _)) _ hbound
  filter_upwards [(hN.const_mul_atTop hr).eventually_ge_atTop 4] with j hj
  have hm : 4 ≤ (P j).n1 := by exact_mod_cast hj.trans (hP j).2.2.2.1
  apply le_trans (CT1_probability_mono (P j) (fun S hS hbad => ?_))
    ((CT1_probability_union (P j) _ _).trans (add_le_add
      (DecisionLemma12_sample_fourth_tail (P j) (hP j).1 hm (a j) (ha j) 2
        (min 1 (r/8)) (by norm_num) (lt_min zero_lt_one (by positivity)) (ha2 j))
      (DecisionLemma12_sample_fourth_tail (P j) (hP j).1 hm (b j) (hb j) (2*C)
        (r/8) (by dsimp [C]; positivity) (by positivity) (hb2 j))))
  by_cases h1 : min 1 (r/8) ≤ |(∑ i ∈ S, a j i)/(sizes j : ℝ)|
  · exact Or.inl h1
  · exact Or.inr (le_of_not_gt (fun h2 => hbad (hgood j S hS (lt_of_not_ge h1) h2)))

private def CT1_armVar {n} (q : Fin n → ℝ) (S : Finset (Fin n)) (a : Bool) : ℝ :=
  armMean (fun i => (q i-armMean q S a)^2) S a

private lemma CT1_mean_sq {n} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    mean (fun i => (q i-mean q)^2) = ((n : ℝ)-1)/(n : ℝ)*popVar q := by
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  change (∑ i, (q i-mean q)^2)/(n : ℝ) =
    ((n : ℝ)-1)/(n : ℝ)*((∑ i, (q i-mean q)^2)/((n : ℝ)-1))
  field_simp [hn1]
  <;> ring

private lemma CT1_arm_error {n} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hc : 2 ≤ n-P.n1)
    (q : Fin n → ℝ) (r K : ℝ) (hr : 0 < r) (hK : 0 ≤ K)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (hf : ∑ i, (q i-mean q)^4 ≤ K*n*(popVar q)^2) (a : Bool) :
    expectation P (fun S => |CT1_armVar q S a-popVar q|) ≤
      popVar q*(Real.sqrt (2*K/(r*n))+1/(r*n)+1/(n : ℝ)) := by
  let z := fun i => q i-mean q
  let F := fun S => armMean (fun i => z i^2) S a-mean (fun i => z i^2)
  let G := fun S => (armMean q S a-mean q)^2
  have hn := (CT1_sizes P hP).1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
  have hv := CT1_popVar_nonneg hP.1 q
  have hsize : r*n ≤ (if a then (P.n1 : ℝ) else controlSize P) := by
    cases a <;> simp only [Bool.false_eq_true,↓reduceIte,controlSize] <;> linarith
  have hsp : 0 < (if a then (P.n1 : ℝ) else controlSize P) := (mul_pos hr hn).trans_le hsize
  have hvar : popVar (fun i => z i^2) ≤ 2*K*(popVar q)^2 := by
    change (∑ i, (z i^2-mean (fun i => z i^2))^2)/((n : ℝ)-1) ≤ _
    rw [DecisionLemma12_sum_centered_sq (by have := hP.1; omega)]
    apply (div_le_iff₀ (by linarith : 0 < (n : ℝ)-1)).mpr
    have hmean := mul_nonneg hn.le (sq_nonneg (mean (fun i => z i^2)))
    have hfour : (∑ i, (z i^2)^2) ≤ K*n*(popVar q)^2 := by simpa only [← pow_mul] using hf
    nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ)-2)
      (show 0 ≤ K*(popVar q)^2 by positivity)]
  have hF : expectation P (fun S => |F S|) ≤ popVar q*Real.sqrt (2*K/(r*n)) := by
    apply (DecisionLemma12_Eabs P hP F).trans
    have hmse := DecisionLemma12_mse_arm P hP hm hc (fun i => z i^2) a
    have hb : expectation P (fun S => F S^2) ≤ (2*K/(r*n))*(popVar q)^2 := by
      calc
        _ ≤ popVar (fun i => z i^2)/(if a then (P.n1 : ℝ) else controlSize P) := hmse
        _ ≤ (2*K*(popVar q)^2)/(if a then (P.n1 : ℝ) else controlSize P) :=
          div_le_div_of_nonneg_right hvar hsp.le
        _ ≤ (2*K*(popVar q)^2)/(r*n) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hr hn) hsize
        _ = _ := by ring
    have h := Real.sqrt_le_sqrt hb
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2*K/(r*n)),Real.sqrt_sq hv] at h
    simpa only [mul_comm] using h
  have hG : expectation P G ≤ popVar q/(r*n) :=
    (DecisionLemma12_mse_arm P hP hm hc q a).trans
      (div_le_div_of_nonneg_left hv (mul_pos hr hn) hsize)
  have herr (S) (hS : S ∈ assignments P) :
      |CT1_armVar q S a-popVar q| ≤ |F S|+G S+popVar q/(n : ℝ) := by
    have hcard := (Finset.mem_powersetCard.mp hS).2
    have hsn : S.Nonempty := Finset.card_pos.mp (by omega)
    have hcn : Sᶜ.Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_compl,Fintype.card_fin,hcard]; omega)
    have he : CT1_armVar q S a = armMean (fun i => z i^2) S a-G S := by
      cases a
      · exact square_centering Sᶜ q (mean q) hcn
      · exact square_centering S q (mean q) hsn
    have hcenter := CT1_mean_sq hP.1 q
    have he' : CT1_armVar q S a-popVar q = F S-G S-popVar q/(n : ℝ) := by
      rw [he]
      dsimp [F]
      change armMean (fun i => z i^2) S a-G S-popVar q =
        armMean (fun i => z i^2) S a-mean (fun i => (q i-mean q)^2)-G S-popVar q/(n : ℝ)
      rw [hcenter]
      field_simp
      <;> ring
    rw [he']
    have hg : 0 ≤ G S := sq_nonneg _
    have hvn : 0 ≤ popVar q/(n : ℝ) := by positivity
    exact abs_le.mpr ⟨by linarith [neg_abs_le (F S)],by linarith [le_abs_self (F S)]⟩
  have he := DecisionLemma12_expectation_mono P herr
  simp_rw [DecisionLemma12_expectation_add,expectation_const P hP] at he
  calc
    _ ≤ expectation P (fun S => |F S|)+expectation P G+popVar q/(n : ℝ) := he
    _ ≤ popVar q*Real.sqrt (2*K/(r*n))+popVar q/(r*n)+popVar q/(n : ℝ) := by
      linarith only [hF,hG]
    _ = _ := by ring

private lemma CT1_sigma_arms {n} (P : Population n) (hP : ValidDesign P)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawSigma2 P (observedW P (late P) S) S = (fraction P)^2*(1-fraction P)^2*
      (CT1_armVar (w P true (late P)) S true/(P.n1 : ℝ)+
        CT1_armVar (w P false (late P)) S false/controlSize P) := by
  have hs := CT1_sizes P hP
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have hccard : (Sᶜ.card : ℝ) = controlSize P := by
    rw [Finset.card_compl,Fintype.card_fin,hcard,Nat.cast_sub hP.2.2.le]
    rfl
  have hmean1 : armMean (observedW P (late P) S) S true = groupMean S (w P true (late P)) := by
    apply groupMean_congr
    intro i hi
    exact observedW_treated P _ S i hi
  have hmean0 : armMean (observedW P (late P) S) S false = groupMean Sᶜ (w P false (late P)) := by
    apply groupMean_congr
    intro i hi
    exact observedW_control P _ S i hi
  rw [rawSigma2,hmean1,hmean0]
  have he1 : (∑ i ∈ S, (observedW P (late P) S i-groupMean S (w P true (late P)))^2) =
      ∑ i ∈ S, (w P true (late P) i-groupMean S (w P true (late P)))^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [observedW_treated P _ S i hi]
  have he0 : (∑ i ∈ Sᶜ, (observedW P (late P) S i-groupMean Sᶜ (w P false (late P)))^2) =
      ∑ i ∈ Sᶜ, (w P false (late P) i-groupMean Sᶜ (w P false (late P)))^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [observedW_control P _ S i hi]
  rw [he1,he0]
  simp only [CT1_armVar,armMean,Bool.false_eq_true,↓reduceIte,groupMean,hcard,hccard]
  field_simp
  <;> ring

private lemma CT1_B_pos {n} (P : Population n) (hP : ValidDesign P) (hT : 0 < CT1_total P) :
    0 < CT1_B P := by
  have hs := CT1_sizes P hP
  have h1 := CT1_popVar_nonneg hP.1 (w P true (late P))
  have h0 := CT1_popVar_nonneg hP.1 (w P false (late P))
  have hf : 0 < (fraction P)^2*(1-fraction P)^2 := by
    exact mul_pos (sq_pos_of_pos hs.2.2.2.1) (sq_pos_of_pos (sub_pos.mpr hs.2.2.2.2))
  have he : CT1_B P = ((fraction P)^2*(1-fraction P)^2)*
      (popVar (w P true (late P))/(P.n1 : ℝ)+popVar (w P false (late P))/controlSize P) := by
    dsimp [CT1_B,S2]
    ring
  rw [he]
  apply mul_pos hf
  by_cases hh : 0 < popVar (w P true (late P))
  · exact add_pos_of_pos_of_nonneg (div_pos hh hs.2.1) (div_nonneg h0 hs.2.2.1.le)
  · have hh0 : 0 < popVar (w P false (late P)) := by dsimp [CT1_total] at hT; linarith
    exact add_pos_of_nonneg_of_pos (div_nonneg h1 hs.2.1.le) (div_pos hh0 hs.2.2.1)

private lemma CT1_observed_ratio_bound {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A) (hT : 0 < CT1_total P) (hr : 0 < r)
    (hm : 2 ≤ P.n1) (hc : 2 ≤ n-P.n1) (κ : ℝ) (hκ : 0 < κ) :
    probability P (fun S => |rawSigma2 P (observedW P (late P) S) S/CT1_B P-1| ≥ κ) ≤
      (Real.sqrt (2*A^4/(r*n))+1/(r*n)+1/(n : ℝ))/κ := by
  let u := popVar (w P true (late P))/(P.n1 : ℝ)+popVar (w P false (late P))/controlSize P
  let e := Real.sqrt (2*A^4/(r*n))+1/(r*n)+1/(n : ℝ)
  have hs := CT1_sizes P hP.1
  have hB := CT1_B_pos P hP.1 hT
  have hf : 0 < (fraction P)^2*(1-fraction P)^2 := by
    exact mul_pos (sq_pos_of_pos hs.2.2.2.1) (sq_pos_of_pos (sub_pos.mpr hs.2.2.2.2))
  have hBu : CT1_B P = ((fraction P)^2*(1-fraction P)^2)*u := by dsimp [CT1_B,S2,u]; ring
  have hu : 0 < u := (mul_pos_iff_of_pos_left hf).mp (hBu ▸ hB)
  let E := fun a S => |CT1_armVar (w P a (late P)) S a-popVar (w P a (late P))|
  have he (a) : expectation P (E a) ≤ popVar (w P a (late P))*e :=
    CT1_arm_error P hP.1 hm hc _ r (A^4) hr (by positivity)
      hP.2.2.2.1 hP.2.2.2.2.1 (CT1_fourth P δ r A hP a) a
  have hpoint (S) (hS : S ∈ assignments P) :
      |rawSigma2 P (observedW P (late P) S) S/CT1_B P-1| ≤
        (E true S/(P.n1 : ℝ)+E false S/controlSize P)/u := by
    rw [CT1_sigma_arms P hP.1 S hS,hBu,mul_div_mul_left _ _ hf.ne']
    have hid : (CT1_armVar (w P true (late P)) S true/(P.n1 : ℝ)+
        CT1_armVar (w P false (late P)) S false/controlSize P)/u-1 =
        ((CT1_armVar (w P true (late P)) S true-popVar (w P true (late P)))/(P.n1 : ℝ)+
          (CT1_armVar (w P false (late P)) S false-popVar (w P false (late P)))/controlSize P)/u := by
      apply (eq_div_iff hu.ne').mpr
      rw [sub_mul,div_mul_cancel₀ _ hu.ne',one_mul]
      dsimp [u]
      ring
    rw [hid,abs_div,abs_of_pos hu]
    apply div_le_div_of_nonneg_right _ hu.le
    have h := abs_add_le
      ((CT1_armVar (w P true (late P)) S true-popVar (w P true (late P)))/(P.n1 : ℝ))
      ((CT1_armVar (w P false (late P)) S false-popVar (w P false (late P)))/controlSize P)
    simpa only [abs_div,abs_of_pos hs.2.1,abs_of_pos hs.2.2.1] using h
  have hmean := DecisionLemma12_expectation_mono P hpoint
  rw [expectation_div,DecisionLemma12_expectation_add,expectation_div,expectation_div] at hmean
  have hbound : expectation P (fun S => |rawSigma2 P (observedW P (late P) S) S/CT1_B P-1|) ≤ e := by
    apply hmean.trans
    apply (div_le_iff₀ hu).mpr
    have h1 := div_le_div_of_nonneg_right (he true) hs.2.1.le
    have h0 := div_le_div_of_nonneg_right (he false) hs.2.2.1.le
    calc
      _ ≤ popVar (w P true (late P))*e/(P.n1 : ℝ)+
          popVar (w P false (late P))*e/controlSize P := add_le_add h1 h0
      _ = e*u := by dsimp [u]; ring
  have hmark := DecisionLemma12_markov P
    (fun S => |rawSigma2 P (observedW P (late P) S) S/CT1_B P-1| ≥ κ)
    (fun S => |rawSigma2 P (observedW P (late P) S) S/CT1_B P-1|) κ
    (fun _ _ => abs_nonneg _) (fun _ _ h => h)
  exact (le_div_iff₀ hκ).mpr (by linarith)

private lemma CT1_observed_ratio_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (δ r A : ℝ) (hr : 0 < r)
    (hP : ∀ j, Theta (P j) δ r A) (hT : ∀ j, 0 < CT1_total (P j))
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun j => probability (P j) (fun S =>
      |rawSigma2 (P j) (observedW (P j) (late (P j)) S) S/CT1_B (P j)-1| ≥ κ))
      atTop (nhds 0) := by
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hi : Tendsto (fun j => 1/(sizes j : ℝ)) atTop (nhds 0) := by
    simpa [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hlin : Tendsto (fun j => 2*A^4/(r*(sizes j : ℝ))) atTop (nhds 0) := by
    convert hi.const_mul (2*A^4/r) using 1 <;> first | funext j; ring | simp
  have hroot : Tendsto (fun j => Real.sqrt (2*A^4/(r*(sizes j : ℝ)))) atTop (nhds 0) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hlin
  have hlin' : Tendsto (fun j => 1/(r*(sizes j : ℝ))) atTop (nhds 0) := by
    convert hi.const_mul (1/r) using 1 <;> first | funext j; ring | simp
  have hb : Tendsto (fun j => (Real.sqrt (2*A^4/(r*(sizes j : ℝ)))+
      1/(r*(sizes j : ℝ))+1/(sizes j : ℝ))/κ) atTop (nhds 0) := by
    simpa using ((hroot.add hlin').add hi).div_const κ
  apply squeeze_zero' (Eventually.of_forall (fun _ => DecisionLemma12_probability_nonneg _ _)) _ hb
  filter_upwards [(hN.const_mul_atTop hr).eventually_ge_atTop 2] with j hj
  have hm : 2 ≤ (P j).n1 := by exact_mod_cast hj.trans (hP j).2.2.2.1
  have hc : 2 ≤ sizes j-(P j).n1 := by
    have hh : (2 : ℝ) ≤ ((sizes j-(P j).n1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hP j).1.2.2.le]
      linarith [(hP j).2.2.2.2.1]
    exact_mod_cast hh
  exact CT1_observed_ratio_bound (P j) δ r A (hP j) (hT j) hr hm hc κ hκ

private lemma CT1_mix_B_upper {n} (P : Population n) (hP : ValidDesign P)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty) :
    designVariance P (rawTau P (CT1_mix P)) ≤ CT1_B P := by
  have he : designVariance P (rawTau P (CT1_mix P)) = designVariance P (tau P (late P)) :=
    NDS_variance_congr P (CT1_mix_tau P hP hm hc)
  rw [he,NDS_neyman_variance P hP]
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
  have hd : 0 ≤ Sdiff2 P (late P)/(n : ℝ) := by
    have hden : 0 ≤ (n : ℝ)-1 := by linarith
    dsimp [Sdiff2]
    positivity
  exact sub_le_self _ hd

private lemma CT1_mix_CLT (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hP : ∀ j, Theta (P j) δ r A) (hT : ∀ j, 0 < CT1_total (P j)) :
    (∀ j, 0 < popVar (CT1_mix (P j))) ∧
    ∀ t : ℝ, 0 ≤ t → Tendsto (fun j => probability (P j) (fun S =>
      |rawTau (P j) (CT1_mix (P j)) S /
        Real.sqrt (designVariance (P j) (rawTau (P j) (CT1_mix (P j))))| ≤ t))
      atTop (nhds (SH_absNormalCDF t)) := by
  let C := (1-max δ 0)*r^2
  have hC : 0 < C := mul_pos (sub_pos.mpr (max_lt hδ (by norm_num))) (sq_pos_of_pos hr.1)
  have hlo (j) : C*CT1_total (P j) ≤ popVar (CT1_mix (P j)) :=
    CT1_mix_lower (P j) δ r A hδ hr hA (hP j)
  have hv (j) : 0 < popVar (CT1_mix (P j)) := (mul_pos hC (hT j)).trans_le (hlo j)
  have hfour (j) : ∑ i, (CT1_mix (P j) i-mean (CT1_mix (P j)))^4 ≤
      (8*A^4/C^2)*sizes j*(popVar (CT1_mix (P j)))^2 := by
    have hh := pow_le_pow_left₀ (mul_pos hC (hT j)).le (hlo j) 2
    have hdiv : (CT1_total (P j))^2 ≤ (popVar (CT1_mix (P j)))^2/C^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hC)).mpr
      nlinarith only [hh]
    apply (CT1_mix_fourth (P j) δ r A (hP j)).trans
    have hm := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ 8*A^4*sizes j by positivity)
    convert hm using 1 <;> ring
  refine ⟨hv,fun t ht => ?_⟩
  apply CT1_abs_cdf sizes P _ _ t ht
  exact CT1_rawCLT sizes hsizes P (fun j => CT1_mix (P j)) (fun j => (hP j).1)
    hv r (8*A^4/C^2) hr.1 (by positivity) (fun j => (hP j).2.2.2.1)
    (fun j => (hP j).2.2.2.2.1) hfour

private lemma CT1_cutoffs (α x : ℝ) (hα : 0 < α ∧ α < 1)
    (hx0 : 0 < x) (hx : x < 1-α) :
    ∃ c a b : ℝ, 0 < c ∧ c < a ∧ a < b ∧ x < SH_absNormalCDF c ∧
      SH_absNormalCDF b < 1-α := by
  obtain ⟨c,hc⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := (1+(2*x+(1-α))/3)/2)
    (by linarith) (by linarith)
  obtain ⟨b,hb⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := (1+(x+2*(1-α))/3)/2)
    (by linarith) (by linarith)
  have hc0 : 0 < c := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero,hc]
    linarith
  have hcb : c < b := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [hc,hb]
    linarith
  refine ⟨c,(c+b)/2,b,hc0,by linarith,by linarith,?_,?_⟩
  · dsimp [SH_absNormalCDF]
    rw [hc]
    linarith
  · dsimp [SH_absNormalCDF]
    rw [hb]
    linarith

private lemma CT1_quantile_lower {n} (P : Population n) (hP : ValidDesign P)
    (g : Finset (Fin n) → ℝ≥0∞) (α : ℝ) (hα : 0 < α ∧ α < 1) (a : ℝ≥0∞)
    (ha : probability P (fun S => g S ≤ a) < 1-α) : a < quantile P g α := by
  by_contra hn
  have hq := le_of_not_gt hn
  have hm := CT1_probability_mono P (fun S hS (h : g S ≤ quantile P g α) => h.trans hq)
  have hv := quantile_valid P hP g α hα
  linarith

private lemma CT1_positive_coverage (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (δ r A α : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hα : 0 < α ∧ α < 1)
    (hP : ∀ j, Theta (P j) δ r A) (hT : ∀ j, 0 < CT1_total (P j))
    (x : ℝ) (hx0 : 0 < x) (hx : x < 1-α) :
    ∀ᶠ j in atTop, x < coverage (P j) (late (P j)) α := by
  obtain ⟨c,a,b,hc0,hca,hab,hxc,hb⟩ := CT1_cutoffs α x hα hx0 hx
  have ha0 := hc0.trans hca
  have hK : 0 ≤ CT1_frozenK r A := by dsimp [CT1_frozenK]; positivity
  have hfixed := CT1_fixed_cdf_upper r (CT1_frozenK r A) a b (1-α) hr.1 hK ha0 hab hb
  have hfixedseq := hsizes.tendsto_atTop.eventually hfixed
  have hmix := CT1_mix_CLT sizes hsizes P δ r A hδ hr hA hP hT
  have hκ : 0 < (a^2-c^2)/a^2 := div_pos (by nlinarith) (sq_pos_of_pos ha0)
  have herr := CT1_observed_ratio_limit sizes hsizes P δ r A hr.1 hP hT _ hκ
  have hfrozen := CT1_frozen_bad_limit sizes hsizes P δ r A hr.1 hP hT
  have hlim := ((hmix.2 c hc0.le).sub herr).sub hfrozen
  simp only [sub_zero] at hlim
  filter_upwards [hfixedseq,(tendsto_order.1 hlim).1 x hxc] with j hj hxj
  apply hxj.trans_le
  let R := fun S => |rawTau (P j) (CT1_mix (P j)) S /
    Real.sqrt (designVariance (P j) (rawTau (P j) (CT1_mix (P j))))| ≤ c
  let E := fun S => |rawSigma2 (P j) (observedW (P j) (late (P j)) S) S/CT1_B (P j)-1| ≥
    (a^2-c^2)/a^2
  let F := fun S => ¬ CT1_frozenGood (P j) r A S
  have hinc : probability (P j) R ≤ coverage (P j) (late (P j)) α+
      (probability (P j) E+probability (P j) F) := by
    have hU : probability (P j) (fun S => accepted (P j) (late (P j)) α S ∨ (E S ∨ F S)) ≤
        coverage (P j) (late (P j)) α+(probability (P j) E+probability (P j) F) :=
      (CT1_probability_union (P j) (accepted (P j) (late (P j)) α) (fun S => E S ∨ F S)).trans
        (add_le_add le_rfl (CT1_probability_union (P j) E F))
    apply le_trans (CT1_probability_mono (P j) (fun S hS hR => ?_)) hU
    by_cases hE : E S
    · exact Or.inr (Or.inl hE)
    by_cases hF : F S
    · exact Or.inr (Or.inr hF)
    have hg : CT1_frozenGood (P j) r A S := not_not.mp hF
    have hcdf := hj (P j) (observedW (P j) (late (P j)) S) (hP j).1 hg.1
      (hP j).2.2.2.1 (hP j).2.2.2.2.1 hg.2
    have hq := CT1_quantile_lower (P j) (hP j).1 _ α hα (ENNReal.ofReal a) hcdf
    have hstat := CT1_student_lower
      (rawTau (P j) (CT1_mix (P j)) S)
      (rawSigma2 (P j) (observedW (P j) (late (P j)) S) S)
      (designVariance (P j) (rawTau (P j) (CT1_mix (P j)))) (CT1_B (P j)) a c
      (CT1_sigma_nonneg _ _ _)
      (CT1_rawTau_variance_pos (P j) (hP j).1 _ (hmix.1 j))
      (CT1_B_pos (P j) (hP j).1 (hT j))
      (CT1_mix_B_upper (P j) (hP j).1 (hP j).2.1 (hP j).2.2.1)
      ha0 hc0.le hca hR (lt_of_not_ge hE)
    rw [CT1_mix_tau (P j) (hP j).1 (hP j).2.1 (hP j).2.2.1 S hS] at hstat
    exact Or.inl (hstat.trans hq.le)
  change probability (P j) R-probability (P j) E-probability (P j) F ≤ coverage (P j) (late (P j)) α
  linarith

private lemma CT1_zero_coverage {n} (P : Population n) (δ r A α : ℝ)
    (hP : Theta P δ r A) (hT : CT1_total P = 0) : coverage P (late P) α = 1 := by
  have hn := CT1_sizes P hP.1
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hP.1.1
    linarith
  have h1 := CT1_popVar_nonneg hP.1.1 (w P true (late P))
  have h0 := CT1_popVar_nonneg hP.1.1 (w P false (late P))
  have hv (a : Bool) : popVar (w P a (late P)) = 0 := by
    cases a <;> dsimp [CT1_total] at hT <;> linarith
  have hw (a : Bool) (i : Fin n) : w P a (late P) i = mean (w P false (late P)) := by
    have hsum : (∑ j, (w P a (late P) j-mean (w P a (late P)))^2) = 0 := by
      have hh := (div_eq_iff hn1).mp (hv a)
      simpa only [zero_mul] using hh
    have hi := Finset.single_le_sum (f := fun j => (w P a (late P) j-mean (w P a (late P)))^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hsum] at hi
    have heq : w P a (late P) i = mean (w P a (late P)) := by nlinarith [sq_nonneg (w P a (late P) i-mean (w P a (late P)))]
    rw [heq]
    cases a
    · rfl
    · exact mean_w_equal_at_late P hP.2.1 hP.2.2.1
  have htrue : ∀ S ∈ assignments P, accepted P (late P) α S := by
    intro S hS
    unfold accepted
    rw [observedW_constant P (late P) (mean (w P false (late P))) hw S]
    have hz : rawAR P (fun _ => mean (w P false (late P))) S = 0 := by
      simp [rawAR,rawTau_constant P hP.1 _ S hS,absStudent]
    rw [hz]
    exact bot_le
  have hne : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using hP.1.2.2.le
  have hcard : ((assignments P).card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hne
  unfold coverage probability
  rw [Finset.filter_eq_self.mpr htrue]
  exact div_self hcard

private lemma CT1_uniform_coverage (δ r A α : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hα : 0 < α ∧ α < 1)
    (x : ℝ) (hx0 : 0 < x) (hx : x < 1-α) :
    ∀ᶠ n in atTop, ∀ P : Population n, Theta P δ r A → x ≤ coverage P (late P) α := by
  have hu := CT1_uniform_eventual
    (fun n (P : Population n) => Theta P δ r A ∧ 0 < CT1_total P)
    (fun n P => x < coverage P (late P) α) (by
      intro sizes hsizes P hP
      exact CT1_positive_coverage sizes hsizes P δ r A α hδ hr hA hα
        (fun j => (hP j).1) (fun j => (hP j).2) x hx0 hx)
  filter_upwards [hu] with n hn P hP
  by_cases hT : 0 < CT1_total P
  · exact (hn P ⟨hP,hT⟩).le
  · have hnonneg : 0 ≤ CT1_total P := add_nonneg
      (CT1_popVar_nonneg hP.1.1 _) (CT1_popVar_nonneg hP.1.1 _)
    have hz : CT1_total P = 0 := le_antisymm (le_of_not_gt hT) hnonneg
    rw [CT1_zero_coverage P δ r A α hP hz]
    linarith [hα.1]

/-- Uniform marginal coverage with both beta and model infima. -/
theorem corrected_theorem1_proof (δ r A α : ℝ) (hδ : δ < 1)
    (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hα : 0 < α ∧ α < 1) :
    ENNReal.ofReal (1-α) ≤ Filter.liminf (fun n => infCoverageTheta n δ r A α)
      (atTop ⊓ Filter.principal {n | ∃ P : Population n, Theta P δ r A}) := by
  apply (le_liminf_iff).mpr
  intro y hy
  have hyn : y ≠ ⊤ := ne_top_of_lt hy
  have hyr : y.toReal < 1-α := (ENNReal.lt_ofReal_iff_toReal_lt hyn).mp hy
  obtain ⟨x,hyx,hx⟩ := exists_between hyr
  have hx0 : 0 < x := ENNReal.toReal_nonneg.trans_lt hyx
  have hu := CT1_uniform_coverage δ r A α hδ hr hA hα x hx0 hx
  apply eventually_inf_principal.mpr
  filter_upwards [hu] with n hn hne
  have hbound : ENNReal.ofReal x ≤ infCoverageTheta n δ r A α := by
    unfold infCoverageTheta
    apply le_iInf
    intro β
    apply le_iInf
    intro P
    apply ENNReal.ofReal_le_ofReal
    simpa only [P.property.2] using hn P.val P.property.1
  exact ((ENNReal.lt_ofReal_iff_toReal_lt hyn).mpr hyx).trans_le hbound

end
end AronowAudit.P002.Wave1
