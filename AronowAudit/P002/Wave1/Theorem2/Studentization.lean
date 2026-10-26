import AronowAudit.P002.Wave1.Gap.GLP0022B2

/-! Scalar CLT, absolute CDF, and studentization lemmas for regression adjustment. -/

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

local instance T2C_U_normalNullSingleton : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma T2C_U_popVar_nonneg {n} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    0 ≤ popVar q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by linarith)

lemma T2C_U_probability_mono {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S → F S) :
    probability P E ≤ probability P F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (assignments P).filter E ⊆
    (assignments P).filter F from fun S hS =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1,
        h S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2⟩)

lemma T2C_U_probability_congr {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S ↔ F S) :
    probability P E = probability P F := by
  apply le_antisymm
  · exact T2C_U_probability_mono P (fun S hS => (h S hS).mp)
  · exact T2C_U_probability_mono P (fun S hS => (h S hS).mpr)


lemma T2C_U_rawTau_mean {n} (P : Population n) (q : Fin n → ℝ)
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

lemma T2C_U_rawTau_variance {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) :
    designVariance P (rawTau P q) =
      (fraction P)^2 * (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
  calc
    _ = designVariance P (fun S => fraction P * groupMean S q - fraction P * mean q) := by
      apply NDS_variance_congr
      intro S hS
      rw [T2C_U_rawTau_mean P q S hS]
      ring
    _ = _ := by rw [NDS_variance_affine P hP, NDS_groupMean_variance P hP]; ring


lemma T2C_U_standardize {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (hq : 0 < popVar q)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P q S / Real.sqrt (designVariance P (rawTau P q)) =
      (groupMean S q - mean q) /
        Real.sqrt ((1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q) := by
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hp : 0 < fraction P := div_pos hm (hm.trans hmn)
  rw [T2C_U_rawTau_mean P q S hS, T2C_U_rawTau_variance P hP]
  rw [mul_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp.le]
  exact mul_div_mul_left _ _ hp.ne'

/-- A fourth-moment condition implies the Hájek maximal-entry condition. -/
lemma T2C_U_maximum_bound {n} (P : Population n) (q : Fin n → ℝ)
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

lemma T2C_U_rawCLT (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
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
    (fun j => T2C_U_maximum_bound (P j) (q j) (hP j).1 (hq j) r K hr hK (hmin j) (hfour j)) hb
  intro t
  have h := finitePopulationCLT sizes hsizes P q hP hq hmax t
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  convert h using 1
  funext j
  exact T2C_U_probability_congr (P j) (fun S hS => by
    rw [T2C_U_standardize (P j) (hP j) (q j) (hq j) S hS])

lemma T2C_U_uniform_eventual {X : ℕ → Type*} (H G : ∀ n, X n → Prop)
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

lemma T2C_U_cdf_lt (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
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
    exact hj.trans_le (T2C_U_probability_mono (P j) (fun S hS hx => hx.trans_lt ha))
  · intro z hz
    filter_upwards [(tendsto_order.1 (hseq t)).2 z hz] with j hj
    exact (T2C_U_probability_mono (P j) (fun S hS hx => hx.le)).trans_lt hj

lemma T2C_U_abs_cdf (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
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
  have h := (hseq t).sub (T2C_U_cdf_lt sizes P x hseq (-t))
  rw [AronowAudit.P053.NormalCompletion.normal_cdf_neg] at h
  convert h using 1 <;> simp only [SH_absNormalCDF] <;> ring

lemma T2C_U_absStudent_sq (x s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) :
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

lemma T2C_U_standard_sq (x V a : ℝ) (hV : 0 < V) (ha : 0 ≤ a) :
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

lemma T2C_U_student_upper (x s V a b : ℝ) (hs : 0 ≤ s)
    (hV : 0 < V) (ha : 0 < a) (hab : a < b)
    (hstudent : absStudent x s ≤ ENNReal.ofReal a)
    (hgood : |s/V-1| < (b^2-a^2)/a^2) :
    |x / Real.sqrt V| ≤ b := by
  apply (T2C_U_standard_sq x V b hV (ha.trans hab).le).mpr
  have h := (T2C_U_absStudent_sq x s a hs ha.le).mp hstudent
  have hratio := (abs_lt.mp hgood).2
  have hscale : a^2*s ≤ b^2*V := by
    have hh := (lt_div_iff₀ (sq_pos_of_pos ha)).mp hratio
    have he : (s/V-1)*a^2*V = a^2*s-a^2*V := by field_simp; <;> ring
    have hh' := mul_lt_mul_of_pos_right hh hV
    rw [he] at hh'
    nlinarith
  exact h.trans hscale

lemma T2C_U_student_lower (x s V B a c : ℝ)
    (hs : 0 ≤ s) (hV : 0 < V) (hB : 0 < B) (hVB : V ≤ B)
    (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (hraw : |x / Real.sqrt V| ≤ c)
    (hgood : |s/B-1| < (a^2-c^2)/a^2) :
    absStudent x s ≤ ENNReal.ofReal a := by
  apply (T2C_U_absStudent_sq x s a hs ha.le).mpr
  have h := (T2C_U_standard_sq x V c hV hc).mp hraw
  have hratio := (abs_lt.mp hgood).1
  rw [← neg_div] at hratio
  have hh := (div_lt_iff₀ (sq_pos_of_pos ha)).mp hratio
  have he : (s/B-1)*a^2*B = a^2*s-a^2*B := by field_simp; <;> ring
  have hh' := mul_lt_mul_of_pos_right hh hB
  rw [he] at hh'
  have hcb := mul_le_mul_of_nonneg_left hVB (sq_nonneg c)
  nlinarith

end
end AronowAudit.P002.Wave1
