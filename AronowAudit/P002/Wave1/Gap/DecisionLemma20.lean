import AronowAudit.P002.P002_Audit
import AronowAudit.P002.Wave1.Gap.DecisionLemma12
import AronowAudit.P002.Wave1.Gap.GP0022B3
import AronowAudit.P002.Wave1.E61Eigenvalue
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT

/-!
P002-T7: corrected Lemma 20, Supplement p. 42, in the positive residual-variance
scope.

Scalar sampling fourth moments and first Borel--Cantelli give sampled residual
scores and second moments. Together with sampled Gram control these yield an
eventually positive pooled residual variance and a uniform relative fourth-moment
bound, uniformly over the pooled coefficient vector. The finite-population CLT
then proves (E.59). Finite sampling moment bounds and the actual OLS normal
equations prove (E.58) and (E.61), including the singular-arm exceptional events;
a tail comparison proves (E.60). Only the marginal randomization laws are used.
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

lemma DecisionLemma20_norm_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 ≤ normSq b := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma DecisionLemma20_fullrank {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (c : ℝ) (hc : 0 < c)
    (h : ∀ b, c * normSq b ≤ dotProduct b (gram x S *ᵥ b)) :
    (gram x S).det ≠ 0 := by
  have hker (b : Option (Fin k) → ℝ) (hb : gram x S *ᵥ b = 0) : b = 0 := by
    have H := h b
    rw [hb, dotProduct_zero] at H
    have hz : normSq b = 0 := le_antisymm
      (nonpos_of_mul_nonpos_right H hc) (DecisionLemma20_norm_nonneg b)
    funext s
    have hi : b s ^ 2 ≤ normSq b :=
      Finset.single_le_sum (fun t _ => sq_nonneg (b t)) (Finset.mem_univ s)
    rw [hz] at hi
    exact (sq_nonpos_iff _).mp hi
  have hi : Function.Injective (gram x S).mulVec := by
    intro b d hbd
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, hbd, sub_self]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

lemma DecisionLemma20_population_fullrank {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r) :
    (gram P.x Finset.univ).det ≠ 0 := by
  have hn : 0 < n := by have := hP.1.1; omega
  apply DecisionLemma20_fullrank P.x Finset.univ (min 1 e) (lt_min zero_lt_one he)
  intro b
  rw [gram_quadratic]
  simpa only [groupMean, mean, Finset.card_univ, Fintype.card_fin] using
    (corrected_augmented_gram P.x hn e hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2).2.2.2 b

lemma DecisionLemma20_pooled_score {n k} (x : Fin n → Fin k → ℝ)
    (q : Fin n → ℝ) (hg : (gram x Finset.univ).det ≠ 0) :
    score x Finset.univ (fun i => q i - dotProduct (augmented x i)
      (ols x Finset.univ q)) = 0 := by
  rw [score_residual, ← ols_normal_equations x Finset.univ q hg, sub_self]

lemma DecisionLemma20_pooled_mean {n k} (x : Fin n → Fin k → ℝ)
    (q : Fin n → ℝ) (hg : (gram x Finset.univ).det ≠ 0) :
    mean (fun i => q i - dotProduct (augmented x i) (ols x Finset.univ q)) = 0 := by
  have h := congrFun (DecisionLemma20_pooled_score x q hg) none
  simpa only [score, augmented, one_mul, groupMean, mean, Finset.card_univ,
    Fintype.card_fin, Pi.zero_apply] using h

lemma DecisionLemma20_fourth_bound {n} (q : Fin n → ℝ) (B V : ℝ)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (h : fourthNorm q ≤ B * Real.sqrt V) :
    mean (fun i => q i ^ 4) ≤ B ^ 4 * V ^ 2 := by
  have h4 : 0 ≤ mean (fun i => q i ^ 4) := by
    exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (Nat.cast_nonneg _)
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 4
  have hid : (Real.sqrt (Real.sqrt (mean (fun i => q i ^ 4)))) ^ 4 =
      mean (fun i => q i ^ 4) := by
    calc
      _ = ((Real.sqrt (Real.sqrt (mean (fun i => q i ^ 4)))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (mean (fun i => q i ^ 4))) ^ 2 := by
        rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = _ := Real.sq_sqrt h4
  change (Real.sqrt (Real.sqrt (mean (fun i => q i ^ 4)))) ^ 4 ≤ _ at hpow
  rw [hid, mul_pow] at hpow
  have hv : (Real.sqrt V) ^ 4 = V ^ 2 := by
    calc
      _ = ((Real.sqrt V) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  simpa only [hv] using hpow

/-- A scalar sampling strong law with only the fixed-size marginal laws. -/
lemma DecisionLemma20_ae_sample {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (Z : ∀ j, Ω → Finset (Fin (sizes j)))
    (hP : ∀ j, ValidDesign (P j)) (hZ : RandomizationSequence P μ Z)
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hl : ∀ j, r * sizes j ≤ ((P j).n1 : ℝ))
    (a : ∀ j, Fin (sizes j) → ℝ)
    (hb : ∀ j, mean (fun i => a j i ^ 2) ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun j =>
      (∑ i ∈ Z j ω, (a j i - mean (a j))) / (sizes j : ℝ)) atTop (nhds 0) := by
  have hn (j) : 0 < sizes j := by have := (hP j).1; omega
  have hnR (j) : (0 : ℝ) < sizes j := by exact_mod_cast hn j
  have htop : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hsizes.tendsto_atTop
  have hm : ∀ᶠ j in atTop, 4 ≤ (P j).n1 := by
    filter_upwards [(htop.const_mul_atTop hr).eventually_ge_atTop 4] with j hj
    exact_mod_cast hj.trans (hl j)
  have hb' (j) : ∑ i, (a j i - mean (a j)) ^ 2 ≤ C * sizes j := by
    rw [DecisionLemma12_sum_centered_sq (hn j)]
    have h := (div_le_iff₀ (hnR j)).mp (hb j)
    nlinarith [mul_nonneg (hnR j).le (sq_nonneg (mean (a j)))]
  have hω : ∀ᵐ ω ∂μ, ∀ q : ℕ, ∀ᶠ j in atTop,
      |(∑ i ∈ Z j ω, (a j i - mean (a j))) / (sizes j : ℝ)| < 1 / ((q : ℝ)+1) := by
    apply ae_all_iff.mpr
    intro q
    exact DecisionLemma12_ae_sample_small μ sizes hsizes P Z hP hZ hm _
      (fun j => DecisionLemma12_sum_centered (hn j) _) C _ hC (by positivity) hb'
  filter_upwards [hω] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hω q)
  exact ⟨J, fun j hj => by simpa only [Real.dist_eq, sub_zero] using (hJ j hj).trans hq⟩

lemma DecisionLemma20_arm_mean_error {n} (P : Population n) (hP : ValidDesign P)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) (a : Fin n → ℝ)
    (r : ℝ) (hr : 0 < r) (hl : r*n ≤ (P.n1 : ℝ))
    (hu : (P.n1 : ℝ) ≤ (1-r)*n) (b : Bool) :
    |groupMean (if b then S else Sᶜ) a - mean a| ≤
      |(∑ i ∈ S, (a i - mean a)) / (n : ℝ)| / r := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1; omega)
  have hs : S.card = P.n1 := (Finset.mem_powersetCard.mp hS).2
  have hc : (Sᶜ.card : ℝ) = (n : ℝ) - P.n1 := by
    rw [Finset.card_compl, Fintype.card_fin, hs, Nat.cast_sub hP.2.2.le]
  have hsz : r*n ≤ ((if b then S else Sᶜ).card : ℝ) := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hs, hc] <;> linarith
  have hszpos : 0 < ((if b then S else Sᶜ).card : ℝ) := (mul_pos hr hn).trans_le hsz
  have ht : (∑ i ∈ Sᶜ, (a i - mean a)) = -(∑ i ∈ S, (a i - mean a)) := by
    have H := Finset.sum_add_sum_compl S (fun i => a i - mean a)
    rw [DecisionLemma12_sum_centered (by exact_mod_cast hn)] at H
    linarith
  have he (T : Finset (Fin n)) (hT : (T.card : ℝ) ≠ 0) :
      groupMean T a - mean a = (∑ i ∈ T, (a i - mean a)) / T.card := by
    simp only [groupMean, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [he _ hszpos.ne', abs_div, abs_of_pos hszpos, abs_div, abs_of_pos hn]
  have hsabs : |∑ i ∈ (if b then S else Sᶜ), (a i - mean a)| =
      |∑ i ∈ S, (a i - mean a)| := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, ht, abs_neg]
  rw [hsabs, div_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    (by simpa only [mul_comm] using hsz)

lemma DecisionLemma20_ae_arm_means {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (Z : ∀ j, Ω → Finset (Fin (sizes j)))
    (hP : ∀ j, ValidDesign (P j)) (hZ : RandomizationSequence P μ Z)
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hl : ∀ j, r * sizes j ≤ ((P j).n1 : ℝ))
    (hu : ∀ j, ((P j).n1 : ℝ) ≤ (1-r) * sizes j)
    (a : ∀ j, Fin (sizes j) → ℝ) (hb : ∀ j, mean (fun i => a j i ^ 2) ≤ C) :
    ∀ᵐ ω ∂μ, ∀ b : Bool, Tendsto (fun j =>
      groupMean (if b then Z j ω else (Z j ω)ᶜ) (a j) - mean (a j)) atTop (nhds 0) := by
  filter_upwards [DecisionLemma20_ae_sample μ sizes hsizes P Z hP hZ r C hr hC hl a hb,
    DecisionLemma12_ae_assignment P μ Z hZ] with ω hω hS
  intro b
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun j => ?_))
    (by simpa only [abs_zero, zero_div] using hω.abs.div_const r)
  rw [Real.norm_eq_abs]
  exact DecisionLemma20_arm_mean_error (P j) (hP j) (Z j ω) (hS j) (a j) r hr (hl j) (hu j) b

lemma DecisionLemma20_mean_div {n} (q : Fin n → ℝ) (c : ℝ) :
    mean (fun i => q i / c) = mean q / c := by
  simp only [mean, ← Finset.sum_div]
  ring

def DecisionLemma20_standardResidual {n k} (P : CovPopulation n k) (a : Bool) : Fin n → ℝ :=
  fun i => residual P a (late P.pop) i / Real.sqrt (popVar (residual P a (late P.pop)))

lemma DecisionLemma20_residual_moments {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hB : 0 ≤ B) (hP : Xi P δ e A B r)
    (hv : ∀ a, 0 < popVar (residual P a (late P.pop))) (a : Bool) :
    score P.x Finset.univ (DecisionLemma20_standardResidual P a) = 0 ∧
    mean (fun i => DecisionLemma20_standardResidual P a i ^ 2) = ((n : ℝ)-1)/n ∧
    mean (fun i => DecisionLemma20_standardResidual P a i ^ 4) ≤ B ^ 4 := by
  have hg := DecisionLemma20_population_fullrank P δ e A B r he hP
  have hmean := DecisionLemma20_pooled_mean P.x (w P.pop a (late P.pop)) hg
  have hscore := DecisionLemma20_pooled_score P.x (w P.pop a (late P.pop)) hg
  change mean (residual P a (late P.pop)) = 0 at hmean
  change score P.x Finset.univ (residual P a (late P.pop)) = 0 at hscore
  have hV : 0 < popVar (residual P a (late P.pop)) := hv a
  have hs4 : (Real.sqrt (popVar (residual P a (late P.pop)))) ^ 4 =
      (popVar (residual P a (late P.pop))) ^ 2 := by
    calc
      _ = ((Real.sqrt (popVar (residual P a (late P.pop)))) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hV.le]
  refine ⟨?_, ?_, ?_⟩
  · ext s
    have h := congrFun hscore s
    change groupMean Finset.univ (fun i => augmented P.x i s *
      (residual P a (late P.pop) i / Real.sqrt _)) = 0
    simp_rw [← mul_div_assoc]
    simp only [groupMean, ← Finset.sum_div, div_right_comm]
    change score P.x Finset.univ (residual P a (late P.pop)) s / _ = 0
    rw [hscore]
    simp
  · have H := FPCLT_second (residual P a (late P.pop)) hV
    simp only [FPCLT_normalize, hmean, sub_zero] at H
    simpa only [DecisionLemma20_standardResidual, mean, H]
  · have hf := DecisionLemma20_fourth_bound (residual P a (late P.pop)) B _ hB hV.le
      (hP.2.2.2.2.2.2.1 a)
    simp only [DecisionLemma20_standardResidual, div_pow, hs4]
    rw [DecisionLemma20_mean_div]
    exact (div_le_iff₀ (sq_pos_of_pos hV)).mpr hf

lemma DecisionLemma20_augmented_fourth {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r) (s : Option (Fin k)) :
    mean (fun i => augmented P.x i s ^ 4) ≤ max 1 A := by
  cases s with
  | none =>
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by have := hP.1.1; omega)
    simpa only [augmented, one_pow, mean, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, div_self hn] using le_max_left (1 : ℝ) A
  | some s => exact (hP.2.2.2.2.2.2.2.2.1 s).trans (le_max_right _ _)

lemma DecisionLemma20_cross {ι : Type*} [Fintype ι]
    (σ t : ℝ) (c h : ι → ℝ) (ht : 0 ≤ t) (hh : ∀ s, |h s| ≤ t) :
    -(t * ((Fintype.card ι : ℝ) * σ ^ 2 + normSq c)) ≤ 2 * σ * dotProduct h c := by
  have hi (s : ι) : -(t * (σ ^ 2 + c s ^ 2)) ≤ 2 * σ * (h s * c s) := by
    have hmul : |2 * σ * (h s * c s)| ≤ t * (σ ^ 2 + c s ^ 2) := by
      calc
        _ = 2 * |σ| * |c s| * |h s| := by rw [abs_mul, abs_mul, abs_mul]; norm_num; ring
        _ ≤ 2 * |σ| * |c s| * t :=
          mul_le_mul_of_nonneg_left (hh s) (by positivity)
        _ ≤ _ := by
          have H := mul_nonneg ht (sq_nonneg (|σ| - |c s|))
          nlinarith [sq_abs σ, sq_abs (c s)]
    exact (abs_le.mp hmul).1
  have H := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset ι)) => hi s)
  simpa only [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, normSq, dotProduct] using H

lemma DecisionLemma20_quadratic_lower {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (u : Fin n → ℝ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hg : ∀ c, (ell/2) * normSq c ≤ dotProduct c (gram x S *ᵥ c))
    (hu : (1/4 : ℝ) ≤ groupMean S (fun i => u i ^ 2))
    (hh : ∀ s, |score x S u s| ≤ ell / (8*((k : ℝ)+1))) :
    ∀ (σ : ℝ) (c : Option (Fin k) → ℝ),
      (ell/8) * (normSq c + σ ^ 2) ≤
        groupMean S (fun i => (σ*u i + dotProduct (augmented x i) c) ^ 2) := by
  intro σ c
  have hnrm := DecisionLemma20_norm_nonneg c
  have hc := DecisionLemma20_cross σ (ell/(8*((k : ℝ)+1))) c (score x S u)
    (by positivity) hh
  simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hc
  have hd : ell/(8*((k : ℝ)+1)) * (((k : ℝ)+1)*σ^2 + normSq c) ≤
      (ell/8)*(σ^2+normSq c) := by
    have hdpos : 0 < (k : ℝ)+1 := by positivity
    have hn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc
      _ ≤ ell/(8*((k : ℝ)+1)) * (((k : ℝ)+1)*(σ^2+normSq c)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg hn hnrm]
      _ = _ := by field_simp <;> ring
  have hexpand : groupMean S (fun i => (σ*u i + dotProduct (augmented x i) c)^2) =
      σ^2 * groupMean S (fun i => u i ^ 2) + 2*σ*dotProduct (score x S u) c +
        dotProduct c (gram x S *ᵥ c) := by
    rw [score_dot, gram_quadratic]
    have hi (i : Fin n) : (σ*u i + dotProduct (augmented x i) c)^2 =
        σ^2 * u i ^ 2 + (2*σ)*(u i*dotProduct (augmented x i) c) +
          (dotProduct (augmented x i) c)^2 := by ring
    simp only [hi, groupMean, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hexpand]
  have H1 := mul_le_mul_of_nonneg_left hu (sq_nonneg σ)
  have H2 := hg c
  have H3 := mul_nonneg (sub_nonneg.mpr hell1) (sq_nonneg σ)
  nlinarith only [hc, hd, H1, H2, H3, mul_nonneg hell.le hnrm]

lemma DecisionLemma20_ae_gram {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k)
    (Z : ∀ j, Ω → Finset (Fin (sizes j))) (δ e A B r : ℝ)
    (he : 0 < e) (hA : 0 < A) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hZ : RandomizationSequence (fun j => (P j).pop) μ Z) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ∀ (a : Bool) (c : Option (Fin k) → ℝ),
      (min 1 e / 2) * normSq c ≤
        dotProduct c (gram (P j).x (if a then Z j ω else (Z j ω)ᶜ) *ᵥ c) := by
  have hsample : E61Eigenvalue.SamplingBound := E61Eigenvalue.n5_proof
    E61Eigenvalue.n1_proof (E61Eigenvalue.n4_proof E61Eigenvalue.n2_proof E61Eigenvalue.n3_proof)
  have hae : E61Eigenvalue.AEEntrywise := E61Eigenvalue.n10_proof
    (E61Eigenvalue.n7_proof hsample E61Eigenvalue.n6_proof)
    E61Eigenvalue.n8_proof E61Eigenvalue.n9_proof
  have hω := hae μ sizes hsizes k P Z δ e A B r hA hr hP hZ id strictMono_id
  filter_upwards [hω] with ω hω
  have hG : ∀ j (c : Option (Fin k) → ℝ),
      min 1 e * normSq c ≤ dotProduct c (gram (P j).x Finset.univ *ᵥ c) := by
    intro j c
    have hn : 0 < sizes j := by have := (hP j).1.1; omega
    rw [gram_quadratic]
    simpa only [groupMean, mean, Finset.card_univ, Fintype.card_fin] using
      (corrected_augmented_gram (P j).x hn e (hP j).2.2.2.2.2.2.2.1
        (hP j).2.2.2.2.2.2.2.2.2).2.2.2 c
  obtain ⟨err, herr, hb⟩ := E61Eigenvalue.n12_proof E61Eigenvalue.n11_proof k
    (fun j a => gram (P j).x (if a then Z j ω else (Z j ω)ᶜ))
    (fun j => gram (P j).x Finset.univ) (min 1 e) hω hG
  have hmin : 0 < min (1 : ℝ) e := lt_min zero_lt_one he
  filter_upwards [herr.eventually (Ioi_mem_nhds (show -(min 1 e)/2 < (0 : ℝ) by linarith))]
    with j hj
  intro a c
  have H := hb j a c
  have hnrm := DecisionLemma20_norm_nonneg c
  nlinarith [mul_nonneg (sub_nonneg.mpr hj.le) hnrm]

/-- Uniform sampled lower bound after adjoining the normalized population residual. -/
lemma DecisionLemma20_ae_residual_gram {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k)
    (Z : ∀ j, Ω → Finset (Fin (sizes j))) (δ e A B r : ℝ)
    (he : 0 < e) (hA : 0 < A) (hB : 0 < B) (hr : 0 < r)
    (hP : ∀ j, Xi (P j) δ e A B r)
    (hv : ∀ j a, 0 < popVar (residual (P j) a (late (P j).pop)))
    (hZ : RandomizationSequence (fun j => (P j).pop) μ Z) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ∀ a (σ : ℝ) (c : Option (Fin k) → ℝ),
      (min 1 e / 8) * (normSq c + σ ^ 2) ≤
        groupMean (if a then Z j ω else (Z j ω)ᶜ)
          (fun i => (σ*DecisionLemma20_standardResidual (P j) a i +
            dotProduct (augmented (P j).x i) c)^2) := by
  have hmom (j a) := DecisionLemma20_residual_moments (P j) δ e A B r he hB.le (hP j) (hv j) a
  have hC : 0 ≤ max (1 : ℝ) A + B ^ 4 := by positivity
  have hC2 : 0 ≤ B ^ 4 := by positivity
  have hl (j) := (hP j).2.2.2.1
  have hu (j) := (hP j).2.2.2.2.1
  have hdesign (j) := (hP j).1
  have hsec : ∀ᵐ ω ∂μ, ∀ a b : Bool, Tendsto (fun j =>
      groupMean (if b then Z j ω else (Z j ω)ᶜ)
        (fun i => DecisionLemma20_standardResidual (P j) a i ^ 2) -
      mean (fun i => DecisionLemma20_standardResidual (P j) a i ^ 2)) atTop (nhds 0) := by
    apply ae_all_iff.mpr
    intro a
    apply DecisionLemma20_ae_arm_means μ sizes hsizes (fun j => (P j).pop) Z hdesign hZ
      r (B^4) hr hC2 hl hu
    intro j
    simpa only [← pow_mul] using (hmom j a).2.2
  have hscore : ∀ᵐ ω ∂μ, ∀ (a : Bool) (s : Option (Fin k)) (b : Bool),
      Tendsto (fun j => score (P j).x (if b then Z j ω else (Z j ω)ᶜ)
        (DecisionLemma20_standardResidual (P j) a) s) atTop (nhds 0) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro s
    have hb (j) : mean (fun i =>
        (augmented (P j).x i s * DecisionLemma20_standardResidual (P j) a i)^2) ≤
          max 1 A + B^4 := by
      calc
        _ ≤ mean (fun i => augmented (P j).x i s ^ 4 +
            DecisionLemma20_standardResidual (P j) a i ^ 4) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply Finset.sum_le_sum
          intro i _
          nlinarith [sq_nonneg ((augmented (P j).x i s)^2 -
            (DecisionLemma20_standardResidual (P j) a i)^2)]
        _ = mean (fun i => augmented (P j).x i s ^ 4) +
            mean (fun i => DecisionLemma20_standardResidual (P j) a i ^ 4) := by
          simp only [mean, Finset.sum_add_distrib, add_div]
        _ ≤ _ := add_le_add (DecisionLemma20_augmented_fourth (P j) δ e A B r (hP j) s)
          (hmom j a).2.2
    have H := DecisionLemma20_ae_arm_means μ sizes hsizes (fun j => (P j).pop) Z hdesign hZ
      r (max 1 A+B^4) hr hC hl hu _ hb
    filter_upwards [H] with ω hω
    intro b
    have hz (j) : mean (fun i =>
        augmented (P j).x i s * DecisionLemma20_standardResidual (P j) a i) = 0 := by
      have H := congrFun (hmom j a).1 s
      simpa only [score, groupMean, mean, Finset.card_univ, Fintype.card_fin,
        Pi.zero_apply] using H
    simpa only [hz, sub_zero, score] using hω b
  filter_upwards [DecisionLemma20_ae_gram μ sizes hsizes k P Z δ e A B r he hA hr hP hZ,
    hsec, hscore] with ω hg hs hh
  have hmin : 0 < min (1 : ℝ) e := lt_min zero_lt_one he
  have hsec' : ∀ᶠ j in atTop, ∀ a : Bool,
      (1/4 : ℝ) ≤ groupMean (if a then Z j ω else (Z j ω)ᶜ)
        (fun i => DecisionLemma20_standardResidual (P j) a i ^ 2) := by
    apply Filter.eventually_all.mpr
    intro a
    filter_upwards [(hs a a).eventually (Ioi_mem_nhds (show -(1/4 : ℝ) < 0 by norm_num))]
      with j hj
    have hn : (2 : ℝ) ≤ sizes j := by exact_mod_cast (hP j).1.1
    have hn0 : (0 : ℝ) < sizes j := by linarith
    have hpop : (1/2 : ℝ) ≤ mean (fun i => DecisionLemma20_standardResidual (P j) a i ^ 2) := by
      rw [(hmom j a).2.1]
      apply (le_div_iff₀ hn0).mpr
      linarith
    linarith
  have hscore' : ∀ᶠ j in atTop, ∀ (a : Bool) (s : Option (Fin k)),
      |score (P j).x (if a then Z j ω else (Z j ω)ᶜ)
        (DecisionLemma20_standardResidual (P j) a) s| ≤ min 1 e/(8*((k : ℝ)+1)) := by
    apply Filter.eventually_all.mpr
    intro a
    apply Filter.eventually_all.mpr
    intro s
    have H : Tendsto (fun j => |score (P j).x (if a then Z j ω else (Z j ω)ᶜ)
        (DecisionLemma20_standardResidual (P j) a) s|) atTop (nhds 0) := by
      simpa only [abs_zero] using (hh a s a).abs
    exact (H.eventually (Iio_mem_nhds (by positivity))).mono (fun _ h => h.le)
  filter_upwards [hg, hsec', hscore'] with j hj hj2 hjh
  intro a σ c
  cases a with
  | false =>
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      DecisionLemma20_quadratic_lower (P j).x ((Z j ω)ᶜ)
        (DecisionLemma20_standardResidual (P j) false) (min 1 e) hmin (min_le_left _ _)
        (by simpa only [Bool.false_eq_true, ↓reduceIte] using hj false)
        (by simpa only [Bool.false_eq_true, ↓reduceIte] using hj2 false)
        (by simpa only [Bool.false_eq_true, ↓reduceIte] using hjh false) σ c
  | true =>
    simpa only [↓reduceIte] using
      DecisionLemma20_quadratic_lower (P j).x (Z j ω)
        (DecisionLemma20_standardResidual (P j) true) (min 1 e) hmin (min_le_left _ _)
        (by simpa only [↓reduceIte] using hj true)
        (by simpa only [↓reduceIte] using hj2 true)
        (by simpa only [↓reduceIte] using hjh true) σ c

lemma DecisionLemma20_dot_fourth {ι : Type*} [Fintype ι] (z c : ι → ℝ) :
    (dotProduct z c)^4 ≤ (Fintype.card ι : ℝ) * (∑ s, z s ^ 4) * (normSq c)^2 := by
  have hCS : (dotProduct z c)^2 ≤ normSq z * normSq c :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z c
  have hz : (normSq z)^2 ≤ (Fintype.card ι : ℝ) * (∑ s, z s ^ 4) := by
    have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => z s ^ 2) (fun _ => (1 : ℝ))
    simpa only [one_pow, mul_one, ← pow_mul, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, normSq, mul_comm] using H
  calc
    _ = ((dotProduct z c)^2)^2 := by ring
    _ ≤ (normSq z * normSq c)^2 := pow_le_pow_left₀ (sq_nonneg _) hCS 2
    _ = (normSq z)^2 * (normSq c)^2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hz (sq_nonneg _)

lemma DecisionLemma20_sum_dot_fourth {n k} (x : Fin n → Fin k → ℝ) (C : ℝ)
    (hx : ∀ s : Option (Fin k), ∑ i, augmented x i s ^ 4 ≤ C*n)
    (c : Option (Fin k) → ℝ) :
    (∑ i, (dotProduct (augmented x i) c)^4) ≤
      ((k : ℝ)+1)^2 * C * n * (normSq c)^2 := by
  have hdim : (Fintype.card (Option (Fin k)) : ℝ) = (k : ℝ)+1 := by simp
  calc
    _ ≤ ∑ i, (((k : ℝ)+1) * (∑ s, augmented x i s ^ 4) * (normSq c)^2) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [hdim] using (DecisionLemma20_dot_fourth (augmented x i) c)
    _ = (((k : ℝ)+1) * (normSq c)^2) * ∑ s : Option (Fin k), ∑ i, augmented x i s ^ 4 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (((k : ℝ)+1) * (normSq c)^2) * ∑ _s : Option (Fin k), C*n :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => hx s)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hdim, nsmul_eq_mul]; ring

lemma DecisionLemma20_add_fourth (a b : ℝ) : (a+b)^4 ≤ 8*a^4+8*b^4 := by
  have h : (a+b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a-b)]
  have H := pow_le_pow_left₀ (sq_nonneg (a+b)) h 2
  nlinarith [sq_nonneg (a^2-b^2)]

/-- The lower bound is uniform in the pooled coefficients, even if arm slopes diverge. -/
lemma DecisionLemma20_pooled_kurtosis {n k} (P : CovPopulation n k)
    (δ e A B r c : ℝ) (he : 0 < e) (hB : 0 < B) (hr : 0 < r) (hc : 0 < c)
    (hP : Xi P δ e A B r) (hv : ∀ a, 0 < popVar (residual P a (late P.pop)))
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop)
    (hlower : ∀ a (σ : ℝ) (b : Option (Fin k) → ℝ),
      c * (normSq b + σ^2) ≤ groupMean (if a then S else Sᶜ)
        (fun i => (σ*DecisionLemma20_standardResidual P a i + dotProduct (augmented P.x i) b)^2)) :
    let q := observedW P.pop (late P.pop) S
    let u := fun i => q i - dotProduct (augmented P.x i) (ols P.x Finset.univ q)
    0 < popVar u ∧
      (∑ i, u i ^ 4) ≤
        (8 * max (B^4) (((k : ℝ)+1)^2*max 1 A) / (r*c)^2) * n * (popVar u)^2 := by
  let q := observedW P.pop (late P.pop) S
  let β := ols P.x Finset.univ q
  let u := fun i => q i - dotProduct (augmented P.x i) β
  let σ := fun a => Real.sqrt (popVar (residual P a (late P.pop)))
  let b := fun a => psi P a (late P.pop) - β
  let T := (normSq (b true) + (σ true)^2) + (normSq (b false) + (σ false)^2)
  let M := max (B^4) (((k : ℝ)+1)^2*max 1 A)
  have hn : 0 < n := by have := hP.1.1; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by
    have H : (2 : ℝ) ≤ n := by exact_mod_cast hP.1.1
    linarith
  have hσ (a) : 0 < σ a := Real.sqrt_pos.mpr (hv a)
  have hg := DecisionLemma20_population_fullrank P δ e A B r he hP
  have hum : mean u = 0 := DecisionLemma20_pooled_mean P.x q hg
  have hterm (a) : 0 ≤ normSq (b a) + (σ a)^2 := by
    exact add_nonneg (DecisionLemma20_norm_nonneg _) (sq_nonneg _)
  have hT : 0 < T := by
    have H := DecisionLemma20_norm_nonneg (b true)
    have H' := hterm false
    dsimp only [T]
    nlinarith [sq_pos_of_pos (hσ true)]
  have hsz (a : Bool) : r*n ≤ ((if a then S else Sᶜ).card : ℝ) := by
    have hs : S.card = P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_compl, Fintype.card_fin, hs,
        Nat.cast_sub hP.1.2.2.le]
      linarith [hP.2.2.2.2.1]
    · simpa only [↓reduceIte, hs] using hP.2.2.2.1
  have hu (a : Bool) (i : Fin n) (hi : i ∈ (if a then S else Sᶜ)) :
      u i = σ a * DecisionLemma20_standardResidual P a i + dotProduct (augmented P.x i) (b a) := by
    have hcancel : σ a * DecisionLemma20_standardResidual P a i = residual P a (late P.pop) i := by
      change σ a * (residual P a (late P.pop) i / σ a) = _
      field_simp [(hσ a).ne']
    rw [hcancel]
    dsimp only [u, q, b]
    rw [dotProduct_sub]
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte] at hi
      rw [observedW_control P.pop (late P.pop) S i hi]
      dsimp only [residual]
      ring
    · simp only [↓reduceIte] at hi
      rw [observedW_treated P.pop (late P.pop) S i hi]
      dsimp only [residual]
      ring
  have harmlower (a : Bool) :
      r*n*c*(normSq (b a)+(σ a)^2) ≤ ∑ i ∈ (if a then S else Sᶜ), u i ^ 2 := by
    have hpos : 0 < ((if a then S else Sᶜ).card : ℝ) := (mul_pos hr hnR).trans_le (hsz a)
    have H := hlower a (σ a) (b a)
    have heq : groupMean (if a then S else Sᶜ) (fun i =>
        (σ a * DecisionLemma20_standardResidual P a i + dotProduct (augmented P.x i) (b a))^2) =
        groupMean (if a then S else Sᶜ) (fun i => u i ^ 2) := by
      apply groupMean_congr
      intro i hi
      rw [hu a i hi]
    rw [heq] at H
    have H' := (le_div_iff₀ hpos).mp H
    have H'' := mul_le_mul_of_nonneg_right (hsz a) (mul_nonneg hc.le (hterm a))
    dsimp only [groupMean] at H'
    nlinarith only [H', H'']
  have hsumlower : r*n*c*T ≤ ∑ i, u i ^ 2 := by
    have H := harmlower true
    have H' := harmlower false
    simp only [Bool.false_eq_true, ↓reduceIte] at H H'
    have ht := Finset.sum_add_sum_compl S (fun i => u i ^ 2)
    dsimp only [T]
    nlinarith only [H, H', ht]
  have hvar : popVar u = (∑ i, u i ^ 2) / ((n : ℝ)-1) := by
    simp only [popVar, hum, sub_zero]
  have hV : 0 < popVar u := by
    rw [hvar]
    apply div_pos _ hn1
    exact (by positivity : 0 < r*n*c*T).trans_le hsumlower
  have hscale : r*c*T ≤ popVar u := by
    have H : (∑ i, u i ^ 2) = popVar u * ((n : ℝ)-1) := (div_eq_iff hn1.ne').mp hvar.symm
    have H' : r*n*c*T ≤ (n : ℝ) * popVar u := by nlinarith only [hsumlower, H, hV]
    nlinarith only [H', hnR]
  have hM : 0 ≤ M := (by positivity : 0 ≤ B^4).trans (le_max_left _ _)
  have hmom (a) := DecisionLemma20_residual_moments P δ e A B r he hB.le hP hv a
  have hres4 (a) : ∑ i, DecisionLemma20_standardResidual P a i ^ 4 ≤ B^4*n :=
    (div_le_iff₀ hnR).mp (hmom a).2.2
  have hx4 (s) : ∑ i, augmented P.x i s ^ 4 ≤ max 1 A * n :=
    (div_le_iff₀ hnR).mp (DecisionLemma20_augmented_fourth P δ e A B r hP s)
  have hupper (a) :
      (∑ i, (σ a * DecisionLemma20_standardResidual P a i + dotProduct (augmented P.x i) (b a))^4) ≤
        8*n*M*((σ a)^4+(normSq (b a))^2) := by
    calc
      _ ≤ ∑ i, (8*(σ a * DecisionLemma20_standardResidual P a i)^4 +
          8*(dotProduct (augmented P.x i) (b a))^4) :=
        Finset.sum_le_sum (fun i _ => DecisionLemma20_add_fourth _ _)
      _ = 8*(σ a)^4*(∑ i, DecisionLemma20_standardResidual P a i ^ 4) +
          8*(∑ i, (dotProduct (augmented P.x i) (b a))^4) := by
        simp only [mul_pow, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      _ ≤ 8*(σ a)^4*(B^4*n) +
          8*(((k : ℝ)+1)^2 * max 1 A * n * (normSq (b a))^2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hres4 a) (by positivity))
          (mul_le_mul_of_nonneg_left (DecisionLemma20_sum_dot_fourth P.x (max 1 A) hx4 (b a)) (by norm_num))
      _ ≤ _ := by
        have H1 := mul_le_mul_of_nonneg_right (show B^4 ≤ M from le_max_left _ _)
          (show 0 ≤ 8*n*(σ a)^4 by positivity)
        have H0 := mul_le_mul_of_nonneg_right
          (show ((k : ℝ)+1)^2 * max 1 A ≤ M from le_max_right _ _)
          (show 0 ≤ 8*n*(normSq (b a))^2 by positivity)
        nlinarith only [H1, H0]
  have hu4 : (∑ i, u i ^ 4) ≤ 8*n*M*T^2 := by
    have Hi (i : Fin n) : u i ^ 4 ≤
        (σ true * DecisionLemma20_standardResidual P true i + dotProduct (augmented P.x i) (b true))^4 +
        (σ false * DecisionLemma20_standardResidual P false i + dotProduct (augmented P.x i) (b false))^4 := by
      by_cases hi : i ∈ S
      · rw [hu true i (by simpa using hi)]
        exact le_add_of_nonneg_right (by positivity)
      · rw [hu false i (by simpa using hi)]
        exact le_add_of_nonneg_left (by positivity)
    have H := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => Hi i)
    rw [Finset.sum_add_distrib] at H
    have H1 := hupper true
    have H0 := hupper false
    have hN1 := DecisionLemma20_norm_nonneg (b true)
    have hN0 := DecisionLemma20_norm_nonneg (b false)
    have hsq : (σ true)^4+(normSq (b true))^2 + ((σ false)^4+(normSq (b false))^2) ≤ T^2 := by
      have Ht := mul_nonneg (hterm true) (hterm false)
      have Ht1 := mul_nonneg hN1 (sq_nonneg (σ true))
      have Ht0 := mul_nonneg hN0 (sq_nonneg (σ false))
      dsimp only [T] at *
      nlinarith only [Ht, Ht1, Ht0]
    have HH := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8*n*M by positivity)
    nlinarith only [H, H1, H0, HH]
  have hTsq : T^2 ≤ (popVar u)^2/(r*c)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (mul_pos hr hc))).mpr
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ r*c*T) hscale 2
    nlinarith only [H]
  change 0 < popVar u ∧ _
  refine ⟨hV, ?_⟩
  calc
    _ ≤ 8*n*M*T^2 := hu4
    _ ≤ 8*n*M*((popVar u)^2/(r*c)^2) :=
      mul_le_mul_of_nonneg_left hTsq (by positivity)
    _ = _ := by dsimp only [M]; ring

lemma DecisionLemma20_ae_pooled_regular {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k)
    (Z : ∀ j, Ω → Finset (Fin (sizes j))) (δ e A B r : ℝ)
    (he : 0 < e) (hA : 0 < A) (hB : 0 < B) (hr : 0 < r)
    (hP : ∀ j, Xi (P j) δ e A B r)
    (hv : ∀ j a, 0 < popVar (residual (P j) a (late (P j).pop)))
    (hZ : RandomizationSequence (fun j => (P j).pop) μ Z) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop,
      let q := observedW (P j).pop (late (P j).pop) (Z j ω)
      let u := fun i => q i - dotProduct (augmented (P j).x i) (ols (P j).x Finset.univ q)
      0 < popVar u ∧ (∑ i, u i ^ 4) ≤
        (8*max (B^4) (((k : ℝ)+1)^2*max 1 A)/(r*(min 1 e/8))^2) * sizes j * (popVar u)^2 := by
  filter_upwards [DecisionLemma20_ae_residual_gram μ sizes hsizes k P Z δ e A B r
    he hA hB hr hP hv hZ, DecisionLemma12_ae_assignment (fun j => (P j).pop) μ Z hZ]
    with ω hω hS
  filter_upwards [hω] with j hj
  exact DecisionLemma20_pooled_kurtosis (P j) δ e A B r (min 1 e/8) he hB hr
    (by positivity) (hP j) (hv j) (Z j ω) (hS j) hj

lemma DecisionLemma20_maximal_term {n} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (hv : 0 < popVar q) (D r : ℝ) (hD : 0 ≤ D) (hr : 0 < r)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (hq : ∑ i, (q i-mean q)^4 ≤ D*n*(popVar q)^2) :
    maximum (fun i => (q i-mean q)^2) /
      (((min P.n1 (n-P.n1) : ℕ) : ℝ)*popVar q) ≤ Real.sqrt (D/(r^2*n)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1; omega)
  have hm : r*n ≤ ((min P.n1 (n-P.n1) : ℕ) : ℝ) := by
    rw [Nat.cast_min, Nat.cast_sub hP.2.2.le]
    exact le_min hl (by linarith)
  have hmpos : 0 < ((min P.n1 (n-P.n1) : ℕ) : ℝ) := (mul_pos hr hn).trans_le hm
  have hcoord (i : Fin n) :
      (q i-mean q)^2 / (((min P.n1 (n-P.n1) : ℕ) : ℝ)*popVar q) ≤ Real.sqrt (D/(r^2*n)) := by
    have hi : (q i-mean q)^4 ≤ D*n*(popVar q)^2 := by
      exact (Finset.single_le_sum (f := fun j => (q j-mean q)^4)
        (fun j _ => by positivity) (Finset.mem_univ i)).trans hq
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hmpos hv))).mpr
    have hden : (r*n)^2 ≤ (((min P.n1 (n-P.n1) : ℕ) : ℝ))^2 :=
      pow_le_pow_left₀ (by positivity) hm 2
    have H := mul_le_mul_of_nonneg_left hden (div_nonneg hD (show 0 ≤ r^2*n by positivity))
    have H' := mul_le_mul_of_nonneg_right H (sq_nonneg (popVar q))
    have hid : D/(r^2*n)*(r*n)^2 = D*n := by field_simp <;> ring
    rw [hid] at H'
    nlinarith only [hi, H']
  apply (div_le_iff₀ (mul_pos hmpos hv)).mpr
  apply maximum_le _ _ (by positivity)
  intro i
  exact (div_le_iff₀ (mul_pos hmpos hv)).mp (hcoord i)

lemma DecisionLemma20_probability_mono {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S → F S) :
    probability P E ≤ probability P F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (assignments P).filter E ⊆ (assignments P).filter F from
    fun S hS => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1,
      h S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2⟩)

lemma DecisionLemma20_probability_tail {n} (P : Population n) (hP : ValidDesign P)
    (X : Finset (Fin n) → ℝ) (x : ℝ) (hx : 0 < x) :
    probability P (fun S => x ≤ |X S|) =
      probability P (fun S => X S ≤ -x) + 1 - probability P (fun S => X S < x) := by
  calc
    _ = expectation P (fun S => if x ≤ |X S| then 1 else 0) :=
      DecisionLemma12_probability_eq_expectation _ _
    _ = expectation P (fun S => (if X S ≤ -x then 1 else 0) + 1 -
        (if X S < x then 1 else 0)) := by
      apply DecisionLemma12_expectation_congr
      intro S _
      by_cases h : X S < x
      · by_cases h' : X S ≤ -x
        · have ht : x ≤ |X S| := (show x ≤ -(X S) by linarith).trans (neg_le_abs _)
          simp only [h, h', ht, ite_true]; norm_num
        · have ht : ¬x ≤ |X S| := not_le.mpr (abs_lt.mpr ⟨by linarith, h⟩)
          simp only [h, h', ht, ite_true, ite_false]; norm_num
      · have ht : x ≤ |X S| := (le_of_not_gt h).trans (le_abs_self _)
        have h' : ¬ X S ≤ -x := by linarith
        simp only [h, h', ht, ite_true, ite_false]; norm_num
    _ = _ := by
      rw [expectation_sub, DecisionLemma12_expectation_add, expectation_const P hP]
      rw [← DecisionLemma12_probability_eq_expectation, ← DecisionLemma12_probability_eq_expectation]

local instance instNullSingletonDecisionLemma20 : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma DecisionLemma20_normal_cdf_continuous (t : ℝ) :
    ContinuousAt (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) t := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  have hmono : Monotone (ProbabilityTheory.cdf μ) := ProbabilityTheory.monotone_cdf μ
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hright : Function.rightLim (ProbabilityTheory.cdf μ) t = ProbabilityTheory.cdf μ t :=
    (hmono.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((ProbabilityTheory.cdf μ).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hle : Function.leftLim (ProbabilityTheory.cdf μ) t ≤ ProbabilityTheory.cdf μ t := hmono.leftLim_le le_rfl
  have hge : ProbabilityTheory.cdf μ t ≤ Function.leftLim (ProbabilityTheory.cdf μ) t := by
    have h0 := (ProbabilityTheory.cdf μ).measure_singleton t
    rw [ProbabilityTheory.measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hle hge, hright]

lemma DecisionLemma20_normalTail_cdf (x : ℝ) (hx : 0 < x) :
    normalTail x = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-x) + 1 -
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  have heq : {z : ℝ | x ≤ |z|} = Set.Iic (-x) ∪ Set.Ici x := by
    ext z
    constructor
    · intro h
      by_cases hz : z ≤ -x
      · exact Or.inl hz
      · right
        by_contra h'
        have H : |z| < x := abs_lt.mpr ⟨by linarith, by exact lt_of_not_ge h'⟩
        exact (not_le.mpr H) h
    · rintro (h | h)
      · change z ≤ -x at h
        exact (show x ≤ -z by linarith).trans (neg_le_abs _)
      · change x ≤ z at h
        exact h.trans (le_abs_self _)
  have hdisj : Disjoint (Set.Iic (-x)) (Set.Ici x) :=
    Set.disjoint_left.mpr (fun z hz hz' => by
      change z ≤ -x at hz
      change x ≤ z at hz'
      linarith)
  have hatom : μ (Set.Ioi x) = μ (Set.Ici x) := measure_congr (Ioi_ae_eq_Ici' (measure_singleton x))
  have hc := measureReal_add_measureReal_compl (μ := μ) (s := Set.Iic x) measurableSet_Iic
  simp only [Set.compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one, hatom] at hc
  rw [normalTail, heq, measure_union hdisj measurableSet_Ici,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, measureReal_def, measureReal_def]
  change (μ (Set.Iic (-x))).toReal + (μ (Set.Ici x)).toReal = _
  linarith

lemma DecisionLemma20_strict_cdf_limit (sizes : ℕ → ℕ)
    (P : ∀ j, Population (sizes j)) (X : ∀ j, Finset (Fin (sizes j)) → ℝ)
    (F : ℝ → ℝ) (t : ℝ) (hF : ContinuousAt F t)
    (h : ∀ s, Tendsto (fun j => probability (P j) (fun S => X j S ≤ s)) atTop (nhds (F s))) :
    Tendsto (fun j => probability (P j) (fun S => X j S < t)) atTop (nhds (F t)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp
      (hF.eventually (eventually_gt_nhds ha))
    have hclose : dist (t-ε/2) t < ε := by
      rw [Real.dist_eq, show t-ε/2-t = -ε/2 by ring, abs_div]
      rw [abs_neg, abs_of_pos hε]
      norm_num
      linarith
    have hsmall : a < F (t-ε/2) := hh hclose
    filter_upwards [(h (t-ε/2)).eventually (eventually_gt_nhds hsmall)] with j hj
    exact hj.trans_le (DecisionLemma20_probability_mono (P j) (fun S _ hS => by
      change X j S ≤ t-ε/2 at hS
      change X j S < t
      linarith))
  · intro a ha
    filter_upwards [(h t).eventually (eventually_lt_nhds ha)] with j hj
    exact (DecisionLemma20_probability_mono (P j) (fun S _ hS => hS.le)).trans_lt hj

lemma DecisionLemma20_tail_of_cdf (sizes : ℕ → ℕ)
    (P : ∀ j, Population (sizes j)) (hP : ∀ j, ValidDesign (P j))
    (X : ∀ j, Finset (Fin (sizes j)) → ℝ)
    (h : ∀ s, Tendsto (fun j => probability (P j) (fun S => X j S ≤ s)) atTop
      (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic s)).toReal)))
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun j => |probability (P j) (fun S => x ≤ |X j S|) - normalTail x|) atTop (nhds 0) := by
  have h' : ∀ s, Tendsto (fun j => probability (P j) (fun S => X j S ≤ s)) atTop
      (nhds (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) s)) := by
    intro s
    simpa only [ProbabilityTheory.cdf_eq_real, measureReal_def] using h s
  have hs := DecisionLemma20_strict_cdf_limit sizes P X _ x (DecisionLemma20_normal_cdf_continuous x) h'
  have H := ((h' (-x)).add_const 1).sub hs
  simp only [← DecisionLemma20_normalTail_cdf x hx] at H
  have heq (j) := DecisionLemma20_probability_tail (P j) (hP j) (X j) x hx
  simp only [← heq] at H
  simpa only [sub_self, abs_zero] using (H.sub_const (normalTail x)).abs

lemma DecisionLemma20_probability_congr {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S ↔ F S) :
    probability P E = probability P F := by
  exact le_antisymm (DecisionLemma20_probability_mono P (fun S hS => (h S hS).mp))
    (DecisionLemma20_probability_mono P (fun S hS => (h S hS).mpr))

lemma DecisionLemma20_oracle_decomposition {n k} (P : CovPopulation n k)
    (hP : ValidDesign P.pop) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    oracleStar P q S =
      groupMean S (fun i => q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q)) -
      groupMean Sᶜ (fun i => q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q)) := by
  let b := ols P.x Finset.univ q
  have hs : S.card = P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
  have hsn : S.Nonempty := Finset.card_pos.mp (by rw [hs]; exact hP.2.1)
  have hcn : Sᶜ.Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_compl, Fintype.card_fin, hs]; exact Nat.sub_pos_of_lt hP.2.2)
  have hi (i : Fin n) : q i-slopeDot (P.x i) b =
      (q i-dotProduct (augmented P.x i) b)+b none := by
    simp only [slopeDot, dotProduct, Fintype.sum_option, augmented, one_mul]
    ring
  change groupMean S (fun i => q i-slopeDot (P.x i) b) -
    groupMean Sᶜ (fun i => q i-slopeDot (P.x i) b) = _
  simp_rw [hi]
  rw [groupMean_add_const _ _ _ hsn, groupMean_add_const _ _ _ hcn]
  ring

lemma DecisionLemma20_oracle_standardized {n k} (P : CovPopulation n k)
    (hP : ValidDesign P.pop) (q : Fin n → ℝ)
    (hx : ∀ s, ∑ i, P.x i s = 0) (hg : (gram P.x Finset.univ).det ≠ 0)
    (hv : 0 < popVar (fun i => q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q)))
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    let u := fun i => q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q)
    oracleStar P q S / Real.sqrt (designVariance P.pop (oracleStar P q)) =
      (groupMean S u - mean u) /
        Real.sqrt ((1/(P.pop.n1 : ℝ)-1/(n : ℝ))*popVar u) := by
  let u := fun i => q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1; omega)
  have hm : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hP.2.1
  have hmN : (P.pop.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hc : 0 < controlSize P.pop := sub_pos.mpr hmN
  have hL : 0 < (1/(P.pop.n1 : ℝ)-1/(n : ℝ))*popVar u :=
    mul_pos (sub_pos.mpr ((one_div_lt_one_div hn hm).mpr hmN)) hv
  have hV := (oracle_variances_proof P hP 0 q hx hg).2
  change designVariance P.pop (oracleStar P q) = popVar u * (1/(P.pop.n1 : ℝ)+1/controlSize P.pop) at hV
  have hVpos : 0 < designVariance P.pop (oracleStar P q) := by rw [hV]; positivity
  have hscale : Real.sqrt (designVariance P.pop (oracleStar P q)) =
      ((n : ℝ)/controlSize P.pop) * Real.sqrt ((1/(P.pop.n1 : ℝ)-1/(n : ℝ))*popVar u) := by
    have hsq : (Real.sqrt (designVariance P.pop (oracleStar P q)))^2 =
        (((n : ℝ)/controlSize P.pop)*Real.sqrt ((1/(P.pop.n1 : ℝ)-1/(n : ℝ))*popVar u))^2 := by
      rw [mul_pow, Real.sq_sqrt hVpos.le, Real.sq_sqrt hL.le, hV]
      dsimp only [controlSize] at *
      field_simp
      <;> ring
    nlinarith [Real.sqrt_nonneg (designVariance P.pop (oracleStar P q)),
      mul_pos (div_pos hn hc) (Real.sqrt_pos.mpr hL)]
  have hstat : oracleStar P q S = ((n : ℝ)/controlSize P.pop)*(groupMean S u-mean u) := by
    rw [DecisionLemma20_oracle_decomposition P hP q S hS]
    have hs : S.card = P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
    have hcs : (Sᶜ.card : ℝ) = controlSize P.pop := by
      rw [Finset.card_compl, Fintype.card_fin, hs, Nat.cast_sub hP.2.2.le]
      rfl
    have ht := Finset.sum_add_sum_compl S u
    change groupMean S u - groupMean Sᶜ u = _
    unfold groupMean mean
    rw [hs, hcs]
    have hcne := hc.ne'
    dsimp only [controlSize] at *
    field_simp
    nlinarith only [ht]
  dsimp only
  rw [hstat, hscale, mul_div_mul_left _ _ (div_pos hn hc).ne']

lemma DecisionLemma20_oracle_CLT (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k)
    (q : ∀ j, Fin (sizes j) → ℝ) (δ e A B r D : ℝ)
    (he : 0 < e) (hr : 0 < r) (hD : 0 ≤ D) (hP : ∀ j, Xi (P j) δ e A B r)
    (hv : ∀ j, 0 < popVar (fun i => q j i-dotProduct (augmented (P j).x i)
      (ols (P j).x Finset.univ (q j))))
    (hq : ∀ j, ∑ i, (q j i-dotProduct (augmented (P j).x i)
      (ols (P j).x Finset.univ (q j)))^4 ≤ D*sizes j*
        (popVar (fun i => q j i-dotProduct (augmented (P j).x i)
          (ols (P j).x Finset.univ (q j))))^2) :
    ∀ x : ℝ, 0 < x → Tendsto (fun j =>
      |probability (P j).pop (fun S => |oracleStar (P j) (q j) S| ≥
        x*Real.sqrt (designVariance (P j).pop (oracleStar (P j) (q j)))) - normalTail x|)
      atTop (nhds 0) := by
  let u := fun j i => q j i-dotProduct (augmented (P j).x i) (ols (P j).x Finset.univ (q j))
  have hg (j) := DecisionLemma20_population_fullrank (P j) δ e A B r he (hP j)
  have hum (j) : mean (u j) = 0 := DecisionLemma20_pooled_mean (P j).x (q j) (hg j)
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hbound : Tendsto (fun j => Real.sqrt (D/(r^2*sizes j))) atTop (nhds 0) := by
    have H : Tendsto (fun j => D/(r^2*sizes j)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (hN.const_mul_atTop (sq_pos_of_pos hr))
    simpa only [Real.sqrt_zero] using H.sqrt
  have hmax : Tendsto (fun j => maximum (fun i => (u j i-mean (u j))^2) /
      (((min (P j).pop.n1 (sizes j-(P j).pop.n1) : ℕ) : ℝ)*popVar (u j))) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun j => by
      apply div_nonneg _ (mul_nonneg (Nat.cast_nonneg _) (hv j).le)
      unfold maximum
      exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)))
      (Filter.Eventually.of_forall (fun j => ?_)) hbound
    apply DecisionLemma20_maximal_term (P j).pop (hP j).1 (u j) (hv j) D r hD hr
      (hP j).2.2.2.1 (hP j).2.2.2.2.1
    simpa only [hum, sub_zero] using hq j
  have hclt := finitePopulationCLT sizes hsizes (fun j => (P j).pop) u
    (fun j => (hP j).1) hv hmax
  have hCDF : ∀ t : ℝ, Tendsto (fun j => probability (P j).pop (fun S =>
      oracleStar (P j) (q j) S / Real.sqrt (designVariance (P j).pop (oracleStar (P j) (q j))) ≤ t))
      atTop (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic t)).toReal)) := by
    intro t
    apply (hclt t).congr
    intro j
    apply DecisionLemma20_probability_congr
    intro S hS
    rw [DecisionLemma20_oracle_standardized (P j) (hP j).1 (q j)
      (hP j).2.2.2.2.2.2.2.1 (hg j) (hv j) S hS]
  intro x hx
  have H := DecisionLemma20_tail_of_cdf sizes (fun j => (P j).pop) (fun j => (hP j).1)
    _ hCDF x hx
  convert H using 1
  funext j
  congr 2
  apply DecisionLemma20_probability_congr
  intro S _
  have hV := (oracle_variances_proof (P j) (hP j).1 0 (q j)
    (hP j).2.2.2.2.2.2.2.1 (hg j)).2
  have hpos : 0 < designVariance (P j).pop (oracleStar (P j) (q j)) := by
    rw [hV]
    apply mul_pos (hv j)
    have hm : (0 : ℝ) < (P j).pop.n1 := by exact_mod_cast (hP j).1.2.1
    have hc : 0 < controlSize (P j).pop := sub_pos.mpr (by exact_mod_cast (hP j).1.2.2)
    positivity
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hpos), le_div_iff₀ (Real.sqrt_pos.mpr hpos)]

lemma DecisionLemma20_expectation_sum {n} {ι : Type*} [Fintype ι]
    (P : Population n) (f : ι → Finset (Fin n) → ℝ) :
    expectation P (fun S => ∑ s, f s S) = ∑ s, expectation P (f s) := by
  simp only [expectation, ← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

lemma DecisionLemma20_popVar_bound {n} (hn : 2 ≤ n) (f : Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : mean (fun i => f i ^ 2) ≤ C) : popVar f ≤ 2*C := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [popVar, DecisionLemma12_sum_centered_sq (by omega)]
  apply (div_le_iff₀ (by linarith : 0 < (n : ℝ)-1)).mpr
  have H := (div_le_iff₀ hn0).mp hf
  nlinarith [mul_nonneg hn0.le (sq_nonneg (mean f)),
    mul_nonneg hC (show 0 ≤ (n : ℝ)-2 by linarith)]

lemma DecisionLemma20_arm_mse {n} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hk : 2 ≤ n-P.n1) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (f : Fin n → ℝ) (hf : mean (fun i => f i ^ 2) ≤ C) (a : Bool) :
    expectation P (fun S => (groupMean (if a then S else Sᶜ) f-mean f)^2) ≤ 2*C/(r*n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1; omega)
  have hs : r*n ≤ (if a then (P.n1 : ℝ) else controlSize P) := by
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, controlSize] <;> linarith
  have hsp : 0 < (if a then (P.n1 : ℝ) else controlSize P) := (mul_pos hr hn).trans_le hs
  calc
    _ ≤ popVar f/(if a then (P.n1 : ℝ) else controlSize P) :=
      DecisionLemma12_mse_arm P hP hm hk f a
    _ ≤ 2*C/(if a then (P.n1 : ℝ) else controlSize P) :=
      div_le_div_of_nonneg_right (DecisionLemma20_popVar_bound hP.1 f C hC hf) hsp.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hr hn) hs

lemma DecisionLemma20_arm_abs {n} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hk : 2 ≤ n-P.n1) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (f : Fin n → ℝ) (hf : mean (fun i => f i ^ 2) ≤ C) (a : Bool) :
    expectation P (fun S => |groupMean (if a then S else Sᶜ) f-mean f|) ≤
      Real.sqrt (2*C/(r*n)) := by
  exact (DecisionLemma12_Eabs P hP _).trans (Real.sqrt_le_sqrt
    (DecisionLemma20_arm_mse P hP hm hk r C hr hC hl hu f hf a))

lemma DecisionLemma20_split_bound {n} (P : Population n) (hP : ValidDesign P)
    (E : Finset (Fin n) → Prop) (g H : Finset (Fin n) → ℝ)
    (t κ : ℝ) (ht : 0 < t) (hκ : 0 < κ)
    (hg : ∀ S ∈ assignments P, 0 ≤ g S) (hH : ∀ S ∈ assignments P, 0 ≤ H S)
    (h : ∀ S ∈ assignments P, E S → g S < t → κ ≤ H S) :
    probability P E ≤ expectation P g/t + expectation P H/κ := by
  have HI (S) (hS : S ∈ assignments P) : (if E S then (1 : ℝ) else 0) ≤ g S/t+H S/κ := by
    by_cases hE : E S
    · simp only [hE, ite_true]
      by_cases hbad : t ≤ g S
      · have Ht : 1 ≤ g S/t := (le_div_iff₀ ht).mpr (by simpa using hbad)
        linarith [div_nonneg (hH S hS) hκ.le]
      · have Hκ : 1 ≤ H S/κ := (le_div_iff₀ hκ).mpr (by simpa using h S hS hE (lt_of_not_ge hbad))
        linarith [div_nonneg (hg S hS) ht.le]
    · simp only [hE, ite_false]
      exact add_nonneg (div_nonneg (hg S hS) ht.le) (div_nonneg (hH S hS) hκ.le)
  rw [DecisionLemma12_probability_eq_expectation]
  have HH := DecisionLemma12_expectation_mono P HI
  simpa only [DecisionLemma12_expectation_add, expectation_div] using HH

def DecisionLemma20_gram_error {n k} (P : CovPopulation n k) (S : Finset (Fin n)) : ℝ :=
  ∑ a : Bool, ∑ s : Option (Fin k), ∑ t : Option (Fin k),
    |gram P.x (if a then S else Sᶜ) s t-gram P.x Finset.univ s t|

lemma DecisionLemma20_gram_error_nonneg {n k} (P : CovPopulation n k) (S : Finset (Fin n)) :
    0 ≤ DecisionLemma20_gram_error P S := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma DecisionLemma20_good_gram {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (S : Finset (Fin n))
    (hgood : DecisionLemma20_gram_error P S < min 1 e/(2*((k : ℝ)+1))) :
    ∀ (a : Bool) (b : Option (Fin k) → ℝ),
      (min 1 e/2)*normSq b ≤ dotProduct b (gram P.x (if a then S else Sᶜ) *ᵥ b) := by
  intro a b
  have hentry (s t) : |gram P.x (if a then S else Sᶜ) s t-gram P.x Finset.univ s t| ≤
      DecisionLemma20_gram_error P S := by
    let entry := fun (b : Bool) s t => |gram P.x (if b then S else Sᶜ) s t-gram P.x Finset.univ s t|
    change entry a s t ≤ ∑ b : Bool, ∑ p, ∑ q, entry b p q
    apply (Finset.single_le_sum (f := entry a s) (fun v _ => abs_nonneg _) (Finset.mem_univ t)).trans
    apply (Finset.single_le_sum (f := fun p => ∑ q, entry a p q)
      (fun v _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)).trans
    exact Finset.single_le_sum (f := fun b => ∑ p, ∑ q, entry b p q)
      (fun v _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)
  have H := E61Eigenvalue.n11_proof k (gram P.x (if a then S else Sᶜ))
    (gram P.x Finset.univ) (DecisionLemma20_gram_error P S) hentry b
  have hn : 0 < n := by have := hP.1.1; omega
  have Hpop := (corrected_augmented_gram P.x hn e hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2).2.2.2 b
  have hpop : min 1 e*normSq b ≤ dotProduct b (gram P.x Finset.univ *ᵥ b) := by
    rw [gram_quadratic]
    simpa only [groupMean, mean, Finset.card_univ, Fintype.card_fin] using Hpop
  have hsmall := (lt_div_iff₀ (show 0 < 2*((k : ℝ)+1) by positivity)).mp hgood
  have hc : min 1 e/2 ≤ min 1 e - ((k : ℝ)+1)*DecisionLemma20_gram_error P S := by linarith
  have Hn := mul_le_mul_of_nonneg_right hc (DecisionLemma20_norm_nonneg b)
  have H' := (abs_le.mp H).1
  linarith

lemma DecisionLemma20_inverse_control {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (c : ℝ) (hc : 0 < c)
    (hG : ∀ b, c*normSq b ≤ dotProduct b (gram x S *ᵥ b)) (h : Option (Fin k) → ℝ) :
    let v := (gram x S)⁻¹ *ᵥ h
    0 ≤ dotProduct h v ∧ dotProduct h v ≤ normSq h/c ∧
      ∀ m, |dotProduct m v| ≤ (normSq m+normSq h)/(2*c) := by
  let v := (gram x S)⁻¹ *ᵥ h
  have hg := DecisionLemma20_fullrank x S c hc hG
  have hGv : gram x S *ᵥ v = h := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]
  have hco : c*normSq v ≤ dotProduct h v := by simpa only [hGv, dotProduct_comm] using hG v
  have hN := DecisionLemma20_norm_nonneg v
  have hH := DecisionLemma20_norm_nonneg h
  have hQ : 0 ≤ dotProduct h v := (mul_nonneg hc.le hN).trans hco
  have hCS : (dotProduct h v)^2 ≤ normSq v*normSq h := by
    simpa only [normSq, dotProduct, mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ h v)
  have hNv : c^2*normSq v ≤ normSq h := by
    by_cases hzero : normSq v = 0
    · simpa only [hzero, mul_zero] using hH
    · have hpos : 0 < normSq v := lt_of_le_of_ne hN (Ne.symm hzero)
      have H := pow_le_pow_left₀ (mul_nonneg hc.le hN) hco 2
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith only [H, hCS]
  have hQbound : dotProduct h v ≤ normSq h/c := by
    apply (le_div_iff₀ hc).mpr
    by_cases hz : dotProduct h v = 0
    · simpa only [hz, zero_mul] using hH
    · have hp : 0 < dotProduct h v := lt_of_le_of_ne hQ (Ne.symm hz)
      have H1 := mul_le_mul_of_nonneg_left hCS hc.le
      have H2 := mul_le_mul_of_nonneg_right hco hH
      apply (mul_le_mul_iff_right₀ hp).mp
      nlinarith only [H1, H2]
  refine ⟨hQ, hQbound, ?_⟩
  intro m
  have hM := DecisionLemma20_norm_nonneg m
  have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ m v
  change (dotProduct m v)^2 ≤ normSq m*normSq v at H
  have H1 := mul_le_mul_of_nonneg_left H (sq_nonneg c)
  have H2 := mul_le_mul_of_nonneg_left hNv hM
  have hs : (2*c*|dotProduct m v|)^2 ≤ (normSq m+normSq h)^2 := by
    nlinarith only [H1, H2, sq_abs (dotProduct m v), sq_nonneg (normSq m-normSq h)]
  have hl := (sq_le_sq₀ (show 0 ≤ 2*c*|dotProduct m v| by positivity) (add_nonneg hM hH)).mp hs
  exact (le_div_iff₀ (show 0 < 2*c by positivity)).mpr (by nlinarith only [hl])

lemma DecisionLemma20_expected_gram {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hr : 0 < r) (hP : Xi P δ e A B r) (hm : 2 ≤ P.pop.n1) (hk : 2 ≤ n-P.pop.n1) :
    expectation P.pop (DecisionLemma20_gram_error P) ≤
      2*((k : ℝ)+1)^2 * Real.sqrt (2*max 1 A/(r*n)) := by
  unfold DecisionLemma20_gram_error
  simp_rw [DecisionLemma20_expectation_sum]
  have hcoord (a : Bool) (s t : Option (Fin k)) :
      expectation P.pop (fun S => |gram P.x (if a then S else Sᶜ) s t-gram P.x Finset.univ s t|) ≤
        Real.sqrt (2*max 1 A/(r*n)) := by
    simpa only [gram, groupMean, mean, Finset.card_univ, Fintype.card_fin] using
      DecisionLemma20_arm_abs P.pop hP.1 hm hk r (max 1 A) hr (by positivity)
        hP.2.2.2.1 hP.2.2.2.2.1 (fun i => augmented P.x i s*augmented P.x i t)
        (E61Eigenvalue.n6_proof n k P δ e A B r hP s t) a
  calc
    _ ≤ ∑ a : Bool, ∑ s : Option (Fin k), ∑ t : Option (Fin k),
        Real.sqrt (2*max 1 A/(r*n)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_le_sum (fun t _ => hcoord a s t)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        Fintype.card_option, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; ring

lemma DecisionLemma20_expected_score {n k} (P : CovPopulation n k) (δ e A B r D : ℝ)
    (hr : 0 < r) (hD : 0 ≤ D) (hP : Xi P δ e A B r)
    (hm : 2 ≤ P.pop.n1) (hk : 2 ≤ n-P.pop.n1) (u : Fin n → ℝ)
    (hu : score P.x Finset.univ u = 0) (hu4 : mean (fun i => u i ^ 4) ≤ D) (a : Bool) :
    expectation P.pop (fun S => normSq (score P.x (if a then S else Sᶜ) u)) ≤
      ((k : ℝ)+1)*2*(max 1 A+D)/(r*n) := by
  have hcoord (s : Option (Fin k)) :
      expectation P.pop (fun S => score P.x (if a then S else Sᶜ) u s ^ 2) ≤
        2*(max 1 A+D)/(r*n) := by
    have hf : mean (fun i => (augmented P.x i s*u i)^2) ≤ max 1 A+D := by
      calc
        _ ≤ mean (fun i => augmented P.x i s ^ 4+u i ^ 4) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg ((augmented P.x i s)^2-u i ^ 2)])
        _ = mean (fun i => augmented P.x i s ^ 4)+mean (fun i => u i ^ 4) := by
          simp only [mean, Finset.sum_add_distrib, add_div]
        _ ≤ _ := add_le_add (DecisionLemma20_augmented_fourth P δ e A B r hP s) hu4
    have hz : mean (fun i => augmented P.x i s*u i) = 0 := by
      have H := congrFun hu s
      simpa only [score, groupMean, mean, Finset.card_univ, Fintype.card_fin, Pi.zero_apply] using H
    simpa only [score, hz, sub_zero] using DecisionLemma20_arm_mse P.pop hP.1 hm hk r
      (max 1 A+D) hr (by positivity) hP.2.2.2.1 hP.2.2.2.2.1 _ hf a
  unfold normSq
  rw [DecisionLemma20_expectation_sum]
  calc
    _ ≤ ∑ _s : Option (Fin k), 2*(max 1 A+D)/(r*n) := Finset.sum_le_sum (fun s _ => hcoord s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

def DecisionLemma20_meanX {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) : Option (Fin k) → ℝ :=
  fun s => groupMean S (fun i => xCirc x i s)

lemma DecisionLemma20_expected_meanX {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hr : 0 < r) (hP : Xi P δ e A B r)
    (hm : 2 ≤ P.pop.n1) (hk : 2 ≤ n-P.pop.n1) (a : Bool) :
    expectation P.pop (fun S => normSq (DecisionLemma20_meanX P.x (if a then S else Sᶜ))) ≤
      ((k : ℝ)+1)*2*(max 1 A+1)/(r*n) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := hP.1.1; omega)
  have hcoord (s : Option (Fin k)) :
      expectation P.pop (fun S => (DecisionLemma20_meanX P.x (if a then S else Sᶜ) s)^2) ≤
        2*(max 1 A+1)/(r*n) := by
    have hz : mean (fun i => xCirc P.x i s) = 0 := by
      cases s <;> simp only [xCirc, mean, Finset.sum_const_zero, zero_div, hP.2.2.2.2.2.2.2.1]
    have hf : mean (fun i => xCirc P.x i s ^ 2) ≤ max 1 A+1 := by
      cases s with
      | none => simp only [xCirc, zero_pow (by decide : (2 : ℕ) ≠ 0), mean, Finset.sum_const_zero, zero_div]; positivity
      | some s =>
        change mean (fun i => P.x i s ^ 2) ≤ _
        calc
          _ ≤ mean (fun i => P.x i s ^ 4+1) := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (P.x i s ^ 2-1)])
          _ = mean (fun i => P.x i s ^ 4)+1 := by simp [mean, Finset.sum_add_distrib, add_div, hn]
          _ ≤ _ := add_le_add ((hP.2.2.2.2.2.2.2.2.1 s).trans (le_max_right _ _)) (le_refl 1)
    simpa only [DecisionLemma20_meanX, hz, sub_zero] using DecisionLemma20_arm_mse P.pop hP.1
      hm hk r (max 1 A+1) hr (by positivity) hP.2.2.2.1 hP.2.2.2.2.1 _ hf a
  unfold normSq
  rw [DecisionLemma20_expectation_sum]
  calc
    _ ≤ ∑ _s : Option (Fin k), 2*(max 1 A+1)/(r*n) := Finset.sum_le_sum (fun s _ => hcoord s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

lemma DecisionLemma20_score_scale {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (u : Fin n → ℝ) (c : ℝ) :
    score x S (fun i => c*u i) = c • score x S u := by
  ext s
  simp only [score, groupMean, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (augmented x _ s) c, ← Finset.mul_sum]
  ring

lemma DecisionLemma20_ols_normalized {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (q u : Fin n → ℝ) (b : Option (Fin k) → ℝ) (σ : ℝ)
    (h : ∀ i, q i-dotProduct (augmented x i) b = σ*u i)
    (hg : (gram x S).det ≠ 0) :
    ols x S q-b = σ • ((gram x S)⁻¹ *ᵥ score x S u) := by
  rw [ols_error x S q b hg]
  simp_rw [h]
  rw [DecisionLemma20_score_scale, Matrix.mulVec_smul]

lemma DecisionLemma20_meanX_dot {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (b : Option (Fin k) → ℝ) :
    dotProduct (DecisionLemma20_meanX x S) b = groupMean S (fun i => slopeDot (x i) b) := by
  simp only [dotProduct, Fintype.sum_option, DecisionLemma20_meanX, xCirc, groupMean,
    Finset.sum_const_zero, zero_div, zero_mul, zero_add, slopeDot, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [div_mul_eq_mul_div]

lemma DecisionLemma20_adjusted_difference {n k} (P : CovPopulation n k) (q : Fin n → ℝ)
    (S : Finset (Fin n)) :
    adjustedTau P q S-oracleStar P q S =
      -dotProduct (DecisionLemma20_meanX P.x S) (fitted P q S true-ols P.x Finset.univ q) +
      dotProduct (DecisionLemma20_meanX P.x Sᶜ) (fitted P q S false-ols P.x Finset.univ q) := by
  rw [DecisionLemma20_meanX_dot, DecisionLemma20_meanX_dot]
  simp only [adjustedTau, oracleStar, adjustedWith, groupMean, slopeDot, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, sub_div]
  ring

lemma DecisionLemma20_normalized_pooled {n k} (x : Fin n → Fin k → ℝ)
    (q : Fin n → ℝ) (hn : 0 < n) (hg : (gram x Finset.univ).det ≠ 0) (D : ℝ)
    (hv : 0 < popVar (fun i => q i-dotProduct (augmented x i) (ols x Finset.univ q)))
    (hq : ∑ i, (q i-dotProduct (augmented x i) (ols x Finset.univ q))^4 ≤
      D*n*(popVar (fun i => q i-dotProduct (augmented x i) (ols x Finset.univ q)))^2) :
    let z := fun i => q i-dotProduct (augmented x i) (ols x Finset.univ q)
    let σ := Real.sqrt (popVar z)
    let u := fun i => z i/σ
    score x Finset.univ u = 0 ∧
      mean (fun i => u i ^ 2) = ((n : ℝ)-1)/n ∧ mean (fun i => u i ^ 4) ≤ D ∧
      ∀ i, z i = σ*u i := by
  let z := fun i => q i-dotProduct (augmented x i) (ols x Finset.univ q)
  let σ := Real.sqrt (popVar z)
  let u := fun i => z i/σ
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hz := DecisionLemma20_pooled_score x q hg
  have hm : mean z = 0 := DecisionLemma20_pooled_mean x q hg
  have hrepr (i) : z i = σ*u i := by dsimp only [u]; field_simp [hσ.ne']
  have hu : u = fun i => σ⁻¹*z i := by ext i; dsimp only [u]; ring
  have hσ4 : σ^4 = (popVar z)^2 := by
    calc
      _ = (σ^2)^2 := by ring
      _ = _ := by dsimp only [σ]; rw [Real.sq_sqrt hv.le]
  change score x Finset.univ u = 0 ∧ mean (fun i => u i ^ 2) = ((n : ℝ)-1)/n ∧
    mean (fun i => u i ^ 4) ≤ D ∧ ∀ i, z i = σ*u i
  refine ⟨?_, ?_, ?_, hrepr⟩
  · rw [hu, DecisionLemma20_score_scale]
    change σ⁻¹ • score x Finset.univ z = 0
    rw [hz, smul_zero]
  · have H := FPCLT_second z hv
    simp only [FPCLT_normalize, hm, sub_zero] at H
    change (∑ i, (z i/Real.sqrt (popVar z))^2)/(n : ℝ) = _
    rw [H]
  · change mean (fun i => (z i/σ)^4) ≤ D
    simp only [div_pow, hσ4]
    rw [DecisionLemma20_mean_div]
    apply (div_le_iff₀ (sq_pos_of_pos hv)).mpr
    apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
    nlinarith only [hq]

lemma DecisionLemma20_rss_normalized {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (hS : S.Nonempty) (q u : Fin n → ℝ)
    (b : Option (Fin k) → ℝ) (σ : ℝ) (h : ∀ i, q i-dotProduct (augmented x i) b = σ*u i)
    (hg : (gram x S).det ≠ 0) :
    rss x S q (ols x S q)/(S.card : ℝ) = σ^2 *
      (groupMean S (fun i => u i ^ 2) - dotProduct (score x S u) ((gram x S)⁻¹ *ᵥ score x S u)) := by
  have H := residual_sum_squares_identity x S q b hS hg
  simp_rw [h] at H
  rw [DecisionLemma20_score_scale, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul] at H
  simp only [smul_eq_mul] at H
  rw [H]
  simp only [groupMean, mul_pow, ← Finset.mul_sum]
  ring

lemma DecisionLemma20_good_statistic {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (q u : Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (h : ∀ i, q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q) = σ*u i)
    (S : Finset (Fin n))
    (hgood : DecisionLemma20_gram_error P S < min 1 e/(2*((k : ℝ)+1))) :
    |adjustedTau P q S-oracleStar P q S| ≤
      σ/(min 1 e) * ∑ a : Bool,
        (normSq (DecisionLemma20_meanX P.x (if a then S else Sᶜ))+
          normSq (score P.x (if a then S else Sᶜ) u)) := by
  have hG := DecisionLemma20_good_gram P δ e A B r he hP S hgood
  have hc : 0 < min (1 : ℝ) e/2 := by positivity
  have harm (a : Bool) : |dotProduct (DecisionLemma20_meanX P.x (if a then S else Sᶜ))
      (fitted P q S a-ols P.x Finset.univ q)| ≤ σ/(min 1 e) *
        (normSq (DecisionLemma20_meanX P.x (if a then S else Sᶜ))+
          normSq (score P.x (if a then S else Sᶜ) u)) := by
    have hg := DecisionLemma20_fullrank P.x (if a then S else Sᶜ) (min 1 e/2) hc (hG a)
    have H := (DecisionLemma20_inverse_control P.x (if a then S else Sᶜ) (min 1 e/2) hc
      (hG a) (score P.x (if a then S else Sᶜ) u)).2.2
      (DecisionLemma20_meanX P.x (if a then S else Sᶜ))
    have hb := DecisionLemma20_ols_normalized P.x (if a then S else Sᶜ) q u
      (ols P.x Finset.univ q) σ h hg
    change |dotProduct _ (ols P.x (if a then S else Sᶜ) q-_)| ≤ _
    rw [hb, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos hσ]
    have HH := mul_le_mul_of_nonneg_left H hσ.le
    convert HH using 1 <;> ring
  rw [DecisionLemma20_adjusted_difference]
  calc
    _ ≤ |dotProduct (DecisionLemma20_meanX P.x S) (fitted P q S true-ols P.x Finset.univ q)| +
        |dotProduct (DecisionLemma20_meanX P.x Sᶜ) (fitted P q S false-ols P.x Finset.univ q)| := by
      simpa only [abs_neg] using abs_add_le
        (-dotProduct (DecisionLemma20_meanX P.x S) (fitted P q S true-ols P.x Finset.univ q))
        (dotProduct (DecisionLemma20_meanX P.x Sᶜ) (fitted P q S false-ols P.x Finset.univ q))
    _ ≤ _ := by
      have H1 := harm true
      have H0 := harm false
      simp only [Bool.false_eq_true, ↓reduceIte] at H1 H0
      simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      linarith

lemma DecisionLemma20_good_variance {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (q u : Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (h : ∀ i, q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q) = σ*u i)
    (hm : mean (fun i => u i ^ 2) = ((n : ℝ)-1)/n)
    (hV : designVariance P.pop (oracleStar P q) = σ^2*(1/(P.pop.n1 : ℝ)+1/controlSize P.pop))
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop)
    (hgood : DecisionLemma20_gram_error P S < min 1 e/(2*((k : ℝ)+1))) :
    |adjustedSigma2 P q S/designVariance P.pop (oracleStar P q)-1| ≤
      (∑ a : Bool, |groupMean (if a then S else Sᶜ) (fun i => u i ^ 2)-mean (fun i => u i ^ 2)|) +
      (2/min 1 e)*(∑ a : Bool, normSq (score P.x (if a then S else Sᶜ) u)) + 1/(n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1.1; omega)
  have hn1 : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hP.1.2.1
  have hn0 : 0 < controlSize P.pop := sub_pos.mpr (by exact_mod_cast hP.1.2.2)
  have hc : 0 < min (1 : ℝ) e/2 := by positivity
  have hG := DecisionLemma20_good_gram P δ e A B r he hP S hgood
  let Q := fun (a : Bool) => dotProduct (score P.x (if a then S else Sᶜ) u)
    ((gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ score P.x (if a then S else Sᶜ) u)
  have hQ (a : Bool) : 0 ≤ Q a ∧ Q a ≤ normSq (score P.x (if a then S else Sᶜ) u)/(min 1 e/2) :=
    ⟨(DecisionLemma20_inverse_control P.x (if a then S else Sᶜ) (min 1 e/2) hc (hG a)
      (score P.x (if a then S else Sᶜ) u)).1,
      (DecisionLemma20_inverse_control P.x (if a then S else Sᶜ) (min 1 e/2) hc (hG a)
      (score P.x (if a then S else Sᶜ) u)).2.1⟩
  have hs : S.card = P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
  have hcs : (Sᶜ.card : ℝ) = controlSize P.pop := by
    rw [Finset.card_compl, Fintype.card_fin, hs, Nat.cast_sub hP.1.2.2.le]
    rfl
  have hrss (a : Bool) : rss P.x (if a then S else Sᶜ) q (fitted P q S a) /
      ((if a then S else Sᶜ).card : ℝ) = σ^2 *
        (groupMean (if a then S else Sᶜ) (fun i => u i ^ 2)-Q a) := by
    apply DecisionLemma20_rss_normalized P.x _ _ q u _ σ h
      (DecisionLemma20_fullrank P.x _ _ hc (hG a))
    apply Finset.card_pos.mp
    have hmpos := hP.1.2.1
    have hmlt := hP.1.2.2
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, hs, Finset.card_compl, Fintype.card_fin] <;>
      omega
  have hratio : adjustedSigma2 P q S/designVariance P.pop (oracleStar P q)-1 =
      (1-fraction P.pop)*(groupMean S (fun i => u i ^ 2)-mean (fun i => u i ^ 2)-Q true) +
      fraction P.pop*(groupMean Sᶜ (fun i => u i ^ 2)-mean (fun i => u i ^ 2)-Q false)-1/(n : ℝ) := by
    have H1 := hrss true
    have H0 := hrss false
    simp only [Bool.false_eq_true, ↓reduceIte, hs, hcs] at H1 H0
    rw [adjustedSigma2, hV, hm]
    have H1' := (div_eq_iff hn1.ne').mp H1
    have H0' := (div_eq_iff hn0.ne').mp H0
    simp only [fitted, Bool.false_eq_true, ↓reduceIte] at H1' H0' ⊢
    rw [H1', H0']
    dsimp only [fraction, controlSize] at *
    field_simp
    <;> ring
  rw [hratio]
  have hp : 0 ≤ fraction P.pop := by unfold fraction; positivity
  have hp1 : fraction P.pop ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hP.1.2.2.le)
  have H := DecisionLemma12_convex_error (fraction P.pop)
    (groupMean S (fun i => u i ^ 2)-mean (fun i => u i ^ 2))
    (groupMean Sᶜ (fun i => u i ^ 2)-mean (fun i => u i ^ 2)) (Q true) (Q false) (1/(n : ℝ))
    hp hp1 (hQ true).1 (hQ false).1 (by positivity)
  have HQ1 := (hQ true).2
  have HQ0 := (hQ false).2
  simp only [Bool.false_eq_true, ↓reduceIte] at HQ1 HQ0
  have HQ1' : Q true ≤ (2/min 1 e)*normSq (score P.x S u) := by
    convert HQ1 using 1 <;> ring
  have HQ0' : Q false ≤ (2/min 1 e)*normSq (score P.x Sᶜ u) := by
    convert HQ0 using 1 <;> ring
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  convert H.trans (show _ ≤ _ from ?_) using 1
  nlinarith only [HQ1', HQ0']

lemma DecisionLemma20_statistic_bound {n k} (P : CovPopulation n k) (δ e A B r D : ℝ)
    (he : 0 < e) (hr : 0 < r) (hD : 0 ≤ D) (hP : Xi P δ e A B r)
    (hm : 2 ≤ P.pop.n1) (hk : 2 ≤ n-P.pop.n1) (q u : Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (h : ∀ i, q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q) = σ*u i)
    (hu : score P.x Finset.univ u = 0) (hu4 : mean (fun i => u i ^ 4) ≤ D)
    (hV : designVariance P.pop (oracleStar P q) = σ^2*(1/(P.pop.n1 : ℝ)+1/controlSize P.pop))
    (κ : ℝ) (hκ : 0 < κ) :
    probability P.pop (fun S => |adjustedTau P q S-oracleStar P q S| ≥
      κ*Real.sqrt (designVariance P.pop (oracleStar P q))) ≤
      (2*((k : ℝ)+1)^2 * Real.sqrt (2*max 1 A/(r*n))) / (min 1 e/(2*((k : ℝ)+1))) +
      (Real.sqrt n/min 1 e * (4*((k : ℝ)+1)*(2*max 1 A+D+1)/(r*n)))/κ := by
  let H := fun S : Finset (Fin n) => ∑ a : Bool,
    (normSq (DecisionLemma20_meanX P.x (if a then S else Sᶜ)) + normSq (score P.x (if a then S else Sᶜ) u))
  have hmin : 0 < min (1 : ℝ) e := lt_min zero_lt_one he
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1.1; omega)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hn1 : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hP.1.2.1
  have hn0 : 0 < controlSize P.pop := sub_pos.mpr (by exact_mod_cast hP.1.2.2)
  have hn1le : (P.pop.n1 : ℝ) ≤ n := by exact_mod_cast hP.1.2.2.le
  have hscale : σ/Real.sqrt n ≤ Real.sqrt (designVariance P.pop (oracleStar P q)) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hn.le, hV]
    have hL : 1/(n : ℝ) ≤ 1/(P.pop.n1 : ℝ)+1/controlSize P.pop := by
      exact (one_div_le_one_div_of_le hn1 hn1le).trans (le_add_of_nonneg_right (by positivity))
    have H := mul_le_mul_of_nonneg_left hL (sq_nonneg σ)
    simpa only [mul_one_div] using H
  have Hnonneg (S) : 0 ≤ H S := Finset.sum_nonneg (fun _ _ =>
    add_nonneg (DecisionLemma20_norm_nonneg _) (DecisionLemma20_norm_nonneg _))
  have hprob := DecisionLemma20_split_bound P.pop hP.1
    (fun S => |adjustedTau P q S-oracleStar P q S| ≥ κ*Real.sqrt (designVariance P.pop (oracleStar P q)))
    (DecisionLemma20_gram_error P)
    (fun S => Real.sqrt n/min 1 e * H S) (min 1 e/(2*((k : ℝ)+1))) κ (by positivity) hκ
    (fun S _ => DecisionLemma20_gram_error_nonneg P S) (fun S _ =>
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hmin.le) (Hnonneg S))
    (fun S hS hE hgood => by
      have Hstat := DecisionLemma20_good_statistic P δ e A B r he hP q u σ hσ h S hgood
      have HC : σ*(κ/Real.sqrt n) ≤ σ*(H S/min 1 e) := by
        calc
          _ = κ*(σ/Real.sqrt n) := by ring
          _ ≤ κ*Real.sqrt (designVariance P.pop (oracleStar P q)) :=
            mul_le_mul_of_nonneg_left hscale hκ.le
          _ ≤ |adjustedTau P q S-oracleStar P q S| := hE
          _ ≤ σ/(min 1 e)*H S := Hstat
          _ = _ := by ring
      have HC' := (mul_le_mul_iff_right₀ hσ).mp HC
      have HD := (div_le_div_iff₀ hsqrt hmin).mp HC'
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hmin).mpr (by nlinarith only [HD]))
  have HE : expectation P.pop H ≤ 4*((k : ℝ)+1)*(2*max 1 A+D+1)/(r*n) := by
    unfold H
    simp_rw [DecisionLemma20_expectation_sum, DecisionLemma12_expectation_add]
    have H1 := DecisionLemma20_expected_meanX P δ e A B r hr hP hm hk true
    have H0 := DecisionLemma20_expected_meanX P δ e A B r hr hP hm hk false
    have HU1 := DecisionLemma20_expected_score P δ e A B r D hr hD hP hm hk u hu hu4 true
    have HU0 := DecisionLemma20_expected_score P δ e A B r D hr hD hP hm hk u hu hu4 false
    have HH := add_le_add (add_le_add H1 HU1) (add_le_add H0 HU0)
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] at HH ⊢
    convert HH using 1 <;> ring
  rw [expectation_mul] at hprob
  apply hprob.trans
  exact add_le_add
    (div_le_div_of_nonneg_right (DecisionLemma20_expected_gram P δ e A B r hr hP hm hk) (by positivity))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left HE (by positivity)) hκ.le)

lemma DecisionLemma20_variance_bound {n k} (P : CovPopulation n k) (δ e A B r D : ℝ)
    (he : 0 < e) (hr : 0 < r) (hD : 0 ≤ D) (hP : Xi P δ e A B r)
    (hm : 2 ≤ P.pop.n1) (hk : 2 ≤ n-P.pop.n1) (q u : Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (h : ∀ i, q i-dotProduct (augmented P.x i) (ols P.x Finset.univ q) = σ*u i)
    (hu : score P.x Finset.univ u = 0) (hu4 : mean (fun i => u i ^ 4) ≤ D)
    (hu2 : mean (fun i => u i ^ 2) = ((n : ℝ)-1)/n)
    (hV : designVariance P.pop (oracleStar P q) = σ^2*(1/(P.pop.n1 : ℝ)+1/controlSize P.pop))
    (κ : ℝ) (hκ : 0 < κ) :
    probability P.pop (fun S => |adjustedSigma2 P q S/designVariance P.pop (oracleStar P q)-1| ≥ κ) ≤
      (2*((k : ℝ)+1)^2 * Real.sqrt (2*max 1 A/(r*n))) / (min 1 e/(2*((k : ℝ)+1))) +
      (2*Real.sqrt (2*D/(r*n)) + (2/min 1 e)*(4*((k : ℝ)+1)*(max 1 A+D)/(r*n)) + 1/(n : ℝ))/κ := by
  let H := fun S : Finset (Fin n) =>
    (∑ a : Bool, |groupMean (if a then S else Sᶜ) (fun i => u i ^ 2)-mean (fun i => u i ^ 2)|) +
    (2/min 1 e)*(∑ a : Bool, normSq (score P.x (if a then S else Sᶜ) u)) + 1/(n : ℝ)
  have hmin : 0 < min (1 : ℝ) e := lt_min zero_lt_one he
  have Hnonneg (S) : 0 ≤ H S := by
    apply add_nonneg _ (by positivity)
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => DecisionLemma20_norm_nonneg _)))
  have hprob := DecisionLemma20_split_bound P.pop hP.1
    (fun S => |adjustedSigma2 P q S/designVariance P.pop (oracleStar P q)-1| ≥ κ)
    (DecisionLemma20_gram_error P) H
    (min 1 e/(2*((k : ℝ)+1))) κ (by positivity) hκ
    (fun S _ => DecisionLemma20_gram_error_nonneg P S) (fun S _ => Hnonneg S)
    (fun S hS hE hgood => hE.trans (DecisionLemma20_good_variance P δ e A B r he hP q u σ
      hσ h hu2 hV S hS hgood))
  have HE : expectation P.pop H ≤ 2*Real.sqrt (2*D/(r*n)) +
      (2/min 1 e)*(4*((k : ℝ)+1)*(max 1 A+D)/(r*n)) + 1/(n : ℝ) := by
    unfold H
    simp_rw [DecisionLemma12_expectation_add, expectation_mul, DecisionLemma20_expectation_sum]
    rw [expectation_const P.pop hP.1]
    have hU4 : mean (fun i => (u i ^ 2)^2) ≤ D := by simpa only [← pow_mul] using hu4
    have H1 := DecisionLemma20_arm_abs P.pop hP.1 hm hk r D hr hD
      hP.2.2.2.1 hP.2.2.2.2.1 _ hU4 true
    have H0 := DecisionLemma20_arm_abs P.pop hP.1 hm hk r D hr hD
      hP.2.2.2.1 hP.2.2.2.2.1 _ hU4 false
    have HU1 := DecisionLemma20_expected_score P δ e A B r D hr hD hP hm hk u hu hu4 true
    have HU0 := DecisionLemma20_expected_score P δ e A B r D hr hD hP hm hk u hu hu4 false
    have HH := mul_le_mul_of_nonneg_left (add_le_add HU0 HU1) (show 0 ≤ 2/min 1 e by positivity)
    have HH' := add_le_add (add_le_add (add_le_add H1 H0) HH) (le_refl (1/(n : ℝ)))
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] at HH' ⊢
    convert HH' using 1 <;> ring
  exact hprob.trans (add_le_add
    (div_le_div_of_nonneg_right (DecisionLemma20_expected_gram P δ e A B r hr hP hm hk) (by positivity))
    (div_le_div_of_nonneg_right HE hκ.le))

lemma DecisionLemma20_feasible_limits (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (q : ∀ j, Fin (sizes j) → ℝ)
    (δ e A B r D : ℝ) (he : 0 < e) (hr : 0 < r) (hD : 0 ≤ D)
    (hP : ∀ j, Xi (P j) δ e A B r)
    (hm : ∀ j, 2 ≤ (P j).pop.n1) (hk : ∀ j, 2 ≤ sizes j-(P j).pop.n1)
    (hv : ∀ j, 0 < popVar (fun i => q j i-dotProduct (augmented (P j).x i)
      (ols (P j).x Finset.univ (q j))))
    (hq : ∀ j, ∑ i, (q j i-dotProduct (augmented (P j).x i)
      (ols (P j).x Finset.univ (q j)))^4 ≤ D*sizes j*
        (popVar (fun i => q j i-dotProduct (augmented (P j).x i)
          (ols (P j).x Finset.univ (q j))))^2) :
    (∀ κ : ℝ, 0 < κ → Tendsto (fun j => probability (P j).pop (fun S =>
      |adjustedTau (P j) (q j) S-oracleStar (P j) (q j) S| ≥
        κ*Real.sqrt (designVariance (P j).pop (oracleStar (P j) (q j))))) atTop (nhds 0)) ∧
    (∀ κ : ℝ, 0 < κ → Tendsto (fun j => probability (P j).pop (fun S =>
      |adjustedSigma2 (P j) (q j) S/designVariance (P j).pop (oracleStar (P j) (q j))-1| ≥ κ))
      atTop (nhds 0)) := by
  let z := fun j i => q j i-dotProduct (augmented (P j).x i) (ols (P j).x Finset.univ (q j))
  let σ := fun j => Real.sqrt (popVar (z j))
  let u := fun j i => z j i/σ j
  have hmin : 0 < min (1 : ℝ) e := lt_min zero_lt_one he
  have hg (j) := DecisionLemma20_population_fullrank (P j) δ e A B r he (hP j)
  have hσ (j) : 0 < σ j := Real.sqrt_pos.mpr (hv j)
  have hnorm (j) := DecisionLemma20_normalized_pooled (P j).x (q j)
    (show 0 < sizes j by have := (hP j).1.1; omega) (hg j) D (hv j) (hq j)
  have hV (j) : designVariance (P j).pop (oracleStar (P j) (q j)) =
      (σ j)^2*(1/((P j).pop.n1 : ℝ)+1/controlSize (P j).pop) := by
    rw [(oracle_variances_proof (P j) (hP j).1 0 (q j) (hP j).2.2.2.2.2.2.2.1 (hg j)).2]
    dsimp only [σ]
    rw [Real.sq_sqrt (hv j).le]
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hinv : Tendsto (fun j => 1/(sizes j : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hroot (C : ℝ) : Tendsto (fun j => Real.sqrt (2*C/(r*sizes j))) atTop (nhds 0) := by
    have H := hinv.const_mul (2*C/r)
    have H' : Tendsto (fun j => 2*C/(r*sizes j)) atTop (nhds 0) := by
      convert H using 1 <;> first | (funext j; ring) | ring
    simpa only [Real.sqrt_zero] using H'.sqrt
  have hcommon : Tendsto (fun j => (2*((k : ℝ)+1)^2 * Real.sqrt (2*max 1 A/(r*sizes j))) /
      (min 1 e/(2*((k : ℝ)+1)))) atTop (nhds 0) := by
    simpa only [mul_zero, zero_div] using ((hroot (max 1 A)).const_mul (2*((k : ℝ)+1)^2)).div_const _
  have hsqrt : Tendsto (fun j => Real.sqrt (sizes j)/sizes j) atTop (nhds 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hN)
  constructor
  · intro κ hκ
    have Hsmall : Tendsto (fun j => (Real.sqrt (sizes j)/min 1 e *
        (4*((k : ℝ)+1)*(2*max 1 A+D+1)/(r*sizes j)))/κ) atTop (nhds 0) := by
      have H := hsqrt.const_mul (4*((k : ℝ)+1)*(2*max 1 A+D+1)/(min 1 e*r*κ))
      convert H using 1 <;> first | (funext j; ring) | ring
    have Hb := hcommon.add Hsmall
    simp only [add_zero] at Hb
    apply squeeze_zero' (Eventually.of_forall (fun j => DecisionLemma12_probability_nonneg _ _))
      (Eventually.of_forall (fun j => ?_)) Hb
    exact DecisionLemma20_statistic_bound (P j) δ e A B r D he hr hD (hP j) (hm j) (hk j)
      (q j) (u j) (σ j) (hσ j) (hnorm j).2.2.2 (hnorm j).1 (hnorm j).2.2.1 (hV j) κ hκ
  · intro κ hκ
    have Hlin : Tendsto (fun j => 4*((k : ℝ)+1)*(max 1 A+D)/(r*sizes j)) atTop (nhds 0) := by
      have H := hinv.const_mul (4*((k : ℝ)+1)*(max 1 A+D)/r)
      convert H using 1 <;> first | (funext j; ring) | ring
    have Hsmall : Tendsto (fun j => (2*Real.sqrt (2*D/(r*sizes j)) +
        (2/min 1 e)*(4*((k : ℝ)+1)*(max 1 A+D)/(r*sizes j))+1/(sizes j : ℝ))/κ)
        atTop (nhds 0) := by
      simpa only [mul_zero, add_zero, zero_div] using
        ((((hroot D).const_mul 2).add (Hlin.const_mul (2/min 1 e))).add hinv).div_const κ
    have Hb := hcommon.add Hsmall
    simp only [add_zero] at Hb
    apply squeeze_zero' (Eventually.of_forall (fun j => DecisionLemma12_probability_nonneg _ _))
      (Eventually.of_forall (fun j => ?_)) Hb
    exact DecisionLemma20_variance_bound (P j) δ e A B r D he hr hD (hP j) (hm j) (hk j)
      (q j) (u j) (σ j) (hσ j) (hnorm j).2.2.2 (hnorm j).1 (hnorm j).2.2.1
      (hnorm j).2.1 (hV j) κ hκ

lemma DecisionLemma20_probability_union {n} (P : Population n)
    (E F G : Finset (Fin n) → Prop) (h : ∀ S ∈ assignments P, E S → F S ∨ G S) :
    probability P E ≤ probability P F+probability P G := by
  rw [DecisionLemma12_probability_eq_expectation, DecisionLemma12_probability_eq_expectation,
    DecisionLemma12_probability_eq_expectation, ← DecisionLemma12_expectation_add]
  apply DecisionLemma12_expectation_mono
  intro S hS
  have H := h S hS
  by_cases hE : E S <;> by_cases hF : F S <;> by_cases hG : G S <;>
    simp_all <;> norm_num

lemma DecisionLemma20_normalTail_continuous (x : ℝ) (hx : 0 < x) : ContinuousAt normalTail x := by
  have H := (((DecisionLemma20_normal_cdf_continuous (-x)).comp continuous_neg.continuousAt).add_const 1).sub
    (DecisionLemma20_normal_cdf_continuous x)
  have heq : normalTail =ᶠ[nhds x] (fun t =>
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-t)+1-
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t) := by
    filter_upwards [eventually_gt_nhds hx] with t ht
    exact DecisionLemma20_normalTail_cdf t ht
  change Tendsto normalTail (nhds x) (nhds (normalTail x))
  rw [DecisionLemma20_normalTail_cdf x hx]
  exact H.tendsto.congr' heq.symm

lemma DecisionLemma20_abs_triangle (a b : ℝ) : |b| ≤ |a|+|a-b| := by
  have H := abs_add_le a (b-a)
  rw [show a+(b-a)=b by ring, abs_sub_comm b a] at H
  exact H

lemma DecisionLemma20_transfer_tail (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (f g : ∀ j, Finset (Fin (sizes j)) → ℝ) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (herror : ∀ ε : ℝ, 0 < ε → Tendsto (fun j => probability (P j)
      (fun S => |f j S-g j S| ≥ ε*s j)) atTop (nhds 0))
    (htail : ∀ x : ℝ, 0 < x → Tendsto (fun j =>
      |probability (P j) (fun S => |g j S| ≥ x*s j)-normalTail x|) atTop (nhds 0)) :
    ∀ x : ℝ, 0 < x → Tendsto (fun j =>
      |probability (P j) (fun S => |f j S| ≥ x*s j)-normalTail x|) atTop (nhds 0) := by
  have htail' (x : ℝ) (hx : 0 < x) : Tendsto (fun j => probability (P j)
      (fun S => |g j S| ≥ x*s j)) atTop (nhds (normalTail x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using htail x hx
  intro x hx
  have hc := DecisionLemma20_normalTail_continuous x hx
  have hlim : Tendsto (fun j => probability (P j) (fun S => |f j S| ≥ x*s j))
      atTop (nhds (normalTail x)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.mp
        (hc.eventually (eventually_gt_nhds ha))
      let ε := min (δ/2) (x/2)
      have hε : 0 < ε := lt_min (by positivity) (by positivity)
      have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
      have hnormal : a < normalTail (x+ε) := hδp (by
        rw [Real.dist_eq, show x+ε-x=ε by ring, abs_of_pos hε]
        exact hεδ)
      have H := (htail' (x+ε) (by positivity)).sub (herror ε hε)
      simp only [sub_zero] at H
      filter_upwards [H.eventually (eventually_gt_nhds hnormal)] with j hj
      have Hp := DecisionLemma20_probability_union (P j)
        (fun S => |g j S| ≥ (x+ε)*s j) (fun S => |f j S| ≥ x*s j)
        (fun S => |f j S-g j S| ≥ ε*s j) (fun S _ hS => by
          by_cases hF : x*s j ≤ |f j S|
          · exact Or.inl hF
          · right
            by_contra hE
            have Hf := lt_of_not_ge hF
            have He := lt_of_not_ge hE
            have Htri := DecisionLemma20_abs_triangle (f j S) (g j S)
            linarith)
      linarith
    · intro a ha
      obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.mp
        (hc.eventually (eventually_lt_nhds ha))
      let ε := min (δ/2) (x/2)
      have hε : 0 < ε := lt_min (by positivity) (by positivity)
      have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
      have hεx : 0 < x-ε := by have H : ε ≤ x/2 := min_le_right _ _; linarith
      have hnormal : normalTail (x-ε) < a := hδp (by
        rw [Real.dist_eq, show x-ε-x = -ε by ring, abs_neg, abs_of_pos hε]
        exact hεδ)
      have H := (htail' (x-ε) hεx).add (herror ε hε)
      simp only [add_zero] at H
      filter_upwards [H.eventually (eventually_lt_nhds hnormal)] with j hj
      have Hp := DecisionLemma20_probability_union (P j)
        (fun S => |f j S| ≥ x*s j) (fun S => |g j S| ≥ (x-ε)*s j)
        (fun S => |f j S-g j S| ≥ ε*s j) (fun S _ hS => by
          by_cases hG : (x-ε)*s j ≤ |g j S|
          · exact Or.inl hG
          · right
            by_contra hE
            have Hg := lt_of_not_ge hG
            have He := lt_of_not_ge hE
            have Htri := DecisionLemma20_abs_triangle (g j S) (f j S)
            rw [abs_sub_comm (g j S) (f j S)] at Htri
            linarith)
      linarith
  simpa only [sub_self, abs_zero] using (hlim.sub_const (normalTail x)).abs

theorem corrected_lemma20_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ n, Xi (P n) δ e A B r)
    (hpositive : ∀ n a, 0 < popVar (residual (P n) a (late (P n).pop)))
    (hZ : RandomizationSequence (fun n => (P n).pop) μ Z)
    (sub : ℕ → ℕ) (hsub : StrictMono sub) :
    ∀ᵐ ω ∂μ,
      (∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
        let N := sub j
        let q := observedW (P N).pop (late (P N).pop) (Z N ω)
        probability (P N).pop (fun S => |adjustedTau (P N) q S-oracleStar (P N) q S| ≥
          κ*Real.sqrt (designVariance (P N).pop (oracleStar (P N) q)))) atTop (nhds 0)) ∧
      (∀ x : ℝ, 0 < x → Tendsto (fun j =>
        let N := sub j
        let q := observedW (P N).pop (late (P N).pop) (Z N ω)
        |probability (P N).pop (fun S => |oracleStar (P N) q S| ≥
          x*Real.sqrt (designVariance (P N).pop (oracleStar (P N) q))) - normalTail x|)
        atTop (nhds 0)) ∧
      (∀ x : ℝ, 0 < x → Tendsto (fun j =>
        let N := sub j
        let q := observedW (P N).pop (late (P N).pop) (Z N ω)
        |probability (P N).pop (fun S => |adjustedTau (P N) q S| ≥
          x*Real.sqrt (designVariance (P N).pop (oracleStar (P N) q))) - normalTail x|)
        atTop (nhds 0)) ∧
      (∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
        let N := sub j
        let q := observedW (P N).pop (late (P N).pop) (Z N ω)
        probability (P N).pop (fun S => |adjustedSigma2 (P N) q S /
          designVariance (P N).pop (oracleStar (P N) q) - 1| ≥ κ)) atTop (nhds 0)) := by
  let D := 8*max (B^4) (((k : ℝ)+1)^2*max 1 A)/(r*(min 1 e/8))^2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hsize : StrictMono (fun j => sizes (sub j)) := hsizes.comp hsub
  have hZ' : RandomizationSequence (fun j => (P (sub j)).pop) μ (fun j => Z (sub j)) :=
    fun j E => hZ (sub j) E
  have hregular := DecisionLemma20_ae_pooled_regular μ (fun j => sizes (sub j)) hsize k
    (fun j => P (sub j)) (fun j => Z (sub j)) δ e A B r he hA hB hr.1
    (fun j => hP (sub j)) (fun j => hpositive (sub j)) hZ'
  have hN : Tendsto (fun j => (sizes (sub j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize.tendsto_atTop
  have hlarge : ∀ᶠ j in atTop, 2 ≤ (P (sub j)).pop.n1 ∧ 2 ≤ sizes (sub j)-(P (sub j)).pop.n1 := by
    filter_upwards [(hN.const_mul_atTop hr.1).eventually_ge_atTop 2] with j hj
    have H1 : (2 : ℝ) ≤ (P (sub j)).pop.n1 := hj.trans (hP (sub j)).2.2.2.1
    have H0 : (2 : ℝ) ≤ ((sizes (sub j)-(P (sub j)).pop.n1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hP (sub j)).1.2.2.le]
      linarith [(hP (sub j)).2.2.2.2.1]
    exact ⟨by exact_mod_cast H1, by exact_mod_cast H0⟩
  filter_upwards [hregular] with ω hω
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hω.and hlarge)
  let ns := fun j => sizes (sub (j+J))
  let Ps := fun j => P (sub (j+J))
  let qs := fun j => observedW (Ps j).pop (late (Ps j).pop) (Z (sub (j+J)) ω)
  have hns : StrictMono ns := fun i j hij => hsizes (hsub (Nat.add_lt_add_right hij J))
  have hPs (j) : Xi (Ps j) δ e A B r := hP (sub (j+J))
  have hreg (j) :
      0 < popVar (fun i => qs j i-dotProduct (augmented (Ps j).x i) (ols (Ps j).x Finset.univ (qs j))) ∧
      (∑ i, (qs j i-dotProduct (augmented (Ps j).x i) (ols (Ps j).x Finset.univ (qs j)))^4) ≤
        D*ns j*(popVar (fun i => qs j i-dotProduct (augmented (Ps j).x i)
          (ols (Ps j).x Finset.univ (qs j))))^2 := (hJ (j+J) (by omega)).1
  have hm (j) : 2 ≤ (Ps j).pop.n1 := (hJ (j+J) (by omega)).2.1
  have hc (j) : 2 ≤ ns j-(Ps j).pop.n1 := (hJ (j+J) (by omega)).2.2
  have hfeasible := DecisionLemma20_feasible_limits ns hns k Ps qs δ e A B r D he hr.1 hD
    hPs hm hc (fun j => (hreg j).1) (fun j => (hreg j).2)
  have horacle := DecisionLemma20_oracle_CLT ns hns k Ps qs δ e A B r D he hr.1 hD
    hPs (fun j => (hreg j).1) (fun j => (hreg j).2)
  have hscale (j) : 0 < Real.sqrt (designVariance (Ps j).pop (oracleStar (Ps j) (qs j))) := by
    apply Real.sqrt_pos.mpr
    have hg := DecisionLemma20_population_fullrank (Ps j) δ e A B r he (hPs j)
    rw [(oracle_variances_proof (Ps j) (hPs j).1 0 (qs j) (hPs j).2.2.2.2.2.2.2.1 hg).2]
    apply mul_pos (hreg j).1
    have H1 : (0 : ℝ) < (Ps j).pop.n1 := by exact_mod_cast (hPs j).1.2.1
    have H0 : 0 < controlSize (Ps j).pop := sub_pos.mpr (by exact_mod_cast (hPs j).1.2.2)
    positivity
  have hadjusted := DecisionLemma20_transfer_tail ns (fun j => (Ps j).pop)
    (fun j => adjustedTau (Ps j) (qs j)) (fun j => oracleStar (Ps j) (qs j))
    (fun j => Real.sqrt (designVariance (Ps j).pop (oracleStar (Ps j) (qs j))))
    hscale hfeasible.1 horacle
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro κ hκ
    exact (tendsto_add_atTop_iff_nat J).mp (hfeasible.1 κ hκ)
  · intro x hx
    exact (tendsto_add_atTop_iff_nat J).mp (horacle x hx)
  · intro x hx
    exact (tendsto_add_atTop_iff_nat J).mp (hadjusted x hx)
  · intro κ hκ
    exact (tendsto_add_atTop_iff_nat J).mp (hfeasible.2 κ hκ)

end
end AronowAudit.P002.Wave1
