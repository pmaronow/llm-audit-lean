import AronowAudit.P002.P002_Audit
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import Mathlib.Logic.Equiv.Fintype

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open StatLean.HypothesisTesting

/-- Centering and scaling by the finite-population standard deviation. -/
def FPCLT_normalize {n : ℕ} (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  (q i - mean q) / Real.sqrt (popVar q)

theorem FPCLT_center {n : ℕ} (q : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, FPCLT_normalize q i = 0 := by
  unfold FPCLT_normalize
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mean]
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem FPCLT_second {n : ℕ} (q : Fin n → ℝ) (hv : 0 < popVar q) :
    ∑ i, FPCLT_normalize q i ^ 2 = (n : ℝ) - 1 := by
  simp only [FPCLT_normalize, div_pow, Real.sq_sqrt hv.le, ← Finset.sum_div]
  have hn : (n : ℝ) - 1 ≠ 0 := by
    intro he
    have hz : popVar q = 0 := by simp [popVar, he]
    linarith
  have h := (div_eq_iff hn).mp (show
      (∑ i, (q i - mean q)^2) / ((n : ℝ) - 1) = popVar q from rfl)
  exact (div_eq_iff hv.ne').mpr (by linarith)

/-- The assignment selected by a permutation of an injective block. -/
def FPCLT_sample {n m : ℕ} (a : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n) := Finset.univ.image (fun i => σ (a i))

theorem FPCLT_sample_card {n m : ℕ} (a : Fin m → Fin n)
    (ha : Function.Injective a) (σ : Equiv.Perm (Fin n)) :
    (FPCLT_sample a σ).card = m := by
  rw [FPCLT_sample, Finset.card_image_of_injective _ (show Function.Injective (fun i => σ (a i)) from
    fun i j hij => ha (σ.injective hij))]
  simp

theorem FPCLT_sample_mul {n m : ℕ} (a : Fin m → Fin n)
    (τ σ : Equiv.Perm (Fin n)) :
    FPCLT_sample a (τ * σ) = (FPCLT_sample a σ).map τ.toEmbedding := by
  ext x
  simp only [FPCLT_sample, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_map, Equiv.Perm.mul_apply, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ (a i), ⟨i, rfl⟩, hi⟩
  · rintro ⟨y, ⟨i, rfl⟩, hi⟩
    exact ⟨i, hi⟩

theorem FPCLT_equal_fibers {n m : ℕ} (a : Fin m → Fin n)
    (S T : Finset (Fin n)) (hST : S.card = T.card) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => FPCLT_sample a σ = S).card =
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => FPCLT_sample a σ = T).card := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S T hST
  apply Finset.card_bij (fun σ _ => τ * σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [FPCLT_sample_mul, hσ, hτ]
  · intro σ hσ ρ hρ heq
    exact mul_left_cancel heq
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨τ⁻¹ * σ, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply (Finset.map_injective τ.toEmbedding)
    rw [← FPCLT_sample_mul]
    simpa [hτ] using hσ

/-- Uniform permutations induce the uniform fixed-size assignment law. -/
theorem FPCLT_uniform {n : ℕ} (P : Population n)
    (a : Fin P.n1 → Fin n) (ha : Function.Injective a)
    (E : Finset (Fin n) → Prop) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), (if E (FPCLT_sample a σ) then (1 : ℝ) else 0) =
      probability P E := by
  let B := FPCLT_sample a 1
  let c := (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => FPCLT_sample a σ = B).card
  have hc : 0 < c := by
    apply Finset.card_pos.mpr
    exact ⟨1, by simp [B]⟩
  have hmem (σ : Equiv.Perm (Fin n)) : FPCLT_sample a σ ∈ assignments P := by
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, FPCLT_sample_card a ha σ⟩
  have hfiber (S : Finset (Fin n)) (hS : S ∈ assignments P) :
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => FPCLT_sample a σ = S).card = c := by
    apply FPCLT_equal_fibers
    rw [(Finset.mem_powersetCard.mp hS).2, FPCLT_sample_card a ha]
  have hcount (F : Finset (Fin n) → Prop) :
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => F (FPCLT_sample a σ)).card =
        ((assignments P).filter F).card * c := by
    have hh := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Equiv.Perm (Fin n))) ((assignments P).filter F)
      (FPCLT_sample a)
    have hfilter : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
        FPCLT_sample a σ ∈ (assignments P).filter F) =
        Finset.univ.filter (fun σ => F (FPCLT_sample a σ)) := by
      ext σ
      simp [hmem σ]
    rw [hfilter] at hh
    rw [← hh]
    calc
      _ = ∑ _S ∈ (assignments P).filter F, c := by
        apply Finset.sum_congr rfl
        intro S hS
        exact hfiber S (Finset.mem_filter.mp hS).1
      _ = _ := by simp
  have hall := hcount (fun _ => True)
  simp only [Finset.filter_true, Finset.card_univ] at hall
  have hsum : (∑ σ : Equiv.Perm (Fin n), if E (FPCLT_sample a σ) then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => E (FPCLT_sample a σ)).card : ℝ) := by
    simp
  rw [hsum, hcount E, probability, hall, Nat.cast_mul, Nat.cast_mul]
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← div_eq_inv_mul]
  exact mul_div_mul_right _ _ hcR

/-- The maximum normalized square is bounded away from zero, uniformly in `n ≥ 2`. -/
theorem FPCLT_max_lower {n : ℕ} (q : Fin n → ℝ) (hn : 2 ≤ n)
    (hv : 0 < popVar q) :
    (1 / 2 : ℝ) ≤ maximum (fun i => (q i - mean q)^2) / popVar q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsum : ∑ i, (q i - mean q)^2 ≤
      (n : ℝ) * maximum (fun i => (q i - mean q)^2) := by
    calc
      _ ≤ ∑ _i : Fin n, maximum (fun i => (q i - mean q)^2) :=
        Finset.sum_le_sum fun i _ => le_maximum _ i
      _ = _ := by simp
  have heq : ∑ i, (q i - mean q)^2 = popVar q * ((n : ℝ)-1) :=
    (div_eq_iff (by linarith)).mp rfl
  apply (le_div_iff₀ hv).mpr
  nlinarith

theorem FPCLT_min_cast {n : ℕ} (P : Population n) (hP : ValidDesign P) :
    ((min P.n1 (n - P.n1) : ℕ) : ℝ) = min (P.n1 : ℝ) ((n : ℝ) - P.n1) := by
  rw [Nat.cast_min, Nat.cast_sub hP.2.2.le]

/-- A vanishing maximum ratio forces the smaller arm to diverge. -/
theorem FPCLT_min_grows {N : ℕ → ℕ} (D : ∀ j, Population (N j))
    (q : ∀ j, Fin (N j) → ℝ) (hD : ∀ j, ValidDesign (D j))
    (hv : ∀ j, 0 < popVar (q j))
    (hr : Tendsto (fun j => maximum (fun i => (q j i - mean (q j))^2) /
      (((min (D j).n1 (N j - (D j).n1) : ℕ) : ℝ) * popVar (q j))) atTop (nhds 0)) :
    Tendsto (fun j => ((min (D j).n1 (N j - (D j).n1) : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  let B : ℝ := max b 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have he : 0 < (1 / (2 * B) : ℝ) := by positivity
  filter_upwards [hr.eventually (gt_mem_nhds he)] with j hj
  let L : ℝ := ((min (D j).n1 (N j - (D j).n1) : ℕ) : ℝ)
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast (show 0 < min (D j).n1 (N j - (D j).n1) from
      lt_min (hD j).2.1 (Nat.sub_pos_of_lt (hD j).2.2))
  have hlo := FPCLT_max_lower (q j) (hD j).1 (hv j)
  have hrB := (div_lt_iff₀ (mul_pos hL (hv j))).mp hj
  have hcancel : maximum (fun i => (q j i - mean (q j))^2) / popVar (q j) <
      L / (2 * B) := by
    apply (div_lt_iff₀ (hv j)).mpr
    dsimp [L] at *
    convert hrB using 1 <;> ring
  have hLB : B < L := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * B)).mp (lt_of_le_of_lt hlo hcancel)
    linarith
  exact le_trans (le_max_left b 0) (by dsimp [B] at hLB; linarith)

/-- The maximum condition kills every Lindeberg summand eventually. -/
theorem FPCLT_lindeberg {N : ℕ → ℕ} (D : ∀ j, Population (N j))
    (q : ∀ j, Fin (N j) → ℝ) (hD : ∀ j, ValidDesign (D j))
    (hv : ∀ j, 0 < popVar (q j))
    (hr : Tendsto (fun j => maximum (fun i => (q j i - mean (q j))^2) /
      (((min (D j).n1 (N j - (D j).n1) : ℕ) : ℝ) * popVar (q j))) atTop (nhds 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun j => (N j : ℝ)⁻¹ *
      ∑ i, (if ε * Real.sqrt (min ((D j).n1 : ℝ) ((N j : ℝ) - (D j).n1)) ≤
        |FPCLT_normalize (q j) i| then FPCLT_normalize (q j) i ^ 2 else 0))
      atTop (nhds 0) := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [hr.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hj
  symm
  have hL : 0 < ((min (D j).n1 (N j - (D j).n1) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < min (D j).n1 (N j - (D j).n1) from
      lt_min (hD j).2.1 (Nat.sub_pos_of_lt (hD j).2.2))
  have hmax := (div_lt_iff₀ (mul_pos hL (hv j))).mp hj
  have hL' : 0 ≤ min ((D j).n1 : ℝ) ((N j : ℝ) - (D j).n1) := by
    rw [← FPCLT_min_cast (D j) (hD j)]
    positivity
  have hsummand (i : Fin (N j)) :
      ¬ ε * Real.sqrt (min ((D j).n1 : ℝ) ((N j : ℝ) - (D j).n1)) ≤
        |FPCLT_normalize (q j) i| := by
    have hcoord := le_maximum (fun i => (q j i - mean (q j))^2) i
    have hd : FPCLT_normalize (q j) i ^ 2 < ε^2 *
        min ((D j).n1 : ℝ) ((N j : ℝ) - (D j).n1) := by
      rw [FPCLT_normalize, div_pow, Real.sq_sqrt (hv j).le]
      apply (div_lt_iff₀ (hv j)).mpr
      rw [FPCLT_min_cast (D j) (hD j)] at hmax
      nlinarith
    have hs := Real.sq_sqrt hL'
    have hnon : 0 ≤ ε * Real.sqrt (min ((D j).n1 : ℝ) ((N j : ℝ) - (D j).n1)) := by positivity
    intro hh
    have habs := sq_abs (FPCLT_normalize (q j) i)
    nlinarith [sq_nonneg (|FPCLT_normalize (q j) i| -
      ε * Real.sqrt (min ((D j).n1 : ℝ) ((N j : ℝ) - (D j).n1)))]
  simp only [if_neg (hsummand _), Finset.sum_const_zero, mul_zero]

/-- Exact identity of the two standardized statistics. -/
theorem FPCLT_standardize {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (q : Fin n → ℝ) (hv : 0 < popVar q)
    (a : Fin P.n1 → Fin n) (ha : Function.Injective a) (σ : Equiv.Perm (Fin n)) :
    (groupMean (FPCLT_sample a σ) q - mean q) /
      Real.sqrt ((1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q) =
      (∑ i, FPCLT_normalize q (σ (a i))) / blockSumScale n P.n1 := by
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hN : (0 : ℝ) < n := by exact_mod_cast (lt_trans hP.2.1 hP.2.2)
  have hmN : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hA : 0 < (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
    apply mul_pos _ hv
    exact sub_pos.mpr ((one_div_lt_one_div hN hm).mpr hmN)
  have hb : 0 < blockSumScale n P.n1 := by
    rw [blockSumScale, Real.sqrt_pos]
    exact div_pos (mul_pos hm (sub_pos.mpr hmN)) hN
  have hs := Real.sqrt_pos.mpr hA
  have hvS := Real.sqrt_pos.mpr hv
  have hscale : (P.n1 : ℝ) * Real.sqrt ((1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q) =
      Real.sqrt (popVar q) * blockSumScale n P.n1 := by
    have hsq : ((P.n1 : ℝ) * Real.sqrt ((1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q))^2 =
        (Real.sqrt (popVar q) * blockSumScale n P.n1)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hv.le,
        blockSumScale, Real.sq_sqrt (by positivity)]
      field_simp
      <;> ring
    nlinarith [mul_pos hm hs, mul_pos hvS hb]
  have hsum : ∑ i, FPCLT_normalize q (σ (a i)) =
      ((∑ i, q (σ (a i))) - (P.n1 : ℝ) * mean q) / Real.sqrt (popVar q) := by
    simp only [FPCLT_normalize, ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hraw : ∑ x ∈ FPCLT_sample a σ, q x = ∑ i, q (σ (a i)) := by
    exact Finset.sum_image (fun i _ j _ he => (σ.injective.comp ha) he)
  rw [groupMean, FPCLT_sample_card a ha, hraw, hsum]
  apply (div_eq_div_iff hs.ne' hb.ne').mpr
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hvS.ne').mpr
  calc
    _ = ((∑ i, q (σ (a i))) - (P.n1 : ℝ) * mean q) *
        (Real.sqrt (popVar q) * blockSumScale n P.n1) / (P.n1 : ℝ) := by
      field_simp
      <;> ring
    _ = _ := by rw [← hscale]; field_simp; <;> ring

/-- Hájek's finite-population central limit theorem for uniform fixed-size sampling. -/
theorem finitePopulationCLT :
  ∀ (sizes : ℕ → ℕ), StrictMono sizes →
  ∀ (D : ∀ j, Population (sizes j))
    (q : ∀ j, Fin (sizes j) → ℝ),
    (∀ j, ValidDesign (D j)) →
    (∀ j, 0 < popVar (q j)) →
    Tendsto (fun j =>
      maximum (fun i => (q j i - mean (q j)) ^ 2) /
        (((min (D j).n1 (sizes j - (D j).n1) : ℕ) : ℝ) *
          popVar (q j))) atTop (nhds 0) →
    ∀ t : ℝ, Tendsto (fun j => probability (D j) (fun S =>
      (groupMean S (q j) - mean (q j)) /
        Real.sqrt ((1 / ((D j).n1 : ℝ) - 1 / (sizes j : ℝ)) *
          popVar (q j)) ≤ t))
      atTop (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic t)).toReal)) := by
  intro sizes hsize D q hD hv hr t
  let a : ∀ j, Fin (D j).n1 → Fin (sizes j) := fun j => Fin.castLE (hD j).2.2.le
  have ha : ∀ j, Function.Injective (a j) := fun j => Fin.castLE_injective _
  have hcent : ∀ j, ∑ i, FPCLT_normalize (q j) i = 0 := fun j =>
    FPCLT_center (q j) (by have := (hD j).1; omega)
  have hmin := FPCLT_min_grows D q hD hv hr
  have hm : Tendsto (fun j => ((D j).n1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun j => by exact_mod_cast (min_le_left (D j).n1
      (sizes j - (D j).n1))) hmin
  have hNm : Tendsto (fun j => (sizes j : ℝ) - (D j).n1) atTop atTop := by
    apply tendsto_atTop_mono _ hmin
    intro j
    rw [FPCLT_min_cast (D j) (hD j)]
    exact min_le_right _ _
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize.tendsto_atTop
  have hvar : Tendsto (fun j => (sizes j : ℝ)⁻¹ * ∑ i, FPCLT_normalize (q j) i^2)
      atTop (nhds 1) := by
    have hlim : Tendsto (fun j => 1 - (sizes j : ℝ)⁻¹) atTop (nhds (1 - 0 : ℝ)) :=
      tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp hN)
    convert hlim using 1
    · funext j
      rw [FPCLT_second (q j) (hv j)]
      have hn : (sizes j : ℝ) ≠ 0 := by
        have : 0 < sizes j := by have := (hD j).1; omega
        exact_mod_cast this.ne'
      field_simp
      <;> ring
    · norm_num
  have hclt := tendsto_perm_cdf_blockSum a ha (fun j => FPCLT_normalize (q j))
    hcent hm hNm hvar (FPCLT_lindeberg D q hD hv hr) t
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def] at hclt
  convert hclt using 1
  funext j
  rw [← FPCLT_uniform (D j) (a j) (ha j)]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  have hb : 0 < blockSumScale (sizes j) (D j).n1 := by
    rw [blockSumScale, Real.sqrt_pos]
    have hm : (0 : ℝ) < (D j).n1 := by exact_mod_cast (hD j).2.1
    have hmN : ((D j).n1 : ℝ) < sizes j := by exact_mod_cast (hD j).2.2
    exact div_pos (mul_pos hm (sub_pos.mpr hmN)) (lt_trans hm hmN)
  rw [FPCLT_standardize (D j) (hD j) (q j) (hv j) (a j) (ha j) σ,
    div_le_iff₀ hb]

end
end AronowAudit.P002.Wave1
