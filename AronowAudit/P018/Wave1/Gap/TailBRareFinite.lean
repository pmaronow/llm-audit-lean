import AronowAudit.P018.Wave1.Gap.GP0181B1
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
Finite-sample calculations for the actual countable rare-category model.
The coordinates used below are (intercept + slope, slope); the reported
coefficients and sandwich use the original model definitions.
-/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

instance TailB_rare_countable : Countable RareUnit :=
  (show Function.Injective (fun u : RareUnit => (u.m, u.label.val, u.A, u.B)) from by
    intro u v h
    cases u with | mk m c a b =>
      cases v with | mk n d e f =>
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, hcd, rfl, rfl⟩
        have : c = d := Fin.ext hcd
        subst d
        rfl).countable

theorem TailB_rare_lintegral (f : RareUnit → ℝ≥0∞) :
    (∫⁻ u, f u ∂rareLaw) = ∑' m : ℕ,
      ENNReal.ofReal ((2 : ℝ)^(-(m+1 : ℤ))/((m+1 : ℝ)*4)) *
        (∑ c : Fin (m+1), ∑ a : Bool, ∑ b : Bool, f ⟨m,c,a,b⟩) := by
  simp only [rareLaw, lintegral_sum_measure, lintegral_smul_measure,
    lintegral_finsetSum_measure, lintegral_dirac, smul_eq_mul]

theorem TailB_rare_probability : IsProbabilityMeasure rareLaw := by
  constructor
  have h := TailB_rare_lintegral (fun _ => 1)
  simp only [lintegral_one] at h
  rw [h]
  have ht (m : ℕ) :
      ENNReal.ofReal ((2 : ℝ)^(-(m+1 : ℤ))/((m+1 : ℝ)*4)) *
        (∑ _ : Fin (m+1), ∑ _ : Bool, ∑ _ : Bool, (1 : ℝ≥0∞)) =
      (2 : ℝ≥0∞)^(-1-m : ℤ) := by
    have hm : (m+1 : ℝ) ≠ 0 := by positivity
    have he : (∑ _ : Fin (m+1), ∑ _ : Bool, ∑ _ : Bool, (1 : ℝ≥0∞)) =
        ENNReal.ofReal ((m+1 : ℝ)*4) := by
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_add (Nat.cast_nonneg m) (by norm_num)]
      norm_num
    rw [he, ← ENNReal.ofReal_mul (by positivity)]
    have hr : (2 : ℝ)^(-(m+1 : ℤ))/((m+1 : ℝ)*4) * ((m+1 : ℝ)*4) =
        (2 : ℝ)^(-(m+1 : ℤ)) := by field_simp
    rw [hr]
    rw [show (-1-m : ℤ) = -((m+1 : ℕ) : ℤ) by omega,
      show -(m+1 : ℤ) = -((m+1 : ℕ) : ℤ) by omega,
      _root_.zpow_neg, ENNReal.zpow_neg, zpow_natCast, zpow_natCast,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  simp_rw [ht]
  exact ENNReal.tsum_two_zpow_neg_add_one

theorem TailB_rare_delta_pos (m : ℕ) (hm : 0 < m) : 0 < rareDelta m := by
  unfold rareDelta
  positivity

theorem TailB_rare_delta_le_one (m : ℕ) (hm : 0 < m) : rareDelta m ≤ 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (1 : ℝ) ≤ 2^(m*m+2) := one_le_pow₀ (by norm_num)
  unfold rareDelta
  apply (div_le_one (by positivity)).2
  nlinarith

theorem TailB_rare_s_bounds (u v : RareUnit) : 0 < rareS u v ∧ rareS u v ≤ 1 := by
  unfold rareS
  split_ifs
  · exact ⟨TailB_rare_delta_pos _ (by omega), TailB_rare_delta_le_one _ (by omega)⟩
  · norm_num

theorem TailB_rare_sign_abs (b : Bool) : |signValue b| = 1 := by cases b <;> norm_num [signValue]

theorem TailB_rare_a_bound (u v : RareUnit) : |rareA u v| ≤ 2 := by
  unfold rareA
  split_ifs
  · simpa only [TailB_rare_sign_abs, one_add_one_eq_two] using abs_add_le (signValue u.A) (signValue v.A)
  · norm_num

theorem TailB_rare_standing : RepeatedStanding rareRepeated := by
  refine ⟨TailB_rare_probability, ?_, ?_, ⟨4, by norm_num, ?_⟩, ⟨0, ?_⟩⟩
  · intros; norm_num [rareRepeated]
  · intros; exact ⟨measurable_of_countable _, measurable_of_countable _⟩
  · intro N d t
    apply Filter.Eventually.of_forall
    intro uv
    have hs := TailB_rare_s_bounds uv.1 uv.2
    have ha := TailB_rare_a_bound uv.1 uv.2
    have hu : |signValue uv.1.B + signValue uv.2.B| ≤ 2 := by
      simpa only [TailB_rare_sign_abs, one_add_one_eq_two] using abs_add_le (signValue uv.1.B) (signValue uv.2.B)
    constructor
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)).2
      intro j
      fin_cases j
      · change |(1 : ℝ)| ≤ 4
        norm_num
      · change |1 + (if t.val = 0 then rareS uv.1 uv.2 else -rareS uv.1 uv.2)| ≤ 4
        split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
    · change |signValue uv.1.B + signValue uv.2.B +
        (if t.val = 0 then rareA uv.1 uv.2 else -rareA uv.1 uv.2)| ≤ 4
      have ht : |if t.val = 0 then rareA uv.1 uv.2 else -rareA uv.1 uv.2| ≤ 2 := by
        split_ifs <;> simpa only [abs_neg] using ha
      exact (abs_add_le _ _).trans (by linarith)
  · intros; rfl

def TailB_rare_s {N : ℕ} (ω : Fin N → RareUnit) (d : Dyad N) : ℝ :=
  rareS (ω (firstUnit d)) (ω (secondUnit d))
def TailB_rare_a {N : ℕ} (ω : Fin N → RareUnit) (d : Dyad N) : ℝ :=
  rareA (ω (firstUnit d)) (ω (secondUnit d))
def TailB_rare_u {N : ℕ} (ω : Fin N → RareUnit) (d : Dyad N) : ℝ :=
  signValue (ω (firstUnit d)).B + signValue (ω (secondUnit d)).B
def TailB_rare_S {N : ℕ} (ω : Fin N → RareUnit) : ℝ := ∑ d : Dyad N, (TailB_rare_s ω d)^2
def TailB_rare_U {N : ℕ} (ω : Fin N → RareUnit) : ℝ := ∑ d : Dyad N, TailB_rare_u ω d
def TailB_rare_W {N : ℕ} (ω : Fin N → RareUnit) : ℝ := ∑ d : Dyad N, TailB_rare_s ω d * TailB_rare_a ω d

theorem TailB_rare_X (N : ℕ) (d : Dyad N) (t : Fin 2) (u v : RareUnit) :
    rareRepeated.X N d t u v = ![1,1+(if t.val=0 then rareS u v else -rareS u v)] := rfl
theorem TailB_rare_Y (N : ℕ) (d : Dyad N) (t : Fin 2) (u v : RareUnit) :
    rareRepeated.Y N d t u v = signValue u.B+signValue v.B+
      (if t.val=0 then rareA u v else -rareA u v) := rfl

theorem TailB_rare_D_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Dreal N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  exact div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)

theorem TailB_rare_S_pos {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) : 0 < TailB_rare_S ω := by
  have hcard : 0 < Fintype.card (Dyad N) := by
    have := TailB_rare_D_pos hN
    rw [← printed_card_real] at this
    exact_mod_cast this
  obtain ⟨d⟩ := Fintype.card_pos_iff.mp hcard
  exact Finset.sum_pos (fun d _ => sq_pos_of_pos (TailB_rare_s_bounds _ _).1) ⟨d, mem_univ d⟩

theorem TailB_rare_gram {N : ℕ} (ω : Fin N → RareUnit) :
    repeatedGram rareRepeated ω =
      !![2*Dreal N, 2*Dreal N; 2*Dreal N, 2*Dreal N+2*TailB_rare_S ω] := by
  have hb (d : Dyad N) : (∑ t, outer (repeatedX rareRepeated ω d t)
      (repeatedX rareRepeated ω d t)) =
      !![2,2;2,2+2*(TailB_rare_s ω d)^2] := by
    change (∑ t : Fin 2, outer _ _) = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ, outer, repeatedX, TailB_rare_X, TailB_rare_s,
        Matrix.sum_apply] <;> ring
  simp only [repeatedGram, hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sum_apply, TailB_rare_S, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← printed_card_real, nsmul_eq_mul] <;> ring

theorem TailB_rare_gram_det {N : ℕ} (ω : Fin N → RareUnit) :
    (repeatedGram rareRepeated ω).det = 4*Dreal N*TailB_rare_S ω := by
  rw [TailB_rare_gram, Matrix.det_fin_two]
  simp
  ring

theorem TailB_rare_gram_pos {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) :
    0 < (repeatedGram rareRepeated ω).det := by
  rw [TailB_rare_gram_det]
  exact mul_pos (mul_pos (by norm_num) (TailB_rare_D_pos hN)) (TailB_rare_S_pos hN ω)

theorem TailB_rare_gram_inv {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) :
    (repeatedGram rareRepeated ω)⁻¹ =
      !![(Dreal N+TailB_rare_S ω)/(2*Dreal N*TailB_rare_S ω), -1/(2*TailB_rare_S ω);
        -1/(2*TailB_rare_S ω), 1/(2*TailB_rare_S ω)] := by
  apply Matrix.inv_eq_left_inv
  rw [TailB_rare_gram]
  have hd := ne_of_gt (TailB_rare_D_pos hN)
  have hs := ne_of_gt (TailB_rare_S_pos hN ω)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    field_simp [hd, hs] <;> ring

theorem TailB_rare_xy {N : ℕ} (ω : Fin N → RareUnit) :
    (∑ d : Dyad N, ∑ t, score (repeatedX rareRepeated ω d t)
      (repeatedY rareRepeated ω d t)) =
      ![2*TailB_rare_U ω, 2*TailB_rare_U ω+2*TailB_rare_W ω] := by
  have hb (d : Dyad N) : (∑ t, score (repeatedX rareRepeated ω d t)
      (repeatedY rareRepeated ω d t)) =
      ![2*TailB_rare_u ω d, 2*TailB_rare_u ω d+2*TailB_rare_s ω d*TailB_rare_a ω d] := by
    change (∑ t : Fin 2, score _ _) = _
    ext i
    fin_cases i <;>
      norm_num [Fin.sum_univ_succ, score, repeatedX, repeatedY, TailB_rare_X, TailB_rare_Y,
        TailB_rare_s, TailB_rare_a, TailB_rare_u, Finset.sum_apply] <;> ring
  simp only [hb]
  ext i
  fin_cases i <;>
    simp [TailB_rare_U, TailB_rare_W, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

theorem TailB_rare_exact_fit {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) :
    repeatedOLS rareRepeated ω =
      ![TailB_rare_U ω / Dreal N - TailB_rare_W ω / TailB_rare_S ω,
        TailB_rare_W ω / TailB_rare_S ω] := by
  unfold repeatedOLS
  rw [TailB_rare_gram_inv hN, TailB_rare_xy]
  have hd := ne_of_gt (TailB_rare_D_pos hN)
  have hs := ne_of_gt (TailB_rare_S_pos hN ω)
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hd, hs] <;> ring

theorem TailB_rare_residual_formula {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit)
    (d : Dyad N) (t : Fin 2) :
    repeatedY rareRepeated ω d t - dot (repeatedX rareRepeated ω d t)
      (repeatedOLS rareRepeated ω) =
      TailB_rare_u ω d - TailB_rare_U ω / Dreal N +
        (if t.val = 0 then 1 else -1) *
          (TailB_rare_a ω d - TailB_rare_s ω d * (TailB_rare_W ω / TailB_rare_S ω)) := by
  rw [TailB_rare_exact_fit hN]
  simp [repeatedY, repeatedX, TailB_rare_X, TailB_rare_Y, dot, Fin.sum_univ_succ,
    TailB_rare_u, TailB_rare_s, TailB_rare_a]
  split_ifs <;> ring

def TailB_rare_r {N : ℕ} (ω : Fin N → RareUnit) (d : Dyad N) : ℝ :=
  TailB_rare_a ω d - TailB_rare_s ω d * (TailB_rare_W ω / TailB_rare_S ω)

theorem TailB_rare_block_score {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) (d : Dyad N) :
    repeatedBlockScore rareRepeated (repeatedOLS rareRepeated ω) ω d =
      ![2*(TailB_rare_u ω d-TailB_rare_U ω/Dreal N),
        2*(TailB_rare_u ω d-TailB_rare_U ω/Dreal N)+2*TailB_rare_s ω d*TailB_rare_r ω d] := by
  unfold repeatedBlockScore
  change (∑ t : Fin 2, _) = _
  simp_rw [TailB_rare_residual_formula hN]
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_succ, score, repeatedX, TailB_rare_X, TailB_rare_s, TailB_rare_r] <;> ring

theorem TailB_rare_sandwich_meat {N : ℕ} (P : Mat 2) (hP : P 0 1 = P 1 0)
    (q : Dyad N → Vec 2) :
    sandwich P (meat members q) = meat members (fun d => P.mulVec (q d)) := by
  unfold sandwich meat
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [outer, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hP] <;> ring
  · simp

theorem TailB_rare_influence_slope {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) (d : Dyad N) :
    ((repeatedGram rareRepeated ω)⁻¹.mulVec
      (repeatedBlockScore rareRepeated (repeatedOLS rareRepeated ω) ω d)) 1 =
      TailB_rare_s ω d * TailB_rare_r ω d / TailB_rare_S ω := by
  rw [TailB_rare_gram_inv hN, TailB_rare_block_score hN]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem TailB_rare_variance_formula {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) :
    (repeatedVariance rareRepeated ω) 1 1 =
      (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then
        (TailB_rare_s ω d * TailB_rare_r ω d) *
          (TailB_rare_s ω f * TailB_rare_r ω f) else 0) / (TailB_rare_S ω)^2 := by
  have hP : (repeatedGram rareRepeated ω)⁻¹ 0 1 =
      (repeatedGram rareRepeated ω)⁻¹ 1 0 := by rw [TailB_rare_gram_inv hN]; rfl
  rw [repeatedVariance, TailB_rare_sandwich_meat _ hP]
  simp only [meat, Matrix.sum_apply, matrix_ite_apply, outer, Matrix.of_apply,
    TailB_rare_influence_slope hN, Matrix.zero_apply, overlap]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs with h <;> simp [h, div_mul_div_comm, pow_two]

theorem TailB_rare_centered_overlap {N : ℕ} (v : Fin N → ℝ) (hv : ∑ i, v i = 0) :
    (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then
      (v (firstUnit d)+v (secondUnit d)) * (v (firstUnit f)+v (secondUnit f)) else 0) =
      ((N : ℝ)-2)*((N : ℝ)-3)*(∑ i, (v i)^2) := by
  let q : Dyad N → Vec 1 := fun d _ => v (firstUnit d)+v (secondUnit d)
  have h := congrArg (fun M : Mat 1 => M 0 0)
    (overlap_meat_identity members members_card (fun d e h => Subtype.ext h) q)
  have hu (i : Fin N) : unitScore members q i 0 = ((N : ℝ)-2)*v i := by
    simp only [unitScore, Finset.sum_apply, ite_apply, Pi.zero_apply]
    change (∑ d : Dyad N, if i ∈ members d then v (firstUnit d)+v (secondUnit d) else 0) = _
    rw [printed_incident_add, hv, add_zero]
  have he := printed_pair_square v
  rw [hv] at he
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero] at he
  simp only [meat, Matrix.sum_apply, matrix_ite_apply, outer, Matrix.of_apply, Matrix.zero_apply,
    Matrix.sub_apply, dyadMeat, hu, q] at h
  change _ = _ at h
  have ht : (∑ i : Fin N, (((N : ℝ)-2)*v i)*(((N : ℝ)-2)*v i)) =
      ((N : ℝ)-2)^2 * ∑ i, (v i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros; ring
  simp_rw [← pow_two] at h
  rw [show (∑ i : Fin N, (((N : ℝ)-2)*v i)^2) =
      ((N : ℝ)-2)^2 * ∑ i, (v i)^2 by simpa only [pow_two] using ht, he] at h
  calc
    _ = ((N : ℝ)-2)^2*(∑ i, (v i)^2) - ((N : ℝ)-2)*(∑ i, (v i)^2) := by
      convert h using 1 <;> simp only [overlap, pow_two] <;> congr! 3
    _ = _ := by ring

def TailB_rare_Abar {N : ℕ} (ω : Fin N → RareUnit) : ℝ :=
  (∑ i, signValue (ω i).A)/(N : ℝ)
def TailB_rare_Bbar {N : ℕ} (ω : Fin N → RareUnit) : ℝ :=
  (∑ i, signValue (ω i).B)/(N : ℝ)
def TailB_rare_event (N m : ℕ) : Set (Fin N → RareUnit) :=
  {ω | (∀ i, (ω i).m = m) ∧ Function.Injective (fun i => (ω i).label.val)}

theorem TailB_rare_U_mean {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) :
    TailB_rare_U ω / Dreal N = 2*TailB_rare_Bbar ω := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold TailB_rare_U TailB_rare_u
  rw [printed_pair_add (fun i => signValue (ω i).B)]
  unfold TailB_rare_Bbar Dreal
  field_simp [show (N : ℝ) ≠ 0 by linarith, show (N : ℝ)-1 ≠ 0 by linarith]
  <;> ring

theorem TailB_rare_event_small {N m : ℕ} {ω : Fin N → RareUnit}
    (hω : ω ∈ TailB_rare_event N m) (d : Dyad N) :
    rareSmall (ω (firstUnit d)) (ω (secondUnit d)) :=
  ⟨(hω.1 _).trans (hω.1 _).symm,
    fun h => (printed_endpoints_lt d).ne (hω.2 h)⟩

theorem TailB_rare_event_s {N m : ℕ} {ω : Fin N → RareUnit}
    (hω : ω ∈ TailB_rare_event N m) (d : Dyad N) :
    TailB_rare_s ω d = rareDelta (m+1) := by
  simp only [TailB_rare_s, rareS, if_pos (TailB_rare_event_small hω d), hω.1]

theorem TailB_rare_event_a {N m : ℕ} {ω : Fin N → RareUnit}
    (hω : ω ∈ TailB_rare_event N m) (d : Dyad N) :
    TailB_rare_a ω d = signValue (ω (firstUnit d)).A + signValue (ω (secondUnit d)).A := by
  exact if_pos (TailB_rare_event_small hω d)

theorem TailB_rare_event_S {N m : ℕ} {ω : Fin N → RareUnit}
    (hω : ω ∈ TailB_rare_event N m) : TailB_rare_S ω = Dreal N*(rareDelta (m+1))^2 := by
  simp only [TailB_rare_S, TailB_rare_event_s hω, sum_const, card_univ, nsmul_eq_mul,
    printed_card_real]

theorem TailB_rare_event_slope {N m : ℕ} (hN : 2 ≤ N) {ω : Fin N → RareUnit}
    (hω : ω ∈ TailB_rare_event N m) :
    repeatedOLS rareRepeated ω 1 = 2*TailB_rare_Abar ω / rareDelta (m+1) := by
  rw [TailB_rare_exact_fit hN]
  change TailB_rare_W ω / TailB_rare_S ω = _
  have hw : TailB_rare_W ω = rareDelta (m+1)*((N : ℝ)-1)*∑ i, signValue (ω i).A := by
    simp only [TailB_rare_W, TailB_rare_event_s hω, TailB_rare_event_a hω,
      ← Finset.mul_sum]
    rw [printed_pair_add (fun i => signValue (ω i).A)]
    ring
  rw [hw, TailB_rare_event_S hω]
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold Dreal TailB_rare_Abar
  field_simp [show (N : ℝ) ≠ 0 by linarith, show (N : ℝ)-1 ≠ 0 by linarith,
    ne_of_gt (TailB_rare_delta_pos (m+1) (by omega))]
  <;> ring

theorem TailB_rare_event_variance {N m : ℕ} (hN : 2 ≤ N) {ω : Fin N → RareUnit}
    (hω : ω ∈ TailB_rare_event N m) :
    (repeatedVariance rareRepeated ω) 1 1 =
      ((N : ℝ)-2)*((N : ℝ)-3) *
        (∑ i, (signValue (ω i).A-TailB_rare_Abar ω)^2) /
          ((Dreal N)^2*(rareDelta (m+1))^2) := by
  let v : Fin N → ℝ := fun i => signValue (ω i).A-TailB_rare_Abar ω
  have hv : ∑ i, v i = 0 := by
    simp only [v, Finset.sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold TailB_rare_Abar
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (show N ≠ 0 by omega)]
    ring
  have hr (d : Dyad N) : TailB_rare_r ω d = v (firstUnit d)+v (secondUnit d) := by
    have hb := TailB_rare_event_slope hN hω
    rw [TailB_rare_exact_fit hN] at hb
    change TailB_rare_W ω / TailB_rare_S ω = _ at hb
    simp only [TailB_rare_r, TailB_rare_event_s hω, TailB_rare_event_a hω, hb, v]
    field_simp [ne_of_gt (TailB_rare_delta_pos (m+1) (by omega))]
    ring
  rw [TailB_rare_variance_formula hN, TailB_rare_event_S hω]
  simp_rw [TailB_rare_event_s hω, hr]
  have he : (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then
      (rareDelta (m+1)*(v (firstUnit d)+v (secondUnit d))) *
        (rareDelta (m+1)*(v (firstUnit f)+v (secondUnit f))) else 0) =
      (rareDelta (m+1))^2 * ((N : ℝ)-2)*((N : ℝ)-3)*∑ i, (v i)^2 := by
    calc
      _ = (rareDelta (m+1))^2 *
          (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then
            (v (firstUnit d)+v (secondUnit d))*(v (firstUnit f)+v (secondUnit f)) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f hf
        split_ifs <;> ring
      _ = _ := by rw [TailB_rare_centered_overlap v hv]; ring
  rw [he]
  dsimp [v]
  field_simp [ne_of_gt (TailB_rare_D_pos hN), ne_of_gt (TailB_rare_delta_pos (m+1) (by omega))]
  <;> ring

/-! Category counts.  Counting all pairs in one group is sufficient; the
geometric envelope permits the global number of nonsmall pairs to be used. -/

theorem TailB_rare_category_count {N k : ℕ} (hk : 1 ≤ k)
    (p : Fin N → Prop) [DecidablePred p] (f : Fin N → Fin k) (G : ℝ) (hG : 0 ≤ G)
    (hg : (∑ d : Dyad N, if p (firstUnit d) ∧ p (secondUnit d) ∧
      f (firstUnit d) = f (secondUnit d) then (1 : ℝ) else 0) ≤ G) :
    (∑ d : Dyad N, if p (firstUnit d) ∧ p (secondUnit d) then (1 : ℝ) else 0) ≤
      2*(k : ℝ)^2*(G+1) := by
  classical
  let n : ℝ := ∑ i, if p i then 1 else 0
  let a : Fin k → ℝ := fun c => ∑ i, if p i ∧ f i = c then 1 else 0
  let F : Fin N → Fin N → ℝ := fun i j => if p i ∧ p j ∧ f i = f j then 1 else 0
  let g : ℝ := ∑ d : Dyad N, F (firstUnit d) (secondUnit d)
  have hasum : ∑ c, a c = n := by
    dsimp [a, n]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : p i <;> simp [hp]
  have hprod (i j : Fin N) : (∑ c : Fin k,
      (if p i ∧ f i = c then (1 : ℝ) else 0) *
        (if p j ∧ f j = c then 1 else 0)) = F i j := by
    by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj, F]
  have hasq : ∑ c, (a c)^2 = 2*g+n := by
    have he : (∑ c, (a c)^2) = ∑ i : Fin N, ∑ j : Fin N, F i j := by
      calc
        _ = ∑ c : Fin k, ∑ i : Fin N, ∑ j : Fin N,
            (if p i ∧ f i = c then (1 : ℝ) else 0) *
              (if p j ∧ f j = c then 1 else 0) := by
          simp only [a, pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.sum_comm]
        _ = ∑ i : Fin N, ∑ j : Fin N, ∑ c : Fin k,
            (if p i ∧ f i = c then (1 : ℝ) else 0) *
              (if p j ∧ f j = c then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intros; rw [Finset.sum_comm]
        _ = _ := by simp_rw [hprod]
    have hs : ∀ i j, F i j = F j i := by
      intro i j
      simp [F, and_comm, and_left_comm, eq_comm]
    have hp := printed_pair_sum F hs
    have hd (i : Fin N) : F i i = if p i then 1 else 0 := by simp [F]
    simp only [Finset.sum_sub_distrib, hd] at hp
    rw [he]
    change 2*g = (∑ i, ∑ j, F i j)-n at hp
    linarith
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin k))
    (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, hasum, hasq] at hc
  have hgn : g ≤ G := hg
  have hkn : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  have hn2 : n^2 ≤ 4*(k : ℝ)^2*(G+1) := by
    have hkg : 0 ≤ ((k : ℝ)^2-k)*G := mul_nonneg (by linarith) hG
    have hkg' : 0 ≤ (k : ℝ)*(G-g) := mul_nonneg (by positivity) (by linarith)
    nlinarith [sq_nonneg (n-(k : ℝ)), sq_nonneg (k : ℝ)]
  let H : Fin N → Fin N → ℝ := fun i j => if p i ∧ p j then 1 else 0
  have hH : ∀ i j, H i j = H j i := by intros; simp [H, and_comm]
  have hpair := printed_pair_sum H hH
  have hrow (i : Fin N) : (∑ j, H i j)-H i i =
      (if p i then n-1 else 0) := by
    by_cases hi : p i <;> simp [H, n, hi]
  have htotal : (∑ i, if p i then n-1 else 0) = n^2-n := by
    have he (i : Fin N) : (if p i then n-1 else 0) = (if p i then (1 : ℝ) else 0)*(n-1) := by
      split_ifs <;> ring
    simp_rw [he]
    rw [← Finset.sum_mul]
    change n*(n-1) = _
    ring
  simp_rw [hrow] at hpair
  rw [htotal] at hpair
  have hn : 0 ≤ n := Finset.sum_nonneg (by intros; split_ifs <;> norm_num)
  change 2*(∑ d : Dyad N, if p (firstUnit d) ∧ p (secondUnit d) then (1 : ℝ) else 0) = _ at hpair
  linarith

def TailB_rare_G {N : ℕ} (ω : Fin N → RareUnit) : ℝ :=
  ∑ d : Dyad N, if rareSmall (ω (firstUnit d)) (ω (secondUnit d)) then 0 else 1

def TailB_rare_B {N : ℕ} (ω : Fin N → RareUnit) (m : ℕ) : ℝ :=
  ∑ d : Dyad N, if (ω (firstUnit d)).m = m ∧ (ω (secondUnit d)).m = m then 1 else 0

def TailB_rare_label {N : ℕ} (ω : Fin N → RareUnit) (m : ℕ) (i : Fin N) : Fin (m+1) :=
  ⟨if h : (ω i).m = m then (ω i).label.val else 0, by
    split_ifs with h
    · simpa only [h] using (ω i).label.isLt
    · omega⟩

theorem TailB_rare_group_count {N : ℕ} (ω : Fin N → RareUnit) (m : ℕ) :
    TailB_rare_B ω m ≤ 2*(m+1 : ℝ)^2*(TailB_rare_G ω+1) := by
  have hG : 0 ≤ TailB_rare_G ω := Finset.sum_nonneg (by intros; split_ifs <;> norm_num)
  have hg : (∑ d : Dyad N, if (ω (firstUnit d)).m = m ∧ (ω (secondUnit d)).m = m ∧
      TailB_rare_label ω m (firstUnit d) = TailB_rare_label ω m (secondUnit d) then (1 : ℝ) else 0) ≤
      TailB_rare_G ω := by
    apply Finset.sum_le_sum
    intro d hd
    split_ifs with h h'
    · have he := congrArg Fin.val h.2.2
      simp only [TailB_rare_label, dif_pos h.1, dif_pos h.2.1] at he
      exact False.elim (h'.2 he)
    · norm_num
    · norm_num
    · norm_num
  simpa only [TailB_rare_B, Nat.cast_add, Nat.cast_one] using
    TailB_rare_category_count (by omega : 1 ≤ m+1) (fun i => (ω i).m = m)
      (TailB_rare_label ω m) (TailB_rare_G ω) hG hg

theorem TailB_rare_delta_count_weight (m : ℕ) :
    rareDelta (m+1)*(2*(m+1 : ℝ)^2) ≤ (1/2 : ℝ)^(m+2) := by
  have hm : (m+1 : ℝ) ≠ 0 := by positivity
  have he : m+3 ≤ (m+1)*(m+1)+2 := by nlinarith
  have hp : (2 : ℝ)^(m+3) ≤ 2^((m+1)*(m+1)+2) :=
    pow_le_pow_right₀ (by norm_num) he
  have heq : rareDelta (m+1)*(2*(m+1 : ℝ)^2) =
      2/(2 : ℝ)^((m+1)*(m+1)+2) := by
    unfold rareDelta
    push_cast
    field_simp
    <;> ring
  rw [heq, _root_.one_div_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [pow_succ, one_mul, mul_assoc, mul_comm, mul_left_comm] using hp

theorem TailB_rare_weight_sum (M : Finset ℕ) :
    (∑ m ∈ M, (1/2 : ℝ)^(m+2)) ≤ 1/2 := by
  have h := summable_geometric_two.sum_le_tsum M (fun i _ => by positivity)
  rw [tsum_geometric_two] at h
  simp_rw [pow_add]
  rw [← Finset.sum_mul]
  norm_num
  linarith

theorem TailB_rare_weighted_small_bound {N : ℕ} (ω : Fin N → RareUnit)
    (hG : 1 ≤ TailB_rare_G ω) :
    (∑ d : Dyad N, if rareSmall (ω (firstUnit d)) (ω (secondUnit d)) then
      TailB_rare_s ω d else 0) ≤ TailB_rare_G ω := by
  classical
  let M : Finset ℕ := univ.image (fun i : Fin N => (ω i).m)
  have hM : (∑ d : Dyad N, if rareSmall (ω (firstUnit d)) (ω (secondUnit d)) then
      TailB_rare_s ω d else 0) ≤ ∑ m ∈ M, rareDelta (m+1)*TailB_rare_B ω m := by
    simp only [TailB_rare_B, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro d hd
    by_cases hs : rareSmall (ω (firstUnit d)) (ω (secondUnit d))
    · rw [if_pos hs]
      have hm : (ω (firstUnit d)).m ∈ M := mem_image.mpr ⟨_, mem_univ _, rfl⟩
      calc
        _ = rareDelta ((ω (firstUnit d)).m+1) *
            (if (ω (firstUnit d)).m = (ω (firstUnit d)).m ∧
              (ω (secondUnit d)).m = (ω (firstUnit d)).m then (1 : ℝ) else 0) := by
          simp [TailB_rare_s, rareS, hs, hs.1]
        _ ≤ _ := Finset.single_le_sum
          (f := fun m => rareDelta (m+1) * (if (ω (firstUnit d)).m = m ∧
            (ω (secondUnit d)).m = m then (1 : ℝ) else 0))
          (fun m _ => mul_nonneg (TailB_rare_delta_pos (m+1) (by omega)).le
            (by split_ifs <;> norm_num)) hm
    · rw [if_neg hs]
      exact Finset.sum_nonneg (fun m _ => mul_nonneg
        (TailB_rare_delta_pos _ (by omega)).le (by split_ifs <;> norm_num))
  calc
    _ ≤ ∑ m ∈ M, rareDelta (m+1)*TailB_rare_B ω m := hM
    _ ≤ ∑ m ∈ M, (1/2 : ℝ)^(m+2)*(TailB_rare_G ω+1) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        _ ≤ rareDelta (m+1)*(2*(m+1 : ℝ)^2*(TailB_rare_G ω+1)) :=
          mul_le_mul_of_nonneg_left (TailB_rare_group_count ω m)
            (TailB_rare_delta_pos _ (by omega)).le
        _ = (rareDelta (m+1)*(2*(m+1 : ℝ)^2))*(TailB_rare_G ω+1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (TailB_rare_delta_count_weight m) (by linarith)
    _ = (∑ m ∈ M, (1/2 : ℝ)^(m+2))*(TailB_rare_G ω+1) := by rw [Finset.sum_mul]
    _ ≤ (1/2)*(TailB_rare_G ω+1) :=
      mul_le_mul_of_nonneg_right (TailB_rare_weight_sum M) (by linarith)
    _ ≤ _ := by linarith

theorem TailB_rare_mean_sign_bound {N : ℕ} (hN : 0 < N) (f : Fin N → Bool) :
    |(∑ i, signValue (f i))/(N : ℝ)| ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_div, abs_of_pos hn, div_le_iff₀ hn, one_mul]
  calc
    _ ≤ ∑ i, |signValue (f i)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [TailB_rare_sign_abs, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]

theorem TailB_rare_G_le_S {N : ℕ} (ω : Fin N → RareUnit) : TailB_rare_G ω ≤ TailB_rare_S ω := by
  apply Finset.sum_le_sum
  intro d hd
  dsimp [TailB_rare_s]
  split_ifs with h
  · exact sq_nonneg _
  · simp [rareS, h]

theorem TailB_rare_W_bound {N : ℕ} (ω : Fin N → RareUnit) (hG : 1 ≤ TailB_rare_G ω) :
    |TailB_rare_W ω| ≤ 2*TailB_rare_G ω := by
  calc
    _ ≤ ∑ d : Dyad N, |TailB_rare_s ω d*TailB_rare_a ω d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2*(∑ d : Dyad N, if rareSmall (ω (firstUnit d)) (ω (secondUnit d)) then
        TailB_rare_s ω d else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      by_cases h : rareSmall (ω (firstUnit d)) (ω (secondUnit d))
      · rw [if_pos h, abs_mul,
          abs_of_pos (show 0 < TailB_rare_s ω d from (TailB_rare_s_bounds _ _).1)]
        have ha : |TailB_rare_a ω d| ≤ 2 := TailB_rare_a_bound _ _
        calc
          _ ≤ TailB_rare_s ω d*2 := mul_le_mul_of_nonneg_left ha
            (show 0 ≤ TailB_rare_s ω d from (TailB_rare_s_bounds _ _).1.le)
          _ = _ := by ring
      · simp [TailB_rare_a, rareA, h]
    _ ≤ _ := mul_le_mul_of_nonneg_left (TailB_rare_weighted_small_bound ω hG) (by norm_num)

theorem TailB_rare_slope_bound {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit)
    (hG : 1 ≤ TailB_rare_G ω) : |TailB_rare_W ω / TailB_rare_S ω| ≤ 2 := by
  rw [abs_div, abs_of_pos (TailB_rare_S_pos hN ω), div_le_iff₀ (TailB_rare_S_pos hN ω)]
  exact (TailB_rare_W_bound ω hG).trans (by linarith [TailB_rare_G_le_S ω])

theorem TailB_rare_small_symm (u v : RareUnit) : rareSmall u v ↔ rareSmall v u := by
  simp only [rareSmall, eq_comm, ne_comm]

theorem TailB_rare_all_small_event {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit)
    (h : ∀ d : Dyad N, rareSmall (ω (firstUnit d)) (ω (secondUnit d))) :
    ∃ m : ℕ, ω ∈ TailB_rare_event N m := by
  have hp (i j : Fin N) (hij : i ≠ j) : rareSmall (ω i) (ω j) := by
    rcases lt_or_gt_of_ne hij with hij | hji
    · have he := printed_mkDyad_endpoints i j hij
      simpa only [he.1, he.2] using h (printed_mkDyad i j hij.ne)
    · have he := printed_mkDyad_endpoints j i hji
      exact (TailB_rare_small_symm _ _).mpr
        (by simpa only [he.1, he.2] using h (printed_mkDyad j i hji.ne))
  let i0 : Fin N := ⟨0, by omega⟩
  refine ⟨(ω i0).m, ?_, ?_⟩
  · intro i
    by_cases hi : i = i0
    · rw [hi]
    · exact (hp i i0 hi).1
  · intro i j he
    by_contra hij
    exact (hp i j hij).2 he

theorem TailB_rare_nonsmall_count {N : ℕ} (ω : Fin N → RareUnit) (d : Dyad N)
    (hd : ¬rareSmall (ω (firstUnit d)) (ω (secondUnit d))) : 1 ≤ TailB_rare_G ω := by
  have h := Finset.single_le_sum (s := (univ : Finset (Dyad N)))
    (f := fun d => if rareSmall (ω (firstUnit d)) (ω (secondUnit d)) then (0 : ℝ) else 1)
    (fun _ _ => by split_ifs <;> norm_num) (mem_univ d)
  simpa only [TailB_rare_G, if_neg hd] using h

theorem TailB_rare_small_or_count {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) :
    (∃ m : ℕ, ω ∈ TailB_rare_event N m) ∨ 1 ≤ TailB_rare_G ω := by
  by_cases hG : 1 ≤ TailB_rare_G ω
  · exact Or.inr hG
  · left
    apply TailB_rare_all_small_event hN ω
    intro d
    by_contra hd
    exact hG (TailB_rare_nonsmall_count ω d hd)

theorem TailB_rare_event_r {N m : ℕ} (hN : 2 ≤ N) {ω : Fin N → RareUnit}
    (hω : ω ∈ TailB_rare_event N m) (d : Dyad N) :
    TailB_rare_r ω d = signValue (ω (firstUnit d)).A+signValue (ω (secondUnit d)).A-
      2*TailB_rare_Abar ω := by
  have hb := TailB_rare_event_slope hN hω
  rw [TailB_rare_exact_fit hN] at hb
  change TailB_rare_W ω / TailB_rare_S ω = _ at hb
  simp only [TailB_rare_r, TailB_rare_event_s hω, TailB_rare_event_a hω, hb]
  field_simp [ne_of_gt (TailB_rare_delta_pos (m+1) (by omega))]

theorem TailB_rare_r_bound {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit) (d : Dyad N) :
    |TailB_rare_r ω d| ≤ 4 := by
  rcases TailB_rare_small_or_count hN ω with ⟨m, hω⟩ | hG
  · rw [TailB_rare_event_r hN hω]
    have hm := TailB_rare_mean_sign_bound (by omega : 0 < N) (fun i => (ω i).A)
    change |TailB_rare_Abar ω| ≤ 1 at hm
    have ha : |signValue (ω (firstUnit d)).A+signValue (ω (secondUnit d)).A| ≤ 2 := by
      simpa only [TailB_rare_sign_abs, one_add_one_eq_two] using
        abs_add_le (signValue (ω (firstUnit d)).A) (signValue (ω (secondUnit d)).A)
    calc
      _ ≤ |signValue (ω (firstUnit d)).A+signValue (ω (secondUnit d)).A| +
          |2*TailB_rare_Abar ω| := abs_sub _ _
      _ ≤ _ := by rw [abs_mul]; norm_num; linarith
  · have hs := TailB_rare_s_bounds (ω (firstUnit d)) (ω (secondUnit d))
    have hb := TailB_rare_slope_bound hN ω hG
    have ha := TailB_rare_a_bound (ω (firstUnit d)) (ω (secondUnit d))
    calc
      _ ≤ |TailB_rare_a ω d| + |TailB_rare_s ω d*(TailB_rare_W ω/TailB_rare_S ω)| := abs_sub _ _
      _ ≤ 2+1*2 := by
        apply add_le_add ha
        rw [abs_mul, abs_of_pos (show 0 < TailB_rare_s ω d from hs.1)]
        exact mul_le_mul hs.2 hb (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num

theorem TailB_rare_residual_bound {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit)
    (d : Dyad N) (t : Fin 2) :
    |repeatedY rareRepeated ω d t-dot (repeatedX rareRepeated ω d t)
      (repeatedOLS rareRepeated ω)| ≤ 8 := by
  rw [TailB_rare_residual_formula hN]
  have hu : |TailB_rare_u ω d| ≤ 2 := by
    simpa only [TailB_rare_u, TailB_rare_sign_abs, one_add_one_eq_two] using
      abs_add_le (signValue (ω (firstUnit d)).B) (signValue (ω (secondUnit d)).B)
  have hmean : |TailB_rare_U ω / Dreal N| ≤ 2 := by
    rw [TailB_rare_U_mean hN, abs_mul]
    norm_num
    have := TailB_rare_mean_sign_bound (by omega : 0 < N) (fun i => (ω i).B)
    change |TailB_rare_Bbar ω| ≤ 1 at this
    linarith
  have hr := TailB_rare_r_bound hN ω d
  change |TailB_rare_u ω d-TailB_rare_U ω/Dreal N +
    (if t.val = 0 then 1 else -1)*TailB_rare_r ω d| ≤ 8
  calc
    _ ≤ |TailB_rare_u ω d-TailB_rare_U ω/Dreal N| +
        |(if t.val = 0 then 1 else -1)*TailB_rare_r ω d| := abs_add_le _ _
    _ ≤ (|TailB_rare_u ω d|+|TailB_rare_U ω/Dreal N|)+4 := by
      apply add_le_add (abs_sub _ _)
      split_ifs <;> simpa only [one_mul, neg_one_mul, abs_neg] using hr
    _ ≤ _ := by linarith

theorem TailB_rare_variance_abs_bound {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → RareUnit)
    (hG : 1 ≤ TailB_rare_G ω) :
    |(repeatedVariance rareRepeated ω) 1 1| ≤ 16*(Dreal N)^2 := by
  have hS : 1 ≤ TailB_rare_S ω := hG.trans (TailB_rare_G_le_S ω)
  have hq (d : Dyad N) : |TailB_rare_s ω d*TailB_rare_r ω d| ≤ 4 := by
    rw [abs_mul, abs_of_pos (show 0 < TailB_rare_s ω d from (TailB_rare_s_bounds _ _).1)]
    exact (mul_le_mul (TailB_rare_s_bounds _ _).2 (TailB_rare_r_bound hN ω d)
      (abs_nonneg _) (by norm_num)).trans (by norm_num)
  rw [TailB_rare_variance_formula hN, abs_div, abs_of_pos (sq_pos_of_pos (TailB_rare_S_pos hN ω))]
  apply (div_le_iff₀ (sq_pos_of_pos (TailB_rare_S_pos hN ω))).2
  calc
    _ ≤ ∑ d : Dyad N, ∑ f : Dyad N, (16 : ℝ) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro f hf
      split_ifs
      · rw [abs_mul]
        exact (mul_le_mul (hq d) (hq f) (abs_nonneg _) (by norm_num)).trans (by norm_num)
      · norm_num
    _ = 16*(Dreal N)^2 := by
      simp only [sum_const, card_univ, nsmul_eq_mul, printed_card_real]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (by nlinarith : 1 ≤ (TailB_rare_S ω)^2)
        (show 0 ≤ 16*(Dreal N)^2 by positivity)
      simpa only [mul_one] using h

theorem TailB_rare_negative_part_bound {N : ℕ} (hN : 4 ≤ N) (ω : Fin N → RareUnit) :
    max (-((repeatedVariance rareRepeated ω) 1 1)) 0 ≤ 16*(Dreal N)^2 := by
  rcases TailB_rare_small_or_count (by omega) ω with ⟨m, hω⟩ | hG
  · have hV : 0 ≤ (repeatedVariance rareRepeated ω) 1 1 := by
      rw [TailB_rare_event_variance (by omega) hω]
      have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Finset.sum_nonneg (by intros; positivity))
      · positivity
    rw [max_eq_right (by linarith)]
    positivity
  · exact max_le ((neg_le_abs _).trans (TailB_rare_variance_abs_bound (by omega) ω hG)) (by positivity)

theorem TailB_rare_negative_part_integral (N : ℕ) (hN : 4 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal (max (-((repeatedVariance rareRepeated ω) 1 1)) 0)
      ∂repeatedLaw rareRepeated N) < ∞ := by
  letI TailB_rare_probability_local : IsProbabilityMeasure rareLaw := TailB_rare_probability
  calc
    _ ≤ ∫⁻ _ : Fin N → RareUnit, ENNReal.ofReal (16*(Dreal N)^2) ∂repeatedLaw rareRepeated N :=
      lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (TailB_rare_negative_part_bound hN ω))
    _ = ENNReal.ofReal (16*(Dreal N)^2) := by
      rw [lintegral_const]
      change _ * (Measure.pi (fun _ : Fin N => rareLaw)) Set.univ = _
      simp
    _ < ∞ := ENNReal.ofReal_lt_top

/-! Exact atom masses and lower bounds for extended integrals. -/

def TailB_rare_p (m : ℕ) : ℝ := (2 : ℝ)^(-(m+1 : ℤ))/((m+1 : ℝ)*4)

theorem TailB_rare_p_pos (m : ℕ) : 0 < TailB_rare_p m := by unfold TailB_rare_p; positivity

theorem TailB_rare_atom (u : RareUnit) : rareLaw {u} = ENNReal.ofReal (TailB_rare_p u.m) := by
  rw [rareLaw, Measure.sum_apply _ (measurableSet_singleton u)]
  rw [tsum_eq_single u.m]
  · cases u with | mk m c a b =>
      simp only [Measure.smul_apply, Measure.finsetSum_apply, measurableSet_singleton,
        Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul]
      simp only [Fintype.sum_bool]
      cases a <;> cases b <;> simp [TailB_rare_p, RareUnit.mk.injEq]
  · intro m hm
    have hne (c : Fin (m+1)) (a b : Bool) : (RareUnit.mk m c a b) ≠ u := by
      intro he
      exact hm (congrArg RareUnit.m he)
    simp [Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply, hne]

theorem TailB_rare_row_atom {N : ℕ} (ω : Fin N → RareUnit) :
    repeatedLaw rareRepeated N {ω} = ∏ i, ENNReal.ofReal (TailB_rare_p (ω i).m) := by
  letI TailB_rare_probability_atom_local : IsProbabilityMeasure rareLaw := TailB_rare_probability
  change Measure.pi (fun _ : Fin N => rareLaw) {ω} = _
  rw [Measure.pi_singleton]
  simp_rw [TailB_rare_atom]


theorem TailB_rare_point_integral_bound {N m : ℕ} (f : (Fin N → RareUnit) → ℝ)
    (ω : Fin N → RareUnit) (hω : ∀ i, (ω i).m = m) :
    ENNReal.ofReal (f ω*(TailB_rare_p m)^N) ≤
      ∫⁻ z, ENNReal.ofReal (f z) ∂repeatedLaw rareRepeated N := by
  have hm : repeatedLaw rareRepeated N {ω} = ENNReal.ofReal ((TailB_rare_p m)^N) := by
    rw [TailB_rare_row_atom]
    simp only [hω, prod_const, card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow (TailB_rare_p_pos m).le]
  rw [lintegral_countable']
  have h := ENNReal.le_tsum (f := fun z : Fin N → RareUnit =>
    ENNReal.ofReal (f z)*repeatedLaw rareRepeated N {z}) ω
  rw [hm, ← ENNReal.ofReal_mul' (pow_nonneg (TailB_rare_p_pos m).le N)] at h
  exact h

theorem TailB_rare_p_eq (m : ℕ) :
    TailB_rare_p m = 1/((m+1 : ℝ)*(2 : ℝ)^(m+3)) := by
  unfold TailB_rare_p
  rw [show -(m+1 : ℤ) = -((m+1 : ℕ) : ℤ) by omega, _root_.zpow_neg, zpow_natCast]
  rw [show m+3 = (m+1)+2 by omega, pow_add]
  norm_num
  field_simp
  <;> ring

theorem TailB_rare_p_lower (m : ℕ) :
    1/(2 : ℝ)^(2*(m+1)+2) ≤ TailB_rare_p m := by
  have ht : (m+1 : ℝ) ≤ (2 : ℝ)^(m+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m+1)).le
  rw [TailB_rare_p_eq]
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (m+1 : ℝ)*2^(m+3) ≤ (2 : ℝ)^(m+1)*2^(m+3) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem TailB_rare_atom_growth (N m : ℕ) (hm : 4*N+2 ≤ m+1) :
    (2 : ℝ)^(m+1) ≤ (TailB_rare_p m)^N / rareDelta (m+1) := by
  have ht : (1 : ℝ) ≤ m+1 := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
  have hd : rareDelta (m+1) ≤ 1/(2 : ℝ)^((m+1)*(m+1)+2) := by
    unfold rareDelta
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    exact le_mul_of_one_le_left (by positivity) (by nlinarith)
  have he : (m+1)+(2*(m+1)+2)*N ≤ (m+1)*(m+1)+2 := by
    have h1 : 2*N+2 ≤ m+1 := by omega
    have h2 : (2*N+2)*(m+1) ≤ (m+1)*(m+1) := Nat.mul_le_mul_right (m+1) h1
    nlinarith
  apply (le_div_iff₀ (TailB_rare_delta_pos (m+1) (by omega))).2
  calc
    _ ≤ (2 : ℝ)^(m+1)*(1/(2 : ℝ)^((m+1)*(m+1)+2)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ 1/(2 : ℝ)^((2*(m+1)+2)*N) := by
      rw [mul_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      rw [one_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) he
    _ = (1/(2 : ℝ)^(2*(m+1)+2))^N := by rw [_root_.one_div_pow, ← pow_mul]
    _ ≤ _ := by gcongr; exact TailB_rare_p_lower m

theorem TailB_rare_infinite_of_atoms (N : ℕ) (f : (Fin N → RareUnit) → ℝ)
    (c : ℝ) (hc : 0 < c)
    (s : (m : ℕ) → N ≤ m+1 → Fin N → RareUnit)
    (hs : ∀ m h i, (s m h i).m = m)
    (hf : ∀ m h, c/rareDelta (m+1) ≤ f (s m h)) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂repeatedLaw rareRepeated N) = ∞ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  obtain ⟨k, hk⟩ := exists_nat_gt ((r : ℝ)/c)
  let m : ℕ := max k (4*N+2)
  have hm : 4*N+2 ≤ m+1 := by dsimp [m]; omega
  have hNm : N ≤ m+1 := by omega
  have hk' : (r : ℝ) ≤ c*(m+1 : ℝ) := by
    have hkm : (k : ℝ) ≤ m+1 := by exact_mod_cast (show k ≤ m+1 by dsimp [m]; omega)
    have hrk : (r : ℝ) < (k : ℝ)*c := (div_lt_iff₀ hc).mp hk
    nlinarith
  have ht : (m+1 : ℝ) ≤ (2 : ℝ)^(m+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m+1)).le
  have hl : (r : ℝ) ≤ f (s m hNm)*(TailB_rare_p m)^N := by
    calc
      _ ≤ c*(m+1 : ℝ) := hk'
      _ ≤ c*(2 : ℝ)^(m+1) := mul_le_mul_of_nonneg_left ht hc.le
      _ ≤ c*((TailB_rare_p m)^N/rareDelta (m+1)) :=
        mul_le_mul_of_nonneg_left (TailB_rare_atom_growth N m hm) hc.le
      _ = (c/rareDelta (m+1))*(TailB_rare_p m)^N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hf m hNm) (pow_nonneg (TailB_rare_p_pos m).le N)
  calc
    (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := by simp
    _ ≤ ENNReal.ofReal (f (s m hNm)*(TailB_rare_p m)^N) := ENNReal.ofReal_le_ofReal hl
    _ ≤ _ := TailB_rare_point_integral_bound f (s m hNm) (hs m hNm)

def TailB_rare_sample (N m : ℕ) (hNm : N ≤ m+1) (A B : Fin N → Bool) : Fin N → RareUnit :=
  fun i => ⟨m, ⟨i.val, lt_of_lt_of_le i.isLt hNm⟩, A i, B i⟩

theorem TailB_rare_sample_event (N m : ℕ) (hNm : N ≤ m+1) (A B : Fin N → Bool) :
    TailB_rare_sample N m hNm A B ∈ TailB_rare_event N m := by
  refine ⟨fun _ => rfl, ?_⟩
  intro i j h
  exact Fin.ext h

theorem TailB_rare_all_positive_slope (N m : ℕ) (hN : 2 ≤ N) (hNm : N ≤ m+1) :
    repeatedOLS rareRepeated (TailB_rare_sample N m hNm (fun _ => true) (fun _ => true)) 1 =
      2/rareDelta (m+1) := by
  rw [TailB_rare_event_slope hN (TailB_rare_sample_event _ _ _ _ _)]
  have ha : TailB_rare_Abar (TailB_rare_sample N m hNm (fun _ => true) (fun _ => true)) = 1 := by
    simp only [TailB_rare_Abar, TailB_rare_sample, signValue, Bool.true_eq, if_true,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast (show N ≠ 0 by omega))
  rw [ha, mul_one]

theorem TailB_rare_coefficient_integrals (N : ℕ) (hN : 3 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal ((repeatedOLS rareRepeated ω 1)^2) ∂repeatedLaw rareRepeated N) = ∞ ∧
    (∫⁻ ω, ENNReal.ofReal |repeatedOLS rareRepeated ω 1| ∂repeatedLaw rareRepeated N) = ∞ := by
  let s := fun m h => TailB_rare_sample N m h (fun _ => true) (fun _ => true)
  have hs : ∀ m h i, (s m h i).m = m := by intros; rfl
  have hb : ∀ m h, repeatedOLS rareRepeated (s m h) 1 = 2/rareDelta (m+1) := by
    intros; exact TailB_rare_all_positive_slope _ _ (by omega) _
  constructor
  · apply TailB_rare_infinite_of_atoms N _ 2 (by norm_num) s hs
    intro m h
    rw [hb]
    have hd := TailB_rare_delta_pos (m+1) (by omega)
    have hd' := TailB_rare_delta_le_one (m+1) (by omega)
    have hh : (1 : ℝ) ≤ 2/rareDelta (m+1) := (le_div_iff₀ hd).2 (by linarith)
    nlinarith
  · apply TailB_rare_infinite_of_atoms N _ 2 (by norm_num) s hs
    intro m h
    rw [hb, abs_of_pos (div_pos (by norm_num) (TailB_rare_delta_pos (m+1) (by omega)))]

theorem TailB_rare_sign_square (b : Bool) : (signValue b)^2 = 1 := by cases b <;> norm_num [signValue]

theorem TailB_rare_A_dispersion {N : ℕ} (hN : 0 < N) (ω : Fin N → RareUnit) :
    (∑ i, (signValue (ω i).A-TailB_rare_Abar ω)^2) =
      (N : ℝ)-(N : ℝ)*(TailB_rare_Abar ω)^2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he (i : Fin N) : (signValue (ω i).A-TailB_rare_Abar ω)^2 =
      1-2*TailB_rare_Abar ω*signValue (ω i).A+(TailB_rare_Abar ω)^2 := by
    nlinarith [TailB_rare_sign_square (ω i).A]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  unfold TailB_rare_Abar
  field_simp [hn]
  <;> ring

def TailB_rare_one_negative {N : ℕ} (i : Fin N) : Bool := if i.val = 0 then false else true

theorem TailB_rare_one_negative_sum (N : ℕ) (hN : 0 < N) :
    (∑ i : Fin N, signValue (TailB_rare_one_negative i)) = (N : ℝ)-2 := by
  let i0 : Fin N := ⟨0, hN⟩
  have he (i : Fin N) : signValue (TailB_rare_one_negative i) =
      1-2*(if i = i0 then (1 : ℝ) else 0) := by
    by_cases hi : i = i0
    · subst i; norm_num [TailB_rare_one_negative, i0, signValue]
    · have hv : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
      simp [TailB_rare_one_negative, hi, hv, signValue]
  simp only [he, Finset.sum_sub_distrib, Finset.mul_sum,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp

theorem TailB_rare_one_negative_dispersion (N m : ℕ) (hN : 2 ≤ N) (hNm : N ≤ m+1) :
    (∑ i, (signValue (TailB_rare_sample N m hNm TailB_rare_one_negative (fun _ => true) i).A-
      TailB_rare_Abar (TailB_rare_sample N m hNm TailB_rare_one_negative (fun _ => true)))^2) =
      4*((N : ℝ)-1)/(N : ℝ) := by
  rw [TailB_rare_A_dispersion (by omega)]
  have hm : TailB_rare_Abar (TailB_rare_sample N m hNm TailB_rare_one_negative (fun _ => true)) =
      ((N : ℝ)-2)/(N : ℝ) := by
    unfold TailB_rare_Abar
    simp only [TailB_rare_sample]
    rw [TailB_rare_one_negative_sum _ (by omega)]
  rw [hm]
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (show N ≠ 0 by omega)]
  <;> ring

theorem TailB_rare_positive_part_integral (N : ℕ) (hN : 4 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal (max ((repeatedVariance rareRepeated ω) 1 1) 0)
      ∂repeatedLaw rareRepeated N) = ∞ := by
  let s := fun m h => TailB_rare_sample N m h TailB_rare_one_negative (fun _ => true)
  let c : ℝ := ((N : ℝ)-2)*((N : ℝ)-3)*(4*((N : ℝ)-1)/(N : ℝ))/(Dreal N)^2
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos
      (mul_pos (by linarith) (by linarith)) (div_pos (by linarith) (by linarith)))
      (sq_pos_of_pos (TailB_rare_D_pos (by omega)))
  apply TailB_rare_infinite_of_atoms N _ c hc s (by intros; rfl)
  intro m h
  have hv : (repeatedVariance rareRepeated (s m h)) 1 1 = c/(rareDelta (m+1))^2 := by
    rw [TailB_rare_event_variance (by omega) (TailB_rare_sample_event _ _ _ _ _),
      TailB_rare_one_negative_dispersion _ _ (by omega)]
    dsimp [c]
    ring
  rw [hv, max_eq_left (by positivity)]
  have hd := TailB_rare_delta_pos (m+1) (by omega)
  have hd' := TailB_rare_delta_le_one (m+1) (by omega)
  apply (div_le_div_iff₀ hd (sq_pos_of_pos hd)).2
  exact mul_le_mul_of_nonneg_left (by nlinarith : (rareDelta (m+1))^2 ≤ rareDelta (m+1)) hc.le

/-- The finite-pathology part of P018-T19, at the original thresholds. -/
theorem TailB_rare_finite_pathologies :
    IsProbabilityMeasure rareLaw ∧ RepeatedStanding rareRepeated ∧
    (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → RareUnit, (repeatedGram rareRepeated ω).det > 0 ∧
      (∀ d : Dyad N, ∀ t : Fin 2, |repeatedY rareRepeated ω d t -
        dot (repeatedX rareRepeated ω d t) (repeatedOLS rareRepeated ω)| ≤ 8)) ∧
    (∀ N : ℕ, 3 ≤ N →
      (∫⁻ ω, ENNReal.ofReal ((repeatedOLS rareRepeated ω 1)^2) ∂ repeatedLaw rareRepeated N) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal |repeatedOLS rareRepeated ω 1| ∂ repeatedLaw rareRepeated N) = ∞) ∧
    (∀ N : ℕ, 4 ≤ N →
      (∫⁻ ω, ENNReal.ofReal (max ((repeatedVariance rareRepeated ω) 1 1) 0) ∂ repeatedLaw rareRepeated N) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal (max (-((repeatedVariance rareRepeated ω) 1 1)) 0) ∂ repeatedLaw rareRepeated N) < ∞) := by
  refine ⟨TailB_rare_probability, TailB_rare_standing, ?_, TailB_rare_coefficient_integrals, ?_⟩
  · intro N hN ω
    exact ⟨TailB_rare_gram_pos hN ω, TailB_rare_residual_bound hN ω⟩
  · intro N hN
    exact ⟨TailB_rare_positive_part_integral N hN, TailB_rare_negative_part_integral N hN⟩

end AronowAudit.P018.Wave1
