import AronowAudit.P018.Wave1.Gap.GP0181B1
import AronowAudit.P018.Wave1.PrintedScalarCorollaries.N2

/-! P018-T9: the positive, bounded, concentrated-weight counterexample. -/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

local instance instProbabilityFairGLP0182B4 : IsProbabilityMeasure fairLaw := by
  unfold fairLaw
  infer_instance

local instance instProbabilitySampleGLP0182B4 (N : ℕ) :
    IsProbabilityMeasure (unitSampleLaw signKernel N) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => fairLaw))
  infer_instance

def concentrated_weights_q {N : ℕ} (i : Fin N) : ℝ := (1/2 : ℝ) ^ (i.val+1)
def concentrated_weights_x (N : ℕ) : ℝ := (1/2 : ℝ)^N
def concentrated_weights_S (N : ℕ) : ℝ := ∑ i : Fin N, concentrated_weights_q i
def concentrated_weights_G (N p : ℕ) : ℝ := ∑ i : Fin N, concentrated_weights_q i ^ p
def concentrated_weights_W (N : ℕ) : ℝ := ∑ d : Dyad N, concentratedWeight d

theorem concentrated_weights_factor {N : ℕ} (d : Dyad N) :
    concentratedWeight d = concentrated_weights_q (firstUnit d) *
      concentrated_weights_q (secondUnit d) := by
  unfold concentratedWeight concentrated_weights_q
  have he : ((firstUnit d).val + (secondUnit d).val + 2 : ℤ) =
      (((firstUnit d).val+1+((secondUnit d).val+1) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [_root_.zpow_neg, he, zpow_natCast]
  simp only [pow_add, one_div, inv_pow, _root_.mul_inv_rev]
  ring

theorem concentrated_weights_pair_linear {N : ℕ} (q u : Fin N → ℝ) :
    (∑ d : Dyad N, q (firstUnit d) * q (secondUnit d) *
      (u (firstUnit d) + u (secondUnit d))) =
    ∑ i, q i * ((∑ j, q j) - q i) * u i := by
  have h := printed_pair_sum (fun i j => q i*q j*(u i+u j))
    (fun i j => by ring)
  have hr (i : Fin N) :
      (∑ j, q i*q j*(u i+u j)) - q i*q i*(u i+u i) =
      q i*u i*(∑ j, q j) + q i*(∑ j, q j*u j) - 2*q i^2*u i := by
    simp_rw [mul_add, mul_assoc]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  simp_rw [hr] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum] at h
  have ht : (∑ i, q i * ((∑ j, q j) - q i) * u i) =
      (∑ i, q i*u i)*(∑ j, q j) - ∑ i, q i^2*u i := by
    simp_rw [mul_sub, sub_mul]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      ring
  rw [ht]
  have hsum2 : (∑ i, 2*q i^2*u i) = 2*∑ i, q i^2*u i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum2] at h
  nlinarith [h]

theorem concentrated_weights_G_formula (N p : ℕ) (hp : 0 < p) :
    concentrated_weights_G N p = (1 - concentrated_weights_x N ^ p) / (2^p-1) := by
  have hden : (2 : ℝ)^p - 1 ≠ 0 := by
    have : (1 : ℝ) < 2^p := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  induction N with
  | zero => simp [concentrated_weights_G, concentrated_weights_x]
  | succ N ih =>
    rw [concentrated_weights_G, Fin.sum_univ_castSucc]
    simp only [concentrated_weights_q, Fin.val_castSucc, Fin.val_last]
    change concentrated_weights_G N p + ((1/2 : ℝ)^(N+1))^p = _
    rw [ih]
    simp only [concentrated_weights_x, pow_succ, mul_pow, one_div, inv_pow]
    field_simp
    <;> ring

theorem concentrated_weights_S_formula (N : ℕ) :
    concentrated_weights_S N = 1-concentrated_weights_x N := by
  have h := concentrated_weights_G_formula N 1 (by omega)
  norm_num [concentrated_weights_G] at h
  exact h

theorem concentrated_weights_W_formula (N : ℕ) :
    concentrated_weights_W N =
      (1-concentrated_weights_x N)*(1-2*concentrated_weights_x N)/3 := by
  have h := printed_pair_sum (fun i j : Fin N => concentrated_weights_q i * concentrated_weights_q j)
    (fun i j => mul_comm _ _)
  simp_rw [← concentrated_weights_factor] at h
  change 2 * concentrated_weights_W N = _ at h
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
  have hg := concentrated_weights_G_formula N 2 (by omega)
  change (∑ i : Fin N, concentrated_weights_q i ^ 2) = _ at hg
  simp_rw [← pow_two] at h
  change 2 * concentrated_weights_W N = (concentrated_weights_S N)^2 -
    concentrated_weights_G N 2 at h
  rw [concentrated_weights_G_formula N 2 (by omega), concentrated_weights_S_formula] at h
  norm_num at h
  nlinarith

theorem concentrated_weights_x_bounds {N : ℕ} (hN : 2 ≤ N) :
    0 < concentrated_weights_x N ∧ concentrated_weights_x N ≤ 1/4 := by
  constructor
  · exact pow_pos (by norm_num) _
  · have h := pow_le_pow_of_le_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) ≤ 1) hN
    norm_num [concentrated_weights_x] at *
    exact h

theorem concentrated_weights_W_lower {N : ℕ} (hN : 2 ≤ N) :
    (1/8 : ℝ) ≤ concentrated_weights_W N := by
  rw [concentrated_weights_W_formula]
  obtain ⟨hx0, hx⟩ := concentrated_weights_x_bounds hN
  nlinarith [sq_nonneg (concentrated_weights_x N - 1/4)]

theorem concentrated_weights_bounds {N : ℕ} (d : Dyad N) :
    0 < concentratedWeight d ∧ concentratedWeight d ≤ 1/8 := by
  rw [concentrated_weights_factor]
  have hij := printed_endpoints_lt d
  have hn : 3 ≤ (firstUnit d).val+1+((secondUnit d).val+1) := by
    have : (firstUnit d).val < (secondUnit d).val := hij
    omega
  simp only [concentrated_weights_q, ← pow_add]
  constructor
  · positivity
  · have h := pow_le_pow_of_le_one (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num : (1/2 : ℝ) ≤ 1) hn
    norm_num at h
    exact h

def concentrated_weights_c {N : ℕ} (i : Fin N) : ℝ :=
  concentrated_weights_q i * (concentrated_weights_S N - concentrated_weights_q i) /
    concentrated_weights_W N

theorem concentrated_weights_ols_scalar {N : ℕ} (ω : Fin N → Bool) :
    weightedOLS signKernel concentratedWeight ω 0 =
      (concentrated_weights_W N)⁻¹ *
        ∑ d : Dyad N, concentratedWeight d * response signKernel ω d := by
  have hg : weightedGram signKernel concentratedWeight ω =
      Matrix.of (fun _ _ : Fin 1 => concentrated_weights_W N) := by
    ext a b
    fin_cases a; fin_cases b
    simp [weightedGram, concentrated_weights_W, Matrix.sum_apply, outer,
      design, signKernel, Matrix.of_apply]
  rw [weightedOLS, hg, Matrix.inv_def]
  simp [Matrix.det_unique, Matrix.adjugate_subsingleton, Ring.inverse_eq_inv,
    Matrix.mulVec, dotProduct, Fin.sum_univ_one, Finset.sum_apply, score,
    design, signKernel]

theorem concentrated_weights_ols_linear {N : ℕ} (ω : Fin N → Bool) :
    weightedOLS signKernel concentratedWeight ω 0 =
      ∑ i, concentrated_weights_c i * signValue (ω i) := by
  rw [concentrated_weights_ols_scalar]
  simp_rw [concentrated_weights_factor, response, signKernel]
  rw [concentrated_weights_pair_linear concentrated_weights_q (fun i => signValue (ω i))]
  simp only [concentrated_weights_c, concentrated_weights_S, div_eq_mul_inv,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem concentrated_weights_variance (N : ℕ) :
    variance (fun ω => weightedOLS signKernel concentratedWeight ω 0)
      (unitSampleLaw signKernel N) = ∑ i : Fin N, concentrated_weights_c i ^ 2 := by
  simp_rw [concentrated_weights_ols_linear]
  have h := variance_sum_pi (μ := fun _ : Fin N => fairLaw)
    (X := fun i b => concentrated_weights_c i * signValue b)
    (fun i => PrintedScalarCorollaries.sign_memLp.const_mul _)
  have he : (∑ i : Fin N, fun ω : Fin N → Bool => concentrated_weights_c i * signValue (ω i)) =
      (fun ω => ∑ i, concentrated_weights_c i * signValue (ω i)) := by ext ω; simp
  rw [he] at h
  simpa only [variance_const_mul, PrintedScalarCorollaries.sign_variance,
    mul_one, unitSampleLaw, signKernel] using h

theorem concentrated_weights_variance_lower {N : ℕ} (hN : 2 ≤ N) :
    (9/16 : ℝ) ≤ variance (fun ω => weightedOLS signKernel concentratedWeight ω 0)
      (unitSampleLaw signKernel N) := by
  let i : Fin N := ⟨0, by omega⟩
  obtain ⟨hx0, hx⟩ := concentrated_weights_x_bounds hN
  have hs : 0 < 1-concentrated_weights_x N := by linarith
  have hs' : 0 < 1-2*concentrated_weights_x N := by linarith
  have hc : concentrated_weights_c i = 3/(4*(1-concentrated_weights_x N)) := by
    simp only [concentrated_weights_c, concentrated_weights_S_formula,
      concentrated_weights_W_formula, concentrated_weights_q, i]
    norm_num
    field_simp
    <;> ring
  have hcl : (3/4 : ℝ) ≤ concentrated_weights_c i := by
    rw [hc, le_div_iff₀ (by positivity)]
    nlinarith
  rw [concentrated_weights_variance]
  have hsingle : concentrated_weights_c i ^ 2 ≤ ∑ j : Fin N, concentrated_weights_c j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (mem_univ i)
  nlinarith

theorem concentrated_weights_variance_formula (N : ℕ) :
    variance (fun ω => weightedOLS signKernel concentratedWeight ω 0)
      (unitSampleLaw signKernel N) =
      (concentrated_weights_S N ^ 2 * concentrated_weights_G N 2 -
        2 * concentrated_weights_S N * concentrated_weights_G N 3 +
          concentrated_weights_G N 4) / concentrated_weights_W N ^ 2 := by
  rw [concentrated_weights_variance]
  calc
    _ = ∑ i : Fin N, (concentrated_weights_S N ^ 2 * concentrated_weights_q i ^ 2 -
        2 * concentrated_weights_S N * concentrated_weights_q i ^ 3 +
          concentrated_weights_q i ^ 4) / concentrated_weights_W N ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [concentrated_weights_c]
      ring
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, concentrated_weights_G]

theorem concentrated_weights_variance_limit :
    Tendsto (fun N : ℕ => variance
      (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N))
      atTop (𝓝 (36/35)) := by
  have hx : Tendsto concentrated_weights_x atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hS : Tendsto concentrated_weights_S atTop (𝓝 1) := by
    change Tendsto (fun N => concentrated_weights_S N) atTop (𝓝 1)
    simp only [concentrated_weights_S_formula]
    convert tendsto_const_nhds.sub hx using 1 <;> norm_num
  have hW : Tendsto concentrated_weights_W atTop (𝓝 (1/3)) := by
    change Tendsto (fun N => concentrated_weights_W N) atTop (𝓝 (1/3))
    simp only [concentrated_weights_W_formula]
    convert ((tendsto_const_nhds.sub hx).mul
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hx))).div_const 3 using 1 <;> norm_num
  have hG (p : ℕ) (hp : 0 < p) :
      Tendsto (fun N => concentrated_weights_G N p) atTop (𝓝 (1/(2^p-1))) := by
    simp only [concentrated_weights_G_formula _ _ hp]
    convert (tendsto_const_nhds.sub (hx.pow p)).div_const (2^p-1) using 1 <;>
      simp [Nat.ne_of_gt hp]
  simp_rw [concentrated_weights_variance_formula]
  convert (((hS.pow 2).mul (hG 2 (by omega))).sub
    ((tendsto_const_nhds.mul hS).mul (hG 3 (by omega)))).add
      (hG 4 (by omega)) |>.div (hW.pow 2) (by norm_num) using 1 <;> norm_num

def concentrated_weights_tail (N : ℕ) : ℝ :=
  ∑ i : Fin N, if 8 ≤ i.val then concentrated_weights_q i else 0

def concentrated_weights_event (N : ℕ) : Set (Fin N → Bool) :=
  {ω | ∀ i : Fin N, i.val < 8 → ω i = true}

def concentrated_weights_distance {N : ℕ} (ω : Fin N → Bool) : ℝ :=
  ∑ d : Dyad N, concentratedWeight d * |response signKernel ω d - 2|

theorem concentrated_weights_q_pos {N : ℕ} (i : Fin N) :
    0 < concentrated_weights_q i := by
  exact pow_pos (by norm_num) _

theorem concentrated_weights_tail_formula {N : ℕ} (hN : 8 ≤ N) :
    concentrated_weights_tail N = (1/256 : ℝ) - concentrated_weights_x N := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hi (i : Fin 8) : ¬8 ≤ i.val := by omega
    norm_num [concentrated_weights_tail, hi, concentrated_weights_x]
  | succ N hN ih =>
    rw [concentrated_weights_tail, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, if_pos hN]
    change concentrated_weights_tail N + (1/2 : ℝ)^(N+1) = _
    rw [ih]
    simp only [concentrated_weights_x, pow_succ]
    ring

theorem concentrated_weights_tail_le {N : ℕ} (hN : 8 ≤ N) :
    concentrated_weights_tail N ≤ (1/256 : ℝ) := by
  rw [concentrated_weights_tail_formula hN]
  have hx : 0 ≤ concentrated_weights_x N := by unfold concentrated_weights_x; positivity
  linarith

theorem concentrated_weights_event_probability {N : ℕ} (hN : 8 ≤ N) :
    (unitSampleLaw signKernel N (concentrated_weights_event N)).toReal = 1/256 := by
  classical
  let s : Finset (Fin N) := univ.filter (fun i => i.val < 8)
  have hs : s.card = 8 := by
    have hcard : s.card = (univ : Finset (Fin 8)).card := by
      apply Finset.card_bij (fun i hi => (⟨i.val, (mem_filter.mp hi).2⟩ : Fin 8))
      · intros; exact mem_univ _
      · intro a ha b hb hab
        exact Fin.ext (congrArg (fun i : Fin 8 => i.val) hab)
      · intro b hb
        refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
        · simp [s, b.isLt]
        · rfl
    simpa using hcard
  have he : concentrated_weights_event N = (s : Set (Fin N)).pi (fun _ => ({true} : Set Bool)) := by
    ext ω
    simp [concentrated_weights_event, Set.mem_pi, s]
  change ((Measure.pi (fun _ : Fin N => fairLaw)) (concentrated_weights_event N)).toReal = _
  rw [he, Measure.pi_pi_finset]
  have hf : fairLaw ({true} : Set Bool) = (2 : ℝ≥0∞)⁻¹ := by
    simp [fairLaw, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  simp only [hf, Finset.prod_const, hs]
  norm_num

theorem concentrated_weights_sign_bounds (b : Bool) :
    -1 ≤ signValue b ∧ signValue b ≤ 1 := by
  cases b <;> norm_num [signValue]

theorem concentrated_weights_distance_le {N : ℕ} (hN : 8 ≤ N)
    (ω : Fin N → Bool) (hω : ω ∈ concentrated_weights_event N) :
    concentrated_weights_distance ω ≤ (1/64 : ℝ) := by
  have hresp (d : Dyad N) : |response signKernel ω d - 2| =
      (1-signValue (ω (firstUnit d))) + (1-signValue (ω (secondUnit d))) := by
    have ha := concentrated_weights_sign_bounds (ω (firstUnit d))
    have hb := concentrated_weights_sign_bounds (ω (secondUnit d))
    change |signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) - 2| = _
    rw [abs_of_nonpos (by linarith)]
    ring
  have hd : concentrated_weights_distance ω =
      ∑ i : Fin N, concentrated_weights_q i *
        (concentrated_weights_S N - concentrated_weights_q i) * (1-signValue (ω i)) := by
    unfold concentrated_weights_distance
    simp_rw [hresp, concentrated_weights_factor]
    exact concentrated_weights_pair_linear concentrated_weights_q (fun i => 1-signValue (ω i))
  have hS : concentrated_weights_S N ≤ 1 := by
    rw [concentrated_weights_S_formula]
    have : 0 ≤ concentrated_weights_x N := by unfold concentrated_weights_x; positivity
    linarith
  have hi (i : Fin N) : concentrated_weights_q i *
        (concentrated_weights_S N - concentrated_weights_q i) * (1-signValue (ω i)) ≤
      2 * (if 8 ≤ i.val then concentrated_weights_q i else 0) := by
    have hq := (concentrated_weights_q_pos i).le
    have hqS : concentrated_weights_q i ≤ concentrated_weights_S N :=
      Finset.single_le_sum (fun j _ => (concentrated_weights_q_pos j).le) (mem_univ i)
    have ha0 : 0 ≤ concentrated_weights_q i * (concentrated_weights_S N - concentrated_weights_q i) :=
      mul_nonneg hq (sub_nonneg.mpr hqS)
    have haq : concentrated_weights_q i * (concentrated_weights_S N - concentrated_weights_q i) ≤
        concentrated_weights_q i := by nlinarith
    by_cases hi : 8 ≤ i.val
    · rw [if_pos hi]
      have hs := concentrated_weights_sign_bounds (ω i)
      nlinarith [mul_nonneg ha0 (by linarith : 0 ≤ 2-(1-signValue (ω i)))]
    · have he := hω i (by omega)
      simp [hi, he, signValue]
  calc
    concentrated_weights_distance ω = _ := hd
    _ ≤ ∑ i : Fin N, 2*(if 8 ≤ i.val then concentrated_weights_q i else 0) := sum_le_sum (fun i _ => hi i)
    _ = 2*concentrated_weights_tail N := by rw [concentrated_weights_tail, Finset.mul_sum]
    _ ≤ 2*(1/256 : ℝ) := mul_le_mul_of_nonneg_left (concentrated_weights_tail_le hN) (by norm_num)
    _ ≤ 1/64 := by norm_num

def concentrated_weights_z {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) : ℝ :=
  concentratedWeight d * (response signKernel ω d - weightedOLS signKernel concentratedWeight ω 0)

theorem concentrated_weights_mean_error {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) :
    |weightedOLS signKernel concentratedWeight ω 0 - 2| ≤
      concentrated_weights_distance ω / concentrated_weights_W N := by
  have hw : 0 < concentrated_weights_W N := lt_of_lt_of_le (by norm_num) (concentrated_weights_W_lower hN)
  have he : weightedOLS signKernel concentratedWeight ω 0 - 2 =
      (concentrated_weights_W N)⁻¹ *
        ∑ d : Dyad N, concentratedWeight d * (response signKernel ω d - 2) := by
    rw [concentrated_weights_ols_scalar]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    change _ = (concentrated_weights_W N)⁻¹ *
      (∑ d : Dyad N, concentratedWeight d * response signKernel ω d) -
        (concentrated_weights_W N)⁻¹ * (concentrated_weights_W N * 2)
    field_simp [hw.ne']
    <;> ring
  rw [he, abs_mul, abs_inv, abs_of_pos hw]
  have hs : |∑ d : Dyad N, concentratedWeight d * (response signKernel ω d - 2)| ≤
      concentrated_weights_distance ω := by
    have h := Finset.abs_sum_le_sum_abs (s := (univ : Finset (Dyad N)))
      (f := fun d => concentratedWeight d * (response signKernel ω d - 2))
    simpa only [abs_mul, abs_of_pos (concentrated_weights_bounds _).1,
      concentrated_weights_distance] using h
  calc
    _ ≤ (concentrated_weights_W N)⁻¹ * concentrated_weights_distance ω :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hw.le)
    _ = _ := by ring

theorem concentrated_weights_score_bound {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) :
    (∑ d : Dyad N, |concentrated_weights_z ω d|) ≤ 2 * concentrated_weights_distance ω := by
  have hw : 0 < concentrated_weights_W N := lt_of_lt_of_le (by norm_num) (concentrated_weights_W_lower hN)
  have he := (le_div_iff₀ hw).mp (concentrated_weights_mean_error hN ω)
  calc
    _ = ∑ d : Dyad N, concentratedWeight d *
        |response signKernel ω d - weightedOLS signKernel concentratedWeight ω 0| := by
      simp only [concentrated_weights_z, abs_mul, abs_of_pos (concentrated_weights_bounds _).1]
    _ ≤ ∑ d : Dyad N, concentratedWeight d *
        (|response signKernel ω d - 2| + |weightedOLS signKernel concentratedWeight ω 0 - 2|) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (concentrated_weights_bounds d).1.le
      have h := abs_sub_le (response signKernel ω d) 2
        (weightedOLS signKernel concentratedWeight ω 0)
      simpa only [abs_sub_comm 2 (weightedOLS signKernel concentratedWeight ω 0)] using h
    _ = concentrated_weights_distance ω + concentrated_weights_W N *
        |weightedOLS signKernel concentratedWeight ω 0 - 2| := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        concentrated_weights_distance, concentrated_weights_W]
    _ ≤ _ := by nlinarith

theorem concentrated_weights_variance_scalar {N : ℕ} (ω : Fin N → Bool) :
    (weightedVariance signKernel concentratedWeight ω) 0 0 =
      (concentrated_weights_W N)⁻¹ *
        (∑ d : Dyad N, ∑ f : Dyad N,
          if overlap d f then concentrated_weights_z ω d * concentrated_weights_z ω f else 0) *
        (concentrated_weights_W N)⁻¹ := by
  have hg : weightedGram signKernel concentratedWeight ω =
      Matrix.of (fun _ _ : Fin 1 => concentrated_weights_W N) := by
    ext a b
    fin_cases a; fin_cases b
    simp [weightedGram, concentrated_weights_W, Matrix.sum_apply, outer,
      design, signKernel, Matrix.of_apply]
  unfold weightedVariance
  rw [hg]
  simp [sandwich, Matrix.inv_def, Matrix.det_unique,
    Matrix.adjugate_subsingleton, Ring.inverse_eq_inv, Matrix.mul_apply,
    Fin.sum_univ_one, Matrix.sum_apply, meat, matrix_ite_apply, outer, score, dot,
    design, signKernel, concentrated_weights_z, overlap]
  left
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem concentrated_weights_meat_bound {N : ℕ} (z : Dyad N → ℝ) :
    |∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then z d * z f else 0| ≤
      (∑ d : Dyad N, |z d|)^2 := by
  calc
    _ ≤ ∑ d : Dyad N, |∑ f : Dyad N, if overlap d f then z d*z f else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : Dyad N, ∑ f : Dyad N, |if overlap d f then z d*z f else 0| :=
      Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d : Dyad N, ∑ f : Dyad N, |z d| * |z f| := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro f hf
      by_cases hdf : overlap d f
      · simp only [if_pos hdf, abs_mul, le_refl]
      · simp only [if_neg hdf, abs_zero]
        exact mul_nonneg (abs_nonneg (z d)) (abs_nonneg (z f))
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

theorem concentrated_weights_sandwich_small {N : ℕ} (hN : 8 ≤ N)
    (ω : Fin N → Bool) (hω : ω ∈ concentrated_weights_event N) :
    |(weightedVariance signKernel concentratedWeight ω) 0 0| ≤ 1/16 := by
  have hN2 : 2 ≤ N := by omega
  have hw := concentrated_weights_W_lower hN2
  have hwp : 0 < concentrated_weights_W N := by linarith
  have hscore := concentrated_weights_score_bound hN2 ω
  have hdist := concentrated_weights_distance_le hN ω hω
  have hsum : 0 ≤ ∑ d : Dyad N, |concentrated_weights_z ω d| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsumle : (∑ d : Dyad N, |concentrated_weights_z ω d|) ≤ 1/32 := by linarith
  rw [concentrated_weights_variance_scalar, abs_mul, abs_mul, abs_inv, abs_of_pos hwp]
  have hm := concentrated_weights_meat_bound (concentrated_weights_z ω)
  have hinv : 0 ≤ (concentrated_weights_W N)⁻¹ := inv_nonneg.mpr hwp.le
  have hinvle : (concentrated_weights_W N)⁻¹ ≤ 8 := by
    rw [inv_le_iff_one_le_mul₀ hwp]
    linarith
  calc
    _ ≤ (concentrated_weights_W N)⁻¹ *
        (∑ d : Dyad N, |concentrated_weights_z ω d|)^2 * (concentrated_weights_W N)⁻¹ := by
      gcongr
    _ ≤ 8*(1/32 : ℝ)^2*8 := by gcongr
    _ = 1/16 := by norm_num

theorem concentrated_weights_deviation_on_event {N : ℕ} (hN : 8 ≤ N)
    (ω : Fin N → Bool) (hω : ω ∈ concentrated_weights_event N) :
    (N : ℝ)/2 ≤ |(N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 -
      (N : ℝ)*variance (fun u => weightedOLS signKernel concentratedWeight u 0)
        (unitSampleLaw signKernel N)| := by
  have hv := concentrated_weights_variance_lower (N := N) (by omega)
  have he := concentrated_weights_sandwich_small hN ω hω
  have hg : (1/2 : ℝ) ≤ |(weightedVariance signKernel concentratedWeight ω) 0 0 -
      variance (fun u => weightedOLS signKernel concentratedWeight u 0)
        (unitSampleLaw signKernel N)| := by
    have ha := le_abs_self ((weightedVariance signKernel concentratedWeight ω) 0 0)
    have hb := neg_le_abs ((weightedVariance signKernel concentratedWeight ω) 0 0 -
      variance (fun u => weightedOLS signKernel concentratedWeight u 0)
        (unitSampleLaw signKernel N))
    linarith
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem concentrated_weights_deviation_probability {N : ℕ} (hN : 8 ≤ N) :
    (1/256 : ℝ) ≤ (unitSampleLaw signKernel N {ω |
      (N : ℝ)/2 ≤ |(N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 -
        (N : ℝ)*variance (fun u => weightedOLS signKernel concentratedWeight u 0)
          (unitSampleLaw signKernel N)|}).toReal := by
  rw [← concentrated_weights_event_probability hN]
  exact measureReal_mono (fun ω hω => concentrated_weights_deviation_on_event hN ω hω)

theorem concentrated_weights_no_target :
    ¬(∃ V : ℕ → ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)*variance
        (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)-V N)
        atTop (𝓝 0) ∧
      inProbability (unitSampleLaw signKernel) (fun N ω =>
        (N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 - V N)) := by
  rintro ⟨V, hV, hp⟩
  have habs : Tendsto (fun N : ℕ => |(N : ℝ)*variance
      (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)-V N|)
      atTop (𝓝 0) := by simpa using hV.abs
  have he : ∀ᶠ (N : ℕ) in atTop, |(N : ℝ)*variance
      (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)-V N| ≤ 1 :=
    habs.eventually_le_const (by norm_num)
  have hprob := hp 1 (by norm_num)
  have hlow : ∀ᶠ (N : ℕ) in atTop, (1/256 : ℝ) ≤
      (unitSampleLaw signKernel N {ω | 1 ≤ ‖(N : ℝ)*
        (weightedVariance signKernel concentratedWeight ω) 0 0 - V N‖}).toReal := by
    filter_upwards [he, eventually_ge_atTop 8] with N he hN
    apply (concentrated_weights_deviation_probability hN).trans
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    change (N : ℝ)/2 ≤ _ at hω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
    have htri := abs_sub_le ((N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0)
      (V N) ((N : ℝ)*variance
        (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N))
    rw [abs_sub_comm (V N)] at htri
    have hn : (8 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hbad : (1/256 : ℝ) ≤ 0 := ge_of_tendsto hprob hlow
  norm_num at hbad

theorem concentrated_weights_counterexample_proof :
    (∀ N : ℕ, 2 ≤ N → ∀ d : Dyad N, 0 < concentratedWeight d ∧ concentratedWeight d ≤ 1/8) ∧
    (∀ N : ℕ, 2 ≤ N → (9/16 : ℝ) ≤ ProbabilityTheory.variance
      (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)) ∧
    Tendsto (fun N : ℕ => ProbabilityTheory.variance
      (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N))
      atTop (𝓝 (36/35)) ∧
    (∀ N : ℕ, 8 ≤ N → (1/256 : ℝ) ≤ (unitSampleLaw signKernel N {ω |
      (N : ℝ)/2 ≤ |(N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 -
        (N : ℝ)*ProbabilityTheory.variance (fun u => weightedOLS signKernel concentratedWeight u 0)
          (unitSampleLaw signKernel N)|}).toReal) ∧
    ¬(∃ V : ℕ → ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)*ProbabilityTheory.variance
        (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)-V N)
        atTop (𝓝 0) ∧
      inProbability (unitSampleLaw signKernel) (fun N ω =>
        (N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0 - V N)) := by
  exact ⟨fun N hN d => concentrated_weights_bounds d,
    fun N hN => concentrated_weights_variance_lower hN,
    concentrated_weights_variance_limit,
    fun N hN => concentrated_weights_deviation_probability hN,
    concentrated_weights_no_target⟩

end AronowAudit.P018.Wave1
