import AronowAudit.P013.P013_Audit
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Topology.Order.LiminfLimsup

/-!
Block endpoint bounds, finite CDF and quantile identities, and studentized limits.
The finite probability identities require no measurability assumptions on
changing finite support types.
-/

namespace AronowAudit.P013.Wave1

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-!
### The least-block definition -/

lemma block_endpoint_bounds_pos (r : ℕ) (hr : 1 ≤ r) : 0 < blockEnd r := by
  simp only [blockEnd, if_neg (by omega : r ≠ 0)]
  positivity

lemma block_endpoint_bounds_mono : Monotone blockEnd := by
  intro r s hrs
  by_cases hr : r = 0
  · subst r
    simp [blockEnd]
  · have hs : s ≠ 0 := by omega
    simp only [blockEnd, if_neg hr, if_neg hs]
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
      (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hrs)


lemma block_endpoint_bounds_nat_le_pow (i : ℕ) : i ≤ 2 ^ i := by
  induction i with
  | zero => norm_num
  | succ i hi =>
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ i := by positivity
    omega

lemma block_endpoint_bounds_nonempty (i : ℕ) :
    ({r : ℕ | 1 ≤ r ∧ i ≤ blockEnd r} : Set ℕ).Nonempty := by
  refine ⟨i + 1, by omega, ?_⟩
  simp only [blockEnd, if_neg (by omega : i + 1 ≠ 0)]
  exact (Nat.le_succ i).trans ((block_endpoint_bounds_nat_le_pow (i + 1)).trans
    (block_endpoint_bounds_nat_le_pow (2 ^ (i + 1))))

lemma block_endpoint_bounds_index_iff (i r : ℕ) (hi : 1 ≤ i) (hr : 1 ≤ r) :
    blockIndex i = r ↔ blockEnd (r - 1) < i ∧ i ≤ blockEnd r := by
  have hne := block_endpoint_bounds_nonempty i
  have hleast : IsLeast {s : ℕ | 1 ≤ s ∧ i ≤ blockEnd s} (blockIndex i) :=
    isLeast_csInf hne
  constructor
  · intro h
    have hmem : 1 ≤ r ∧ i ≤ blockEnd r := by simpa [h] using hleast.1
    refine ⟨?_, hmem.2⟩
    by_cases hr1 : r = 1
    · rw [hr1]
      show blockEnd 0 < i
      simp only [blockEnd, ↓reduceIte]
      omega
    · by_contra hnot
      have hprev : r - 1 ∈ {s : ℕ | 1 ≤ s ∧ i ≤ blockEnd s} :=
        ⟨by omega, le_of_not_gt hnot⟩
      have hh := hleast.2 hprev
      rw [h] at hh
      omega
  · rintro ⟨hprev, hlast⟩
    change sInf {s : ℕ | 1 ≤ s ∧ i ≤ blockEnd s} = r
    apply (csInf_eq_iff hne r).2
    refine ⟨⟨hr, hlast⟩, ?_⟩
    intro s hs
    by_contra hnot
    have hs' : s ≤ r - 1 := by omega
    have hend := block_endpoint_bounds_mono hs'
    exact (not_le_of_gt hprev) (hs.2.trans hend)

/-- Any finite collection of indices confined to the first p positions has
cardinality at most p. The map is the actual index, so no suffix count is assumed. -/
lemma block_endpoint_bounds_prefix_card {N p : ℕ} (s : Finset (Fin N))
    (hs : ∀ i ∈ s, i.val < p) : s.card ≤ p := by
  have hcard : s.card ≤ (range p).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin N => i.val)
    · intro i hi
      exact mem_range.mpr (hs i hi)
    · intro i hi j hj hij
      exact Fin.ext hij
  simpa only [card_range] using hcard

lemma block_endpoint_bounds_count (r : ℕ) (hr : 1 ≤ r) :
    ((r % 2 = 1) → (blockBUnits (blockEnd r)).card ≤ blockEnd (r - 1)) ∧
    ((r % 2 = 0) → blockEnd r - (blockBUnits (blockEnd r)).card ≤ blockEnd (r - 1)) := by
  classical
  have hsuffix (i : Fin (blockEnd r)) (hi : blockEnd (r - 1) < i.val + 1) :
      blockIndex (i.val + 1) = r :=
    (block_endpoint_bounds_index_iff _ r (by omega) hr).2 ⟨hi, by omega⟩
  constructor
  · intro hodd
    apply block_endpoint_bounds_prefix_card
    intro i hi
    have heven : blockIndex (i.val + 1) % 2 = 0 := (mem_filter.mp hi).2
    by_contra hnot
    have hidx := hsuffix i (by omega)
    rw [hidx, hodd] at heven
    norm_num at heven
  · intro heven
    let C : Finset (Fin (blockEnd r)) :=
      univ.filter (fun i => ¬ blockIndex (i.val + 1) % 2 = 0)
    have hC : C.card ≤ blockEnd (r - 1) := by
      apply block_endpoint_bounds_prefix_card
      intro i hi
      have hodd : ¬ blockIndex (i.val + 1) % 2 = 0 := (mem_filter.mp hi).2
      by_contra hnot
      exact hodd (by rw [hsuffix i (by omega), heven])
    have hsplit : (blockBUnits (blockEnd r)).card + C.card = blockEnd r := by
      simpa only [blockBUnits, C, card_univ, Fintype.card_fin] using
        (Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (blockEnd r))))
          (fun i => blockIndex (i.val + 1) % 2 = 0))
    omega

lemma block_endpoint_bounds_ratio (r : ℕ) (hr : 2 ≤ r) :
    (blockEnd (r-1) : ℝ)/(blockEnd r : ℝ) = 1/(2 : ℝ)^(2^(r-1)) := by
  have hr0 : r ≠ 0 := by omega
  have hp0 : r - 1 ≠ 0 := by omega
  have hexp : 2 ^ r = 2 ^ (r - 1) + 2 ^ (r - 1) := by
    calc
      2 ^ r = 2 ^ ((r - 1) + 1) := by congr 1 <;> omega
      _ = _ := by rw [pow_succ]; omega
  have hpow : blockEnd r = blockEnd (r - 1) * blockEnd (r - 1) := by
    simp only [blockEnd, if_neg hr0, if_neg hp0]
    rw [hexp, pow_add]
  have hp : (0 : ℝ) < (blockEnd (r - 1) : ℝ) := by
    exact_mod_cast block_endpoint_bounds_pos (r - 1) (by omega)
  rw [hpow, Nat.cast_mul]
  have hcast : (blockEnd (r - 1) : ℝ) = (2 : ℝ) ^ (2 ^ (r - 1)) := by
    simp only [blockEnd, if_neg hp0, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hcast]
  field_simp [ne_of_gt hp] <;> ring

theorem block_endpoint_bounds_proof (r : ℕ) (hr : 1 ≤ r) :
    (r % 2 = 1 →
      0 ≤ ((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ∧
      ((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ≤
        (blockEnd (r-1) : ℝ)/(blockEnd r : ℝ)) ∧
    (r % 2 = 0 →
      0 ≤ 1-((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ∧
      1-((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ≤
        (blockEnd (r-1) : ℝ)/(blockEnd r : ℝ)) ∧
    (2 ≤ r → (blockEnd (r-1) : ℝ)/(blockEnd r : ℝ) = 1/(2 : ℝ)^(2^(r-1))) := by
  classical
  have hN : (0 : ℝ) < (blockEnd r : ℝ) := by
    exact_mod_cast block_endpoint_bounds_pos r hr
  have hbN : (blockBUnits (blockEnd r)).card ≤ blockEnd r := by
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have hbN' : ((blockBUnits (blockEnd r)).card : ℝ) ≤ (blockEnd r : ℝ) := by
    exact_mod_cast hbN
  refine ⟨?_, ?_, fun h => block_endpoint_bounds_ratio r h⟩
  · intro hodd
    refine ⟨div_nonneg (Nat.cast_nonneg _) hN.le, ?_⟩
    apply div_le_div_of_nonneg_right _ hN.le
    exact_mod_cast (block_endpoint_bounds_count r hr).1 hodd
  · intro heven
    have hcount : blockEnd r ≤
        (blockBUnits (blockEnd r)).card + blockEnd (r - 1) := by
      have hh := (block_endpoint_bounds_count r hr).2 heven
      omega
    have hcount' : (blockEnd r : ℝ) ≤
        ((blockBUnits (blockEnd r)).card : ℝ) + (blockEnd (r - 1) : ℝ) := by
      exact_mod_cast hcount
    constructor
    · have hh : ((blockBUnits (blockEnd r)).card : ℝ) / (blockEnd r : ℝ) ≤ 1 :=
        (div_le_one hN).2 hbN'
      linarith
    · apply (le_div_iff₀ hN).2
      have hid : (1 - ((blockBUnits (blockEnd r)).card : ℝ) / (blockEnd r : ℝ)) *
          (blockEnd r : ℝ) = (blockEnd r : ℝ) - ((blockBUnits (blockEnd r)).card : ℝ) := by
        field_simp [ne_of_gt hN] <;> ring
      rw [hid]
      linarith

/-!
### Finite CDF and quantile identities -/

lemma corrected_concentration_coverage_probability_le_one
    {Ω : Type*} [Fintype Ω] (P : Design Ω) (A : Ω → Prop) :
    probability P A ≤ 1 := by
  classical
  calc
    probability P A ≤ probability P (fun _ => True) :=
      probability_mono P _ _ (fun _ _ => trivial)
    _ = 1 := by simp only [probability, if_true, P.total]

lemma corrected_concentration_coverage_union_bound
    {Ω : Type*} [Fintype Ω] (P : Design Ω) (A B C : Ω → Prop)
    (h : ∀ z, A z → B z ∨ C z) :
    probability P A ≤ probability P B + probability P C := by
  classical
  unfold probability
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro z _
  have hp := (P.positive z).le
  by_cases ha : A z <;> by_cases hb : B z <;> by_cases hc : C z
    <;> simp only [ha, hb, hc, ite_true, ite_false]
    <;> first | linarith | exact False.elim ((h z ha).elim hb hc)

lemma corrected_concentration_coverage_Ioc
    {Ω : Type*} [Fintype Ω] (P : Design Ω) (X : Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    probability P (fun z => a < X z ∧ X z ≤ b) =
      probability P (fun z => X z ≤ b) - probability P (fun z => X z ≤ a) := by
  classical
  unfold probability
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro z _
  by_cases ha : X z ≤ a
  · have hb : X z ≤ b := ha.trans hab
    simp [ha, hb, not_lt.mpr ha]
  · have ha' : a < X z := lt_of_not_ge ha
    by_cases hb : X z ≤ b <;> simp [ha, ha', hb]

/-- An elementary continuous squeeze, adapted from
P011.CoverageCompletion.continuous_squeeze_zero.
The adapted proof originates in StatLean's `SteinMethod` module
(Apache-2.0); see NOTICE at the repository root.
-/
lemma corrected_concentration_coverage_squeeze
    {G : ℕ → ℝ} {F : ℝ → ℝ} (hF : ContinuousAt F 0)
    (hb : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, F (-ε) - ε ≤ G n ∧ G n ≤ F ε + ε) :
    Tendsto G atTop (𝓝 (F 0)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hF (η / 2) (by linarith)
  let ε := min (δ / 2) (η / 4)
  have he : 0 < ε := lt_min (by linarith) (by linarith)
  have hed : ε ≤ δ / 2 := min_le_left _ _
  have heη : ε ≤ η / 4 := min_le_right _ _
  have hl := hclose (show dist (-ε) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos he]; linarith)
  have hr := hclose (show dist ε 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos he]; linarith)
  rw [Real.dist_eq, abs_lt] at hl hr
  filter_upwards [hb ε he] with n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hn.1, hn.2]

lemma corrected_concentration_coverage_normal_continuous : Continuous normalCDF := by
  letI : MeasureTheory.NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  exact continuous_iff_continuousAt.mpr
    (fun t => AronowAudit.P053.NormalCompletion.cdf_continuousAt _ t)

lemma corrected_concentration_coverage_quantile_eq (α : ℝ) :
    normalCritical α = AronowAudit.P053.normalCritical α := by
  unfold normalCritical AronowAudit.P053.normalCritical
  congr 1
  ext t
  simp only [Set.mem_setOf_eq, AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
  rfl

lemma corrected_concentration_coverage_quantile (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < normalCritical α ∧ normalCDF (normalCritical α) = 1 - α / 2 := by
  rw [corrected_concentration_coverage_quantile_eq]
  refine ⟨AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1, ?_⟩
  rw [normalCDF, ← AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
  exact AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα hα1

/-- The closed interval is bounded below by (-a,a] and above by
(-a-ε,a]. Thus no assertion about atoms in the finite designs is needed. -/
lemma corrected_concentration_coverage_interval
    {L : ℕ → Type*} [∀ n, Fintype (L n)]
    (P : ∀ n, Design (L n)) (X : ∀ n, L n → ℝ)
    (hX : TendsNormal P X 0 1) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n => probability (P n) (fun z => |X n z| ≤ a)) atTop
      (𝓝 (2 * normalCDF a - 1)) := by
  let Ψ : ℝ → ℝ := fun e => normalCDF a - normalCDF (-a - e)
  have hΨ : Continuous Ψ := by
    dsimp [Ψ]
    exact continuous_const.sub
      (corrected_concentration_coverage_normal_continuous.comp
        (continuous_const.sub continuous_id))
  have hlim (b : ℝ) : Tendsto
      (fun n => probability (P n) (fun z => X n z ≤ a) -
        probability (P n) (fun z => X n z ≤ b)) atTop
      (𝓝 (normalCDF a - normalCDF b)) := (hX a).sub (hX b)
  have ht : Tendsto (fun n => probability (P n) (fun z => |X n z| ≤ a))
      atTop (𝓝 (Ψ 0)) := by
    apply corrected_concentration_coverage_squeeze hΨ.continuousAt
    intro ε hε
    have hl := (hlim (-a)).eventually
      (eventually_gt_nhds (show normalCDF a - normalCDF (-a) - ε <
        normalCDF a - normalCDF (-a) by linarith))
    have hu := (hlim (-a - ε)).eventually
      (eventually_lt_nhds (show normalCDF a - normalCDF (-a - ε) <
        normalCDF a - normalCDF (-a - ε) + ε by linarith))
    filter_upwards [hl, hu] with n hnlo hnhi
    have hlow : probability (P n) (fun z => X n z ≤ a) -
        probability (P n) (fun z => X n z ≤ -a) ≤
        probability (P n) (fun z => |X n z| ≤ a) := by
      rw [← corrected_concentration_coverage_Ioc (P n) (X n) (-a) a (by linarith)]
      apply probability_mono
      intro z hz
      exact abs_le.mpr ⟨hz.1.le, hz.2⟩
    have hupp : probability (P n) (fun z => |X n z| ≤ a) ≤
        probability (P n) (fun z => X n z ≤ a) -
        probability (P n) (fun z => X n z ≤ -a - ε) := by
      rw [← corrected_concentration_coverage_Ioc (P n) (X n) (-a - ε) a (by linarith)]
      apply probability_mono
      intro z hz
      have hz' := abs_le.mp hz
      exact ⟨by linarith [hz'.1], hz'.2⟩
    have hm : normalCDF (-a) ≤ normalCDF (-a - -ε) :=
      ProbabilityTheory.monotone_cdf _ (by linarith)
    dsimp [Ψ]
    constructor <;> linarith
  have hsym : normalCDF (-a) = 1 - normalCDF a :=
    AronowAudit.P053.NormalCompletion.normal_cdf_neg a
  simpa [Ψ, hsym, show normalCDF a - (1 - normalCDF a) =
    2 * normalCDF a - 1 by ring] using ht

lemma corrected_concentration_coverage_liminf
    (g f : ℕ → ℝ) (a : ℝ) (ht : Tendsto g atTop (𝓝 a))
    (hgf : ∀ n, g n ≤ f n) (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1) :
    a ≤ liminf f atTop := by
  have hlo : atTop.IsBoundedUnder (· ≥ ·) f := isBoundedUnder_of ⟨0, hf0⟩
  have hhi : atTop.IsBoundedUnder (· ≤ ·) f := isBoundedUnder_of ⟨1, hf1⟩
  apply (le_liminf_iff hhi.isCoboundedUnder_flip hlo).2
  intro y hy
  filter_upwards [ht.eventually_const_lt hy] with n hn
  exact hn.trans_le (hgf n)

theorem corrected_concentration_coverage_proof {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (estimate Vhat : ∀ n : ℕ, L n → ℝ) (target : ℕ → ℝ)
    (V : ℕ → ℝ) (hV : ∀ n : ℕ, V n = variance (P n) (estimate n) ∧ 0 < V n)
    (c : ℝ) (hc : 0 < c) (hv : Tendsto (fun n : ℕ => (n+1 : ℝ)*V n) atTop (𝓝 c))
    (hclt : TendsNormal P (fun (n : ℕ) z => (estimate n z-target n)/Real.sqrt (V n)) 0 1)
    (hex : ∀ n : ℕ, (n+1 : ℝ)*V n ≤ expectation (P n) (fun z => (n+1 : ℝ)*Vhat n z))
    (hvar : Tendsto (fun n : ℕ => variance (P n) (fun z => (n+1 : ℝ)*Vhat n z)) atTop (𝓝 0)) :
    ConvergesInProbability P (fun (n : ℕ) z => (n+1 : ℝ)*Vhat n z-
      expectation (P n) (fun z => (n+1 : ℝ)*Vhat n z)) 0 ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        2*normalCDF (normalCritical α*Real.sqrt (1-ε))-1 ≤
          liminf (fun n : ℕ => probability (P n) (fun z => 0 ≤ Vhat n z ∧
            |estimate n z-target n| ≤ normalCritical α*Real.sqrt (Vhat n z))) atTop) ∧
      1-α ≤ liminf (fun n : ℕ => probability (P n) (fun z => 0 ≤ Vhat n z ∧
        |estimate n z-target n| ≤ normalCritical α*Real.sqrt (Vhat n z))) atTop) := by
  have hcenter := variance_concentration P (fun n z => (n+1 : ℝ) * Vhat n z) hvar
  refine ⟨hcenter, ?_⟩
  intro α hα hα1
  obtain ⟨hq, hqCDF⟩ := corrected_concentration_coverage_quantile α hα hα1
  let C : ℕ → ℝ := fun n => probability (P n) (fun z => 0 ≤ Vhat n z ∧
    |estimate n z-target n| ≤ normalCritical α * Real.sqrt (Vhat n z))
  have hfixed : ∀ ε : ℝ, 0 < ε → ε < 1 →
      2 * normalCDF (normalCritical α * Real.sqrt (1-ε)) - 1 ≤ liminf C atTop := by
    intro ε hε hε1
    have htail := relative_lower_tail_tends_zero P
      (fun n z => (n+1 : ℝ) * Vhat n z) (fun n => (n+1 : ℝ) * V n)
      (fun n => mul_pos (by positivity) (hV n).2) c hc hv hex hvar ε hε
    have hevent (n : ℕ) (z : L n) :
        (n+1 : ℝ) * Vhat n z < (1-ε) * ((n+1 : ℝ) * V n) ↔
          Vhat n z < (1-ε) * V n := by
      rw [show (1-ε) * ((n+1 : ℝ) * V n) = (n+1 : ℝ) * ((1-ε) * V n) by ring]
      exact mul_lt_mul_iff_right₀ (by positivity : (0 : ℝ) < n+1)
    have htail' : Tendsto (fun n => probability (P n)
        (fun z => Vhat n z < (1-ε) * V n)) atTop (𝓝 0) := by
      simpa only [hevent] using htail
    have hcentral := corrected_concentration_coverage_interval P
      (fun n z => (estimate n z-target n) / Real.sqrt (V n)) hclt
      (normalCritical α * Real.sqrt (1-ε))
      (mul_pos hq (Real.sqrt_pos.2 (by linarith)))
    have hdiff := hcentral.sub htail'
    apply corrected_concentration_coverage_liminf
      (fun n => probability (P n) (fun z =>
        |(estimate n z-target n) / Real.sqrt (V n)| ≤
          normalCritical α * Real.sqrt (1-ε)) -
        probability (P n) (fun z => Vhat n z < (1-ε) * V n)) C
      (2 * normalCDF (normalCritical α * Real.sqrt (1-ε)) - 1)
      (by simpa only [sub_zero] using hdiff)
    · intro n
      exact finite_wald_coverage_bound (P n) (estimate n) (Vhat n)
        (target n) (V n) ε (normalCritical α) (hV n).2 hε hε1 hq.le
    · intro n
      exact probability_nonneg _ _
    · intro n
      exact corrected_concentration_coverage_probability_le_one _ _
  refine ⟨hfixed, ?_⟩
  let η : ℕ → ℝ := fun k => (1 / ((k : ℝ) + 1)) / 2
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have hη0 (k : ℕ) : 0 < η k := by dsimp [η]; positivity
  have hη1 (k : ℕ) : η k < 1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    dsimp [η]
    linarith
  have hcont : Continuous (fun e : ℝ =>
      2 * normalCDF (normalCritical α * Real.sqrt (1-e)) - 1) :=
    (continuous_const.mul (corrected_concentration_coverage_normal_continuous.comp
      (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_const.sub continuous_id))))).sub continuous_const
  have ht : Tendsto (fun k =>
      2 * normalCDF (normalCritical α * Real.sqrt (1-η k)) - 1)
      atTop (𝓝 (1-α)) := by
    have hh := hcont.continuousAt.tendsto.comp hη
    have hlim : 2 * normalCDF (normalCritical α * Real.sqrt (1 - 0)) - 1 = 1 - α := by
      rw [sub_zero, Real.sqrt_one, mul_one, hqCDF]
      ring
    rw [hlim] at hh
    exact hh
  exact le_of_tendsto ht (Eventually.of_forall (fun k => hfixed (η k) (hη0 k) (hη1 k)))

/-!
### Changing finite-space continuity and random thresholds -/

lemma corrected_studentized_limit_det
    {L : ℕ → Type*} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (𝓝 c)) :
    ConvergesInProbability P (fun n _ => a n) c := by
  intro ε hε
  have he : ∀ᶠ n in atTop, |a n - c| < ε := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp ha ε hε
  apply tendsto_congr' (he.mono fun n hn => ?_) |>.mpr tendsto_const_nhds
  simp [probability, show ¬ ε < |a n - c| from not_lt.mpr hn.le]

lemma corrected_studentized_limit_moving_center
    {L : ℕ → Type*} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (X : ∀ n, L n → ℝ) (a : ℕ → ℝ) (c : ℝ)
    (hX : ConvergesInProbability P (fun n z => X n z - a n) 0)
    (ha : Tendsto a atTop (𝓝 c)) : ConvergesInProbability P X c := by
  intro ε hε
  have he : ∀ᶠ n in atTop, |a n - c| < ε / 2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp ha (ε / 2) (by linarith)
  have hsmall := hX (ε / 2) (by linarith)
  simp only [sub_zero] at hsmall
  apply squeeze_zero' (Eventually.of_forall (fun n => probability_nonneg _ _)) ?_ hsmall
  filter_upwards [he] with n hn
  apply probability_mono
  intro z hz
  have htri : |X n z - c| ≤ |X n z - a n| + |a n - c| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (X n z - a n) (a n - c)
  linarith

lemma corrected_studentized_limit_continuous_pair
    {L : ℕ → Type*} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (X Y : ∀ n, L n → ℝ) (a b : ℝ)
    (hX : ConvergesInProbability P X a) (hY : ConvergesInProbability P Y b)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousAt f (a, b)) :
    ConvergesInProbability P (fun n z => f (X n z, Y n z)) (f (a, b)) := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hf ε hε
  have hd : 0 < δ / 2 := by linarith
  have hlim := (hX (δ / 2) hd).add (hY (δ / 2) hd)
  apply squeeze_zero (fun n => probability_nonneg _ _)
    (fun n => corrected_concentration_coverage_union_bound (P n) _ _ _ ?_)
    (by simpa only [add_zero] using hlim)
  intro z hz
  by_cases hx : δ / 2 < |X n z - a|
  · exact Or.inl hx
  by_cases hy : δ / 2 < |Y n z - b|
  · exact Or.inr hy
  have hpair : dist (X n z, Y n z) (a, b) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt (by linarith [le_of_not_gt hx]) (by linarith [le_of_not_gt hy])
  have hh := hclose hpair
  rw [Real.dist_eq] at hh
  exact False.elim ((not_lt_of_ge hh.le) hz)

/-- A random threshold converging in probability to t can be replaced by t
inside a CDF with a continuous limit. This is sufficient for studentization
and does not require independence, tightness or a fixed underlying space. -/
lemma corrected_studentized_limit_threshold
    {L : ℕ → Type*} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (Z T : ∀ n, L n → ℝ) (t : ℝ)
    (hZ : TendsNormal P Z 0 1) (hT : ConvergesInProbability P T t) :
    Tendsto (fun n => probability (P n) (fun z => Z n z ≤ T n z)) atTop
      (𝓝 (normalCDF t)) := by
  let F : ℝ → ℝ := fun e => normalCDF (t + e)
  have hF : Continuous F :=
    corrected_concentration_coverage_normal_continuous.comp (continuous_const.add continuous_id)
  have ht : Tendsto (fun n => probability (P n) (fun z => Z n z ≤ T n z))
      atTop (𝓝 (F 0)) := by
    apply corrected_concentration_coverage_squeeze hF.continuousAt
    intro ε hε
    let Bad : ∀ n, L n → Prop := fun n z => ε / 2 < |T n z - t|
    have hbad : Tendsto (fun n => probability (P n) (Bad n)) atTop (𝓝 0) :=
      hT (ε / 2) (by linarith)
    have hlower (n : ℕ) : probability (P n) (fun z => Z n z ≤ t - ε) ≤
        probability (P n) (fun z => Z n z ≤ T n z) + probability (P n) (Bad n) := by
      apply corrected_concentration_coverage_union_bound
      intro z hz
      by_cases hb : Bad n z
      · exact Or.inr hb
      · left
        have hclose := abs_le.mp (le_of_not_gt hb)
        linarith [hclose.1]
    have hupper (n : ℕ) : probability (P n) (fun z => Z n z ≤ T n z) ≤
        probability (P n) (fun z => Z n z ≤ t + ε) + probability (P n) (Bad n) := by
      apply corrected_concentration_coverage_union_bound
      intro z hz
      by_cases hb : Bad n z
      · exact Or.inr hb
      · left
        have hclose := abs_le.mp (le_of_not_gt hb)
        linarith [hclose.2]
    have hl := (hZ (t - ε)).eventually
      (eventually_gt_nhds (show normalCDF (t - ε) - ε / 2 < normalCDF (t - ε) by linarith))
    have hu := (hZ (t + ε)).eventually
      (eventually_lt_nhds (show normalCDF (t + ε) < normalCDF (t + ε) + ε / 2 by linarith))
    have hb := hbad.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))
    filter_upwards [hl, hu, hb] with n hln hun hbn
    dsimp [F]
    simp only [← sub_eq_add_neg]
    constructor <;> linarith [hlower n, hupper n]
  simpa only [F, add_zero] using ht

/-- Transfer probabilities when two event predicates agree on a set whose
complement has vanishing probability. -/
lemma corrected_studentized_limit_event_transfer
    {L : ℕ → Type*} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (A B G : ∀ n, L n → Prop) (a : ℝ)
    (heq : ∀ n z, G n z → (A n z ↔ B n z))
    (hbad : Tendsto (fun n => probability (P n) (fun z => ¬ G n z)) atTop (𝓝 0))
    (hB : Tendsto (fun n => probability (P n) (B n)) atTop (𝓝 a)) :
    Tendsto (fun n => probability (P n) (A n)) atTop (𝓝 a) := by
  have hAB (n : ℕ) : probability (P n) (A n) ≤
      probability (P n) (B n) + probability (P n) (fun z => ¬ G n z) := by
    apply corrected_concentration_coverage_union_bound
    intro z hz
    by_cases hg : G n z
    · exact Or.inl ((heq n z hg).1 hz)
    · exact Or.inr hg
  have hBA (n : ℕ) : probability (P n) (B n) ≤
      probability (P n) (A n) + probability (P n) (fun z => ¬ G n z) := by
    apply corrected_concentration_coverage_union_bound
    intro z hz
    by_cases hg : G n z
    · exact Or.inl ((heq n z hg).2 hz)
    · exact Or.inr hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hB.sub hbad)
    (by simpa only [add_zero] using hB.add hbad)
  · intro n
    linarith [hBA n]
  · exact hAB

lemma corrected_studentized_limit_threshold_identity
    (estimate target V Vhat x : ℝ) (hV : 0 < V) (hhat : 0 < Vhat) :
    ((estimate - target) / Real.sqrt Vhat ≤ x) ↔
      ((estimate - target) / Real.sqrt V ≤ x * Real.sqrt (Vhat / V)) := by
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsH : 0 < Real.sqrt Vhat := Real.sqrt_pos.2 hhat
  have hid : (x * Real.sqrt (Vhat / V)) * Real.sqrt V = x * Real.sqrt Vhat := by
    rw [Real.sqrt_div hhat.le]
    field_simp [ne_of_gt hsV] <;> ring
  rw [div_le_iff₀ hsH, div_le_iff₀ hsV, hid]

lemma corrected_studentized_limit_gaussian_cdf
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s) (x : ℝ) :
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0
      ⟨c / s, div_nonneg hc.le hs.le⟩) x = normalCDF (x * Real.sqrt (s / c)) := by
  let b : ℝ := Real.sqrt (s / c)
  have hb : 0 < b := Real.sqrt_pos.2 (div_pos hs hc)
  have hb2 : b ^ 2 = s / c := Real.sq_sqrt (div_nonneg hs.le hc.le)
  have hvariance : (1 : ℝ≥0) / NNReal.mk (b ^ 2) (sq_nonneg _) =
      ⟨c / s, div_nonneg hc.le hs.le⟩ := by
    apply NNReal.eq
    rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk]
    change (1 : ℝ) / b ^ 2 = c / s
    rw [hb2]
    field_simp
  have hmap : (ProbabilityTheory.gaussianReal 0 1).map (fun y : ℝ => y / b) =
      ProbabilityTheory.gaussianReal 0 ⟨c / s, div_nonneg hc.le hs.le⟩ := by
    simpa only [zero_div, hvariance] using
      (ProbabilityTheory.gaussianReal_map_div_const (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) b)
  haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0
      ⟨c / s, div_nonneg hc.le hs.le⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  rw [ProbabilityTheory.cdf_eq_real, ← hmap,
    MeasureTheory.map_measureReal_apply (by fun_prop : Measurable (fun y : ℝ => y / b))
      measurableSet_Iic]
  change (ProbabilityTheory.gaussianReal 0 1).real
      ((fun y : ℝ => y / b) ⁻¹' Set.Iic x) = normalCDF (x * b)
  rw [normalCDF, ProbabilityTheory.cdf_eq_real]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_Iic]
  exact div_le_iff₀ hb

theorem corrected_studentized_limit_proof {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (estimate Vhat : ∀ n : ℕ, L n → ℝ) (target V : ℕ → ℝ)
    (hV : ∀ n : ℕ, V n = variance (P n) (estimate n) ∧ 0 < V n)
    (c s : ℝ) (hc : 0 < c) (hsc : c ≤ s)
    (hv : Tendsto (fun n : ℕ => (n+1 : ℝ)*V n) atTop (𝓝 c))
    (hclt : TendsNormal P (fun (n : ℕ) z => (estimate n z-target n)/Real.sqrt (V n)) 0 1)
    (hex : ∀ n : ℕ, (n+1 : ℝ)*V n ≤ expectation (P n) (fun z => (n+1 : ℝ)*Vhat n z))
    (hvar : Tendsto (fun n : ℕ => variance (P n) (fun z => (n+1 : ℝ)*Vhat n z)) atTop (𝓝 0))
    (hs : Tendsto (fun n : ℕ => expectation (P n) (fun z => (n+1 : ℝ)*Vhat n z)) atTop (𝓝 s)) :
    ConvergesInProbability P (fun (n : ℕ) z => (n+1 : ℝ)*Vhat n z) s ∧
    ConvergesInProbability P (fun (n : ℕ) z => Real.sqrt (V n / Vhat n z)) (Real.sqrt (c/s)) ∧
    0 < Real.sqrt (c/s) ∧ Real.sqrt (c/s) ≤ 1 ∧
    TendsNormal P (fun (n : ℕ) z => (estimate n z-target n)/Real.sqrt (Vhat n z)) 0
      ⟨c/s, div_nonneg hc.le (le_trans hc.le hsc)⟩ := by
  have hspos : 0 < s := hc.trans_le hsc
  let W : ∀ n, L n → ℝ := fun n z => (n+1 : ℝ) * Vhat n z
  let v : ℕ → ℝ := fun n => (n+1 : ℝ) * V n
  have hW : ConvergesInProbability P W s :=
    corrected_studentized_limit_moving_center P W
      (fun n => expectation (P n) (W n)) s (variance_concentration P W hvar) hs
  have hdet : ConvergesInProbability P (fun n _ => v n) c :=
    corrected_studentized_limit_det P v c hv
  have hcancel (n : ℕ) (z : L n) : v n / W n z = V n / Vhat n z :=
    mul_div_mul_left _ _ (by positivity : (n+1 : ℝ) ≠ 0)
  have hcancel' (n : ℕ) (z : L n) : W n z / v n = Vhat n z / V n :=
    mul_div_mul_left _ _ (by positivity : (n+1 : ℝ) ≠ 0)
  have hratio : ConvergesInProbability P
      (fun n z => Real.sqrt (V n / Vhat n z)) (Real.sqrt (c / s)) := by
    have hf : ContinuousAt (fun p : ℝ × ℝ => Real.sqrt (p.1 / p.2)) (c, s) :=
      Real.continuous_sqrt.continuousAt.comp
        (continuousAt_fst.div continuousAt_snd (ne_of_gt hspos))
    have hh := corrected_studentized_limit_continuous_pair P
      (fun n _ => v n) W c s hdet hW _ hf
    simpa only [hcancel] using hh
  have hdenom : ConvergesInProbability P
      (fun n z => Real.sqrt (Vhat n z / V n)) (Real.sqrt (s / c)) := by
    have hf : ContinuousAt (fun p : ℝ × ℝ => Real.sqrt (p.1 / p.2)) (s, c) :=
      Real.continuous_sqrt.continuousAt.comp
        (continuousAt_fst.div continuousAt_snd (ne_of_gt hc))
    have hh := corrected_studentized_limit_continuous_pair P
      W (fun n _ => v n) s c hW hdet _ hf
    simpa only [hcancel'] using hh
  have hscale : 0 < Real.sqrt (c / s) := Real.sqrt_pos.2 (div_pos hc hspos)
  have hscale1 : Real.sqrt (c / s) ≤ 1 :=
    Real.sqrt_le_one.2 ((div_le_one hspos).2 hsc)
  refine ⟨hW, hratio, hscale, hscale1, ?_⟩
  let G : ∀ n, L n → Prop := fun n z => s / 2 < W n z
  have hbad : Tendsto (fun n => probability (P n) (fun z => ¬ G n z)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => probability_nonneg _ _)
      (fun n => probability_mono (P n) _ _ ?_) (hW (s / 4) (by positivity))
    intro z hz
    have hz' : W n z ≤ s / 2 := le_of_not_gt hz
    have hneg : W n z - s ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith
  intro x
  have hthreshold : ConvergesInProbability P
      (fun n z => x * Real.sqrt (Vhat n z / V n)) (x * Real.sqrt (s / c)) := by
    have hx : ConvergesInProbability P (fun _ _ => x) x :=
      corrected_studentized_limit_det P (fun _ => x) x tendsto_const_nhds
    exact corrected_studentized_limit_continuous_pair P
      (fun _ _ => x) (fun n z => Real.sqrt (Vhat n z / V n))
      x (Real.sqrt (s / c)) hx hdenom (fun p => p.1 * p.2)
      (continuousAt_fst.mul continuousAt_snd)
  have ht := corrected_studentized_limit_threshold P
    (fun n z => (estimate n z - target n) / Real.sqrt (V n))
    (fun n z => x * Real.sqrt (Vhat n z / V n))
    (x * Real.sqrt (s / c)) hclt hthreshold
  have hcdf : Tendsto (fun n => probability (P n)
      (fun z => (estimate n z - target n) / Real.sqrt (Vhat n z) ≤ x)) atTop
      (𝓝 (normalCDF (x * Real.sqrt (s / c)))) := by
    apply corrected_studentized_limit_event_transfer P
      (fun n z => (estimate n z - target n) / Real.sqrt (Vhat n z) ≤ x)
      (fun n z => (estimate n z - target n) / Real.sqrt (V n) ≤
        x * Real.sqrt (Vhat n z / V n)) G _ ?_ hbad ht
    intro n z hz
    have hWpos : 0 < W n z := lt_trans (by positivity : 0 < s / 2) hz
    have hhat : 0 < Vhat n z := by
      have hN : (0 : ℝ) < n+1 := by positivity
      exact (mul_pos_iff_of_pos_left hN).1 hWpos
    exact corrected_studentized_limit_threshold_identity
      (estimate n z) (target n) (V n) (Vhat n z) x (hV n).2 hhat
  have heq : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0
      ⟨c/s, div_nonneg hc.le (le_trans hc.le hsc)⟩) x =
      normalCDF (x * Real.sqrt (s / c)) :=
    corrected_studentized_limit_gaussian_cdf c s hc hspos x
  rw [heq]
  exact hcdf

end

end AronowAudit.P013.Wave1
