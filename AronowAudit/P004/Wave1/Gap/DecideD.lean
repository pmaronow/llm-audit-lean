import AronowAudit.P004.Wave1.LinePopulation.N3
import AronowAudit.P004.Wave1.LinePopulation.N4
import AronowAudit.P004.Wave1.LinePopulation.N5
import AronowAudit.P004.Wave1.LinePopulation.N6
import AronowAudit.P004.Wave1.LinePopulation.N7
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.Wave1.DesignLimits.DL2
import AronowAudit.P004.Wave1.DesignLimits.DL4
import AronowAudit.P004.Wave1.DesignLimits.DL8
import AronowAudit.P004.Wave1.DesignLimits.NF

/-! P004-T43: failure of existence of the printed experimental coverage limit. -/

namespace AronowAudit.P004.Wave1

universe u

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical Topology

/-- Balanced pairs, with a final zero for an odd population size. -/
def DecideD_sign : (N : ℕ) → Fin N → ℝ
  | 0 => Fin.elim0
  | 1 => fun _ => 0
  | N + 2 => Fin.cases 1 (Fin.cases (-1) (DecideD_sign N))

def DecideD_mass (N : ℕ) : ℝ := ∑ i, (DecideD_sign N i)^2

lemma DecideD_sign_facts (N : ℕ) :
    (∑ i, DecideD_sign N i) = 0 ∧
    (∀ i, |DecideD_sign N i| ≤ 1 ∧
      (DecideD_sign N i)^4 = (DecideD_sign N i)^2) ∧
    0 ≤ DecideD_mass N ∧ (N : ℝ) - 1 ≤ DecideD_mass N ∧ DecideD_mass N ≤ N := by
  induction N using Nat.twoStepInduction with
  | zero => simp [DecideD_sign, DecideD_mass]
  | one => simp [DecideD_sign, DecideD_mass, Fin.sum_univ_succ]
  | more N ih _ =>
    obtain ⟨hs, hb, hm0, hml, hmu⟩ := ih
    have hm : DecideD_mass (N+2) = 2 + DecideD_mass N := by
      simp [DecideD_mass, DecideD_sign, Fin.sum_univ_succ]
      ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [DecideD_sign, Fin.sum_univ_succ, hs]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · norm_num [DecideD_sign]
      · refine Fin.cases ?_ (fun k => ?_) j
        · change |(-1 : ℝ)| ≤ 1 ∧ (-1 : ℝ)^4 = (-1 : ℝ)^2
          norm_num
        · simpa [DecideD_sign] using hb k
    all_goals rw [hm]; push_cast; linarith

lemma DecideD_mass_ratio :
    Tendsto (fun N : ℕ => DecideD_mass N / N) atTop (𝓝 1) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun N : ℕ => 1 - (N : ℝ)⁻¹) atTop (𝓝 1) by
      simpa using tendsto_const_nhds.sub hi) tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have h := div_le_div_of_nonneg_right (DecideD_sign_facts N).2.2.2.1 hn.le
    simpa [sub_div, div_self hn.ne', one_div] using h
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (div_le_one (Nat.cast_pos.mpr hN)).mpr (DecideD_sign_facts N).2.2.2.2

def DecideD_table (b : Bool) (N : ℕ) : CircleTable N := fun i z =>
  if b then 2 * DecideD_sign N i * bit (z i) else DecideD_sign N i

def DecideD_population (f : ℕ → Bool) (N : ℕ) := linePopulation (DecideD_table (f N) N)

lemma DecideD_table_bound (b : Bool) (N : ℕ) (i : Fin N) (z : Assignment N) :
    |DecideD_table b N i z| ≤ 2 := by
  have h := (DecideD_sign_facts N).2.1 i
  cases b <;> cases hz : z i <;> simp [DecideD_table, bit, hz, abs_mul] <;> linarith

lemma DecideD_update (b : Bool) (N : ℕ) (j k : Fin N) (z : Assignment N) (a : Bool)
    (hk : 0 < 10 * |(j : ℝ) - (k : ℝ)|) :
    DecideD_table b N j (Function.update z k a) = DecideD_table b N j z := by
  have hjk : j ≠ k := by rintro rfl; simp at hk
  simp [DecideD_table, Function.update_of_ne hjk]

lemma DecideD_spatial (f : ℕ → Bool) : SpatialLocalConditions (DecideD_population f) := by
  exact LinePopulation.spatialLocal_of LinePopulation.n5_proof LinePopulation.n6_proof
    LinePopulation.n7_proof (fun N => DecideD_table (f N) N) 2 0 (by norm_num) le_rfl
    (fun N => DecideD_table_bound (f N) N) (fun N => DecideD_update (f N) N)

lemma DecideD_wellDefined (f : ℕ → Bool) :
    ∀ᶠ N in atTop, WellDefined (DecideD_population f N) 0 :=
  Eventually.of_forall fun N => LinePopulation.n4_proof _ 0 le_rfl

lemma DecideD_circle (f : ℕ → Bool) (N : ℕ) :
    circleAverage (DecideD_population f N) 0 = DecideD_table (f N) N :=
  LinePopulation.n3_proof _

lemma DecideD_local (f : ℕ → Bool) :
    ∀ᶠ N in atTop, LocalAt (circleAverage (DecideD_population f N) 0)
      (nodeSeparation (DecideD_population f N)) 0 := by
  apply Eventually.of_forall
  intro N
  simpa [DecideD_population] using LinePopulation.n7_proof (DecideD_table (f N) N) 0 0 le_rfl le_rfl
    (DecideD_update (f N) N)

lemma DecideD_half {N : ℕ} (i : Fin N) : 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 := by
  norm_num

lemma DecideD_bit_mean {N : ℕ} (i : Fin N) :
    expect (fun _ => (1/2 : ℝ)) (fun z : Assignment N => bit (z i)) = 1/2 := by
  simpa [expect_const] using bernoulli_positive_power (fun _ : Fin N => (1/2 : ℝ))
    (fun _ => (1 : ℝ)) i 1 (by omega) (fun j => DecideD_half j)

lemma DecideD_weighted_moments {N : ℕ} (c : Fin N → ℝ) :
    expect (fun _ => (1/2 : ℝ)) (fun z => ∑ i, c i * bit (z i)) = (∑ i, c i)/2 ∧
    variance (fun _ => (1/2 : ℝ)) (fun z => ∑ i, c i * bit (z i)) = (∑ i, (c i)^2)/4 := by
  let p : Fin N → ℝ := fun _ => 1/2
  have hmean (i : Fin N) : expect p (fun z => c i * bit (z i)) = c i/2 := by
    rw [expect_mul, DecideD_bit_mean]
    ring
  have hcov (i j : Fin N) :
      cov p (fun z => c i * bit (z i)) (fun z => c j * bit (z j)) =
        if i=j then (c i)^2/4 else 0 := by
    unfold cov
    rw [hmean, hmean]
    by_cases hij : i=j
    · subst j
      have he : (fun z : Assignment N => c i * bit (z i) * (c i * bit (z i))) =
          fun z => (c i)^2 * bit (z i) := by
        funext z
        cases z i <;> simp [bit] <;> ring
      rw [he, expect_mul, DecideD_bit_mean, if_pos rfl]
      ring
    · rw [if_neg hij, GraphCompletion.expect_mul_of_disjoint_depends p {i}]
      · rw [hmean, hmean]; ring
      · intro z z' hz
        dsimp only
        rw [hz i (by simp)]
      · intro z z' hz
        dsimp only
        rw [hz j (by simpa using Ne.symm hij)]
  constructor
  · change expect p (fun z => ∑ i, c i * bit (z i)) = _
    rw [expect_sum]
    simp only [hmean, Finset.sum_div]
  · change variance p (fun z => ∑ i, c i * bit (z i)) = _
    rw [variance_sum]
    simp only [hcov, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_div]

lemma DecideD_marginal (b : Bool) (N : ℕ) (i : Fin N) (a : Bool) :
    marginal (fun _ => (1/2 : ℝ)) (DecideD_table b N) i a =
      if b then 2 * DecideD_sign N i * bit a else DecideD_sign N i := by
  rw [marginal_is_marginalization _ _ _ _ (fun i => DecideD_half i)]
  simp [DecideD_table, Function.update_self, expect_const]

lemma DecideD_barMu (b : Bool) (N : ℕ) (a : Bool) :
    barMu (fun _ => (1/2 : ℝ)) (DecideD_table b N) a = 0 := by
  simp only [barMu, DecideD_marginal]
  cases b
  · simp [(DecideD_sign_facts N).1]
  · simp only [Bool.true_eq, if_true, ← Finset.sum_mul, ← Finset.mul_sum,
      (DecideD_sign_facts N).1, mul_zero, zero_mul, zero_div]

lemma DecideD_ame (b : Bool) (N : ℕ) :
    ame (fun _ => (1/2 : ℝ)) (DecideD_table b N) = 0 := by
  unfold ame nodeEffect
  rw [Finset.sum_sub_distrib, sub_div]
  change barMu _ _ true - barMu _ _ false = 0
  rw [DecideD_barMu, DecideD_barMu, sub_self]

def DecideD_S (N : ℕ) (z : Assignment N) : ℝ := ∑ i, DecideD_sign N i * bit (z i)
def DecideD_Q (N : ℕ) (z : Assignment N) : ℝ := ∑ i, (DecideD_sign N i)^2 * bit (z i)

lemma DecideD_linear (b : Bool) (N : ℕ) :
    linearHajek (fun _ => (1/2 : ℝ)) (DecideD_table b N) =
      fun z => 4 * DecideD_S N z / N := by
  funext z
  simp only [linearHajek, augmented, DecideD_barMu, sub_zero, sub_self, zero_add]
  have he (i : Fin N) :
      bit (z i) * DecideD_table b N i z / (1/2) -
        (1-bit (z i)) * DecideD_table b N i z / (1-1/2) =
      4 * (DecideD_sign N i * bit (z i)) - (if b then 0 else 2 * DecideD_sign N i) := by
    cases b <;> cases hz : z i <;> norm_num [DecideD_table, bit, hz] <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  cases b <;> simp [DecideD_S, ← Finset.mul_sum, (DecideD_sign_facts N).1]

lemma DecideD_linear_variance (b : Bool) (N : ℕ) :
    variance (fun _ => (1/2 : ℝ)) (linearHajek (fun _ => (1/2 : ℝ))
      (DecideD_table b N)) = 4 * DecideD_mass N / (N : ℝ)^2 := by
  rw [DecideD_linear]
  have he : (fun z : Assignment N => 4 * DecideD_S N z / N) =
      fun z => (∑ i, (4 * DecideD_sign N i) * bit (z i)) / N := by
    funext z
    simp [DecideD_S, Finset.mul_sum, mul_assoc]
  rw [he, variance_div, (DecideD_weighted_moments _).2]
  have hs : (∑ i : Fin N, (4 * DecideD_sign N i)^2) = 16 * DecideD_mass N := by
    simp [DecideD_mass, Finset.mul_sum, mul_pow]
    ring
  rw [hs]
  ring

lemma DecideD_nondegenerate (f : ℕ → Bool) :
    Nondegenerate (fun N => variance (fun _ => (1/2 : ℝ))
      (linearHajek (fun _ => (1/2 : ℝ)) (circleAverage (DecideD_population f N) 0))) := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  rw [DecideD_circle, DecideD_linear_variance]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hm := (DecideD_sign_facts N).2.2.2.1
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith

/-- A finite-array law of large numbers, proved directly from the design variance. -/
lemma DecideD_weighted_inProb (c : ∀ N, Fin N → ℝ) (m : ℝ)
    (hc : ∀ N, (∑ i, (c N i)^2) ≤ (N : ℝ))
    (hm : Tendsto (fun N => (∑ i, c N i) / N) atTop (𝓝 m)) :
    InProb (fun _ _ => (1/2 : ℝ))
      (fun N z => (∑ i, c N i * bit (z i)) / N - m/2) := by
  let p : ∀ N, Fin N → ℝ := fun _ _ => 1/2
  have hp : DesignLimits.AdmissibleSeq p := fun _ i => DecideD_half i
  let X : ∀ N, Assignment N → ℝ := fun N z => (∑ i, c N i * bit (z i)) / N
  let μ : ℕ → ℝ := fun N => ((∑ i, c N i) / N) / 2
  have he (N : ℕ) : expect (p N) (X N) = μ N := by
    dsimp [X, μ, p]
    rw [expect_div, (DecideD_weighted_moments _).1]
    ring
  have hv (N : ℕ) :
      expect (p N) (fun z => (X N z - μ N)^2) = (∑ i, (c N i)^2) / (4 * (N : ℝ)^2) := by
    have h := cov_centered (p N) (X N) (X N)
    rw [he] at h
    change variance (p N) (X N) = _ at h
    simp only [← pow_two] at h
    rw [← h]
    dsimp [X, p]
    rw [variance_div, (DecideD_weighted_moments _).2]
    ring
  have hcenter : InProb p (fun N z => X N z - μ N) := by
    apply (DesignLimits.dl2_proof p hp _).2
    have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ / 4) atTop (𝓝 0) := by
      simpa using (tendsto_natCast_atTop_atTop.inv_tendsto_atTop).div_const (4 : ℝ)
    apply squeeze_zero' _ _ hi
    · apply Eventually.of_forall
      intro N
      rw [hv]
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      rw [hv]
      have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      calc
        (∑ i, (c N i)^2) / (4 * (N : ℝ)^2) ≤ N / (4 * (N : ℝ)^2) :=
          div_le_div_of_nonneg_right (hc N) (by positivity)
        _ = (N : ℝ)⁻¹ / 4 := by field_simp
  have hdet : InProb p (fun N _ => μ N - m/2) := by
    apply (DesignLimits.dl4_proof p hp).2.2
    simpa [μ] using (hm.div_const 2).sub_const (m/2)
  have hadd := (DesignLimits.dl4_proof p hp).1 _ _ hcenter hdet
  convert hadd using 1
  funext N z
  dsimp [X]
  ring

lemma DecideD_S_inProb :
    InProb (fun _ _ => (1/2 : ℝ)) (fun N z => DecideD_S N z / N) := by
  simpa [DecideD_S] using DecideD_weighted_inProb DecideD_sign 0
    (fun N => (DecideD_sign_facts N).2.2.2.2)
    (by simpa only [(DecideD_sign_facts _).1, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

lemma DecideD_Q_inProb :
    InProb (fun _ _ => (1/2 : ℝ)) (fun N z => DecideD_Q N z / N - 1/2) := by
  apply DecideD_weighted_inProb (fun N i => (DecideD_sign N i)^2) 1 _ DecideD_mass_ratio
  intro N
  have he : (∑ i : Fin N, ((DecideD_sign N i)^2)^2) = DecideD_mass N := by
    simp only [← pow_mul, (DecideD_sign_facts N).2.1, DecideD_mass]
  rw [he]
  exact (DecideD_sign_facts N).2.2.2.2

lemma DecideD_count_inProb :
    InProb (fun _ _ => (1/2 : ℝ)) (fun N z => armCount z true / N - 1/2) := by
  have h := DecideD_weighted_inProb (fun N (_ : Fin N) => (1 : ℝ)) 1
    (by intro N; simp) ?_
  · convert h using 1
    funext N z
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [bit, hz]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    simp [ne_of_gt (Nat.cast_pos.mpr hN)]

lemma DecideD_mass_inProb :
    InProb (fun _ _ => (1/2 : ℝ)) (fun N _ => DecideD_mass N / N - 1) := by
  exact (DesignLimits.dl4_proof _ (fun _ i => DecideD_half i)).2.2 _
    (by simpa using DecideD_mass_ratio.sub_const 1)

lemma DecideD_selected {N : ℕ} (c : Fin N → ℝ) (z : Assignment N) (a : Bool) :
    (∑ i, if z i = a then c i else 0) =
      if a then (∑ i, c i * bit (z i)) else (∑ i, c i) - (∑ i, c i * bit (z i)) := by
  cases a
  · simp only [Bool.false_eq_true, if_false, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [bit, hz]
  · simp only [if_true]
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [bit, hz]

lemma DecideD_selected_table (b : Bool) (N : ℕ) (z : Assignment N) (a : Bool) :
    (∑ i, if z i = a then DecideD_table b N i z else 0) =
      if b then (if a then 2 * DecideD_S N z else 0)
      else (if a then DecideD_S N z else -DecideD_S N z) := by
  cases b
  · simpa [DecideD_table, DecideD_S, (DecideD_sign_facts N).1] using
      DecideD_selected (DecideD_sign N) z a
  · cases a
    · apply Finset.sum_eq_zero
      intro i _
      cases hz : z i <;> simp [DecideD_table, bit, hz]
    · simp only [if_true, DecideD_S, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases hz : z i <;> simp [DecideD_table, bit, hz]

lemma DecideD_selected_square (b : Bool) (N : ℕ) (z : Assignment N) (a : Bool) :
    (∑ i, if z i = a then (DecideD_table b N i z)^2 else 0) =
      if b then (if a then 4 * DecideD_Q N z else 0)
      else (if a then DecideD_Q N z else DecideD_mass N - DecideD_Q N z) := by
  cases b
  · simpa [DecideD_table, DecideD_Q, DecideD_mass] using
      DecideD_selected (fun i => (DecideD_sign N i)^2) z a
  · cases a
    · apply Finset.sum_eq_zero
      intro i _
      cases hz : z i <;> simp [DecideD_table, bit, hz]
    · simp only [if_true, DecideD_Q, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases hz : z i <;> simp [DecideD_table, bit, hz] <;> ring

/-- The fitted within-arm square sum, including Lean's empty-arm convention. -/
lemma DecideD_residual_squares {N : ℕ} (R : CircleTable N) (z : Assignment N) (a : Bool) :
    (∑ i, if z i = a then (R i z - armMean R z a)^2 else 0) =
      (∑ i, if z i = a then (R i z)^2 else 0) -
        (∑ i, if z i = a then R i z else 0)^2 / armCount z a := by
  let s : ℝ := ∑ i, if z i = a then R i z else 0
  let n := armCount z a
  have hexpand (i : Fin N) : (if z i = a then (R i z - armMean R z a)^2 else 0) =
      (if z i = a then (R i z)^2 else 0) -
        2 * (s/n) * (if z i = a then R i z else 0) +
        (s/n)^2 * (if z i = a then (1 : ℝ) else 0) := by
    change (if z i = a then (R i z - s/n)^2 else 0) = _
    split_ifs <;> ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  change _ - 2 * (s/n) * s + (s/n)^2 * n = _ - s^2/n
  by_cases hn : n = 0
  · simp [hn]
  · field_simp
    <;> ring

def DecideD_raw (b : Bool) (N : ℕ) (z : Assignment N) : ℝ :=
  rawSAH (fun _ => (1/2 : ℝ)) (DecideD_table b N) (fun i => {i})
    (fun _ a => armMean (DecideD_table b N) z a) z

lemma DecideD_raw_formula (b : Bool) (N : ℕ) (z : Assignment N) :
    DecideD_raw b N z =
      if b then 16 * (DecideD_Q N z - (DecideD_S N z)^2 / armCount z true) / (N : ℝ)^2
      else 4 * (DecideD_mass N - (DecideD_S N z)^2 / armCount z true -
        (DecideD_S N z)^2 / armCount z false) / (N : ℝ)^2 := by
  have hi (i : Fin N) :
      bit (z i) * (DecideD_table b N i z - armMean (DecideD_table b N) z true)^2 / (1/2)^2 +
        (1-bit (z i)) * (DecideD_table b N i z - armMean (DecideD_table b N) z false)^2 / (1-1/2)^2 =
      4 * ((if z i = true then (DecideD_table b N i z - armMean (DecideD_table b N) z true)^2 else 0) +
        (if z i = false then (DecideD_table b N i z - armMean (DecideD_table b N) z false)^2 else 0)) := by
    cases hz : z i <;> norm_num [bit, hz] <;> ring
  unfold DecideD_raw rawSAH
  simp only [Finset.card_singleton, Nat.cast_one, one_mul]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, DecideD_residual_squares,
    DecideD_residual_squares]
  simp only [DecideD_selected_table, DecideD_selected_square]
  cases b <;> simp only [if_true, Bool.false_eq_true, if_false, zero_pow (by omega : 2 ≠ 0),
    zero_div, sub_zero] <;> ring

def DecideD_stats (N : ℕ) (z : Assignment N) : Fin 4 → ℝ :=
  ![DecideD_mass N / N, DecideD_S N z / N, armCount z true / N, DecideD_Q N z / N]

def DecideD_center : Fin 4 → ℝ := ![1, 0, 1/2, 1/2]

def DecideD_varianceMap (b : Bool) (x : Fin 4 → ℝ) : ℝ :=
  (if b then 16 * (x 3 - (x 1)^2 / x 2)
    else 4 * (x 0 - (x 1)^2 / x 2 - (x 1)^2 / (1-x 2))) / (4 * x 0)

def DecideD_W (b : Bool) (N : ℕ) (z : Assignment N) : ℝ :=
  DecideD_varianceMap b (DecideD_stats N z)

lemma DecideD_W_inProb (b : Bool) :
    InProb (fun _ _ => (1/2 : ℝ))
      (fun N z => DecideD_W b N z - (if b then 2 else 1)) := by
  have hcont : ContinuousAt (DecideD_varianceMap b) DecideD_center := by
    have h (i : Fin 4) : ContinuousAt (fun x : Fin 4 → ℝ => x i) DecideD_center :=
      (continuous_apply i).continuousAt
    have ht := ((h 1).pow 2).div (h 2) (by norm_num [DecideD_center])
    have hc := ((h 1).pow 2).div
      ((continuousAt_const : ContinuousAt (fun _ : Fin 4 → ℝ => (1 : ℝ)) DecideD_center).sub (h 2))
      (by norm_num [DecideD_center])
    cases b
    · exact (continuousAt_const.mul (((h 0).sub ht).sub hc)).div
        (continuousAt_const.mul (h 0)) (by norm_num [DecideD_center])
    · exact (continuousAt_const.mul ((h 3).sub ht)).div
        (continuousAt_const.mul (h 0)) (by norm_num [DecideD_center])
  have hstats (i : Fin 4) : InProb (fun _ _ => (1/2 : ℝ))
      (fun N z => DecideD_stats N z i - DecideD_center i) := by
    fin_cases i
    · exact DecideD_mass_inProb
    · change InProb _ (fun N z => DecideD_S N z / N - 0)
      simpa only [sub_zero] using DecideD_S_inProb
    · exact DecideD_count_inProb
    · exact DecideD_Q_inProb
  have h := DesignLimits.dl9_proof (fun _ _ => (1/2 : ℝ)) (fun _ i => DecideD_half i)
    (fun i N z => DecideD_stats N z i) DecideD_center (DecideD_varianceMap b) hcont hstats
  convert h using 1
  funext N z
  cases b <;> norm_num [DecideD_varianceMap, DecideD_center, DecideD_W]

lemma DecideD_W_eq (b : Bool) (N : ℕ) (hN : 0 < N) (z : Assignment N) :
    DecideD_W b N z = DecideD_raw b N z / (4 * DecideD_mass N / (N : ℝ)^2) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hc := MatrixCompletion.counts_total z
  have hc0 : armCount z false = (N : ℝ) - armCount z true := by linarith
  rw [DecideD_raw_formula, hc0]
  unfold DecideD_W DecideD_varianceMap DecideD_stats
  cases b <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Bool.false_eq_true, if_false, if_true]
  all_goals
    try rw [show 1 - armCount z true / N = ((N : ℝ) - armCount z true) / N by field_simp]
  all_goals
    simp only [div_pow, div_div]
    field_simp
    <;> ring

def DecideD_V (N : ℕ) : ℝ := 4 * DecideD_mass N / (N : ℝ)^2

lemma DecideD_V_pos (N : ℕ) (hN : 2 ≤ N) : 0 < DecideD_V N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : 0 < DecideD_mass N := by linarith [(DecideD_sign_facts N).2.2.2.1]
  unfold DecideD_V
  positivity

def DecideD_T (b : Bool) (N : ℕ) (z : Assignment N) : ℝ :=
  hajek (DecideD_table b N) z / Real.sqrt (DecideD_V N)

lemma DecideD_numerator_clt (b : Bool) :
    NormalLimit (fun _ _ => (1/2 : ℝ)) (DecideD_T b) := by
  unfold DecideD_T
  have h := hajek_central_limit_proof (DecideD_population (fun _ => b)) (1/2) 0
    (by norm_num) le_rfl (DecideD_spatial _) (DecideD_wellDefined _)
    (DecideD_nondegenerate _)
  simpa only [DecideD_circle, DecideD_ame, sub_zero, DecideD_linear_variance,
    DecideD_T, DecideD_V] using h

def DecideD_q : ℝ := normalQuantile (3/4)

lemma DecideD_quantiles : 0 < DecideD_q ∧ normalQuantile (1/4) = -DecideD_q := by
  obtain ⟨_, hm, hz, hneg, hquant, _, _⟩ := DesignLimits.nf_proof
  have hq : normalCDF DecideD_q = 3/4 := hquant _ (by norm_num) (by norm_num)
  constructor
  · apply hm.lt_iff_lt.mp
    rw [hz, hq]
    norm_num
  · apply hm.injective
    rw [hquant _ (by norm_num) (by norm_num), hneg, hq]
    norm_num

def DecideD_coverage (b : Bool) (N : ℕ) : ℝ :=
  prob (fun _ => (1/2 : ℝ)) (fun z =>
    |hajek (DecideD_table b N) z / Real.sqrt (DecideD_raw b N z)| ≤ DecideD_q)

lemma DecideD_coverage_limit (b : Bool) :
    Tendsto (DecideD_coverage b) atTop
      (𝓝 (2 * normalCDF (DecideD_q * Real.sqrt (if b then 2 else 1)) - 1)) := by
  let w : ℝ := if b then 2 else 1
  have hw : 0 < w := by cases b <;> norm_num [w]
  let p : ∀ N, Fin N → ℝ := fun _ _ => 1/2
  have hp : DesignLimits.AdmissibleSeq p := fun _ i => DecideD_half i
  let A : ∀ N, Assignment N → Prop := fun N z =>
    |DecideD_T b N z| ≤ DecideD_q * Real.sqrt (DecideD_W b N z)
  let E : ∀ N, Assignment N → Prop := fun N z =>
    w/2 < |DecideD_W b N z - w|
  have hW := DecideD_W_inProb b
  have hA : Tendsto (fun N => prob (p N) (A N)) atTop
      (𝓝 (2 * normalCDF (DecideD_q * Real.sqrt w) - 1)) := by
    simpa only [div_one] using DesignLimits.dl8_proof p hp (DecideD_T b) (DecideD_W b)
      1 w DecideD_q (by norm_num) hw DecideD_quantiles.1
      (by simpa only [div_one] using DecideD_numerator_clt b) hW
  have hE : Tendsto (fun N => prob (p N) (E N)) atTop (𝓝 0) := hW (w/2) (half_pos hw)
  have hequiv (N : ℕ) (hN : 2 ≤ N) (z : Assignment N) (hE : ¬ E N z) :
      A N z ↔ |hajek (DecideD_table b N) z / Real.sqrt (DecideD_raw b N z)| ≤ DecideD_q := by
    have hclose : |DecideD_W b N z - w| ≤ w/2 := le_of_not_gt hE
    have hWp : 0 < DecideD_W b N z := by linarith [(abs_le.mp hclose).1]
    have hVp := DecideD_V_pos N hN
    have hraw : DecideD_raw b N z = DecideD_W b N z * DecideD_V N := by
      have he := DecideD_W_eq b N (by omega) z
      change DecideD_W b N z = DecideD_raw b N z / DecideD_V N at he
      exact ((eq_div_iff hVp.ne').mp he).symm
    have hrp : 0 < DecideD_raw b N z := by rw [hraw]; positivity
    have hs : Real.sqrt (DecideD_raw b N z) =
        Real.sqrt (DecideD_W b N z) * Real.sqrt (DecideD_V N) := by
      rw [hraw, Real.sqrt_mul hWp.le]
    dsimp only [A, DecideD_T]
    rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hVp),
      div_le_iff₀ (Real.sqrt_pos.mpr hVp), abs_div,
      abs_of_pos (Real.sqrt_pos.mpr hrp), div_le_iff₀ (Real.sqrt_pos.mpr hrp), hs]
    rw [mul_assoc]
  have hbound : ∀ᶠ N in atTop,
      prob (p N) (A N) - prob (p N) (E N) ≤ DecideD_coverage b N ∧
        DecideD_coverage b N ≤ prob (p N) (A N) + prob (p N) (E N) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hlo : prob (p N) (A N) ≤ DecideD_coverage b N + prob (p N) (E N) := by
      apply DesignLimits.prob_le_add_of_imp_finite (p N) (hp N)
      intro z hz
      by_cases he : E N z
      · exact Or.inr he
      · exact Or.inl ((hequiv N hN z he).mp hz)
    have hhi : DecideD_coverage b N ≤ prob (p N) (A N) + prob (p N) (E N) := by
      apply DesignLimits.prob_le_add_of_imp_finite (p N) (hp N)
      intro z hz
      by_cases he : E N z
      · exact Or.inr he
      · exact Or.inl ((hequiv N hN z he).mpr hz)
    exact ⟨by linarith, hhi⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hA.sub hE)
    (by simpa only [add_zero] using hA.add hE) (hbound.mono fun _ h => h.1)
    (hbound.mono fun _ h => h.2)

def DecideD_alternating (N : ℕ) : Bool := if Even N then false else true

lemma DecideD_two_limits_distinct :
    2 * normalCDF (DecideD_q * Real.sqrt (1 : ℝ)) - 1 <
      2 * normalCDF (DecideD_q * Real.sqrt (2 : ℝ)) - 1 := by
  have hs : 1 < Real.sqrt (2 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have harg : DecideD_q * Real.sqrt (1 : ℝ) < DecideD_q * Real.sqrt (2 : ℝ) := by
    simpa using mul_lt_mul_of_pos_left hs DecideD_quantiles.1
  have hmono := DesignLimits.nf_proof.2.1 harg
  linarith

/-- The ordinary limit fails, although both subsequences have conservative coverage. -/
lemma DecideD_no_limit :
    ¬ ∃ L : ℝ, Tendsto (fun N => DecideD_coverage (DecideD_alternating N) N) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have he : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    exact eventually_atTop.2 ⟨k, fun n hn => by omega⟩
  have ho : Tendsto (fun n : ℕ => 2*n+1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    exact eventually_atTop.2 ⟨k, fun n hn => by omega⟩
  have hAe : Tendsto (fun n => DecideD_coverage false (2*n)) atTop (𝓝 L) := by
    simpa [Function.comp_def, DecideD_alternating] using hL.comp he
  have hBo : Tendsto (fun n => DecideD_coverage true (2*n+1)) atTop (𝓝 L) := by
    simpa [Function.comp_def, DecideD_alternating] using hL.comp ho
  have hA := (DecideD_coverage_limit false).comp he
  have hB := (DecideD_coverage_limit true).comp ho
  have hLA := tendsto_nhds_unique hAe hA
  have hLB := tendsto_nhds_unique hBo hB
  have hlt := DecideD_two_limits_distinct
  simp only [Bool.false_eq_true, if_false, if_true] at hLA hLB
  rw [← hLA, ← hLB] at hlt
  exact (lt_irrefl _ hlt)

lemma DecideD_printed_probability (f : ℕ → Bool) (N : ℕ) :
    prob (fun _ => (1/2 : ℝ)) (fun z =>
      let R := circleAverage (DecideD_population f N) 0
      let V := rawSAH (fun _ => (1/2 : ℝ)) R (spatialNeighborhoods (DecideD_population f) 0 N)
        (fun _ a => armMean R z a) z
      normalQuantile ((1/2)/2) ≤ (hajek R z - ame (fun _ => (1/2 : ℝ)) R) / Real.sqrt V ∧
        (hajek R z - ame (fun _ => (1/2 : ℝ)) R) / Real.sqrt V ≤ normalQuantile (1-(1/2)/2)) =
      DecideD_coverage (f N) N := by
  unfold DecideD_coverage
  apply DesignLimits.DLbSupport.prob_congr
  intro z
  dsimp only
  rw [DecideD_circle, DecideD_ame, sub_zero]
  have hb : spatialNeighborhoods (DecideD_population f) 0 N = fun i => {i} := by
    funext i
    exact LinePopulation.line_zero_ball _ i
  rw [hb]
  norm_num only [show (1/2 : ℝ)/2 = 1/4 by norm_num,
    show (1 : ℝ) - (1/2)/2 = 3/4 by norm_num]
  rw [DecideD_quantiles.2]
  exact abs_le.symm

/-- The same Euclidean construction in an arbitrary universe. -/
def DecideD_liftLine {N : ℕ} (R : CircleTable N) :
    SpatialPopulation N (ULift.{u} (EuclideanSpace ℝ (Fin 2))) where
  node i := {ULift.up (planePoint (10 * (i : ℝ)) 0)}
  node_nonempty _ := Set.singleton_nonempty _
  zeta := Measure.map (MeasurableEquiv.ulift.symm :
    EuclideanSpace ℝ (Fin 2) ≃ᵐ ULift.{u} (EuclideanSpace ℝ (Fin 2))) (linePopulation R).zeta
  outcome x z := (linePopulation R).outcome x.down z
  bands d := Set.Icc 0 d

lemma DecideD_lift_separation {N : ℕ} (R : CircleTable N) :
    nodeSeparation (DecideD_liftLine.{u} R) = nodeSeparation (linePopulation R) := by
  funext i j
  simp [nodeSeparation, DecideD_liftLine, linePopulation, ULift.dist_eq]

lemma DecideD_lift_region {N : ℕ} (R : CircleTable N) (i : Fin N) (d : ℝ) :
    region (DecideD_liftLine.{u} R) i d = ULift.down ⁻¹' region (linePopulation R) i d := by
  ext x
  simp [region, nodeDistance, DecideD_liftLine, linePopulation,
    Metric.infDist_singleton, ULift.dist_eq]

lemma DecideD_lift_preimage {N : ℕ} (R : CircleTable N) (i : Fin N) (d : ℝ) :
    (MeasurableEquiv.ulift.symm : EuclideanSpace ℝ (Fin 2) ≃ᵐ
      ULift.{u} (EuclideanSpace ℝ (Fin 2))) ⁻¹' region (DecideD_liftLine R) i d =
        region (linePopulation R) i d := by
  rw [DecideD_lift_region]
  rfl

lemma DecideD_lift_mass {N : ℕ} (R : CircleTable N) (i : Fin N) (d : ℝ) :
    (DecideD_liftLine.{u} R).zeta (region (DecideD_liftLine R) i d) =
      (linePopulation R).zeta (region (linePopulation R) i d) := by
  change (Measure.map (MeasurableEquiv.ulift.symm : EuclideanSpace ℝ (Fin 2) ≃ᵐ
    ULift.{u} (EuclideanSpace ℝ (Fin 2))) (linePopulation R).zeta) _ = _
  rw [MeasurableEquiv.map_apply, DecideD_lift_preimage]

lemma DecideD_lift_circle {N : ℕ} (R : CircleTable N) (d : ℝ) :
    circleAverage (DecideD_liftLine.{u} R) d = circleAverage (linePopulation R) d := by
  funext i z
  unfold circleAverage
  rw [DecideD_lift_mass]
  congr 1
  change (∫ x in region (DecideD_liftLine R) i d, (linePopulation R).outcome x.down z
    ∂Measure.map (MeasurableEquiv.ulift.symm : EuclideanSpace ℝ (Fin 2) ≃ᵐ
      ULift.{u} (EuclideanSpace ℝ (Fin 2))) (linePopulation R).zeta) = _
  rw [setIntegral_map_equiv, DecideD_lift_preimage]
  rfl

lemma DecideD_lift_wellDefined {N : ℕ} (R : CircleTable N) (d : ℝ) (hd : 0 ≤ d) :
    WellDefined (DecideD_liftLine.{u} R) d := by
  intro i
  obtain ⟨_, hpos, hfin, _⟩ := LinePopulation.n4_proof R d hd i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [DecideD_lift_region]
    exact (LinePopulation.line_region_measurable R d i).preimage measurable_down
  · rwa [DecideD_lift_mass]
  · rwa [DecideD_lift_mass]
  · intro z
    have hi : Integrable (fun x => (linePopulation R).outcome x z) (linePopulation R).zeta := by
      change Integrable _ (∑ j : Fin N, Measure.dirac (planePoint (10 * (j : ℝ)) 0))
      rw [integrable_finsetSum_measure]
      intro j _
      exact integrable_dirac (by simp)
    have hmap : Integrable (fun x : ULift.{u} (EuclideanSpace ℝ (Fin 2)) =>
        (linePopulation R).outcome x.down z) (DecideD_liftLine R).zeta := by
      rw [DecideD_liftLine, integrable_map_equiv]
      exact hi
    exact hmap.integrableOn

def DecideD_liftPopulation (f : ℕ → Bool) (N : ℕ) :=
  DecideD_liftLine.{u} (DecideD_table (f N) N)

lemma DecideD_lift_spatial (f : ℕ → Bool) : SpatialLocalConditions (DecideD_liftPopulation.{u} f) := by
  obtain ⟨⟨b, hb, hbound⟩, ⟨h, hh, hloc⟩, ⟨c, hcount⟩⟩ := DecideD_spatial f
  refine ⟨⟨b, hb, ?_⟩, ⟨h, hh, ?_⟩, ⟨c, ?_⟩⟩
  · filter_upwards [hbound] with N hN x z
    exact hN x.down z
  · intro d hd
    filter_upwards [hloc d hd] with N hN
    change LocalAt (circleAverage (DecideD_liftLine (DecideD_table (f N) N)) d)
      (nodeSeparation (DecideD_liftLine (DecideD_table (f N) N))) (h d)
    rw [DecideD_lift_circle, DecideD_lift_separation]
    exact hN
  · intro r hr
    filter_upwards [hcount r hr] with N hN i
    change ((ball (nodeSeparation (DecideD_liftLine (DecideD_table (f N) N))) i r).card : ℝ) ≤ c r
    rw [DecideD_lift_separation]
    exact hN i

lemma DecideD_lift_guards (f : ℕ → Bool) :
    (∀ᶠ N in atTop, WellDefined (DecideD_liftPopulation.{u} f N) 0) ∧
    (∀ᶠ N in atTop, LocalAt (circleAverage (DecideD_liftPopulation.{u} f N) 0)
      (nodeSeparation (DecideD_liftPopulation.{u} f N)) 0) ∧
    Nondegenerate (fun N => variance (fun _ => (1/2 : ℝ))
      (linearHajek (fun _ => (1/2 : ℝ)) (circleAverage (DecideD_liftPopulation.{u} f N) 0))) := by
  refine ⟨Eventually.of_forall (fun N => DecideD_lift_wellDefined _ 0 le_rfl), ?_, ?_⟩
  · simpa only [DecideD_liftPopulation, DecideD_lift_circle, DecideD_lift_separation,
      DecideD_population] using DecideD_local f
  · simpa only [DecideD_liftPopulation, DecideD_lift_circle, DecideD_population] using
      DecideD_nondegenerate f

lemma DecideD_lift_probability (f : ℕ → Bool) (N : ℕ) :
    prob (fun _ => (1/2 : ℝ)) (fun z =>
      let R := circleAverage (DecideD_liftPopulation.{u} f N) 0
      let V := rawSAH (fun _ => (1/2 : ℝ)) R (spatialNeighborhoods (DecideD_liftPopulation.{u} f) 0 N)
        (fun _ a => armMean R z a) z
      normalQuantile ((1/2)/2) ≤ (hajek R z - ame (fun _ => (1/2 : ℝ)) R) / Real.sqrt V ∧
        (hajek R z - ame (fun _ => (1/2 : ℝ)) R) / Real.sqrt V ≤ normalQuantile (1-(1/2)/2)) =
      DecideD_coverage (f N) N := by
  have h := DecideD_printed_probability f N
  unfold spatialNeighborhoods at h ⊢
  simpa only [DecideD_liftPopulation, DecideD_lift_circle,
    DecideD_lift_separation, DecideD_population] using h

theorem experimental_wald_coverage_printed_false :
  ¬ (∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d h : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hh : 0 ≤ h)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hv : Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))),
    let R := circleSequence P d
    let B := spatialNeighborhoods P h
    ∀ α : ℝ, 0 < α → α < 1 →
      PrintedCoverage (fun N => prob (fun _ => p) (fun z =>
        let V := rawSAH (fun _ => p) (R N) (B N) (fun _ a => armMean (R N) z a) z
        normalQuantile (α/2) ≤ (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt V ∧
          (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt V ≤ normalQuantile (1-α/2))) α ∧
      ((∀ᶠ N in atTop, 0 ≤ homophilyQ (fun _ => p) (R N) (B N) (fun _ a => barMu (fun _ => p) (R N) a)) →
        PrintedCoverage (fun N => prob (fun _ => p) (fun z =>
          let V := kernelVariance z (residual (R N) z) (Matrix.of (fun i j => if nodeSeparation (P N) i j ≤ h then 1 else 0))
          normalQuantile (α/2) ≤ (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt V ∧
            (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt V ≤ normalQuantile (1-α/2))) α)) := by
  intro h
  have hc := (h (Space := fun _ => ULift.{_} (EuclideanSpace ℝ (Fin 2)))
    (DecideD_liftPopulation DecideD_alternating) (1/2) 0 0
    (by norm_num) le_rfl le_rfl (DecideD_lift_spatial _) (DecideD_lift_guards _).1
    (DecideD_lift_guards _).2.1 (DecideD_lift_guards _).2.2 (1/2) (by norm_num) (by norm_num)).1
  obtain ⟨L, hL, _⟩ := hc
  apply DecideD_no_limit
  exact ⟨L, Filter.Tendsto.congr (DecideD_lift_probability DecideD_alternating) hL⟩

end
end AronowAudit.P004.Wave1
