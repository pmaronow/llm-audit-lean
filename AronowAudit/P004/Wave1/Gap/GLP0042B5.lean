import AronowAudit.P004.P004_Spatial
import AronowAudit.P004.P004_VarianceCompletion
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.Wave1.DesignLimits.NF
import AronowAudit.P004.Wave1.DesignLimits.DL9
import AronowAudit.P004.Wave1.DesignLimits.DL8
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The repeated-star adjusted-PD witness (P004-T7). -/

namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section

set_option maxHeartbeats 1000000

lemma t7_starY_abs (i : Fin 5) : |starY i| ≤ 1 := by
  fin_cases i <;> norm_num [starY]

lemma t7_starPoint_injective {N : ℕ} :
    Function.Injective (starPoint : Fin N → EuclideanSpace ℝ (Fin 2)) := by
  intro i j hij
  have hx := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hij
  have hy := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hij
  change 10 * ((i.val / 5 : ℕ) : ℝ) +
      (if i.val % 5 = 1 then 1 else if i.val % 5 = 3 then -1 else 0) =
    10 * ((j.val / 5 : ℕ) : ℝ) +
      (if j.val % 5 = 1 then 1 else if j.val % 5 = 3 then -1 else 0) at hx
  change (if i.val % 5 = 2 then (1 : ℝ) else if i.val % 5 = 4 then -1 else 0) =
    (if j.val % 5 = 2 then (1 : ℝ) else if j.val % 5 = 4 then -1 else 0) at hy
  have hbound (k : Fin N) :
      (-1 : ℝ) ≤ (if k.val % 5 = 1 then 1 else if k.val % 5 = 3 then -1 else 0) ∧
      (if k.val % 5 = 1 then (1 : ℝ) else if k.val % 5 = 3 then -1 else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hq₁ : ((i.val / 5 : ℕ) : ℝ) < ((j.val / 5 : ℕ) : ℝ) + 1 := by
    linarith [(hbound i).1, (hbound j).2]
  have hq₂ : ((j.val / 5 : ℕ) : ℝ) < ((i.val / 5 : ℕ) : ℝ) + 1 := by
    linarith [(hbound j).1, (hbound i).2]
  have hq₁' : i.val / 5 < j.val / 5 + 1 := by exact_mod_cast hq₁
  have hq₂' : j.val / 5 < i.val / 5 + 1 := by exact_mod_cast hq₂
  have hq : i.val / 5 = j.val / 5 := by omega
  have hi : i.val % 5 < 5 := Nat.mod_lt _ (by omega)
  have hj : j.val % 5 < 5 := Nat.mod_lt _ (by omega)
  have hr : i.val % 5 = j.val % 5 := by
    rw [hq] at hx
    clear hij hbound hq₁ hq₂ hq₁' hq₂' hq
    generalize hri : i.val % 5 = ri at hi hx hy ⊢
    generalize hrj : j.val % 5 = rj at hj hx hy ⊢
    interval_cases ri <;> interval_cases rj
    all_goals try norm_num at hx
    all_goals try norm_num at hy
    all_goals first | rfl | linarith
  apply Fin.val_injective
  omega

lemma t7_star_separation {N : ℕ} (i j : Fin N) :
    nodeSeparation (starPopulation N) i j = dist (starPoint i) (starPoint j) := by
  simp [nodeSeparation, starPopulation]

lemma t7_star_region {N : ℕ} (i : Fin N) :
    region (starPopulation N) i 0 = {starPoint i} := by
  ext x
  simp [region, nodeDistance, starPopulation, Metric.infDist_singleton]

lemma t7_star_outcome_at_atom {N : ℕ} (i : Fin N) (z : Assignment N) :
    (starPopulation N).outcome (starPoint i) z =
      starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩ := by
  change (∑ j : Fin N, if starPoint i = starPoint j then
    starY ⟨j.val % 5, Nat.mod_lt _ (by omega)⟩ else 0) = _
  simp only [t7_starPoint_injective.eq_iff]
  simp

lemma t7_star_mass {N : ℕ} (i : Fin N) :
    (starPopulation N).zeta (region (starPopulation N) i 0) = 1 := by
  rw [t7_star_region]
  change (∑ j : Fin N, Measure.dirac (starPoint j)) {starPoint i} = 1
  rw [Measure.finsetSum_apply]
  simp [Pi.single_apply, t7_starPoint_injective.eq_iff]

lemma t7_star_integrable {N : ℕ} (z : Assignment N) :
    Integrable (fun x => (starPopulation N).outcome x z) (starPopulation N).zeta := by
  change Integrable _ (∑ j : Fin N, Measure.dirac (starPoint j))
  rw [integrable_finsetSum_measure]
  intro j _
  exact integrable_dirac (by simp)

lemma t7_star_wellDefined (N : ℕ) : WellDefined (starPopulation N) 0 := by
  intro i
  refine ⟨?_, ?_, ?_, fun z => (t7_star_integrable z).integrableOn⟩
  · rw [t7_star_region]
    exact measurableSet_singleton _
  · rw [t7_star_mass]
    norm_num
  · rw [t7_star_mass]
    norm_num

lemma t7_star_circleAverage (N : ℕ) (i : Fin N) (z : Assignment N) :
    circleAverage (starPopulation N) 0 i z =
      starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩ := by
  rw [circleAverage, t7_star_mass, t7_star_region]
  rw [integral_singleton]
  have hm : (starPopulation N).zeta.real {starPoint i} = 1 := by
    rw [Measure.real, ← t7_star_region, t7_star_mass]
    norm_num
  simp [hm, t7_star_outcome_at_atom]

lemma t7_star_outcome_abs (N : ℕ) (x : EuclideanSpace ℝ (Fin 2))
    (z : Assignment N) : |(starPopulation N).outcome x z| ≤ 1 := by
  by_cases hx : ∃ i : Fin N, x = starPoint i
  · obtain ⟨i, rfl⟩ := hx
    rw [t7_star_outcome_at_atom]
    exact t7_starY_abs _
  · have hz : (starPopulation N).outcome x z = 0 := by
      change (∑ i : Fin N, if x = starPoint i then
        starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩ else 0) = 0
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi => hx ⟨i, hi⟩)
    rw [hz]
    norm_num

lemma t7_star_circle_deterministic (N : ℕ) (d : ℝ) (i : Fin N)
    (z z' : Assignment N) :
    circleAverage (starPopulation N) d i z = circleAverage (starPopulation N) d i z' := rfl

lemma t7_star_local (N : ℕ) (d : ℝ) :
    LocalAt (circleAverage (starPopulation N) d) (nodeSeparation (starPopulation N)) 0 := by
  intro i j hij ⟨k, hi, hj⟩
  have hi' : i = k := by
    rcases hi with hi | ⟨z, z', _, hne⟩
    · exact hi
    · exact False.elim (hne (t7_star_circle_deterministic N d i z z'))
  have hj' : j = k := by
    rcases hj with hj | ⟨z, z', _, hne⟩
    · exact hj
    · exact False.elim (hne (t7_star_circle_deterministic N d j z z'))
  subst i
  subst j
  simpa [t7_star_separation] using hij

lemma t7_star_index_coord {N : ℕ} (i : Fin N) :
    |(i.val : ℝ) - starPoint i 0 / 2| ≤ 6 := by
  have hn : i.val = 5 * (i.val / 5) + i.val % 5 := by omega
  have hc : (i.val : ℝ) = 5 * ((i.val / 5 : ℕ) : ℝ) + ((i.val % 5 : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hr : ((i.val % 5 : ℕ) : ℝ) < 5 := by
    exact_mod_cast (Nat.mod_lt i.val (by omega : 0 < 5))
  have hr0 : (0 : ℝ) ≤ ((i.val % 5 : ℕ) : ℝ) := Nat.cast_nonneg _
  change |(i.val : ℝ) - (10 * ((i.val / 5 : ℕ) : ℝ) +
    (if i.val % 5 = 1 then 1 else if i.val % 5 = 3 then -1 else 0)) / 2| ≤ 6
  rw [hc]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

lemma t7_star_index_distance {N : ℕ} (i j : Fin N) (r : ℝ)
    (hr : 0 ≤ r) (hij : nodeSeparation (starPopulation N) i j ≤ r) :
    |(i.val : ℝ) - (j.val : ℝ)| ≤ r + 12 := by
  rw [t7_star_separation] at hij
  have hcoord : |starPoint i 0 - starPoint j 0| ≤ r :=
    (show |starPoint i 0 - starPoint j 0| ≤ dist (starPoint i) (starPoint j) from
      by simpa only [Real.dist_eq] using PiLp.dist_apply_le (starPoint i) (starPoint j) 0).trans hij
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp (t7_star_index_coord i)
  obtain ⟨hj₁, hj₂⟩ := abs_le.mp (t7_star_index_coord j)
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hcoord
  apply abs_le.mpr
  constructor <;> linarith

lemma t7_star_ball_card {N : ℕ} (i : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    ((ball (nodeSeparation (starPopulation N)) i r).card : ℝ) ≤ 2*r+25 := by
  classical
  let q : ℤ := ⌊r+12⌋
  let f : Fin N → ℤ := fun j => (j.val : ℤ) - (i.val : ℤ)
  have hq : 0 ≤ q := Int.floor_nonneg.mpr (by linarith)
  have hmaps : Set.MapsTo f
      (↑(ball (nodeSeparation (starPopulation N)) i r) : Set (Fin N))
      (↑(Finset.Icc (-q) q) : Set ℤ) := by
    intro j hj
    have hdist := t7_star_index_distance i j r hr (Finset.mem_filter.mp hj).2
    have hcast : (f j : ℝ) = (j.val : ℝ) - (i.val : ℝ) := by simp [f]
    have hu : f j ≤ q := by
      apply Int.le_floor.mpr
      rw [hcast]
      linarith [(abs_le.mp hdist).1]
    have hl : -f j ≤ q := by
      apply Int.le_floor.mpr
      rw [Int.cast_neg, hcast]
      linarith [(abs_le.mp hdist).2]
    exact Finset.mem_Icc.mpr ⟨by omega, hu⟩
  have hinj : (↑(ball (nodeSeparation (starPopulation N)) i r) : Set (Fin N)).InjOn f := by
    intro j _ k _ hjk
    have he : (j.val : ℤ) = (k.val : ℤ) := by
      dsimp [f] at hjk
      omega
    apply Fin.val_injective
    exact_mod_cast he
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hc : ((Finset.Icc (-q) q).card : ℤ) = 2*q+1 := by
    rw [Int.card_Icc_of_le (-q) q (by omega : -q ≤ q+1)]
    ring
  have hcr : ((Finset.Icc (-q) q).card : ℝ) = 2*(q : ℝ)+1 := by exact_mod_cast hc
  have hf : (q : ℝ) ≤ r+12 := Int.floor_le _
  calc
    _ ≤ ((Finset.Icc (-q) q).card : ℝ) := by exact_mod_cast hcard
    _ = 2*(q : ℝ)+1 := hcr
    _ ≤ 2*r+25 := by linarith

lemma t7_star_spatialLocal : SpatialLocalConditions starPopulation := by
  refine ⟨⟨2, by norm_num, Filter.Eventually.of_forall fun N x z => ?_⟩,
    ⟨fun _ => 0, fun _ _ => le_rfl, fun d _ => Filter.Eventually.of_forall fun N =>
      t7_star_local N d⟩,
    ⟨fun r => 2*r+25, fun r hr => Filter.Eventually.of_forall fun N i =>
      t7_star_ball_card i r hr⟩⟩
  exact (t7_star_outcome_abs N x z).trans_lt (by norm_num)

lemma t7_fixed_marginal {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (y : Fin N → ℝ) (i : Fin N) (a : Bool) :
    marginal p (fun i _ => y i) i a = y i := by
  rw [marginal_is_marginalization _ _ _ _ hp]
  exact expect_const p (y i)

lemma t7_fixed_homophily {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (y : Fin N → ℝ) (B : Fin N → Finset (Fin N)) :
    homophilyQ p (fun i _ => y i) B
      (fun _ a => barMu p (fun i _ => y i) a) = 0 := by
  have hm (a : Bool) : barMu p (fun i _ => y i) a = (∑ i, y i)/N := by
    simp only [barMu, t7_fixed_marginal p hp]
  simp [homophilyQ, residualEffect, nodeEffect, t7_fixed_marginal p hp, hm]

lemma t7_star_homophily (N : ℕ) :
    homophilyQ (fun _ => 1/2) (circleAverage (starPopulation N) 0)
      (spatialNeighborhoods starPopulation (6/5) N)
      (fun _ a => barMu (fun _ => 1/2) (circleAverage (starPopulation N) 0) a) = 0 := by
  have ht : circleAverage (starPopulation N) 0 =
      fun i _ => starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩ := by
    funext i z
    exact t7_star_circleAverage N i z
  rw [ht]
  exact t7_fixed_homophily _ (fun _ => by norm_num) _ _

lemma t7_fixed_variance {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) :
    variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (fun i _ => y i)) =
      4 * (∑ i, (y i - (∑ j, y j)/N)^2) / (N : ℝ)^2 := by
  have hp : ∀ i : Fin N, (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := fun _ => by norm_num
  have hout (i j : Fin N) (hij : j ∉ ({i} : Finset (Fin N))) :
      ¬ sharesSource (fun k _ => y k) i j := by
    rintro ⟨k, hi, hj⟩
    have he₁ : i = k := by
      rcases hi with h | ⟨_, _, _, h⟩
      · exact h
      · exact (h rfl).elim
    have he₂ : j = k := by
      rcases hj with h | ⟨_, _, _, h⟩
      · exact h
      · exact (h rfl).elim
    exact hij (Finset.mem_singleton.mpr (he₂.trans he₁.symm))
  rw [linearHajek, augmented_variance (fun _ => 1/2) _ (fun i => {i}) _ hN hp
    (fun _ => Finset.mem_singleton_self _) hout, t7_fixed_homophily _ hp]
  have hm (a : Bool) : barMu (fun _ => 1/2) (fun i _ => y i) a = (∑ i, y i)/N := by
    simp only [barMu, t7_fixed_marginal _ hp]
  simp only [secondMomentBound, hm, Finset.erase_singleton, Finset.sum_empty,
    Finset.sum_const_zero, add_zero, zero_div, sub_zero, t7_fixed_marginal _ hp]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma t7_sum_blocks (m : ℕ) (f : Fin 5 → ℝ) :
    (∑ i : Fin (5*m), f ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩) =
      (m : ℝ) * ∑ k : Fin 5, f k := by
  have hmod (k : Fin 5) : f ⟨k.val % 5, Nat.mod_lt _ (by omega)⟩ = f k := by
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [Nat.mul_comm 5 m]
  rw [← (finProdFinEquiv : Fin m × Fin 5 ≃ Fin (m*5)).sum_comp]
  simp [Fintype.sum_prod_type, finProdFinEquiv, Nat.add_mod, hmod]

lemma t7_star_block_moments (m : ℕ) :
    (∑ i : Fin (5*m), starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩) = 0 ∧
    (∑ i : Fin (5*m), (starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩)^2) = 4*m := by
  constructor
  · rw [t7_sum_blocks]
    norm_num [starY, Fin.sum_univ_succ]
  · rw [t7_sum_blocks m (fun k => (starY k)^2)]
    norm_num [starY, Fin.sum_univ_succ]
    ring

lemma t7_star_exact_variance (m : ℕ) (hm : 0 < m) :
    (5*m : ℝ) * variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (starBlockTable m)) = 16/5 := by
  have hn : 0 < 5*m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [show starBlockTable m = fun i _ => starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩ from rfl,
    t7_fixed_variance hn]
  simp only [(t7_star_block_moments m).1, zero_div, sub_zero, (t7_star_block_moments m).2]
  push_cast
  field_simp [hm0]
  <;> ring

lemma t7_star_prefix_moments (m r : ℕ) (hr : r < 5) :
    |∑ i : Fin (5*m+r), starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩| ≤ 2 ∧
    4*(m : ℝ) ≤ ∑ i : Fin (5*m+r), (starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩)^2 := by
  have hs : (∑ i : Fin (5*m+r), starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩) =
      ∑ i : Fin r, starY ⟨i.val, lt_trans i.isLt hr⟩ := by
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd, (t7_star_block_moments m).1, zero_add, Fin.val_natAdd]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_of_lt (lt_trans i.isLt hr)]
  have hq : (∑ i : Fin (5*m+r), (starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩)^2) =
      4*(m : ℝ) + ∑ i : Fin r, (starY ⟨i.val, lt_trans i.isLt hr⟩)^2 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd, (t7_star_block_moments m).2, Fin.val_natAdd]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_of_lt (lt_trans i.isLt hr)]
  rw [hs, hq]
  constructor
  · interval_cases r <;> norm_num [starY, Fin.sum_univ_succ]
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma t7_sum_centered_sq {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) :
    (∑ i, (y i - (∑ j, y j)/N)^2) =
      (∑ i, (y i)^2) - (∑ i, y i)^2/N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he (i : Fin N) : (y i - (∑ j, y j)/N)^2 =
      (y i)^2 - 2*((∑ j, y j)/N)*y i + ((∑ j, y j)/N)^2 := by ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn]
  <;> ring

lemma t7_star_nondegenerate :
    Nondegenerate (fun N => variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (circleAverage (starPopulation N) 0))) := by
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 10] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h10 : (10 : ℝ) ≤ N := by exact_mod_cast hN
  let y : Fin N → ℝ := fun i => starY ⟨i.val % 5, Nat.mod_lt _ (by omega)⟩
  have ht : circleAverage (starPopulation N) 0 = fun i _ => y i := by
    funext i z
    exact t7_star_circleAverage N i z
  have hpref := t7_star_prefix_moments (N/5) (N%5) (Nat.mod_lt N (by omega))
  have he : 5*(N/5)+N%5 = N := by omega
  rw [he] at hpref
  change |∑ i, y i| ≤ 2 ∧ 4*((N/5 : ℕ) : ℝ) ≤ ∑ i, (y i)^2 at hpref
  have hq : (N : ℝ)-4 ≤ 5*((N/5 : ℕ) : ℝ) := by
    have hh : (N : ℝ) ≤ 5*((N/5 : ℕ) : ℝ)+4 := by
      exact_mod_cast (show N ≤ 5*(N/5)+4 by omega)
    linarith
  have hss : (4/5 : ℝ)*((N : ℝ)-4) ≤ ∑ i, (y i)^2 := by linarith [hpref.2]
  have hs : (∑ i, y i)^2 ≤ 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg (∑ i, y i)) (by norm_num : (0:ℝ) ≤ 2)).mpr hpref.1
    simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using hh
  rw [ht, t7_fixed_variance (by omega), t7_sum_centered_sq (by omega)]
  have hformula : (N : ℝ) * (4*((∑ i, (y i)^2)-(∑ i, y i)^2/N)/(N : ℝ)^2) =
      (4*(N : ℝ)*(∑ i, (y i)^2)-4*(∑ i, y i)^2)/(N : ℝ)^2 := by
    field_simp [hn.ne']
    <;> ring
  rw [hformula]
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  have hm := mul_le_mul_of_nonneg_left hss hn.le
  nlinarith [mul_nonneg (sub_nonneg.mpr h10) hn.le]

lemma t7_star_offset_bounds {N : ℕ} (i : Fin N) :
    (-1 : ℝ) ≤ (if i.val % 5 = 1 then 1 else if i.val % 5 = 3 then -1 else 0) ∧
    (if i.val % 5 = 1 then (1 : ℝ) else if i.val % 5 = 3 then -1 else 0) ≤ 1 := by
  split_ifs <;> norm_num

lemma t7_star_near_block {N : ℕ} (i j : Fin N)
    (hnear : dist (starPoint i) (starPoint j) ≤ 6/5) : i.val/5 = j.val/5 := by
  have hc := (PiLp.dist_apply_le (starPoint i) (starPoint j) 0).trans hnear
  rw [Real.dist_eq] at hc
  change |(10*((i.val/5 : ℕ) : ℝ) +
      (if i.val%5 = 1 then 1 else if i.val%5 = 3 then -1 else 0)) -
    (10*((j.val/5 : ℕ) : ℝ) +
      (if j.val%5 = 1 then 1 else if j.val%5 = 3 then -1 else 0))| ≤ 6/5 at hc
  have hi : ((i.val/5 : ℕ) : ℝ) < ((j.val/5 : ℕ) : ℝ)+1 := by
    linarith [(abs_le.mp hc).2, (t7_star_offset_bounds i).1, (t7_star_offset_bounds j).2]
  have hj : ((j.val/5 : ℕ) : ℝ) < ((i.val/5 : ℕ) : ℝ)+1 := by
    linarith [(abs_le.mp hc).1, (t7_star_offset_bounds j).1, (t7_star_offset_bounds i).2]
  have hi' : i.val/5 < j.val/5+1 := by exact_mod_cast hi
  have hj' : j.val/5 < i.val/5+1 := by exact_mod_cast hj
  omega

lemma t7_plane_dist_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    (dist x y)^2 = (x 0-y 0)^2+(x 1-y 1)^2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma t7_star_same_block_near {N : ℕ} (i j : Fin N) (hq : i.val/5 = j.val/5) :
    dist (starPoint i) (starPoint j) ≤ 6/5 ↔
      i.val%5 = j.val%5 ∨ i.val%5 = 0 ∨ j.val%5 = 0 := by
  set D := dist (starPoint i) (starPoint j)
  have hd : 0 ≤ D := dist_nonneg
  have hs := t7_plane_dist_sq (starPoint i) (starPoint j)
  change D^2 =
    ((10*((i.val/5 : ℕ) : ℝ) + (if i.val%5 = 1 then 1 else if i.val%5 = 3 then -1 else 0)) -
      (10*((j.val/5 : ℕ) : ℝ) + (if j.val%5 = 1 then 1 else if j.val%5 = 3 then -1 else 0)))^2 +
    ((if i.val%5 = 2 then (1 : ℝ) else if i.val%5 = 4 then -1 else 0) -
      (if j.val%5 = 2 then (1 : ℝ) else if j.val%5 = 4 then -1 else 0))^2 at hs
  rw [hq] at hs
  have hi : i.val%5 < 5 := Nat.mod_lt _ (by omega)
  have hj : j.val%5 < 5 := Nat.mod_lt _ (by omega)
  change D ≤ 6/5 ↔ _
  generalize hri : i.val%5 = ri at hi hs ⊢
  generalize hrj : j.val%5 = rj at hj hs ⊢
  interval_cases ri <;> interval_cases rj
  all_goals norm_num at hs ⊢
  all_goals ring_nf at hs
  all_goals first | (rcases hs with hs | hs <;> nlinarith) | nlinarith

lemma t7_star_near_iff {N : ℕ} (i j : Fin N) :
    nodeSeparation (starPopulation N) i j ≤ 6/5 ↔
      i.val/5 = j.val/5 ∧ (i.val%5 = j.val%5 ∨ i.val%5 = 0 ∨ j.val%5 = 0) := by
  rw [t7_star_separation]
  constructor
  · intro h
    have hq := t7_star_near_block i j h
    exact ⟨hq, (t7_star_same_block_near i j hq).mp h⟩
  · rintro ⟨hq, hr⟩
    exact (t7_star_same_block_near i j hq).mpr hr

lemma t7_star_kernel (m : ℕ) :
    uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5) =
      starBlockKernel m false := by
  ext i j
  simp only [uniformDistanceKernel, Matrix.of_apply, t7_star_near_iff, starBlockKernel,
    Bool.false_eq_true, if_false, starKernel, Fin.ext_iff, Fin.val_zero]
  by_cases hq : i.val/5 = j.val/5 <;> simp [hq]

lemma t7_star_matrices_symmetric (pd : Bool) (i j : Fin 5) :
    (if pd then starPD else starKernel) i j = (if pd then starPD else starKernel) j i := by
  cases pd <;> fin_cases i <;> fin_cases j <;>
    norm_num [starPD, starKernel, starNegativeVector]

lemma t7_star_matrices_abs (pd : Bool) (i j : Fin 5) :
    |(if pd then starPD else starKernel) i j| ≤ 2 := by
  cases pd <;> fin_cases i <;> fin_cases j <;>
    norm_num [starPD, starKernel, starNegativeVector]

lemma t7_block_kernel_symmetric (m : ℕ) (pd : Bool) (i j : Fin (5*m)) :
    starBlockKernel m pd i j = starBlockKernel m pd j i := by
  by_cases h : i.val/5 = j.val/5
  · simp only [starBlockKernel, Matrix.of_apply, if_pos h, if_pos h.symm]
    exact t7_star_matrices_symmetric pd _ _
  · simp only [starBlockKernel, Matrix.of_apply, if_neg h, if_neg (Ne.symm h)]

lemma t7_block_kernel_abs (m : ℕ) (pd : Bool) (i j : Fin (5*m)) :
    |starBlockKernel m pd i j| ≤ 2 := by
  by_cases h : i.val/5 = j.val/5
  · simp only [starBlockKernel, Matrix.of_apply, if_pos h]
    exact t7_star_matrices_abs pd _ _
  · simp only [starBlockKernel, Matrix.of_apply, if_neg h, abs_zero]
    norm_num

lemma t7_block_kernel_trace (m : ℕ) : Matrix.trace (starBlockKernel m true) = 6*m := by
  simp only [Matrix.trace, Matrix.diag_apply, starBlockKernel, Matrix.of_apply, if_true]
  rw [t7_sum_blocks m (fun k => starPD k k)]
  norm_num [starPD, starKernel, starNegativeVector, Fin.sum_univ_succ]
  ring

lemma t7_star_clt (x : ℝ) :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      Real.sqrt (5*m : ℝ)*hajek (starBlockTable m) z / Real.sqrt (16/5) ≤ x)) atTop
      (nhds (normalCDF x)) := by
  have hclt := hajek_central_limit_proof starPopulation (1/2) 0 (by norm_num) le_rfl
    t7_star_spatialLocal (Filter.Eventually.of_forall t7_star_wellDefined) t7_star_nondegenerate
  have hsub : Tendsto (fun m : ℕ => 5*m) atTop atTop := by
    apply tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 5*m)
    exact tendsto_id
  apply ((hclt x).comp hsub).congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  have htab : circleAverage (starPopulation (5*m)) 0 = starBlockTable m := by
    funext i z
    exact t7_star_circleAverage (5*m) i z
  have hame : ame (fun _ => 1/2) (starBlockTable m) = 0 := by
    change ame (fun _ => 1/2) (fun i _ => starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩) = 0
    simp only [ame, nodeEffect,
      t7_fixed_marginal (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num),
      sub_self, Finset.sum_const_zero, zero_div]
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  have hv : variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (starBlockTable m)) =
      (16/5)/(5*m : ℝ) := (eq_div_iff hn).mpr (by
        simpa only [mul_comm] using t7_star_exact_variance m hm)
  dsimp only [Function.comp_apply]
  rw [htab, hame, hv]
  congr 1
  funext z
  apply propext
  rw [sub_zero, Real.sqrt_div (by norm_num)]
  have he : hajek (starBlockTable m) z / (Real.sqrt (16/5)/Real.sqrt (5*m : ℝ)) =
      Real.sqrt (5*m : ℝ)*hajek (starBlockTable m) z / Real.sqrt (16/5) := by
    simp only [div_eq_mul_inv, inv_mul_cancel₀, inv_inv, mul_inv_rev]
    ring
  rw [he]

def t7_blockSet {N : ℕ} (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j => j.val/5 = i.val/5)

lemma t7_blockSet_card {N : ℕ} (i : Fin N) : (t7_blockSet i).card ≤ 5 := by
  classical
  let f : Fin N → Fin 5 := fun j => ⟨j.val%5, Nat.mod_lt _ (by omega)⟩
  have hm : Set.MapsTo f (t7_blockSet i) (Finset.univ : Finset (Fin 5)) := by simp
  have hi : (t7_blockSet i : Set (Fin N)).InjOn f := by
    intro j hj k hk hjk
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    have hr : j.val%5 = k.val%5 := congrArg Fin.val hjk
    apply Fin.val_injective
    omega
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card_of_injOn f hm hi

lemma t7_block_row_abs (m : ℕ) (pd : Bool) (i : Fin (5*m)) :
    (∑ j, |starBlockKernel m pd i j|) ≤ 10 := by
  classical
  have he : (∑ j, |starBlockKernel m pd i j|) =
      ∑ j ∈ t7_blockSet i, |starBlockKernel m pd i j| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hn : i.val/5 ≠ j.val/5 := by
      intro h
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩)
    simp only [starBlockKernel, Matrix.of_apply, if_neg hn, abs_zero]
  rw [he]
  calc
    _ ≤ ∑ _j ∈ t7_blockSet i, (2 : ℝ) := Finset.sum_le_sum (fun j _ => t7_block_kernel_abs m pd i j)
    _ = ((t7_blockSet i).card : ℝ)*2 := by simp
    _ ≤ 10 := by have hc := t7_blockSet_card i; exact_mod_cast (show (t7_blockSet i).card*2 ≤ 10 by omega)

lemma t7_block_variance {N : ℕ} (hN : 0 < N) (X : Fin N → Assignment N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hX : ∀ i z, |X i z| ≤ C)
    (hdep : ∀ i, DependsOn (X i) {k | k.val/5 = i.val/5}) :
    variance (fun _ => 1/2) (fun z => (∑ i, X i z)/N) ≤ 5*C^2/N := by
  have hp : ∀ i : Fin N, (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := fun _ => by norm_num
  have hs (i j : Fin N) : j ∈ t7_blockSet i ↔ i ∈ t7_blockSet j := by
    simp only [t7_blockSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact eq_comm
  have ho (i j : Fin N) (hj : j ∉ t7_blockSet i) :
      cov (fun _ => 1/2) (X i) (X j) = 0 := by
    have hn : j.val/5 ≠ i.val/5 := by simpa only [t7_blockSet, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj
    have hd : DependsOn (X j) ({k : Fin N | k.val/5 = i.val/5}ᶜ) :=
      (hdep j).mono (by
        intro k hk hki
        exact hn (hk.symm.trans hki))
    unfold cov
    rw [GraphCompletion.expect_mul_of_disjoint_depends _ _ _ _ (hdep i) hd, sub_self]
  have hv := finite_covariance_degree_bound (fun _ => 1/2) hp X t7_blockSet hs ho
  have he (i : Fin N) : expect (fun _ => 1/2) (fun z => (X i z)^2) ≤ C^2 := by
    rw [← expect_const (fun _ : Fin N => 1/2) (C^2)]
    apply expect_mono _ hp
    intro z
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hX i z)
  apply hv.trans
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ (∑ _i : Fin N, (5 : ℝ)*C^2)/(N : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (Nat.cast_le.mpr (t7_blockSet_card i)) (he i)
        (by exact (variance_nonneg _ hp (X i)).trans (variance_le_second _ _)) (by norm_num)
    _ = 5*C^2/N := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hn]
      <;> ring

def t7_Converges (U : ∀ m, Assignment (5*m) → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun m => prob (fun _ => 1/2)
    (fun z : Assignment (5*m) => ε < |U m z-c|)) atTop (nhds 0)

lemma t7_block_lln (X : ∀ m, Fin (5*m) → Assignment (5*m) → ℝ)
    (C c : ℝ) (hC : 0 ≤ C) (hX : ∀ m i z, |X m i z| ≤ C)
    (hdep : ∀ m i, DependsOn (X m i) {k | k.val/5 = i.val/5})
    (hmean : ∀ m, 0 < m → expect (fun _ => 1/2) (fun z => (∑ i, X m i z)/(5*m : ℝ)) = c) :
    t7_Converges (fun m z => (∑ i, X m i z)/(5*m : ℝ)) c := by
  intro ε hε
  have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop))
  have hlim : Tendsto (fun m : ℕ => C^2/(m : ℝ)/ε^2) atTop (nhds 0) := by
    convert hinv.const_mul (C^2/ε^2) using 1 <;> try simp only [mul_zero]
    funext m
    ring
  have hupper : ∀ᶠ m in atTop, prob (fun _ => 1/2)
      (fun z : Assignment (5*m) => ε < |(∑ i, X m i z)/(5*m : ℝ)-c|) ≤ C^2/(m : ℝ)/ε^2 := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    let U : Assignment (5*m) → ℝ := fun z => (∑ i, X m i z)/(5*m : ℝ)
    have hp : ∀ i : Fin (5*m), (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := fun _ => by norm_num
    have he : expect (fun _ => 1/2) (fun z => (U z-c)^2) = variance (fun _ => 1/2) U := by
      rw [variance, cov_centered]
      change _ = expect (fun _ => 1/2) (fun z => (U z-expect (fun _ => 1/2) U)*(U z-expect (fun _ => 1/2) U))
      rw [hmean m hm]
      simp only [pow_two]
    have hv := t7_block_variance (by omega : 0 < 5*m) (X m) C hC (hX m) (hdep m)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hv
    calc
      _ ≤ expect (fun _ => 1/2) (fun z => (U z-c)^2)/ε^2 := T34_chebyshev _ hp _ ε hε
      _ = variance (fun _ => 1/2) U/ε^2 := by rw [he]
      _ ≤ (5*C^2/(5*m : ℝ))/ε^2 := div_le_div_of_nonneg_right hv (sq_nonneg ε)
      _ = _ := by ring
  exact squeeze_zero' (Eventually.of_forall fun m => T34_prob_nonneg _ (fun _ => by norm_num) _) hupper hlim

abbrev t7_y {N : ℕ} (i : Fin N) : ℝ := starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩

def t7_sign {N : ℕ} (i : Fin N) (z : Assignment N) : ℝ := 2*bit (z i)-1

lemma t7_sign_abs {N : ℕ} (i : Fin N) (z : Assignment N) : |t7_sign i z| = 1 := by
  cases h : z i <;> norm_num [t7_sign, bit, h]

lemma t7_bit_mean {N : ℕ} (i : Fin N) :
    expect (fun _ => 1/2) (fun z => bit (z i)) = 1/2 := by
  simpa only [pow_one, mul_one, expect_const] using
    bernoulli_positive_power (fun _ : Fin N => 1/2) (fun _ => 1) i 1
      (by norm_num) (fun _ => by norm_num)

lemma t7_sign_mean {N : ℕ} (i : Fin N) : expect (fun _ => 1/2) (t7_sign i) = 0 := by
  unfold t7_sign
  rw [expect_sub, expect_mul, t7_bit_mean, expect_const]
  norm_num

lemma t7_sign_pair {N : ℕ} (i j : Fin N) :
    expect (fun _ => 1/2) (fun z => t7_sign i z*t7_sign j z) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hf : (fun z => t7_sign i z*t7_sign i z) = fun _ : Assignment N => (1 : ℝ) := by
      funext z
      have h := t7_sign_abs i z
      nlinarith [sq_abs (t7_sign i z)]
    rw [hf, expect_const]
  · have hi : DependsOn (t7_sign i) ({i} : Set (Fin N)) := by
      intro x y hxy
      simp only [t7_sign, hxy i (by simp)]
    have hj : DependsOn (t7_sign j) (({i} : Set (Fin N))ᶜ) := by
      intro x y hxy
      simp only [t7_sign, hxy j (by simp [Ne.symm hij])]
    rw [if_neg hij, GraphCompletion.expect_mul_of_disjoint_depends _ _ _ _ hi hj,
      t7_sign_mean, zero_mul]

def t7_quadratic_row (m : ℕ) (pd : Bool) (i : Fin (5*m)) (z : Assignment (5*m)) : ℝ :=
  ∑ j, t7_sign i z*t7_y i*t7_sign j z*t7_y j*starBlockKernel m pd i j

lemma t7_quadratic_row_mean (m : ℕ) (pd : Bool) (i : Fin (5*m)) :
    expect (fun _ => 1/2) (t7_quadratic_row m pd i) = (t7_y i)^2*starBlockKernel m pd i i := by
  have he : t7_quadratic_row m pd i = fun z =>
      ∑ j, (t7_y i*t7_y j*starBlockKernel m pd i j)*(t7_sign i z*t7_sign j z) := by
    funext z
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, expect_sum]
  simp only [expect_mul, t7_sign_pair, mul_ite, mul_one, mul_zero]
  simp [pow_two]

lemma t7_quadratic_row_abs (m : ℕ) (pd : Bool) (i : Fin (5*m)) (z : Assignment (5*m)) :
    |t7_quadratic_row m pd i z| ≤ 10 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ (t7_block_row_abs m pd i)
  apply Finset.sum_le_sum
  intro j _
  simp only [abs_mul, t7_sign_abs, one_mul, mul_one]
  have hy : |t7_y i| * |t7_y j| ≤ 1 := by
    simpa only [mul_one] using mul_le_mul (t7_starY_abs _) (t7_starY_abs _)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (mul_le_mul_of_nonneg_right hy (abs_nonneg _)).trans_eq (one_mul _)

lemma t7_quadratic_row_depends (m : ℕ) (pd : Bool) (i : Fin (5*m)) :
    DependsOn (t7_quadratic_row m pd i) {k | k.val/5 = i.val/5} := by
  intro x y hxy
  unfold t7_quadratic_row
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i.val/5 = j.val/5
  · simp only [t7_sign, hxy i rfl, hxy j hij.symm]
  · simp only [starBlockKernel, Matrix.of_apply, if_neg hij, mul_zero]

lemma t7_quadratic_row_lln (pd : Bool) :
    t7_Converges (fun m z => (∑ i, t7_quadratic_row m pd i z)/(5*m : ℝ))
      (if pd then 9/10 else 4/5) := by
  apply t7_block_lln _ 10 _ (by norm_num) (fun m i z => t7_quadratic_row_abs m pd i z)
    (fun m i => t7_quadratic_row_depends m pd i)
  intro m hm
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [expect_div, expect_sum]
  simp only [t7_quadratic_row_mean, t7_y, starBlockKernel, Matrix.of_apply, if_true]
  rw [t7_sum_blocks m (fun k => (starY k)^2*(if pd then starPD else starKernel) k k)]
  cases pd <;> norm_num [starY, starPD, starKernel, starNegativeVector, Fin.sum_univ_succ]
  all_goals field_simp [hn]
  all_goals ring

def t7_fraction (m : ℕ) (z : Assignment (5*m)) : ℝ := armCount z true/(5*m : ℝ)

def t7_selected_mean (m : ℕ) (z : Assignment (5*m)) : ℝ :=
  (∑ i, t7_y i*bit (z i))/(5*m : ℝ)

lemma t7_fraction_lln : t7_Converges t7_fraction (1/2) := by
  have ht := t7_block_lln (fun m i z => bit (z i)) 1 (1/2) (by norm_num)
    (fun m i z => by cases h : z i <;> norm_num [bit, h])
    (fun m i x y hxy => by
      change bit (x i) = bit (y i)
      rw [hxy i rfl])
    (by
      intro m hm
      have hn : (5*m : ℝ) ≠ 0 := by positivity
      rw [expect_div, expect_sum]
      simp only [t7_bit_mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp [hn]
      <;> ring)
  simpa only [t7_Converges, t7_fraction, MatrixCompletion.sum_bit] using ht

lemma t7_selected_mean_lln : t7_Converges t7_selected_mean 0 := by
  apply t7_block_lln _ 1 _ (by norm_num)
  · intro m i z
    rw [abs_mul]
    cases h : z i <;> simp only [bit, h, Bool.false_eq_true, if_false, if_true, abs_zero,
      abs_one, mul_zero, mul_one]
    · norm_num
    · exact t7_starY_abs _
  · intro m i x y hxy
    change t7_y i*bit (x i) = t7_y i*bit (y i)
    rw [hxy i rfl]
  · intro m _
    rw [expect_div, expect_sum]
    simp only [expect_mul, t7_bit_mean, ← Finset.sum_mul, t7_y, (t7_star_block_moments m).1,
      zero_mul, zero_div]

lemma t7_inverse_half_bound (q : ℝ) (hq : 1/4 ≤ q) :
    |1/q| ≤ 4 ∧ |1/q-2| ≤ 8*|q-1/2| := by
  have hq0 : 0 < q := by linarith
  constructor
  · rw [abs_of_pos (one_div_pos.mpr hq0)]
    apply (div_le_iff₀ hq0).mpr
    linarith
  · have he : 1/q-2 = -2*(q-1/2)/q := by field_simp; ring
    rw [he, abs_div, abs_mul, abs_of_pos hq0]
    norm_num only [abs_neg, show |(2 : ℝ)| = 2 by norm_num]
    apply (div_le_iff₀ hq0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg (q-1/2))]

lemma t7_good_counts (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    0 < armCount z true ∧ 0 < armCount z false := by
  have hn : (0 : ℝ) < 5*m := by positivity
  have he : armCount z true = t7_fraction m z*(5*m : ℝ) := by
    dsimp [t7_fraction]
    field_simp
  have hc := MatrixCompletion.counts_total z
  push_cast at hc
  have hlow : 1/4 ≤ t7_fraction m z := by linarith [(abs_le.mp ht).1]
  have hhigh : t7_fraction m z ≤ 3/4 := by linarith [(abs_le.mp ht).2]
  constructor
  · rw [he]
    exact mul_pos (by linarith) hn
  · nlinarith [mul_nonneg (sub_nonneg.mpr hhigh) hn.le]

lemma t7_fraction_false (m : ℕ) (hm : 0 < m) (z : Assignment (5*m)) :
    1-t7_fraction m z = armCount z false/(5*m : ℝ) := by
  have hc := MatrixCompletion.counts_total z
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  unfold t7_fraction
  apply (eq_div_iff hn).mpr
  field_simp
  push_cast at hc
  linarith

lemma t7_lambda_scaled (m : ℕ) (hm : 0 < m) (z : Assignment (5*m)) (i : Fin (5*m)) :
    (5*m : ℝ)*lambda z i = if z i then 1/t7_fraction m z else -(1/(1-t7_fraction m z)) := by
  have hfalse := t7_fraction_false m hm z
  cases hz : z i
  · simp only [hz, Bool.false_eq_true, if_false, lambda, bit, zero_div, sub_zero,
      zero_sub, one_mul, sub_self]
    rw [hfalse, one_div_div]
    ring
  · simp only [hz, if_true, lambda, bit, sub_self, zero_div, sub_zero, one_mul]
    simp only [t7_fraction, one_div_div]
    ring

lemma t7_lambda_scaled_bounds (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i : Fin (5*m)) :
    |(5*m : ℝ)*lambda z i| ≤ 4 ∧
    |(5*m : ℝ)*lambda z i-2*t7_sign i z| ≤ 8*|t7_fraction m z-1/2| := by
  have hq : 1/4 ≤ t7_fraction m z := by linarith [(abs_le.mp ht).1]
  have hq0 : 1/4 ≤ 1-t7_fraction m z := by linarith [(abs_le.mp ht).2]
  have he : |1-t7_fraction m z-1/2| = |t7_fraction m z-1/2| := by
    rw [show 1-t7_fraction m z-1/2 = -(t7_fraction m z-1/2) by ring, abs_neg]
  have h1 := t7_inverse_half_bound _ hq
  have h0 := t7_inverse_half_bound _ hq0
  rw [he] at h0
  rw [t7_lambda_scaled m hm]
  cases hz : z i
  · simp only [hz, Bool.false_eq_true, if_false, t7_sign, bit, zero_mul, mul_zero, zero_sub,
      mul_neg, mul_one, sub_neg_eq_add, abs_neg]
    have hh : -(1/(1-t7_fraction m z))+2 = -(1/(1-t7_fraction m z)-2) := by ring
    rw [hh, abs_neg]
    exact h0
  · simpa only [hz, if_true, t7_sign, bit, mul_one, sub_self, one_mul, sub_zero,
      show (2 : ℝ)-1 = 1 by norm_num] using h1

lemma t7_conv_map {k : ℕ} (U : Fin k → ∀ m, Assignment (5*m) → ℝ)
    (c : Fin k → ℝ) (F : (Fin k → ℝ) → ℝ) (hF : ContinuousAt F c)
    (hU : ∀ i, t7_Converges (U i) (c i)) :
    t7_Converges (fun m z => F (fun i => U i m z)) (F c) := by
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hF ε hε
  have hb (m : ℕ) (z : Assignment (5*m))
      (hz : ε < |F (fun i => U i m z)-F c|) : ∃ i, δ/2 < |U i m z-c i| := by
    by_contra hn
    have hc (i : Fin k) : dist (U i m z) (c i) < δ := by
      have hi : |U i m z-c i| ≤ δ/2 := le_of_not_gt (fun h => hn ⟨i, h⟩)
      rw [Real.dist_eq]
      linarith
    have hv : dist (fun i => U i m z) c < δ := (dist_pi_lt_iff hδ).mpr hc
    have hh := hnear hv
    rw [Real.dist_eq] at hh
    linarith
  have hu (m : ℕ) : prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      ε < |F (fun i => U i m z)-F c|) ≤
      ∑ i, prob (fun _ => 1/2) (fun z : Assignment (5*m) => δ/2 < |U i m z-c i|) :=
    DesignLimits.DLbSupport.prob_le_sum _ (fun _ => by norm_num) _ _ (hb m)
  have hs : Tendsto (fun m => ∑ i, prob (fun _ => 1/2)
      (fun z : Assignment (5*m) => δ/2 < |U i m z-c i|)) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (s := Finset.univ) (fun i _ => hU i (δ/2) (by linarith)))
  exact squeeze_zero (fun m => T34_prob_nonneg _ (fun _ => by norm_num) _) hu hs

def t7_oracle (m : ℕ) (pd : Bool) (z : Assignment (5*m)) : ℝ :=
  4*((∑ i, t7_quadratic_row m pd i z)/(5*m : ℝ))

lemma t7_oracle_lln (pd : Bool) :
    t7_Converges (fun m z => t7_oracle m pd z) (if pd then 18/5 else 16/5) := by
  have h := t7_conv_map (k := 1) (fun _ : Fin 1 => fun m z =>
    (∑ i, t7_quadratic_row m pd i z)/(5*m : ℝ))
    (fun _ => if pd then 9/10 else 4/5) (fun v : Fin 1 → ℝ => 4*v 0)
    ((continuous_const.mul (continuous_apply 0)).continuousAt)
    (fun _ => t7_quadratic_row_lln pd)
  cases pd <;> simpa only [t7_Converges, t7_oracle, Bool.false_eq_true, if_false, if_true,
    show (4 : ℝ)*(4/5) = 16/5 by norm_num, show (4 : ℝ)*(9/10) = 18/5 by norm_num] using h

def t7_Good (m : ℕ) (z : Assignment (5*m)) : Prop :=
  |t7_fraction m z-1/2| ≤ 1/4 ∧ |t7_selected_mean m z| ≤ 1

lemma t7_good_probability :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => ¬ t7_Good m z)) atTop (nhds 0) := by
  have hu (m : ℕ) : prob (fun _ => 1/2) (fun z : Assignment (5*m) => ¬ t7_Good m z) ≤
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => 1/4 < |t7_fraction m z-1/2|) +
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => 1 < |t7_selected_mean m z|) := by
    apply DesignLimits.DLbSupport.prob_le_add _ (fun _ => by norm_num)
    intro z hz
    by_cases ht : |t7_fraction m z-1/2| ≤ 1/4
    · exact Or.inr (lt_of_not_ge fun h => hz ⟨ht, h⟩)
    · exact Or.inl (lt_of_not_ge ht)
  have hl := (t7_fraction_lln (1/4) (by norm_num)).add (t7_selected_mean_lln 1 (by norm_num))
  simp only [sub_zero, add_zero] at hl
  exact squeeze_zero (fun m => T34_prob_nonneg _ (fun _ => by norm_num) _) hu hl

lemma t7_error_converges (C : ℝ) :
    t7_Converges (fun m z => C*(|t7_fraction m z-1/2|+|t7_selected_mean m z|)) 0 := by
  have h := t7_conv_map ![t7_fraction, t7_selected_mean] ![1/2, 0]
    (fun v => C*(|v 0-1/2|+|v 1|)) (by fun_prop)
    (by intro i; fin_cases i; exact t7_fraction_lln; exact t7_selected_mean_lln)
  simpa only [t7_Converges, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, sub_self, abs_zero, add_zero, mul_zero] using h

lemma t7_good_approx (U V D : ∀ m, Assignment (5*m) → ℝ) (a : ℝ)
    (hU : t7_Converges U a) (hD : t7_Converges D 0)
    (hbound : ∀ᶠ m in atTop, ∀ z, t7_Good m z → |V m z-U m z| ≤ D m z) :
    t7_Converges V a := by
  intro ε hε
  have hε2 : 0 < ε/2 := by linarith
  have hu : ∀ᶠ m in atTop, prob (fun _ => 1/2) (fun z : Assignment (5*m) => ε < |V m z-a|) ≤
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => ¬ t7_Good m z) +
      (prob (fun _ => 1/2) (fun z : Assignment (5*m) => ε/2 < |U m z-a|) +
        prob (fun _ => 1/2) (fun z : Assignment (5*m) => ε/2 < |D m z|)) := by
    filter_upwards [hbound] with m hm
    calc
      _ ≤ prob (fun _ => 1/2) (fun z : Assignment (5*m) => ¬ t7_Good m z) +
          prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
            ε/2 < |U m z-a| ∨ ε/2 < |D m z|) := by
        apply DesignLimits.DLbSupport.prob_le_add (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num)
        intro z hz
        by_cases hg : t7_Good m z
        · right
          by_cases hb : ε/2 < |U m z-a|
          · exact Or.inl hb
          · right
            by_contra hd
            have htri := abs_sub_le (V m z) (U m z) a
            have hB := hm z hg
            have hDl := le_abs_self (D m z)
            have hUl := le_of_not_gt hb
            have hDe := le_of_not_gt hd
            linarith
        · exact Or.inl hg
      _ ≤ _ := add_le_add le_rfl (T34_prob_union (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num) _ _)
  have hl := t7_good_probability.add ((hU (ε/2) hε2).add (hD (ε/2) hε2))
  simp only [sub_zero, add_zero] at hl
  exact squeeze_zero' (Eventually.of_forall fun m => T34_prob_nonneg _ (fun _ => by norm_num) _) hu hl

lemma t7_star_arm_means (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    armMean (starBlockTable m) z true = t7_selected_mean m z/t7_fraction m z ∧
    armMean (starBlockTable m) z false = -t7_selected_mean m z/(1-t7_fraction m z) := by
  let S : ℝ := ∑ i, t7_y i*bit (z i)
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  obtain ⟨h1, h0⟩ := t7_good_counts m hm z ht
  have h1num : (∑ i, if z i = true then starBlockTable m i z else 0) = S := by
    apply Finset.sum_congr rfl
    intro i _
    cases h : z i <;> simp [h, starBlockTable, bit]
  have hsum : (∑ i : Fin (5*m), t7_y i) =
      (∑ i, if z i = true then starBlockTable m i z else 0) +
      ∑ i, if z i = false then starBlockTable m i z else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases h : z i <;> simp [h, starBlockTable]
  rw [(t7_star_block_moments m).1, h1num] at hsum
  have h0num : (∑ i, if z i = false then starBlockTable m i z else 0) = -S := by linarith
  constructor
  · rw [armMean, h1num]
    change S/armCount z true = (S/(5*m : ℝ))/(armCount z true/(5*m : ℝ))
    field_simp [hn, h1.ne']
  · rw [armMean, h0num, t7_fraction_false m hm z]
    change (-S)/armCount z false = -(S/(5*m : ℝ))/(armCount z false/(5*m : ℝ))
    field_simp [hn, h0.ne']

lemma t7_residual_error (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i : Fin (5*m)) :
    |residual (starBlockTable m) z i-t7_y i| ≤ 4*|t7_selected_mean m z| := by
  have hq : 1/4 ≤ t7_fraction m z := by linarith [(abs_le.mp ht).1]
  have hq0 : 1/4 ≤ 1-t7_fraction m z := by linarith [(abs_le.mp ht).2]
  have h1 := (t7_inverse_half_bound _ hq).1
  have h0 := (t7_inverse_half_bound _ hq0).1
  have he : residual (starBlockTable m) z i-t7_y i = -armMean (starBlockTable m) z (z i) := by
    change t7_y i-armMean (starBlockTable m) z (z i)-t7_y i = _
    ring
  rw [he, abs_neg]
  cases hz : z i
  · rw [(t7_star_arm_means m hm z ht).2, abs_div, abs_neg]
    have hh := mul_le_mul_of_nonneg_left h0 (abs_nonneg (t7_selected_mean m z))
    simp only [abs_div, abs_one] at hh
    convert hh using 1 <;> ring
  · rw [(t7_star_arm_means m hm z ht).1, abs_div]
    have hh := mul_le_mul_of_nonneg_left h1 (abs_nonneg (t7_selected_mean m z))
    simp only [abs_div, abs_one] at hh
    convert hh using 1 <;> ring

def t7_a (m : ℕ) (z : Assignment (5*m)) (i : Fin (5*m)) : ℝ :=
  (5*m : ℝ)*lambda z i*residual (starBlockTable m) z i

def t7_b (m : ℕ) (z : Assignment (5*m)) (i : Fin (5*m)) : ℝ := 2*t7_sign i z*t7_y i

lemma t7_b_abs (m : ℕ) (z : Assignment (5*m)) (i : Fin (5*m)) : |t7_b m z i| ≤ 2 := by
  simp only [t7_b, abs_mul, t7_sign_abs, mul_one]
  norm_num only [show |(2 : ℝ)| = 2 by norm_num]
  linarith [t7_starY_abs ⟨i.val%5, Nat.mod_lt _ (by omega)⟩]

lemma t7_a_bounds (m : ℕ) (hm : 0 < m) (z : Assignment (5*m)) (hg : t7_Good m z)
    (i : Fin (5*m)) :
    |t7_a m z i| ≤ 24 ∧ |t7_a m z i-t7_b m z i| ≤
      16*(|t7_fraction m z-1/2|+|t7_selected_mean m z|) := by
  obtain ⟨hl, hld⟩ := t7_lambda_scaled_bounds m hm z hg.1 i
  have hr := t7_residual_error m hm z hg.1 i
  have hy : |t7_y i| ≤ 1 := t7_starY_abs _
  have he : t7_a m z i-t7_b m z i =
      ((5*m : ℝ)*lambda z i)*(residual (starBlockTable m) z i-t7_y i) +
      ((5*m : ℝ)*lambda z i-2*t7_sign i z)*t7_y i := by unfold t7_a t7_b; ring
  have herr : |t7_a m z i-t7_b m z i| ≤
      16*(|t7_fraction m z-1/2|+|t7_selected_mean m z|) := by
    rw [he]
    apply (abs_add_le _ _).trans
    have hmul1 := mul_le_mul hl hr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have hmul2 := mul_le_mul hld hy (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 8*|t7_fraction m z-1/2|)
    simp only [abs_mul] at hmul1 hmul2 ⊢
    apply (add_le_add hmul1 hmul2).trans
    nlinarith [abs_nonneg (t7_fraction m z-1/2)]
  refine ⟨?_, herr⟩
  have htri := abs_sub_le (t7_a m z i) (t7_b m z i) 0
  simp only [sub_zero] at htri
  have hb := t7_b_abs m z i
  linarith [hg.1, hg.2]

lemma t7_quadratic_perturb {N : ℕ} (hN : 0 < N) (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : ∀ i, (∑ j, |Q i j|) ≤ 10) (a b : Fin N → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (ha : ∀ i, |a i| ≤ 24) (hb : ∀ i, |b i| ≤ 2) (hab : ∀ i, |a i-b i| ≤ E) :
    |(∑ i, ∑ j, a i*a j*Q i j)/N - (∑ i, ∑ j, b i*b j*Q i j)/N| ≤ 260*E := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hp (i j : Fin N) : |a i*a j-b i*b j| ≤ 26*E := by
    have he : a i*a j-b i*b j = a i*(a j-b j)+(a i-b i)*b j := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    have h1 := mul_le_mul (ha i) (hab j) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 24)
    have h2 := mul_le_mul (hab i) (hb j) (abs_nonneg _) hE
    simp only [abs_mul] at h1 h2 ⊢
    exact (add_le_add h1 h2).trans_eq (by ring)
  have he : (∑ i, ∑ j, a i*a j*Q i j)-(∑ i, ∑ j, b i*b j*Q i j) =
      ∑ i, ∑ j, (a i*a j-b i*b j)*Q i j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [← sub_div, abs_div, abs_of_pos hn, he]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, ∑ j, |(a i*a j-b i*b j)*Q i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (26*E)*|Q i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hp i j) (abs_nonneg _)
    _ = ∑ i, (26*E)*(∑ j, |Q i j|) := by simp only [Finset.mul_sum]
    _ ≤ ∑ _i : Fin N, (26*E)*10 := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hQ i) (by positivity))
    _ = _ := by simp; ring

lemma t7_variance_approx (m : ℕ) (hm : 0 < m) (pd : Bool) (z : Assignment (5*m))
    (hg : t7_Good m z) :
    |(5*m : ℝ)*kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m pd) -
      t7_oracle m pd z| ≤ 4160*(|t7_fraction m z-1/2|+|t7_selected_mean m z|) := by
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  have h := t7_quadratic_perturb (by omega : 0 < 5*m) (starBlockKernel m pd)
    (t7_block_row_abs m pd) (t7_a m z) (t7_b m z)
    (16*(|t7_fraction m z-1/2|+|t7_selected_mean m z|)) (by positivity)
    (fun i => (t7_a_bounds m hm z hg i).1) (t7_b_abs m z)
    (fun i => (t7_a_bounds m hm z hg i).2)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  have hsA : (∑ i, ∑ j, t7_a m z i*t7_a m z j*starBlockKernel m pd i j) =
      (5*m : ℝ)^2*kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m pd) := by
    simp only [kernelVariance, t7_a, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsB : (∑ i, ∑ j, t7_b m z i*t7_b m z j*starBlockKernel m pd i j) =
      4*(∑ i, t7_quadratic_row m pd i z) := by
    simp only [t7_b, t7_quadratic_row, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsA, hsB] at h
  have heA : (5*m : ℝ)^2*kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m pd)/(5*m : ℝ) =
      (5*m : ℝ)*kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m pd) := by
    field_simp [hn]
    <;> ring
  rw [heA] at h
  dsimp only [t7_oracle]
  convert h using 1 <;> ring

lemma t7_variance_limit (pd : Bool) :
    t7_Converges (fun m z => (5*m : ℝ)*kernelVariance z
      (residual (starBlockTable m) z) (starBlockKernel m pd)) (if pd then 18/5 else 16/5) := by
  apply t7_good_approx (fun m z => t7_oracle m pd z) _
    (fun m z => 4160*(|t7_fraction m z-1/2|+|t7_selected_mean m z|)) _
    (t7_oracle_lln pd) (t7_error_converges 4160)
  filter_upwards [eventually_gt_atTop 0] with m hm z hg
  exact t7_variance_approx m hm pd z hg

def t7_P {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin N) ℝ := 1-residualMaker z

lemma t7_P_entry {N : ℕ} (z : Assignment N) (h1 : 0 < armCount z true)
    (h0 : 0 < armCount z false) (i j : Fin N) :
    t7_P z i j = if z i = z j then 1/armCount z (z i) else 0 := by
  have hc := MatrixCompletion.counts_total z
  dsimp only [t7_P, residualMaker]
  rw [MatrixCompletion.gram_inverse_eq z h1 h0]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, MatrixCompletion.gramInverse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const]
  cases hi : z i <;> cases hj : z j
  all_goals norm_num [designMatrix, bit, hi, hj]
  all_goals field_simp [h1.ne', h0.ne']
  all_goals nlinarith

lemma t7_P_symmetric {N : ℕ} (z : Assignment N) (h1 : 0 < armCount z true)
    (h0 : 0 < armCount z false) (i j : Fin N) : t7_P z i j = t7_P z j i := by
  rw [t7_P_entry z h1 h0, t7_P_entry z h1 h0]
  by_cases h : z i = z j
  · simp only [if_pos h, if_pos h.symm, h]
  · simp only [if_neg h, if_neg (Ne.symm h)]

lemma t7_P_nonneg {N : ℕ} (z : Assignment N) (h1 : 0 < armCount z true)
    (h0 : 0 < armCount z false) (i j : Fin N) : 0 ≤ t7_P z i j := by
  rw [t7_P_entry z h1 h0]
  split_ifs
  · cases hz : z i <;> positivity
  · exact le_rfl

lemma t7_P_rowsum {N : ℕ} (z : Assignment N) (h1 : 0 < armCount z true)
    (h0 : 0 < armCount z false) (i : Fin N) : (∑ j, t7_P z i j) = 1 := by
  have he (j : Fin N) : t7_P z i j = (if z j = z i then (1 : ℝ) else 0)/armCount z (z i) := by
    rw [t7_P_entry z h1 h0]
    by_cases h : z i = z j
    · simp only [if_pos h, if_pos h.symm]
    · simp only [if_neg h, if_neg (Ne.symm h), zero_div]
  simp only [he, ← Finset.sum_div]
  change armCount z (z i)/armCount z (z i) = 1
  cases hz : z i
  · exact div_self h0.ne'
  · exact div_self h1.ne'

lemma t7_P_bound (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i j : Fin (5*m)) : |t7_P z i j| ≤ 4/(5*m : ℝ) := by
  obtain ⟨h1, h0⟩ := t7_good_counts m hm z ht
  have hn : (0 : ℝ) < 5*m := by positivity
  have hct : (5*m : ℝ)/4 ≤ armCount z true := by
    have he : armCount z true = t7_fraction m z*(5*m : ℝ) := by
      dsimp [t7_fraction]
      field_simp
    rw [he]
    nlinarith [mul_nonneg (show 0 ≤ t7_fraction m z-1/4 by linarith [(abs_le.mp ht).1]) hn.le]
  have hcf : (5*m : ℝ)/4 ≤ armCount z false := by
    have hc := MatrixCompletion.counts_total z
    push_cast at hc
    have he : armCount z true = t7_fraction m z*(5*m : ℝ) := by
      dsimp [t7_fraction]
      field_simp
    nlinarith [mul_nonneg (show 0 ≤ 3/4-t7_fraction m z by linarith [(abs_le.mp ht).2]) hn.le]
  rw [abs_of_nonneg (t7_P_nonneg z h1 h0 i j), t7_P_entry z h1 h0]
  split_ifs
  · have ha : (5*m : ℝ)/4 ≤ armCount z (z i) := by cases z i <;> assumption
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (5*m : ℝ)/4) ha
    simpa only [one_div_div] using hh
  · positivity

def t7_B (m : ℕ) (z : Assignment (5*m)) : Matrix (Fin (5*m)) (Fin (5*m)) ℝ :=
  fun i j => (t7_fraction m z*(1-t7_fraction m z))*
    ((5*m : ℝ)*lambda z i)*((5*m : ℝ)*lambda z j)*starBlockKernel m true i j

lemma t7_B_eq (m : ℕ) (hm : 0 < m) (z : Assignment (5*m)) :
    t7_B m z = (armCount z true*armCount z false) •
      Matrix.of (fun i j => lambda z i*lambda z j*starBlockKernel m true i j) := by
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  ext i j
  simp only [t7_B, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  rw [t7_fraction_false m hm z]
  unfold t7_fraction
  field_simp [hn]
  <;> ring

lemma t7_B_symmetric (m : ℕ) (z : Assignment (5*m)) (i j : Fin (5*m)) :
    t7_B m z i j = t7_B m z j i := by
  unfold t7_B
  rw [t7_block_kernel_symmetric m true j i]
  ring

lemma t7_B_abs (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i j : Fin (5*m)) :
    |t7_B m z i j| ≤ 4*|starBlockKernel m true i j| := by
  have hq : 0 ≤ t7_fraction m z := by linarith [(abs_le.mp ht).1]
  have hq1 : 0 ≤ 1-t7_fraction m z := by linarith [(abs_le.mp ht).2]
  have hc : |t7_fraction m z*(1-t7_fraction m z)| ≤ 1/4 := by
    rw [abs_of_nonneg (mul_nonneg hq hq1)]
    nlinarith [sq_nonneg (t7_fraction m z-1/2)]
  have hi := (t7_lambda_scaled_bounds m hm z ht i).1
  have hj := (t7_lambda_scaled_bounds m hm z ht j).1
  change |(t7_fraction m z*(1-t7_fraction m z))*
    ((5*m : ℝ)*lambda z i)*((5*m : ℝ)*lambda z j)*starBlockKernel m true i j| ≤ _
  rw [abs_mul, abs_mul, abs_mul]
  calc
    _ ≤ (1/4 : ℝ)*4*4*|starBlockKernel m true i j| := by gcongr
    _ = _ := by ring

lemma t7_B_row (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i : Fin (5*m)) : (∑ j, |t7_B m z i j|) ≤ 40 := by
  calc
    _ ≤ ∑ j, 4*|starBlockKernel m true i j| := Finset.sum_le_sum (fun j _ => t7_B_abs m hm z ht i j)
    _ = 4*∑ j, |starBlockKernel m true i j| := by rw [Finset.mul_sum]
    _ ≤ 40 := by linarith [t7_block_row_abs m true i]

def t7_D (m : ℕ) (z : Assignment (5*m)) : Matrix (Fin (5*m)) (Fin (5*m)) ℝ :=
  residualMaker z*t7_B m z*residualMaker z

lemma t7_adjustment_B (m : ℕ) (hm : 0 < m) (z : Assignment (5*m)) :
    adjustmentMatrix z (starBlockKernel m true) = (5*m : ℝ)⁻¹ • t7_D m z := by
  rw [t7_D, t7_B_eq m hm]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  dsimp only [adjustmentMatrix]
  congr 1
  push_cast
  ring

lemma t7_D_trace (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    Matrix.trace (t7_D m z) = Matrix.trace (t7_B m z) - Matrix.trace (t7_P z*t7_B m z) := by
  obtain ⟨h1, h0⟩ := t7_good_counts m hm z ht
  have hM := (MatrixCompletion.residual_algebra z h1 h0).2.1
  calc
    _ = Matrix.trace (residualMaker z*(residualMaker z*t7_B m z)) :=
      Matrix.trace_mul_comm (residualMaker z*t7_B m z) (residualMaker z)
    _ = Matrix.trace (residualMaker z*t7_B m z) := by rw [← Matrix.mul_assoc, hM]
    _ = _ := by
      have he : residualMaker z = 1-t7_P z := by unfold t7_P; abel
      rw [he, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]

lemma t7_mu_trace (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    adjustmentMu z (starBlockKernel m true) =
      (Matrix.trace (t7_B m z)-Matrix.trace (t7_P z*t7_B m z))/(5*m : ℝ) := by
  rw [adjustmentMu, t7_adjustment_B m hm, Matrix.trace_smul, t7_D_trace m hm z ht]
  simp only [smul_eq_mul]
  ring

lemma t7_PB_bound (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i j : Fin (5*m)) :
    |(t7_P z*t7_B m z) i j| ≤ 160/(5*m : ℝ) := by
  have hc : (∑ k, |t7_B m z k j|) ≤ 40 := by
    simp_rw [t7_B_symmetric m z _ j]
    exact t7_B_row m hm z ht j
  rw [Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k, (4/(5*m : ℝ))*|t7_B m z k j| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (t7_P_bound m hm z ht i k) (abs_nonneg _)
    _ = (4/(5*m : ℝ))*∑ k, |t7_B m z k j| := by rw [Finset.mul_sum]
    _ ≤ (4/(5*m : ℝ))*40 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

lemma t7_mu_trace_error (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    |adjustmentMu z (starBlockKernel m true)-Matrix.trace (t7_B m z)/(5*m : ℝ)| ≤ 160/(5*m : ℝ) := by
  have hn : (0 : ℝ) < 5*m := by positivity
  have htrace : |Matrix.trace (t7_P z*t7_B m z)| ≤ 160 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin (5*m), (160/(5*m : ℝ)) :=
        Finset.sum_le_sum (fun i _ => t7_PB_bound m hm z ht i i)
      _ = 160 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp [hn.ne']
        <;> ring
  rw [t7_mu_trace m hm z ht]
  have he : (Matrix.trace (t7_B m z)-Matrix.trace (t7_P z*t7_B m z))/(5*m : ℝ) -
      Matrix.trace (t7_B m z)/(5*m : ℝ) = -Matrix.trace (t7_P z*t7_B m z)/(5*m : ℝ) := by ring
  rw [he, abs_div, abs_neg, abs_of_pos hn]
  exact div_le_div_of_nonneg_right htrace hn.le

def t7_diagonal_selected (m : ℕ) (z : Assignment (5*m)) : ℝ :=
  (∑ i, bit (z i)*starBlockKernel m true i i)/(5*m : ℝ)

lemma t7_diagonal_selected_lln : t7_Converges t7_diagonal_selected (3/5) := by
  apply t7_block_lln _ 2 _ (by norm_num)
  · intro m i z
    cases h : z i <;> simp only [bit, h, Bool.false_eq_true, if_false, if_true, mul_zero, zero_mul,
      one_mul, abs_zero]
    · norm_num
    · exact t7_block_kernel_abs m true i i
  · intro m i x y hxy
    change bit (x i)*_ = bit (y i)*_
    rw [hxy i rfl]
  · intro m hm
    have hn : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have he (i : Fin (5*m)) : expect (fun _ => 1/2) (fun z => bit (z i)*starBlockKernel m true i i) =
        starBlockKernel m true i i*(1/2) := by
      have hr : (fun z : Assignment (5*m) => bit (z i)*starBlockKernel m true i i) =
          fun z => starBlockKernel m true i i*bit (z i) := by funext z; ring
      rw [hr, expect_mul, t7_bit_mean]
    rw [expect_div, expect_sum]
    simp only [he, ← Finset.sum_mul]
    change Matrix.trace (starBlockKernel m true)*(1/2)/(5*m : ℝ) = _
    rw [t7_block_kernel_trace]
    field_simp [hn]
    <;> ring

def t7_mu_leading (m : ℕ) (z : Assignment (5*m)) : ℝ :=
  t7_fraction m z*(1-t7_fraction m z)*
    (t7_diagonal_selected m z/(t7_fraction m z)^2 +
      (6/5-t7_diagonal_selected m z)/(1-t7_fraction m z)^2)

lemma t7_mu_leading_limit : t7_Converges t7_mu_leading (6/5) := by
  let F : (Fin 2 → ℝ) → ℝ := fun v => v 0*(1-v 0)*(v 1/(v 0)^2+(6/5-v 1)/(1-v 0)^2)
  have hf : ContinuousAt F ![1/2, 3/5] := by dsimp only [F]; fun_prop (disch := norm_num)
  have hh := t7_conv_map ![t7_fraction, t7_diagonal_selected] ![1/2, 3/5] F hf
    (by intro i; fin_cases i; exact t7_fraction_lln; exact t7_diagonal_selected_lln)
  have hc : F ![1/2, 3/5] = 6/5 := by norm_num [F]
  rw [hc] at hh
  simpa only [t7_Converges, t7_mu_leading, F, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const] using hh

lemma t7_traceB_formula (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    Matrix.trace (t7_B m z)/(5*m : ℝ) = t7_mu_leading m z := by
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  have hq : t7_fraction m z ≠ 0 := by
    have hh := (abs_le.mp ht).1
    linarith
  have hq0 : 1-t7_fraction m z ≠ 0 := by
    have hh := (abs_le.mp ht).2
    linarith
  have hd (i : Fin (5*m)) : t7_B m z i i =
      (t7_fraction m z*(1-t7_fraction m z))*
        ((if z i = true then starBlockKernel m true i i else 0)/(t7_fraction m z)^2 +
          (if z i = false then starBlockKernel m true i i else 0)/(1-t7_fraction m z)^2) := by
    dsimp only [t7_B]
    rw [t7_lambda_scaled m hm z i]
    cases hz : z i <;> simp only [hz, Bool.false_eq_true, Bool.true_eq_false,
      if_false, if_true, zero_div, add_zero, zero_add]
    all_goals field_simp [hq, hq0]
    all_goals ring
  have hs1 : (∑ i, if z i = true then starBlockKernel m true i i else 0) =
      (5*m : ℝ)*t7_diagonal_selected m z := by
    have he (i : Fin (5*m)) : (if z i = true then starBlockKernel m true i i else 0) =
        bit (z i)*starBlockKernel m true i i := by cases h : z i <;> simp [bit, h]
    simp only [he, t7_diagonal_selected]
    field_simp [hn]
  have hs0 : (∑ i, if z i = false then starBlockKernel m true i i else 0) =
      6*m-(5*m : ℝ)*t7_diagonal_selected m z := by
    have he : (∑ i, if z i = true then starBlockKernel m true i i else 0) +
        (∑ i, if z i = false then starBlockKernel m true i i else 0) = Matrix.trace (starBlockKernel m true) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases h : z i <;> simp [h]
    rw [hs1, t7_block_kernel_trace] at he
    linarith
  simp only [Matrix.trace, Matrix.diag_apply, hd, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.sum_div, hs1, hs0]
  unfold t7_mu_leading
  field_simp [hn, hq, hq0]
  <;> ring

lemma t7_deterministic_converges (d : ℕ → ℝ) (a : ℝ) (hd : Tendsto d atTop (nhds a)) :
    t7_Converges (fun m _ => d m) a := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [Metric.tendsto_nhds.mp hd ε hε] with m hm
  rw [Real.dist_eq] at hm
  have hn : ¬ ε < |d m-a| := not_lt_of_ge hm.le
  simp only [prob, if_neg hn, expect_const]

lemma t7_inverse_size_tendsto (C : ℝ) : Tendsto (fun m : ℕ => C/(5*m : ℝ)) atTop (nhds 0) := by
  have ht : Tendsto (fun m : ℕ => (5*m : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 5)).mpr tendsto_natCast_atTop_atTop
  have h := tendsto_inv_atTop_zero.comp ht
  simp only [Function.comp_def] at h
  convert h.const_mul C using 1 <;> try simp only [mul_zero]
  funext m
  ring

lemma t7_mu_limit : t7_Converges (fun m z => adjustmentMu z (starBlockKernel m true)) (6/5) := by
  apply t7_good_approx t7_mu_leading _ (fun m _ => 160/(5*m : ℝ)) _ t7_mu_leading_limit
    (t7_deterministic_converges _ _ (t7_inverse_size_tendsto 160))
  filter_upwards [eventually_gt_atTop 0] with m hm z hg
  rw [← t7_traceB_formula m hm z hg.1]
  exact t7_mu_trace_error m hm z hg.1

lemma t7_BP_bound (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i j : Fin (5*m)) :
    |(t7_B m z*t7_P z) i j| ≤ 160/(5*m : ℝ) := by
  obtain ⟨h1, h0⟩ := t7_good_counts m hm z ht
  have he : (t7_B m z*t7_P z) i j = (t7_P z*t7_B m z) j i := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [t7_B_symmetric m z i k, t7_P_symmetric z h1 h0 k j]
    ring
  rw [he]
  exact t7_PB_bound m hm z ht j i

lemma t7_PBP_bound (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i j : Fin (5*m)) :
    |(t7_P z*t7_B m z*t7_P z) i j| ≤ 160/(5*m : ℝ) := by
  obtain ⟨h1, h0⟩ := t7_good_counts m hm z ht
  have hc : (∑ k, t7_P z k j) = 1 := by
    simp_rw [t7_P_symmetric z h1 h0 _ j]
    exact t7_P_rowsum z h1 h0 j
  rw [Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k, (160/(5*m : ℝ))*t7_P z k j := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (t7_P_nonneg z h1 h0 k j)]
      exact mul_le_mul_of_nonneg_right (t7_PB_bound m hm z ht i k) (t7_P_nonneg z h1 h0 k j)
    _ = (160/(5*m : ℝ))*∑ k, t7_P z k j := by rw [Finset.mul_sum]
    _ = _ := by rw [hc, mul_one]

lemma t7_D_error (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i j : Fin (5*m)) :
    |t7_D m z i j-t7_B m z i j| ≤ 480/(5*m : ℝ) := by
  have he : t7_D m z = t7_B m z-t7_P z*t7_B m z-t7_B m z*t7_P z+
      t7_P z*t7_B m z*t7_P z := by
    have hM : residualMaker z = 1-t7_P z := by unfold t7_P; abel
    rw [t7_D, hM]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hs : t7_D m z i j-t7_B m z i j =
      -((t7_P z*t7_B m z) i j+(t7_B m z*t7_P z) i j)+(t7_P z*t7_B m z*t7_P z) i j := by
    rw [he]
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [hs]
  apply (abs_add_le _ _).trans
  rw [abs_neg]
  have hh := add_le_add (abs_add_le ((t7_P z*t7_B m z) i j) ((t7_B m z*t7_P z) i j))
    (le_refl |(t7_P z*t7_B m z*t7_P z) i j|)
  apply hh.trans
  have h1 := t7_PB_bound m hm z ht i j
  have h2 := t7_BP_bound m hm z ht i j
  have h3 := t7_PBP_bound m hm z ht i j
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)

lemma t7_D_symmetric (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (i j : Fin (5*m)) : t7_D m z i j = t7_D m z j i := by
  obtain ⟨h1, h0⟩ := t7_good_counts m hm z ht
  have hM := (MatrixCompletion.residual_algebra z h1 h0).1
  have hB : (t7_B m z).transpose = t7_B m z := by
    ext a b
    exact t7_B_symmetric m z b a
  have hD : (t7_D m z).transpose = t7_D m z := by
    dsimp only [t7_D]
    simp only [Matrix.transpose_mul, hM, hB, Matrix.mul_assoc]
  simpa only [Matrix.transpose_apply] using congrArg (fun A => A j i) hD

lemma t7_D_square_bound (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    (∑ i, ∑ j, (t7_D m z i j)^2) ≤ 461440*(5*m : ℝ) := by
  have hn : (0 : ℝ) < 5*m := by positivity
  have hB (i j : Fin (5*m)) : |t7_B m z i j| ≤ 8 :=
    (t7_B_abs m hm z ht i j).trans (by linarith [t7_block_kernel_abs m true i j])
  have hsB : (∑ i, ∑ j, (t7_B m z i j)^2) ≤ 320*(5*m : ℝ) := by
    calc
      _ ≤ ∑ i, 8*(∑ j, |t7_B m z i j|) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        nlinarith [sq_abs (t7_B m z i j), abs_nonneg (t7_B m z i j),
          mul_nonneg (sub_nonneg.mpr (hB i j)) (abs_nonneg (t7_B m z i j))]
      _ ≤ ∑ _i : Fin (5*m), (320 : ℝ) := Finset.sum_le_sum (fun i _ => by linarith [t7_B_row m hm z ht i])
      _ = _ := by simp; ring
  have hsE : (∑ i, ∑ j, (t7_D m z i j-t7_B m z i j)^2) ≤ 230400 := by
    calc
      _ ≤ ∑ _i : Fin (5*m), ∑ _j : Fin (5*m), (480/(5*m : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (t7_D_error m hm z ht i j)
      _ = 230400 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp [hn.ne']
        <;> ring
  have hs : (∑ i, ∑ j, (t7_D m z i j)^2) ≤
      2*(∑ i, ∑ j, (t7_B m z i j)^2)+2*(∑ i, ∑ j, (t7_D m z i j-t7_B m z i j)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (t7_D m z i j-2*t7_B m z i j)]
  have hN1 : (1 : ℝ) ≤ 5*m := by exact_mod_cast (by omega : 1 ≤ 5*m)
  linarith

lemma t7_nu_formula (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    adjustmentNu z (starBlockKernel m true) = 2*(∑ i, ∑ j, (t7_D m z i j)^2)/(5*m : ℝ)^2 := by
  have he : Matrix.trace (t7_D m z*t7_D m z) = ∑ i, ∑ j, (t7_D m z i j)^2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [t7_D_symmetric m hm z ht j i]
    ring
  rw [adjustmentNu, t7_adjustment_B m hm]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul, he]
  ring

lemma t7_nu_upper (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) :
    adjustmentNu z (starBlockKernel m true) ≤ 922880/(5*m : ℝ) := by
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  rw [t7_nu_formula m hm z ht]
  calc
    _ ≤ 2*(461440*(5*m : ℝ))/(5*m : ℝ)^2 :=
      div_le_div_of_nonneg_right (by linarith [t7_D_square_bound m hm z ht]) (sq_nonneg _)
    _ = _ := by field_simp [hn]; ring

lemma t7_square_sum_pos {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : Matrix.trace A ≠ 0) :
    0 < ∑ i, ∑ j, (A i j)^2 := by
  by_contra hn
  have hzero : (∑ i, ∑ j, (A i j)^2) = 0 := le_antisymm (le_of_not_gt hn)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hrow (i : Fin N) : (∑ j, (A i j)^2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).mp hzero i (Finset.mem_univ i)
  have hd (i : Fin N) : A i i = 0 :=
    ((Finset.sum_sq_eq_zero_iff Finset.univ (fun j => A i j)).mp (hrow i)) i (Finset.mem_univ i)
  exact hA (by simp only [Matrix.trace, Matrix.diag_apply, hd, Finset.sum_const_zero])

lemma t7_nu_pos (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (hmu : adjustmentMu z (starBlockKernel m true) ≠ 0) :
    0 < adjustmentNu z (starBlockKernel m true) := by
  have hn : (0 : ℝ) < 5*m := by positivity
  have htrace : Matrix.trace (t7_D m z) ≠ 0 := by
    intro h
    apply hmu
    rw [adjustmentMu, t7_adjustment_B m hm, Matrix.trace_smul, h]
    simp
  rw [t7_nu_formula m hm z ht]
  exact div_pos (mul_pos (by norm_num) (t7_square_sum_pos _ htrace)) (sq_pos_of_pos hn)

def t7_df (m : ℕ) (z : Assignment (5*m)) : ℝ :=
  2*(adjustmentMu z (starBlockKernel m true))^2/adjustmentNu z (starBlockKernel m true)

lemma t7_df_lower (m : ℕ) (hm : 0 < m) (z : Assignment (5*m))
    (ht : |t7_fraction m z-1/2| ≤ 1/4) (hmu : 1 ≤ adjustmentMu z (starBlockKernel m true)) :
    (5*m : ℝ)/461440 ≤ t7_df m z := by
  have hn : (0 : ℝ) < 5*m := by positivity
  have hmu0 : adjustmentMu z (starBlockKernel m true) ≠ 0 := by linarith
  have hnu := t7_nu_pos m hm z ht hmu0
  have hu := (le_div_iff₀ hn).mp (t7_nu_upper m hm z ht)
  have hmusq : 1 ≤ (adjustmentMu z (starBlockKernel m true))^2 := by nlinarith
  unfold t7_df
  apply (le_div_iff₀ hnu).mpr
  nlinarith

lemma t7_df_diverges (M : ℝ) :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => t7_df m z ≤ M)) atTop (nhds 0) := by
  have htN : Tendsto (fun m : ℕ => (5*m : ℝ)/461440) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 461440)).mpr
      ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 5)).mpr tendsto_natCast_atTop_atTop)
  have hu : ∀ᶠ m in atTop, prob (fun _ => 1/2) (fun z : Assignment (5*m) => t7_df m z ≤ M) ≤
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => ¬ t7_Good m z) +
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => 1/5 < |adjustmentMu z (starBlockKernel m true)-6/5|) := by
    filter_upwards [eventually_gt_atTop 0, htN.eventually_gt_atTop M] with m hm hM
    apply DesignLimits.DLbSupport.prob_le_add (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num)
    intro z hz
    by_cases hg : t7_Good m z
    · right
      by_contra hbad
      have hmu : 1 ≤ adjustmentMu z (starBlockKernel m true) := by
        linarith [(abs_le.mp (le_of_not_gt hbad)).1]
      have hlow := t7_df_lower m hm z hg.1 hmu
      linarith
    · exact Or.inl hg
  have hl := t7_good_probability.add (t7_mu_limit (1/5) (by norm_num))
  simp only [add_zero] at hl
  exact squeeze_zero' (Eventually.of_forall fun m => T34_prob_nonneg _ (fun _ => by norm_num) _) hu hl

lemma t7_conv_congr (U V : ∀ m, Assignment (5*m) → ℝ) (a : ℝ)
    (hUV : ∀ᶠ m in atTop, ∀ z, U m z = V m z) (hU : t7_Converges U a) : t7_Converges V a := by
  intro ε hε
  apply (hU ε hε).congr'
  filter_upwards [hUV] with m hm
  congr 1
  funext z
  rw [hm z]

lemma t7_adjusted_ratio_limit :
    t7_Converges (fun m z =>
      (kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m true)/
        adjustmentMu z (starBlockKernel m true))/
          variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (starBlockTable m))) (15/16) := by
  let U : ∀ m, Assignment (5*m) → ℝ := fun m z =>
    (5*m : ℝ)*kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m true)
  have hU : t7_Converges U (18/5) := t7_variance_limit true
  let F : (Fin 2 → ℝ) → ℝ := fun v => (v 0/v 1)/(16/5)
  have hf : ContinuousAt F ![18/5, 6/5] := by dsimp only [F]; fun_prop (disch := norm_num)
  have h := t7_conv_map ![U, fun m z => adjustmentMu z (starBlockKernel m true)] ![18/5, 6/5] F hf
    (by intro i; fin_cases i; exact hU; exact t7_mu_limit)
  have hc : F ![18/5, 6/5] = 15/16 := by norm_num [F]
  rw [hc] at h
  apply t7_conv_congr _ _ _ ?_ h
  filter_upwards [eventually_gt_atTop 0] with m hm z
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  have hv : variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (starBlockTable m)) =
      (16/5)/(5*m : ℝ) := (eq_div_iff hn).mpr (by simpa only [mul_comm] using t7_star_exact_variance m hm)
  dsimp only [F, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  rw [hv]
  simp only [div_eq_mul_inv, inv_mul_cancel₀, mul_inv_rev, inv_inv]
  ring

lemma t7_gamma_midpoint_sq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (Real.Gamma ((x+y)/2))^2 ≤ Real.Gamma x * Real.Gamma y := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2) (by norm_num)
  have he : (1/2 : ℝ)*x + (1/2)*y = (x+y)/2 := by ring
  rw [he, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hsq := (sq_le_sq₀ (Real.Gamma_pos_of_pos (by linarith : 0 < (x+y)/2)).le
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr h
  simpa only [mul_pow, Real.sq_sqrt (Real.Gamma_pos_of_pos hx).le,
    Real.sq_sqrt (Real.Gamma_pos_of_pos hy).le] using hsq

lemma t7_gamma_ratio_bounds (x : ℝ) (hx : 0 < x) :
    x/(x+1/2) ≤ (Real.Gamma (x+1/2)/(Real.sqrt x*Real.Gamma x))^2 ∧
    (Real.Gamma (x+1/2)/(Real.sqrt x*Real.Gamma x))^2 ≤ 1 := by
  have hg := Real.Gamma_pos_of_pos hx
  have hh := Real.Gamma_pos_of_pos (by linarith : 0 < x+1/2)
  have hd : 0 < Real.sqrt x * Real.Gamma x := mul_pos (Real.sqrt_pos.mpr hx) hg
  have hu := t7_gamma_midpoint_sq x (x+1) hx (by linarith)
  rw [show (x+(x+1))/2 = x+1/2 by ring, Real.Gamma_add_one hx.ne'] at hu
  have hl := t7_gamma_midpoint_sq (x+1/2) (x+1/2+1) (by linarith) (by linarith)
  rw [show ((x+1/2)+(x+1/2+1))/2 = x+1 by ring,
    Real.Gamma_add_one hx.ne', Real.Gamma_add_one (by linarith : x+1/2 ≠ 0)] at hl
  rw [div_pow]
  constructor
  · apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < x+1/2) (sq_pos_of_pos hd)).mpr
    rw [mul_pow, Real.sq_sqrt hx.le]
    nlinarith [hl]
  · apply (div_le_one (sq_pos_of_pos hd)).mpr
    rw [mul_pow, Real.sq_sqrt hx.le]
    nlinarith [hu]

lemma t7_gamma_ratio_tendsto :
    Tendsto (fun x : ℝ => Real.Gamma (x+1/2)/(Real.sqrt x*Real.Gamma x))
      atTop (nhds 1) := by
  have hinv : Tendsto (fun x : ℝ => 1/(x+1/2)) atTop (nhds 0) :=
    by
      have hadd : Tendsto (fun x : ℝ => x+1/2) atTop atTop :=
        tendsto_atTop_add_const_right atTop (1/2 : ℝ) tendsto_id
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hadd
  have hl : Tendsto (fun x : ℝ => 1-(1/2)*(1/(x+1/2))) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv) using 1 <;> norm_num
  have hs : Tendsto (fun x : ℝ =>
      (Real.Gamma (x+1/2)/(Real.sqrt x*Real.Gamma x))^2) atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have he : 1-(1/2)*(1/(x+1/2)) = x/(x+1/2) := by
        field_simp
        <;> ring
      rw [he]
      exact (t7_gamma_ratio_bounds x hx).1
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (t7_gamma_ratio_bounds x hx).2
  have ht := hs.sqrt
  simp only [Real.sqrt_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.sqrt_sq (div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
    (mul_nonneg (Real.sqrt_nonneg _) (Real.Gamma_pos_of_pos hx).le))]

lemma t7_student_prefactor_tendsto :
    Tendsto (fun ν : ℝ => Real.Gamma ((ν+1)/2) /
      (Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))) atTop
      (nhds (1/Real.sqrt (2*Real.pi))) := by
  have hhalf : Tendsto (fun ν : ℝ => ν/2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have ht := (t7_gamma_ratio_tendsto.comp hhalf).div_const (Real.sqrt (2*Real.pi))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  have hs : Real.sqrt (ν/2) * Real.sqrt (2*Real.pi) = Real.sqrt (ν*Real.pi) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ν/2)]
    congr 1
    ring
  dsimp only [Function.comp_apply]
  rw [show ν/2+1/2 = (ν+1)/2 by ring, div_div]
  congr 1
  rw [mul_right_comm, hs]

lemma t7_student_power_tendsto (x : ℝ) :
    Tendsto (fun ν : ℝ => (1+x^2/ν)^(-(ν+1)/2)) atTop
      (nhds (Real.exp (-x^2/2))) := by
  have hi : Tendsto (fun ν : ℝ => ν⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have he : Tendsto (fun ν : ℝ => -(1+ν⁻¹)/2) atTop (nhds (-(1/2 : ℝ))) := by
    convert ((tendsto_const_nhds.add hi).neg).div_const 2 using 1 <;> norm_num
  have ht := (Real.tendsto_one_add_div_rpow_exp (x^2)).rpow he
    (Or.inl (Real.exp_pos _).ne')
  rw [← Real.exp_mul] at ht
  have hn : x^2 * (-(1/2 : ℝ)) = -x^2/2 := by ring
  rw [hn] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1+x^2/ν)]
  congr 1
  field_simp
  <;> ring

lemma t7_student_density_tendsto (x : ℝ) :
    Tendsto (fun ν : ℝ => studentDensity ν x) atTop
      (nhds (ProbabilityTheory.gaussianPDFReal 0 1 x)) := by
  simpa only [studentDensity, ProbabilityTheory.gaussianPDFReal, NNReal.coe_one,
    mul_one, sub_zero, one_div] using
    t7_student_prefactor_tendsto.mul (t7_student_power_tendsto x)

lemma t7_student_density_continuous (ν : ℝ) (hν : 0 < ν) :
    Continuous (studentDensity ν) := by
  unfold studentDensity
  apply continuous_const.mul
  apply (continuous_const.add ((continuous_id.pow 2).div_const ν)).rpow_const
  intro x
  apply Or.inl
  change 1+x^2/ν ≠ 0
  exact (by positivity : (0 : ℝ) < 1+x^2/ν).ne'

lemma t7_student_prefactor_pos (ν : ℝ) (hν : 0 < ν) :
    0 < Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2)) := by
  exact div_pos (Real.Gamma_pos_of_pos (by linarith))
    (mul_pos (Real.sqrt_pos.mpr (mul_pos hν Real.pi_pos))
      (Real.Gamma_pos_of_pos (by linarith)))

lemma t7_student_density_nonneg (ν x : ℝ) (hν : 0 < ν) :
    0 ≤ studentDensity ν x := by
  exact mul_nonneg (t7_student_prefactor_pos ν hν).le (Real.rpow_nonneg (by positivity) _)

lemma t7_student_power_bound (ν x : ℝ) (hν : 1 ≤ ν) :
    (1+x^2/ν)^(-(ν+1)/2) ≤ 2/(1+x^2) := by
  have hν0 : 0 < ν := by linarith
  have hb := one_add_mul_self_le_rpow_one_add
    (s := x^2/ν) (by
      have hh : (0 : ℝ) ≤ x^2/ν := by positivity
      linarith)
    (p := (ν+1)/2) (by linarith)
  have he : 1+(ν+1)/2*(x^2/ν) = 1+x^2/2+x^2/(2*ν) := by
    field_simp
    <;> ring
  rw [he] at hb
  have hl : (1+x^2)/2 ≤ (1+x^2/ν)^((ν+1)/2) := by
    have hh : 0 ≤ x^2/(2*ν) := by positivity
    nlinarith [sq_nonneg x]
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1+x^2)/2) hl
  rw [one_div_div] at hi
  rw [show -(ν+1)/2 = -((ν+1)/2) by ring, Real.rpow_neg (by positivity)]
  simpa only [one_div] using hi

lemma t7_student_density_bound (ν C : ℝ) (hν : 1 ≤ ν)
    (hC : Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2)) ≤ C)
    (x : ℝ) : ‖studentDensity ν x‖ ≤ (2*C)*(1+x^2)⁻¹ := by
  have hν0 : 0 < ν := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (t7_student_density_nonneg ν x hν0)]
  unfold studentDensity
  calc
    _ ≤ C*(2/(1+x^2)) := mul_le_mul hC (t7_student_power_bound ν x hν)
      (Real.rpow_nonneg (by positivity) _) ((t7_student_prefactor_pos ν hν0).le.trans hC)
    _ = _ := by ring

lemma t7_student_cdf_tendsto (x : ℝ) :
    Tendsto (fun ν : ℝ => studentCDF ν x) atTop (nhds (normalCDF x)) := by
  let L : ℝ := 1/Real.sqrt (2*Real.pi)
  let C : ℝ := L+1
  have hC : ∀ᶠ ν : ℝ in atTop,
      Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2)) ≤ C := by
    exact (t7_student_prefactor_tendsto.eventually (eventually_lt_nhds
      (show L < C by dsimp [C]; linarith))).mono fun _ h => h.le
  have hbound : Integrable (fun t : ℝ => (2*C)*(1+t^2)⁻¹)
      (volume.restrict (Set.Iic x)) :=
    (integrable_inv_one_add_sq.const_mul (2*C)).integrableOn
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Iic x)) (fun t : ℝ => (2*C)*(1+t^2)⁻¹)
    (F := fun ν t => studentDensity ν t) (f := ProbabilityTheory.gaussianPDFReal 0 1)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
      exact (t7_student_density_continuous ν hν).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ), hC] with ν hν hνC
      exact ae_of_all _ fun t => t7_student_density_bound ν C hν hνC t)
    hbound (ae_of_all _ t7_student_density_tendsto)
  have hnormal : (∫ t in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 t) = normalCDF x := by
    rw [normalCDF, ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    exact integral_nonneg (fun _ => ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
  rw [hnormal] at hlim
  exact hlim

lemma t7_student_density_integrable (ν : ℝ) (hν : 1 ≤ ν) :
    Integrable (studentDensity ν) := by
  let C := Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))
  apply (integrable_inv_one_add_sq.const_mul (2*C)).mono'
    (t7_student_density_continuous ν (by linarith)).aestronglyMeasurable
  exact ae_of_all _ fun x => t7_student_density_bound ν C hν le_rfl x

lemma t7_student_cdf_monotone (ν : ℝ) (hν : 1 ≤ ν) : Monotone (studentCDF ν) := by
  intro a b hab
  exact setIntegral_mono_set (t7_student_density_integrable ν hν).integrableOn
    (ae_of_all _ fun x => t7_student_density_nonneg ν x (by linarith))
    (ae_of_all _ fun x hx => le_trans hx hab)

/-- Student quantiles converge to normal quantiles as the real degrees of freedom tend to infinity. -/
lemma t7_student_quantile_normal (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun ν : ℝ => studentQuantile ν a) atTop (nhds (normalQuantile a)) := by
  obtain ⟨_, hmono, _, _, hquant, _, _⟩ := DesignLimits.nf_proof
  have hc : normalCDF (normalQuantile a) = a := hquant a ha0 ha1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let q := normalQuantile a
  have hl : normalCDF (q-ε/2) < a := by
    rw [← hc]
    exact hmono (by dsimp [q]; linarith)
  have hu : a < normalCDF (q+ε/2) := by
    rw [← hc]
    exact hmono (by dsimp [q]; linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (t7_student_cdf_tendsto (q-ε/2)).eventually (eventually_lt_nhds hl),
    (t7_student_cdf_tendsto (q+ε/2)).eventually (eventually_gt_nhds hu)] with ν hν hlν huν
  let S : Set ℝ := {t | a ≤ studentCDF ν t}
  have hs : S.Nonempty := ⟨q+ε/2, huν.le⟩
  have hlo : ∀ t ∈ S, q-ε/2 ≤ t := by
    intro t ht
    by_contra hn
    have hm := t7_student_cdf_monotone ν hν (le_of_lt (lt_of_not_ge hn))
    exact (not_lt_of_ge ht) (hm.trans_lt hlν)
  have hlow : q-ε/2 ≤ sInf S := le_csInf hs hlo
  have hup : sInf S ≤ q+ε/2 := csInf_le ⟨q-ε/2, hlo⟩ huν.le
  change dist (sInf S) q < ε
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

def t7_critical (m : ℕ) (z : Assignment (5*m)) : ℝ := studentQuantile (t7_df m z) (39/40)

lemma t7_critical_limit : t7_Converges t7_critical (normalQuantile (39/40)) := by
  intro ε hε
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp
    (t7_student_quantile_normal (39/40) (by norm_num) (by norm_num)) ε hε)
  have hu (m : ℕ) : prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      ε < |t7_critical m z-normalQuantile (39/40)|) ≤
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => t7_df m z ≤ M) := by
    apply T34_prob_mono (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num)
    intro z hz
    by_contra hn
    have hh := hM (t7_df m z) (le_of_lt (lt_of_not_ge hn))
    rw [Real.dist_eq] at hh
    exact (not_lt_of_ge hh.le) hz
  exact squeeze_zero (fun m => T34_prob_nonneg _ (fun _ => by norm_num) _) hu (t7_df_diverges M)

def t7_ratio (m : ℕ) (z : Assignment (5*m)) : ℝ :=
  (kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m true)/
    adjustmentMu z (starBlockKernel m true))/
      variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (starBlockTable m))

def t7_radius (m : ℕ) (z : Assignment (5*m)) : ℝ := t7_critical m z*Real.sqrt (t7_ratio m z)

lemma t7_radius_limit :
    t7_Converges t7_radius (normalQuantile (39/40)*Real.sqrt (15/16)) := by
  have h := t7_conv_map ![t7_critical, t7_ratio] ![normalQuantile (39/40), 15/16]
    (fun v : Fin 2 → ℝ => v 0*Real.sqrt (v 1)) (by fun_prop)
    (by intro i; fin_cases i; exact t7_critical_limit; exact t7_adjusted_ratio_limit)
  simpa only [t7_Converges, t7_radius, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const] using h

lemma t7_normal_limit_lt (Z : ∀ m, Assignment (5*m) → ℝ)
    (hZ : ∀ x : ℝ, Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => Z m z ≤ x))
      atTop (nhds (normalCDF x))) (x : ℝ) :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => Z m z < x))
      atTop (nhds (normalCDF x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨y, hy, hby⟩ := DesignLimits.DLbSupport.cdf_left x b hb
    filter_upwards [(tendsto_order.mp (hZ y)).1 b hby] with m hm
    exact hm.trans_le (T34_prob_mono (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num) _ _
      (fun z hz => lt_of_le_of_lt hz hy))
  · intro b hb
    filter_upwards [(tendsto_order.mp (hZ x)).2 b hb] with m hm
    exact lt_of_le_of_lt (T34_prob_mono (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num) _ _
      (fun z hz => hz.le)) hm

lemma t7_normal_limit_abs (Z : ∀ m, Assignment (5*m) → ℝ)
    (hZ : ∀ x : ℝ, Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => Z m z ≤ x))
      atTop (nhds (normalCDF x))) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ r))
      atTop (nhds (2*normalCDF r-1)) := by
  have he (m : ℕ) : prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ r) =
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => Z m z ≤ r) -
        prob (fun _ => 1/2) (fun z : Assignment (5*m) => Z m z < -r) := by
    calc
      _ = prob (fun _ => 1/2) (fun z : Assignment (5*m) => -r ≤ Z m z ∧ Z m z ≤ r) :=
        DesignLimits.DLbSupport.prob_congr _ _ _ (fun _ => abs_le)
      _ = _ := DesignLimits.DLbSupport.prob_closed_interval _ _ (-r) r (by linarith)
  have h := (hZ r).sub (t7_normal_limit_lt Z hZ (-r))
  rw [DesignLimits.DLbSupport.normalCDF_neg] at h
  have hh : normalCDF r-(1-normalCDF r) = 2*normalCDF r-1 := by ring
  rw [hh] at h
  exact h.congr (fun m => (he m).symm)

lemma t7_random_radius (Z R : ∀ m, Assignment (5*m) → ℝ)
    (hZ : ∀ x : ℝ, Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => Z m z ≤ x))
      atTop (nhds (normalCDF x))) (r : ℝ) (hr : 0 < r) (hR : t7_Converges R r) :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ R m z))
      atTop (nhds (2*normalCDF r-1)) := by
  have hsand (ε : ℝ) (m : ℕ) :
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ r-ε) -
          prob (fun _ => 1/2) (fun z : Assignment (5*m) => ε < |R m z-r|) ≤
            prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ R m z) ∧
      prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ R m z) ≤
        prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ r+ε) +
          prob (fun _ => 1/2) (fun z : Assignment (5*m) => ε < |R m z-r|) := by
    have hlo : prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ r-ε) ≤
        prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ R m z) +
          prob (fun _ => 1/2) (fun z : Assignment (5*m) => ε < |R m z-r|) := by
      apply DesignLimits.DLbSupport.prob_le_add (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num)
      intro z hz
      by_cases hb : ε < |R m z-r|
      · exact Or.inr hb
      · left
        have hh := abs_le.mp (le_of_not_gt hb)
        linarith
    have hhi : prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ R m z) ≤
        prob (fun _ => 1/2) (fun z : Assignment (5*m) => |Z m z| ≤ r+ε) +
          prob (fun _ => 1/2) (fun z : Assignment (5*m) => ε < |R m z-r|) := by
      apply DesignLimits.DLbSupport.prob_le_add (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num)
      intro z hz
      by_cases hb : ε < |R m z-r|
      · exact Or.inr hb
      · left
        have hh := abs_le.mp (le_of_not_gt hb)
        linarith
    constructor <;> linarith
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨y, hy, hby⟩ := DesignLimits.DLbSupport.cdf_left r ((b+1)/2) (by linarith)
    let l : ℝ := max y 0
    have hl0 : 0 ≤ l := le_max_right _ _
    have hlr : l < r := max_lt_iff.mpr ⟨hy, hr⟩
    have hyl : normalCDF y ≤ normalCDF l := DesignLimits.nf_proof.2.1.monotone (le_max_left _ _)
    have hgap : b < 2*normalCDF l-1 := by linarith
    let ε := r-l
    have hε : 0 < ε := sub_pos.mpr hlr
    have he : r-ε = l := by dsimp [ε]; ring
    have hlim := (t7_normal_limit_abs Z hZ l hl0).sub (hR ε hε)
    simp only [sub_zero] at hlim
    filter_upwards [(tendsto_order.mp hlim).1 b hgap] with m hm
    have hlower := (hsand ε m).1
    rw [he] at hlower
    exact hm.trans_le hlower
  · intro b hb
    obtain ⟨y, hy, hyb⟩ := DesignLimits.DLbSupport.cdf_right r ((b+1)/2) (by linarith)
    have hy0 : 0 ≤ y := (hr.trans hy).le
    have hgap : 2*normalCDF y-1 < b := by linarith
    let ε := y-r
    have hε : 0 < ε := sub_pos.mpr hy
    have he : r+ε = y := by dsimp [ε]; ring
    have hlim := (t7_normal_limit_abs Z hZ y hy0).add (hR ε hε)
    simp only [add_zero] at hlim
    filter_upwards [(tendsto_order.mp hlim).2 b hgap] with m hm
    have hupper := (hsand ε m).2
    rw [he] at hupper
    exact hupper.trans_lt hm

lemma t7_normal_critical_pos : 0 < normalQuantile (39/40) := by
  obtain ⟨_, hmono, hzero, _, hquant, _, _⟩ := DesignLimits.nf_proof
  have hc := hquant (39/40) (by norm_num) (by norm_num)
  apply hmono.lt_iff_lt.mp
  rw [hzero, hc]
  norm_num

lemma t7_coverage_limit :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      let Q := starBlockKernel m true
      let μ := adjustmentMu z Q
      let ν := adjustmentNu z Q
      |hajek (starBlockTable m) z| ≤ studentQuantile (2*μ^2/ν) (39/40) *
        Real.sqrt (kernelVariance z (residual (starBlockTable m) z) Q/μ))) atTop
      (nhds (2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1)) := by
  have hr : 0 < normalQuantile (39/40)*Real.sqrt (15/16) :=
    mul_pos t7_normal_critical_pos (Real.sqrt_pos.mpr (by norm_num))
  have hcov := t7_random_radius
    (fun m z => Real.sqrt (5*m : ℝ)*hajek (starBlockTable m) z/Real.sqrt (16/5))
    t7_radius t7_star_clt _ hr t7_radius_limit
  apply hcov.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  apply DesignLimits.DLbSupport.prob_congr
  intro z
  have hn : (5*m : ℝ) ≠ 0 := by positivity
  have hv : variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (starBlockTable m)) =
      (16/5)/(5*m : ℝ) := (eq_div_iff hn).mpr (by simpa only [mul_comm] using t7_star_exact_variance m hm)
  have hVpos : 0 < variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (starBlockTable m)) := by
    rw [hv]
    positivity
  have hsV := Real.sqrt_pos.mpr hVpos
  have hZ : Real.sqrt (5*m : ℝ)*hajek (starBlockTable m) z/Real.sqrt (16/5) =
      hajek (starBlockTable m) z/Real.sqrt (variance (fun _ => 1/2)
        (linearHajek (fun _ => 1/2) (starBlockTable m))) := by
    rw [hv, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 16/5) (5*m : ℝ)]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  dsimp only [t7_radius, t7_ratio, t7_critical, t7_df]
  rw [hZ, abs_div, abs_of_pos hsV, Real.sqrt_div' _ hVpos.le, ← mul_div_assoc]
  exact div_le_div_iff_of_pos_right hsV

lemma t7_normal_strict_undercoverage :
    2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1 < 19/20 := by
  obtain ⟨_, hmono, hzero, _, hquant, _, _⟩ := DesignLimits.nf_proof
  have hc : normalCDF (normalQuantile (39/40)) = (39/40 : ℝ) :=
    hquant _ (by norm_num) (by norm_num)
  have hpos : 0 < normalQuantile (39/40) := by
    apply hmono.lt_iff_lt.mp
    rw [hzero, hc]
    norm_num
  have hs : Real.sqrt (15/16) < 1 := by
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hq : normalQuantile (39/40) * Real.sqrt (15/16) < normalQuantile (39/40) := by
    nlinarith
  have h := hmono hq
  rw [hc] at h
  linarith

theorem adjusted_pd_asymptotic_counterexample_proof :
    SpatialLocalConditions starPopulation ∧
    (∀ N : ℕ, 0 < N → WellDefined (starPopulation N) 0) ∧
    (∀ N, homophilyQ (fun _ => 1/2) (circleAverage (starPopulation N) 0)
      (spatialNeighborhoods starPopulation (6/5) N)
      (fun _ a => barMu (fun _ => 1/2) (circleAverage (starPopulation N) 0) a) = 0) ∧
    Nondegenerate (fun N => variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (circleAverage (starPopulation N) 0))) ∧
    (∀ m, uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5) = starBlockKernel m false) ∧
    (∀ m : ℕ, 0 < m → (5*m : ℝ) * variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (starBlockTable m)) = 16/5) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      ε < |(5*m : ℝ)*kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m false)-16/5|)) atTop (nhds 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      ε < |(5*m : ℝ)*kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m true)-18/5|)) atTop (nhds 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      ε < |adjustmentMu z (starBlockKernel m true)-6/5|)) atTop (nhds 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      ε < |(kernelVariance z (residual (starBlockTable m) z) (starBlockKernel m true) /
        adjustmentMu z (starBlockKernel m true)) /
          variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (starBlockTable m))-15/16|)) atTop (nhds 0)) ∧
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      let Q := starBlockKernel m true
      let μ := adjustmentMu z Q
      let ν := adjustmentNu z Q
      |hajek (starBlockTable m) z| ≤ studentQuantile (2*μ^2/ν) (39/40) *
        Real.sqrt (kernelVariance z (residual (starBlockTable m) z) Q/μ))) atTop
      (nhds (2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1)) ∧
    2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1 < 19/20 := by
  refine ⟨t7_star_spatialLocal, (fun N _ => t7_star_wellDefined N),
    t7_star_homophily, t7_star_nondegenerate, t7_star_kernel, t7_star_exact_variance,
    ?_, ?_, t7_mu_limit, t7_adjusted_ratio_limit, t7_coverage_limit,
    t7_normal_strict_undercoverage⟩
  · simpa only [t7_Converges, Bool.false_eq_true, if_false] using t7_variance_limit false
  · simpa only [t7_Converges, if_true] using t7_variance_limit true

end
end AronowAudit.P004.Wave1
