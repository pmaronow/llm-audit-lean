import AronowAudit.P004.P004_Spatial
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.Convex.Combination

/-! Exact finite resampling and spatial rectangle-family counterexamples. -/
namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

/- Atomic integration calculations for the signed Monte Carlo witness. -/
private theorem mc_level_point_injective : Function.Injective eightNodeNullPoint := by
  intro i j hij
  have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hij
  have hcast : (i : ℝ) = (j : ℝ) := by
    simp only [eightNodeNullPoint, planePoint, PiLp.toLp_apply,
      Matrix.cons_val_zero] at hcoord
    linarith
  apply Fin.ext
  exact_mod_cast hcast

private theorem mc_level_region (i : Fin 8) :
    region eightNodeNullPopulation i 0 = {eightNodeNullPoint i} := by
  ext x
  simp only [region, nodeDistance, eightNodeNullPopulation, Metric.infDist_singleton,
    Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff]
  exact ⟨fun h => dist_eq_zero.mp (le_antisymm h.2 dist_nonneg),
    fun h => by subst x; simp⟩

private theorem mc_level_mass (i : Fin 8) :
    eightNodeNullPopulation.zeta {eightNodeNullPoint i} = 1 := by
  change (∑ j : Fin 8, Measure.dirac (eightNodeNullPoint j)) {eightNodeNullPoint i} = 1
  rw [Measure.finsetSum_apply]
  simp [Measure.dirac_apply, Pi.single_apply, mc_level_point_injective.eq_iff]

private theorem mc_level_outcome_at_point (i : Fin 8) (z : Assignment 8) :
    eightNodeNullPopulation.outcome (eightNodeNullPoint i) z = eightNodeNullTable i z := by
  change (∑ j : Fin 8, if eightNodeNullPoint i = eightNodeNullPoint j
    then eightNodeNullTable j z else 0) = _
  simp [mc_level_point_injective.eq_iff]

private theorem mc_level_average :
    circleAverage eightNodeNullPopulation 0 = eightNodeNullTable := by
  funext i z
  rw [circleAverage, mc_level_region, integral_singleton]
  simp only [measureReal_def, mc_level_mass, ENNReal.toReal_one,
    one_smul, div_one, mc_level_outcome_at_point]

private theorem mc_level_wellDefined : WellDefined eightNodeNullPopulation 0 := by
  intro i
  rw [mc_level_region]
  refine ⟨measurableSet_singleton _, ?_, ?_, ?_⟩
  · rw [mc_level_mass]; norm_num
  · rw [mc_level_mass]; norm_num
  · intro z
    apply integrableOn_singleton
    · finiteness
    · rw [mc_level_mass]; norm_num


private def mc_level_successes {A : Type*} {P : ℕ} (E : A → Prop)
    (d : Fin P → A) : Finset (Fin P) := Finset.univ.filter (fun i => E (d i))

private theorem mc_level_pattern_mass {A : Type*} [Fintype A] {P : ℕ}
    (w : A → ℝ) (E : A → Prop) (s : Finset (Fin P)) :
    (∑ d : Fin P → A, if mc_level_successes E d = s then ∏ i, w (d i) else 0) =
      ∏ i : Fin P, (∑ a, if (E a ↔ i ∈ s) then w a else 0) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.prod_ite_zero]
  congr 1
  simp only [mc_level_successes, Finset.ext_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

private theorem mc_level_pattern_binomial {A : Type*} [Fintype A] {P : ℕ}
    (w : A → ℝ) (E : A → Prop) (q : ℝ)
    (hq : (∑ a, if E a then w a else 0) = q)
    (hr : (∑ a, if ¬ E a then w a else 0) = 1-q)
    (s : Finset (Fin P)) :
    (∑ d : Fin P → A, if mc_level_successes E d = s then ∏ i, w (d i) else 0) =
      q ^ s.card * (1-q) ^ (P-s.card) := by
  rw [mc_level_pattern_mass]
  have hi (i : Fin P) : (∑ a, if (E a ↔ i ∈ s) then w a else 0) =
      if i ∈ s then q else 1-q := by
    by_cases h : i ∈ s
    · simpa only [h, iff_true, if_true] using hq
    · simpa only [h, iff_false, if_false] using hr
  simp_rw [hi]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
    Finset.filter_not, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin]

private theorem mc_level_binomial_expect {A : Type*} [Fintype A] {P : ℕ}
    (w : A → ℝ) (E : A → Prop) (q : ℝ)
    (hq : (∑ a, if E a then w a else 0) = q)
    (hr : (∑ a, if ¬ E a then w a else 0) = 1-q) (F : ℕ → ℝ) :
    (∑ d : Fin P → A, (∏ i, w (d i)) * F (mc_level_successes E d).card) =
      ∑ b ∈ Finset.range (P+1), (P.choose b : ℝ) * q^b * (1-q)^(P-b) * F b := by
  have hf := Finset.sum_fiberwise (Finset.univ : Finset (Fin P → A))
    (mc_level_successes E) (fun d => (∏ i, w (d i)) * F (mc_level_successes E d).card)
  rw [← hf]
  have hs (s : Finset (Fin P)) :
      (∑ d ∈ Finset.univ.filter (fun d : Fin P → A => mc_level_successes E d = s),
        (∏ i, w (d i)) * F (mc_level_successes E d).card) =
      (q^s.card * (1-q)^(P-s.card)) * F s.card := by
    calc
      _ = (∑ d : Fin P → A, if mc_level_successes E d = s then ∏ i, w (d i) else 0) * F s.card := by
        rw [Finset.sum_mul, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : mc_level_successes E d = s <;> simp [hd]
      _ = _ := by rw [mc_level_pattern_binomial w E q hq hr]
  simp_rw [hs]
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ∑ _s ∈ Finset.powersetCard b (Finset.univ : Finset (Fin P)),
        q^b * (1-q)^(P-b) * F b := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_powersetCard.mp hs).2]
    _ = _ := by simp; ring

private def mc_level_code : Assignment 8 ≃ Fin 256 :=
  (Equiv.piCongrRight fun _ : Fin 8 => finTwoEquiv.symm).trans finFunctionFinEquiv

private theorem mc_level_ht_code (z : Assignment 8) :
    ht (fun _ => 1/2) eightNodeNullTable z =
      (2*((mc_level_code z).val : ℝ)-255)/512 := by
  have hb (b : Bool) : ((finTwoEquiv.symm b).val : ℝ) = bit b := by
    cases b <;> norm_num [finTwoEquiv, bit]
  change _ = (2*((∑ i : Fin 8, (finTwoEquiv.symm (z i)).val * 2^i.val : ℕ) : ℝ)-255)/512
  push_cast
  simp_rw [hb]
  norm_num [ht, eightNodeNullTable, Fin.sum_univ_succ]
  ring

private def mc_level_pair : (Fin 128 × Bool) ≃ Fin 256 where
  toFun a := if a.2 then ⟨255-a.1.val, by omega⟩ else ⟨a.1.val, by omega⟩
  invFun j := if h : j.val < 128 then (⟨j.val,h⟩,false)
    else (⟨255-j.val, by omega⟩,true)
  left_inv a := by
    rcases a with ⟨⟨r,hr⟩,b⟩
    cases b
    · dsimp
      rw [dif_pos hr]
    · dsimp
      rw [dif_neg (by omega : ¬ 255-r < 128)]
      apply Prod.ext
      · apply Fin.ext
        simp only [Fin.val_mk]
        omega
      · rfl
  right_inv j := by
    by_cases h : j.val < 128
    · simp [h]
    · apply Fin.ext
      simp only [h, ↓reduceDIte, Prod.fst, Prod.snd, ↓reduceIte, Fin.val_mk]
      omega

private theorem mc_level_magnitude (r : Fin 128) (b : Bool) :
    |ht (fun _ => 1/2) eightNodeNullTable (mc_level_code.symm (mc_level_pair (r,b)))| =
      (255-2*(r.val : ℝ))/512 := by
  rw [mc_level_ht_code, Equiv.apply_symm_apply]
  have hr : (r.val : ℝ) ≤ 127 := by exact_mod_cast r.is_le
  cases b
  · change |(2*(r.val : ℝ)-255)/512| = _
    rw [abs_of_neg (by linarith)]
    ring
  · change |(2*((255-r.val : ℕ) : ℝ)-255)/512| = _
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [abs_of_pos (by linarith)]
    ring

private def mc_level_assignment : (Fin 128 × Bool) ≃ Assignment 8 :=
  mc_level_pair.trans mc_level_code.symm

private theorem mc_level_comparison (a b : Fin 128 × Bool) :
    |ht (fun _ => 1/2) eightNodeNullTable (mc_level_assignment a)| ≤
      |ht (fun _ => 1/2) eightNodeNullTable (mc_level_assignment b)| ↔ b.1 ≤ a.1 := by
  rw [show mc_level_assignment a = mc_level_code.symm (mc_level_pair a) from rfl,
    show mc_level_assignment b = mc_level_code.symm (mc_level_pair b) from rfl,
    mc_level_magnitude, mc_level_magnitude]
  constructor
  · intro h
    have : (b.1.val : ℝ) ≤ a.1.val := by linarith
    exact_mod_cast this
  · intro h
    have : (b.1.val : ℝ) ≤ a.1.val := by exact_mod_cast h
    linarith

private theorem mc_level_half_weight (z : Assignment 8) :
    designWeight (fun _ => 1/2) z = (1:ℝ)/256 := by
  have h (i : Fin 8) : coin (1/2) (z i) = (1:ℝ)/2 := by cases z i <;> norm_num [coin]
  simp only [designWeight, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

private theorem mc_level_rank_mass (r : Fin 128) :
    (∑ a : Fin 128 × Bool, if a.1 ≤ r then (1:ℝ)/256 else 0) =
      ((r.val:ℝ)+1)/128 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hi : Finset.univ.filter (fun a : Fin 128 => a ≤ r) = Finset.Iic r := by
    ext a
    simp
  calc
    _ = ∑ a : Fin 128, if a ≤ r then (1:ℝ)/128 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> norm_num
    _ = (∑ a : Fin 128, if a ≤ r then (1:ℝ) else 0)/128 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> norm_num
    _ = _ := by rw [Finset.sum_boole, hi, Fin.card_Iic]; push_cast; ring

private theorem mc_level_rank_complement (r : Fin 128) :
    (∑ a : Fin 128 × Bool, if ¬ a.1 ≤ r then (1:ℝ)/256 else 0) =
      1-((r.val:ℝ)+1)/128 := by
  have hsum : (∑ a : Fin 128 × Bool, (1:ℝ)/256) = 1 := by norm_num
  have hh : (∑ a : Fin 128 × Bool, if a.1 ≤ r then (1:ℝ)/256 else 0) +
      (∑ a : Fin 128 × Bool, if ¬ a.1 ≤ r then (1:ℝ)/256 else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  rw [mc_level_rank_mass] at hh
  linarith

private theorem mc_level_exceedances_cons {P : ℕ} (a : Fin 128 × Bool)
    (d : Fin P → Fin 128 × Bool) :
    mcExceedances (ht (fun _ => 1/2) eightNodeNullTable)
      (fun i : Fin (P+1) => mc_level_assignment ((Fin.cons a d : Fin (P+1) → Fin 128 × Bool) i)) =
      (mc_level_successes (fun b : Fin 128 × Bool => b.1 ≤ a.1) d).card := by
  simp only [mcExceedances, mc_level_successes, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ne_eq,
    not_true_eq_false, not_false_eq_true, false_and, true_and, ite_false, zero_add,
    mc_level_comparison]

private theorem mc_level_reject_iff (B : ℕ) :
    (B:ℝ)/100 ≤ 1/20 ↔ B ≤ 5 := by
  constructor
  · intro h
    have : (B:ℝ) ≤ 5 := by linarith
    exact_mod_cast this
  · intro h
    have : (B:ℝ) ≤ 5 := by exact_mod_cast h
    linarith

private theorem mc_level_conditional (r : Fin 128) :
    (∑ d : Fin 100 → Fin 128 × Bool, (∏ _i : Fin 100, (1:ℝ)/256) *
      (if (mc_level_successes (fun a : Fin 128 × Bool => a.1 ≤ r) d).card ≤ 5 then 1 else 0)) =
    ((∑ b ∈ Finset.range 6,
      (100:ℕ).choose b * (r.val+1)^b * (128-(r.val+1))^(100-b) : ℕ) : ℝ)/128^100 := by
  rw [mc_level_binomial_expect (P := 100) (fun _ : Fin 128 × Bool => (1:ℝ)/256)
    (fun a => a.1 ≤ r) (((r.val:ℝ)+1)/128) (by
      convert mc_level_rank_mass r using 1 <;> congr! 3) (by
      convert mc_level_rank_complement r using 1 <;> congr! 3) (fun b => if b ≤ 5 then 1 else 0)]
  have hf : (Finset.range 101).filter (fun b : ℕ => b ≤ 5) = Finset.range 6 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∑ b ∈ Finset.range 6, ((100:ℕ).choose b : ℝ) * (((r.val:ℝ)+1)/128)^b *
        (1-((r.val:ℝ)+1)/128)^(100-b) := by
      rw [← hf, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = _ := by
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b hb
      have hb100 : b ≤ 100 := by have := Finset.mem_range.mp hb; omega
      have hr128 : r.val+1 ≤ 128 := r.is_lt
      have hr : 1-((r.val:ℝ)+1)/128 = ((128-(r.val+1):ℕ):ℝ)/128 := by
        rw [Nat.cast_sub hr128]
        push_cast
        ring
      rw [hr, div_pow, div_pow]
      calc
        _ = (((100:ℕ).choose b:ℝ) * ((r.val:ℝ)+1)^b * ((128-(r.val+1):ℕ):ℝ)^(100-b)) /
            ((128:ℝ)^b * 128^(100-b)) := by ring
        _ = _ := by
          rw [← pow_add, Nat.add_sub_of_le hb100, Nat.cast_sub hr128]
          push_cast
          rw [Nat.cast_sub r.is_le]
          push_cast
          ring

private theorem mc_level_size_identity :
    (∑ draws : Fin 101 → Assignment 8, mcDrawWeight (fun _ => 1/2) draws *
      (if (mcExceedances (ht (fun _ => 1/2) eightNodeNullTable) draws : ℝ)/100 ≤ 1/20
        then 1 else 0)) = eightNodeMCSize := by
  let e : (Fin 101 → Fin 128 × Bool) ≃ (Fin 101 → Assignment 8) :=
    Equiv.piCongrRight fun _ => mc_level_assignment
  rw [← e.sum_comp (fun draws => mcDrawWeight (fun _ => 1/2) draws *
    (if (mcExceedances (ht (fun _ => 1/2) eightNodeNullTable) draws : ℝ)/100 ≤ 1/20 then 1 else 0))]
  change (∑ d : Fin 101 → Fin 128 × Bool, mcDrawWeight (fun _ => 1/2)
    (fun i => mc_level_assignment (d i)) *
      (if (mcExceedances (ht (fun _ => 1/2) eightNodeNullTable)
        (fun i => mc_level_assignment (d i)) : ℝ)/100 ≤ 1/20 then 1 else 0)) = _
  rw [← (Fin.consEquiv (fun _ : Fin 101 => Fin 128 × Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin 128 × Bool, ∑ d : Fin 100 → Fin 128 × Bool,
    mcDrawWeight (fun _ => 1/2)
      (fun i : Fin 101 => mc_level_assignment ((Fin.cons a d : Fin 101 → Fin 128 × Bool) i)) *
      (if (mcExceedances (ht (fun _ => 1/2) eightNodeNullTable)
        (fun i : Fin 101 => mc_level_assignment ((Fin.cons a d : Fin 101 → Fin 128 × Bool) i)) : ℝ)/100 ≤ 1/20 then 1 else 0)) = _
  have hp101 : (∏ _i : Fin 101, (1:ℝ)/256) =
      (1:ℝ)/256 * (∏ _i : Fin 100, (1:ℝ)/256) := Fin.prod_univ_succ _
  simp only [mcDrawWeight, mc_level_half_weight, hp101,
    mc_level_exceedances_cons, mc_level_reject_iff]
  have hc (a : Fin 128 × Bool) :
      (∑ d : Fin 100 → Fin 128 × Bool,
        ((1:ℝ)/256 * ∏ _i : Fin 100, (1:ℝ)/256) *
          (if (mc_level_successes (fun b : Fin 128 × Bool => b.1 ≤ a.1) d).card ≤ 5 then 1 else 0)) =
      (1:ℝ)/256 *
        (((∑ b ∈ Finset.range 6, (100:ℕ).choose b * (a.1.val+1)^b *
          (128-(a.1.val+1))^(100-b) : ℕ) : ℝ)/128^100) := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, mc_level_conditional]
    simp only [mul_assoc]
  simp_rw [hc]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  calc
    _ = ∑ r : Fin 128,
        ((∑ b ∈ Finset.range 6,
          (100:ℕ).choose b * (r.val+1)^b * (128-(r.val+1))^(100-b) : ℕ) : ℝ)/128^101 := by
      apply Finset.sum_congr rfl
      intro r _
      norm_num [pow_succ]
      ring
    _ = eightNodeMCSize := by
      rw [← Finset.sum_div]
      congr 1
      simp only [eightNodeMCSize, eightNodeMCNumerator, Nat.cast_sum]
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [dif_pos (Finset.mem_range.mp hi)]

/-- The finite product design law is exactly the binomial-rank size. -/
theorem mc_level_spatial_counterexample_proof :
    SharpNull eightNodeNullPopulation ∧ WellDefined eightNodeNullPopulation 0 ∧
    (∑ draws : Fin 101 → Assignment 8, mcDrawWeight (fun _ => 1/2) draws *
      (if (mcExceedances (ht (fun _ => 1/2) (circleAverage eightNodeNullPopulation 0)) draws : ℝ)/100 ≤ 1/20
        then 1 else 0)) = eightNodeMCSize ∧ eightNodeMCSize > 1/20 := by
  refine ⟨?_, mc_level_wellDefined, ?_, mc_size_counterexample⟩
  · intro x z
    rfl
  · rw [mc_level_average]
    exact mc_level_size_identity

/- Rectangle integration and range calculations for a family of witnesses. -/
private theorem no_polygon_rectangle_closed (a b c d : ℝ) :
    IsClosed (rectangle a b c d) := by
  change IsClosed ({x : EuclideanSpace ℝ (Fin 2) | a ≤ x 0} ∩
    ({x | x 0 ≤ b} ∩ ({x | c ≤ x 1} ∩ {x | x 1 ≤ d})))
  exact (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).inter
    ((isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0) continuous_const).inter
      ((isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)).inter
        (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) continuous_const)))

private theorem no_polygon_rectangle_volume (a b c d : ℝ) :
    volume (rectangle a b c d) = ENNReal.ofReal (b-a) * ENNReal.ofReal (d-c) := by
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) ⁻¹'
      rectangle a b c d = Set.Icc (![a,c] : Fin 2 → ℝ) ![b,d] := by
    ext x
    change (a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d) ↔
      ((∀ i : Fin 2, ![a,c] i ≤ x i) ∧ ∀ i : Fin 2, x i ≤ ![b,d] i)
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    tauto
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    (no_polygon_rectangle_closed a b c d).measurableSet.nullMeasurableSet,
    hpre, Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ]

private theorem no_polygon_rectangle_convex (a b c d : ℝ) :
    Convex ℝ (rectangle a b c d) := by
  have h (i : Fin 2) : IsLinearMap ℝ (fun x : EuclideanSpace ℝ (Fin 2) => x i) := by
    constructor <;> intros <;> rfl
  change Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | a ≤ x 0} ∩
    ({x | x 0 ≤ b} ∩ ({x | c ≤ x 1} ∩ {x | x 1 ≤ d})))
  exact (convex_halfSpace_ge (h 0) a).inter
    ((convex_halfSpace_le (h 0) b).inter
      ((convex_halfSpace_ge (h 1) c).inter (convex_halfSpace_le (h 1) d)))

private theorem no_polygon_rectangle_polygonal (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    Polygonal (rectangle a b c d) := by
  let v : Fin 2 → Fin 3 → EuclideanSpace ℝ (Fin 2) :=
    ![![planePoint a c, planePoint b c, planePoint b d],
      ![planePoint a c, planePoint a d, planePoint b d]]
  refine ⟨2, v, ?_⟩
  ext x
  constructor
  · intro hx
    let u : ℝ := (x 0-a)/(b-a)
    let t : ℝ := (x 1-c)/(d-c)
    have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.2.2.1) (sub_pos.mpr hcd).le
    have hu1 : u ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2.1])
    have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hcd)).mpr (by linarith [hx.2.2.2])
    have hx0 : u*(b-a) = x 0-a := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab))
    have hx1 : t*(d-c) = x 1-c := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hcd))
    by_cases htu : t ≤ u
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      apply mem_convexHull_of_exists_fintype (![1-u,u-t,t] : Fin 3 → ℝ) (v 0)
      · intro i
        fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]
      · intro i
        exact Set.mem_range_self i
      · ext i
        fin_cases i <;> simp [v, Fin.sum_univ_succ, planePoint,
          PiLp.add_apply, PiLp.smul_apply] <;> nlinarith
    · apply Set.mem_iUnion.mpr
      refine ⟨1, ?_⟩
      apply mem_convexHull_of_exists_fintype (![1-t,t-u,u] : Fin 3 → ℝ) (v 1)
      · intro i
        fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]
      · intro i
        exact Set.mem_range_self i
      · ext i
        fin_cases i <;> simp [v, Fin.sum_univ_succ, planePoint,
          PiLp.add_apply, PiLp.smul_apply] <;> nlinarith
  · intro hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    apply convexHull_min ?_ (no_polygon_rectangle_convex a b c d) hi
    rintro y ⟨j,rfl⟩
    fin_cases i <;> fin_cases j <;> simp [v, rectangle, planePoint, hab.le, hcd.le]

section PolygonFamily
variable {L : ℝ} {hL : 2 ≤ L}

private theorem no_polygon_node_closed (i : Fin 3) :
    IsClosed ((polygonRangeFamily L hL).node i) := by
  fin_cases i <;> exact no_polygon_rectangle_closed _ _ _ _

private theorem no_polygon_region (i : Fin 3) :
    region (polygonRangeFamily L hL) i 0 = (polygonRangeFamily L hL).node i := by
  ext x
  change Metric.infDist x ((polygonRangeFamily L hL).node i) ∈ Set.Icc 0 0 ↔ _
  rw [Set.Icc_self, Set.mem_singleton_iff]
  exact ((no_polygon_node_closed i).mem_iff_infDist_zero
    ((polygonRangeFamily L hL).node_nonempty i)).symm

private theorem no_polygon_node_mass (i : Fin 3) :
    volume ((polygonRangeFamily L hL).node i) =
      if i = 2 then ENNReal.ofReal (L+1) else 1 := by
  fin_cases i <;> norm_num [polygonRangeFamily, no_polygon_rectangle_volume]

private theorem no_polygon_mass_pos (i : Fin 3) :
    0 < volume ((polygonRangeFamily L hL).node i) := by
  rw [no_polygon_node_mass]
  split_ifs
  · exact ENNReal.ofReal_pos.mpr (by linarith)
  · norm_num

private theorem no_polygon_mass_finite (i : Fin 3) :
    volume ((polygonRangeFamily L hL).node i) < ⊤ := by
  rw [no_polygon_node_mass]
  split_ifs <;> simp

private theorem no_polygon_outcome_on_node (i : Fin 3) (z : Assignment 3)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ (polygonRangeFamily L hL).node i) :
    (polygonRangeFamily L hL).outcome x z = if i = 2 then 0 else bit (z 2) := by
  fin_cases i
  · change x ∈ rectangle 0 1 0 1 at hx
    simp [polygonRangeFamily, hx]
  · change x ∈ rectangle L (L+1) 0 1 at hx
    simp [polygonRangeFamily, hx]
  · change x ∈ rectangle 0 (L+1) 2 3 at hx
    have hnot : x ∉ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1 := by
      intro h
      rcases h with h | h <;> have hy := h.2.2.2 <;> have hyl := hx.2.2.1 <;> linarith
    change (if x ∈ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1 then bit (z 2) else 0) = 0
    rw [if_neg hnot]

private theorem no_polygon_wellDefined : WellDefined (polygonRangeFamily L hL) 0 := by
  intro i
  rw [no_polygon_region]
  have hmeas : MeasurableSet ((polygonRangeFamily L hL).node i) :=
    (no_polygon_node_closed i).measurableSet
  refine ⟨hmeas, no_polygon_mass_pos i, no_polygon_mass_finite i, ?_⟩
  intro z
  have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) =>
      if i = 2 then (0 : ℝ) else bit (z 2)) ((polygonRangeFamily L hL).node i) :=
    integrableOn_const (no_polygon_mass_finite i).ne
  exact hc.congr_fun (fun x hx => (no_polygon_outcome_on_node i z x hx).symm) hmeas

private theorem no_polygon_average (i : Fin 3) (z : Assignment 3) :
    circleAverage (polygonRangeFamily L hL) 0 i z = if i = 2 then 0 else bit (z 2) := by
  have hout : Set.EqOn (fun x => (polygonRangeFamily L hL).outcome x z)
      (fun _ => if i = 2 then 0 else bit (z 2)) ((polygonRangeFamily L hL).node i) :=
    fun x hx => no_polygon_outcome_on_node i z x hx
  rw [circleAverage, no_polygon_region,
    setIntegral_congr_fun (no_polygon_node_closed i).measurableSet hout]
  change (∫ _ in (polygonRangeFamily L hL).node i, if i = 2 then (0 : ℝ) else bit (z 2)) /
    (volume ((polygonRangeFamily L hL).node i)).toReal = _
  simp only [setIntegral_const, measureReal_def, smul_eq_mul]
  exact mul_div_cancel_left₀ _ (ENNReal.toReal_ne_zero.mpr
    ⟨(ne_of_gt (no_polygon_mass_pos i)), (no_polygon_mass_finite i).ne⟩)

private theorem no_polygon_vertical_distance (x : EuclideanSpace ℝ (Fin 2)) :
    dist x (planePoint (x 0) 2) = |x 1 - 2| := by
  simp [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq,
    Real.sqrt_sq_eq_abs]

private theorem no_polygon_source_range : FiniteSourceRange (polygonRangeFamily L hL) 2 := by
  intro l x z z' hsame hfar
  by_cases hx : x ∈ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1
  · by_cases hl : l = 2
    · subst l
      have hxy : (0 ≤ x 0 ∧ x 0 ≤ L+1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) := by
        rcases hx with hx | hx
        · rcases hx with ⟨hx0, hx1, hy0, hy1⟩
          exact ⟨⟨hx0, by linarith⟩, hy0, hy1⟩
        · rcases hx with ⟨hx0, hx1, hy0, hy1⟩
          exact ⟨⟨by linarith, hx1⟩, hy0, hy1⟩
      have hproj : planePoint (x 0) 2 ∈ (polygonRangeFamily L hL).node 2 := by
        change planePoint (x 0) 2 ∈ rectangle 0 (L+1) 2 3
        simpa [rectangle, planePoint] using ⟨hxy.1.1, hxy.1.2, (by norm_num : (2 : ℝ) ≤ 3)⟩
      have hd : nodeDistance (polygonRangeFamily L hL) 2 x ≤ 2 := by
        unfold nodeDistance
        calc
          Metric.infDist x ((polygonRangeFamily L hL).node 2) ≤ dist x (planePoint (x 0) 2) :=
            Metric.infDist_le_dist_of_mem hproj
          _ = |x 1 - 2| := no_polygon_vertical_distance x
          _ ≤ 2 := by
            rw [abs_of_nonpos (by linarith [hxy.2.2])]
            linarith [hxy.2.1]
      exact False.elim (not_lt_of_ge hd hfar)
    · have hz : z 2 = z' 2 := hsame 2 (Ne.symm hl)
      simp only [polygonRangeFamily, if_pos hx, hz]
  · simp only [polygonRangeFamily, if_neg hx]

private theorem no_polygon_outcome_bound :
    ∀ x z, |(polygonRangeFamily L hL).outcome x z| < 2 := by
  intro x z
  change |if x ∈ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1 then bit (z 2) else 0| < 2
  split_ifs <;> cases z 2 <;> norm_num [bit]

private theorem no_polygon_shared_source :
    sharesSource (circleAverage (polygonRangeFamily L hL) 0) 0 1 := by
  let z : Assignment 3 := fun _ => false
  let z' : Assignment 3 := Function.update z 2 true
  have hsame : ∀ k : Fin 3, k ≠ 2 → z k = z' k := by
    intro k hk
    simp [z', Function.update_of_ne hk]
  have hzero : circleAverage (polygonRangeFamily L hL) 0 0 z ≠
      circleAverage (polygonRangeFamily L hL) 0 0 z' := by
    norm_num [no_polygon_average, z, z', bit]
  have hone : circleAverage (polygonRangeFamily L hL) 0 1 z ≠
      circleAverage (polygonRangeFamily L hL) 0 1 z' := by
    norm_num [no_polygon_average, z, z', bit]
  exact ⟨2, Or.inr ⟨z, z', hsame, hzero⟩, Or.inr ⟨z, z', hsame, hone⟩⟩

private theorem no_polygon_separation : nodeSeparation (polygonRangeFamily L hL) 0 1 = L-1 := by
  let S : Set ℝ := {r | ∃ x ∈ (polygonRangeFamily L hL).node 0,
    ∃ y ∈ (polygonRangeFamily L hL).node 1, dist x y = r}
  have hmem : L-1 ∈ S := by
    refine ⟨planePoint 1 0, ?_, planePoint L 0, ?_, ?_⟩
    · norm_num [polygonRangeFamily, rectangle, planePoint]
    · norm_num [polygonRangeFamily, rectangle, planePoint]
    · simp [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq,
        Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith : 1-L ≤ 0)]
  have hlow : ∀ r ∈ S, L-1 ≤ r := by
    rintro r ⟨x, hx, y, hy, rfl⟩
    change x ∈ rectangle 0 1 0 1 at hx
    change y ∈ rectangle L (L+1) 0 1 at hy
    have hcoord : |x 0-y 0| ≤ dist x y := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le x y 0
    have hneg : -(x 0-y 0) ≤ |x 0-y 0| := neg_le_abs _
    linarith [hx.2.1, hy.1]
  change sInf S = L-1
  exact le_antisymm (csInf_le ⟨L-1, hlow⟩ hmem) (le_csInf ⟨L-1, hmem⟩ hlow)

private theorem no_polygon_covariance :
    cov (fun _ => 1/2) (circleAverage (polygonRangeFamily L hL) 0 0)
      (circleAverage (polygonRangeFamily L hL) 0 1) = 1/4 := by
  have hav0 : circleAverage (polygonRangeFamily L hL) 0 0 = fun z => bit (z 2) := by
    funext z
    simp [no_polygon_average]
  have hav1 : circleAverage (polygonRangeFamily L hL) 0 1 = fun z => bit (z 2) := by
    funext z
    simp [no_polygon_average]
  have hm (k : ℕ) (hk : 0 < k) :
      expect (fun _ : Fin 3 => 1/2) (fun z => (bit (z 2))^k) = 1/2 := by
    have hp : ∀ j : Fin 3, (0 : ℝ) < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 :=
      fun _ => by norm_num
    have h := bernoulli_positive_power (fun _ : Fin 3 => 1/2)
      (fun _ : Assignment 3 => (1 : ℝ)) (2 : Fin 3) k hk hp
    simpa only [mul_one, expect_const] using h
  rw [hav0, hav1, cov]
  simp only [← pow_two]
  have hm1 : expect (fun _ : Fin 3 => 1/2) (fun z => bit (z 2)) = 1/2 := by
    simpa only [pow_one] using hm 1 (by norm_num)
  rw [hm 2 (by norm_num), hm1]
  norm_num

private theorem no_polygon_nodes_polygonal (i : Fin 3) :
    Polygonal ((polygonRangeFamily L hL).node i) := by
  fin_cases i <;> apply no_polygon_rectangle_polygonal <;> norm_num <;> linarith

private theorem no_polygon_disjoint :
    Pairwise (fun i j => Disjoint ((polygonRangeFamily L hL).node i)
      ((polygonRangeFamily L hL).node j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  fin_cases i <;> fin_cases j <;> simp_all [polygonRangeFamily, rectangle] <;> linarith

end PolygonFamily

/-- Every finite proposed cutoff fails in a positive-area polygon family. -/
theorem no_polygon_cutoff_from_range_alone_proof :
    ∀ h : ℝ, 0 ≤ h → ∃ L : ℝ, ∃ hL : 2 ≤ L,
      h+1 < L ∧ WellDefined (polygonRangeFamily L hL) 0 ∧
      FiniteSourceRange (polygonRangeFamily L hL) 2 ∧
      (∀ x z, |(polygonRangeFamily L hL).outcome x z| < 2) ∧
      (∀ i : Fin 3, Polygonal ((polygonRangeFamily L hL).node i)) ∧
      Pairwise (fun i j => Disjoint ((polygonRangeFamily L hL).node i) ((polygonRangeFamily L hL).node j)) ∧
      nodeSeparation (polygonRangeFamily L hL) 0 1 = L-1 ∧
      h < nodeSeparation (polygonRangeFamily L hL) 0 1 ∧
      sharesSource (circleAverage (polygonRangeFamily L hL) 0) 0 1 ∧
      cov (fun _ => 1/2) (circleAverage (polygonRangeFamily L hL) 0 0)
        (circleAverage (polygonRangeFamily L hL) 0 1) = 1/4 := by
  intro h hh
  have hL : 2 ≤ h+2 := by linarith
  refine ⟨h+2, hL, by linarith, no_polygon_wellDefined, no_polygon_source_range,
    no_polygon_outcome_bound, no_polygon_nodes_polygonal, no_polygon_disjoint,
    no_polygon_separation, ?_, no_polygon_shared_source, no_polygon_covariance⟩
  rw [no_polygon_separation]
  linarith

end
end AronowAudit.P004.Wave1
