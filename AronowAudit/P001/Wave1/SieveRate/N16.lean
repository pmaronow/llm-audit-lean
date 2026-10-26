import AronowAudit.P001.Wave1.SieveRateBlueprint

/-!
# A positive lower bound for the supported injective design event

The probability of the box is `(1 - 1/n)^n`. Pairwise diagonals are null, so
intersecting with injectivity does not change it. The elementary exponential bound
on the reciprocal gives the deliberately loose lower bound `1/6`.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

private theorem design_box_power_lower (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / 6 ≤ (1 - 1 / (n : ℝ)) ^ n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hdenpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hdenzero : (n : ℝ) - 1 ≠ 0 := ne_of_gt hdenpos
  have hq : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : (1 : ℝ) / (n : ℝ) ≤ 1 :=
      (div_le_iff₀ hnpos).2 (by linarith)
    linarith
  let a : ℝ := 1 + 1 / ((n : ℝ) - 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a ≤ 2 := by
    have hdiv : (1 : ℝ) / ((n : ℝ) - 1) ≤ 1 :=
      (div_le_iff₀ hdenpos).2 (by linarith)
    dsimp [a]
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hexp : a ^ (n - 1) ≤ Real.exp 1 := by
    have hbase : a ≤ Real.exp (1 / ((n : ℝ) - 1)) := by
      dsimp [a]
      linarith [Real.add_one_le_exp (1 / ((n : ℝ) - 1))]
    calc
      a ^ (n - 1) ≤ Real.exp (1 / ((n : ℝ) - 1)) ^ (n - 1) :=
        pow_le_pow_left₀ ha hbase (n - 1)
      _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul, hcast]
        congr 1
        field_simp [hdenzero]
  have hpow : a ^ n ≤ 2 * Real.exp 1 := by
    calc
      a ^ n = a ^ ((n - 1) + 1) := by congr 1; omega
      _ = a ^ (n - 1) * a := pow_succ _ _
      _ ≤ Real.exp 1 * 2 := mul_le_mul hexp ha2 ha (Real.exp_nonneg 1)
      _ = 2 * Real.exp 1 := mul_comm _ _
  have hpow6 : a ^ n ≤ 6 := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith only [hpow, he3]
  have hcancel_base : (1 - 1 / (n : ℝ)) * a = 1 := by
    dsimp [a]
    field_simp [hnzero, hdenzero] <;> ring
  have hcancel : (1 - 1 / (n : ℝ)) ^ n * a ^ n = 1 := by
    rw [← mul_pow, hcancel_base, one_pow]
  have hmul := mul_le_mul_of_nonneg_left hpow6 (pow_nonneg hq n)
  nlinarith only [hmul, hcancel]

theorem n16_proof : N16 := by
  classical
  intro n hn
  letI : IsProbabilityMeasure (unifVec n) := by unfold unifVec; infer_instance
  letI : NullSingletonClass (uniformLaw (0 : ℝ) 1) := by
    unfold uniformLaw
    infer_instance
  have hunif : uniformLaw (0 : ℝ) 1 = volume.restrict (Set.Icc (0 : ℝ) 1) := by
    have hdensity :
        (fun x : ℝ => ENNReal.ofReal
          (if x ∈ Set.Icc (0 : ℝ) 1 then (1 - 0)⁻¹ else 0)) =
        (Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
    rw [uniformLaw, hdensity, withDensity_indicator_one measurableSet_Icc]
  have hdelta_meas : MeasurableSet {z : ℝ × ℝ | z.1 = z.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hdelta : (uniformLaw 0 1).prod (uniformLaw 0 1)
      {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    rw [Measure.prod_apply hdelta_meas]
    have hsection (a : ℝ) :
        Prod.mk a ⁻¹' {z : ℝ × ℝ | z.1 = z.2} = {a} := by
      ext b
      simp [eq_comm]
    simp_rw [hsection]
    simp only [measure_singleton, lintegral_zero]
  have hind : iIndepFun (fun i : Fin n => fun x : Fin n → ℝ => x i) (unifVec n) := by
    exact iIndepFun_pi (μ := fun _ : Fin n => uniformLaw 0 1)
      (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hmarg (i : Fin n) :
      (unifVec n).map (fun x : Fin n → ℝ => x i) = uniformLaw 0 1 :=
    (measurePreserving_eval (fun _ : Fin n => uniformLaw 0 1) i).map_eq
  have hzero (i j : Fin n) (hij : i ≠ j) :
      (unifVec n) {x : Fin n → ℝ | x i = x j} = 0 := by
    have hpair : (unifVec n).map (fun x : Fin n → ℝ => (x i, x j)) =
        (uniformLaw 0 1).prod (uniformLaw 0 1) := by
      have heq := (indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable).1 (hind.indepFun hij)
      simpa only [hmarg] using heq
    change (unifVec n) ((fun x : Fin n → ℝ => (x i, x j)) ⁻¹'
      {z : ℝ × ℝ | z.1 = z.2}) = 0
    rw [← Measure.map_apply
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hdelta_meas,
      hpair, hdelta]
  have hpair_ae (i j : Fin n) :
      ∀ᵐ x : Fin n → ℝ ∂(unifVec n), x i = x j → i = j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · have hne : ∀ᵐ x : Fin n → ℝ ∂(unifVec n), x i ≠ x j := by
        apply ae_iff.2
        simpa only [not_not] using hzero i j hij
      filter_upwards [hne] with x hx
      intro hEq
      exact (hx hEq).elim
  have hinj : ∀ᵐ x : Fin n → ℝ ∂(unifVec n), Function.Injective x := by
    have hall : ∀ᵐ x : Fin n → ℝ ∂(unifVec n),
        ∀ i j : Fin n, x i = x j → i = j :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hpair_ae i j
    filter_upwards [hall] with x hx
    intro i j hij
    exact hx i j hij
  let box : Set (Fin n → ℝ) :=
    Set.pi Set.univ (fun _ : Fin n => Set.Icc (1 / (n : ℝ)) 1)
  have hdesign_box : designSet n =ᵐ[unifVec n] box := by
    filter_upwards [hinj] with x hx
    apply propext
    simp [designSet, box, Set.mem_pi, hx, Pi.le_def, forall_and]
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hq : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : (1 : ℝ) / (n : ℝ) ≤ 1 :=
      (div_le_iff₀ hnpos).2 (by linarith)
    linarith
  have hfactor : (uniformLaw 0 1) (Set.Icc (1 / (n : ℝ)) 1) =
      ENNReal.ofReal (1 - 1 / (n : ℝ)) := by
    have hsub : Set.Icc (1 / (n : ℝ)) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact ⟨(by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)).trans hx.1, hx.2⟩
    rw [hunif, Measure.restrict_apply measurableSet_Icc,
      Set.inter_eq_left.mpr hsub, Real.volume_Icc]
  have hbox : (unifVec n) box = ENNReal.ofReal (1 - 1 / (n : ℝ)) ^ n := by
    rw [unifVec, show box = Set.pi Set.univ (fun _ : Fin n => Set.Icc (1 / (n : ℝ)) 1) from rfl,
      Measure.pi_pi]
    simp only [hfactor, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [measure_congr hdesign_box, hbox, ENNReal.toReal_pow, ENNReal.toReal_ofReal hq]
  exact design_box_power_lower n hn

end

end AronowAudit.P001.Wave1.SieveRate
