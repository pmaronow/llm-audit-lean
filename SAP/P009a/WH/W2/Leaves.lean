import SAP.P009a.WH.W2.LeavesBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace SAP.P009a.WH.W2

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

/-- A dependence-weighted covariance sum is bounded by its uniform pairwise bound. -/
theorem dependent_sum_bound {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n)
    (b : Bool) (a : ℕ) (B : ℝ)
    (hc : ∀ i j, |covariance E.design (armResponse E b a i) (armResponse E b a j)| ≤ B) :
    dependentArmCovarianceSum E b a ≤ B*(n:ℝ)*averageDependence E := by
  calc
    _ ≤ ∑ i, ∑ j, dependenceIndicator E i j*B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left (hc i j)
      unfold dependenceIndicator
      split_ifs <;> norm_num
    _ = _ := by
      unfold averageDependence dependenceDegree
      simp_rw [← Finset.sum_mul]
      field_simp

/-- Summing dependent-pair and mixing bounds retains the intermediate absolute sum. -/
theorem mixed_sum_bound {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (b : Bool) (k θ : ℝ)
    (hc : ∀ i j, |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ≤ k^2)
    (hm : ∀ i j, |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ≤
      10*k^2*mixingPower (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ) :
    absoluteArmCovarianceSum E b 1 ≤
      k^2*(n:ℝ)*averageDependence E + 10*k^2*externalMixingSum E θ := by
  calc
    _ ≤ ∑ i, ∑ j, (dependenceIndicator E i j*k^2 +
        (1-dependenceIndicator E i j)*(10*k^2*mixingPower
          (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : SharesCause E i j
      · simpa [dependenceIndicator, hij] using hc i j
      · simpa [dependenceIndicator, hij] using hm i j
    _ = _ := by
      have he (i j : Fin n) : dependenceIndicator E i j*k^2 +
          (1-dependenceIndicator E i j)*(10*k^2*mixingPower
            (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ) =
          k^2*dependenceIndicator E i j + 10*k^2*((1-dependenceIndicator E i j)*mixingPower
            (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ) := by ring
      simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold averageDependence dependenceDegree externalMixingSum
      field_simp

/-- All-pairs assignment mixing is controlled by dependence and external mixing. -/
theorem count_chains {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (k θ : ℝ)
    (hr : Regularity E k 2 1) (hθ : θ ≤ 1) (b : Bool) : WholeCountChains E k θ b := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hi (i j : Fin n) : |covariance E.design (fun z => if z i = b then 1 else 0)
      (fun z => if z j = b then 1 else 0)| ≤
        mixingCoefficient E.design (fun z => z i) (fun z => z j) := by
    rw [Bridge.covariance_correspondence, Bridge.mixing_correspondence]
    convert AronowAudit.P009.Wave1.t4_indicator_alpha (Bridge.toProjectDistribution E.design)
      (fun z => z i) (fun z => z j) {c | c = b} {c | c = b} using 1
    congr 2 <;> funext z <;> split_ifs <;> simp_all
  have hmask (l : Fin n) : (fun z => relevantTreatments E l z l) = (fun z => z l) := by
    funext z
    simp [relevantTreatments, Affects]
  have hcomp (i j : Fin n) : mixingCoefficient E.design (fun z => z i) (fun z => z j) ≤
      mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j) := by
    have hh := AronowAudit.P009.Wave1.t4_alpha_comp (Bridge.toProjectDistribution E.design)
      (relevantTreatments E i) (relevantTreatments E j)
      (fun z => z i) (fun z => z j)
    rw [Bridge.mixing_correspondence, Bridge.mixing_correspondence]
    simpa only [hmask] using hh
  have hp (i j : Fin n) : mixingCoefficient E.design (fun z => z i) (fun z => z j) ≤
      mixingPower (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ := by
    apply (hcomp i j).trans
    change AronowAudit.P009.alpha (Bridge.toProjectDistribution E.design)
      (relevantTreatments E i) (relevantTreatments E j) ≤ AronowAudit.P009.mixPower
      (AronowAudit.P009.alpha (Bridge.toProjectDistribution E.design)
        (relevantTreatments E i) (relevantTreatments E j)) θ
    exact AronowAudit.P009.Wave1.t4_alpha_le_power _ _
      (AronowAudit.P009.MixingBasics.alpha_nonnegative _ _ _)
      (AronowAudit.P009.MixingBasics.alpha_le_one _ _ _) hθ
  have hsum : assignmentMixingSum E ≤ (n:ℝ)*averageDependence E + offAssignmentMixingSum E := by
    calc
      _ ≤ ∑ i, ∑ j, (dependenceIndicator E i j + (1-dependenceIndicator E i j)*
          mixingCoefficient E.design (fun z => z i) (fun z => z j)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : SharesCause E i j
        · have hal : mixingCoefficient E.design (fun z => z i) (fun z => z j) ≤ 1 := by
            rw [Bridge.mixing_correspondence]
            exact AronowAudit.P009.MixingBasics.alpha_le_one _ _ _
          simpa [dependenceIndicator, hij] using hal
        · simp [dependenceIndicator, hij]
      _ = _ := by
        unfold averageDependence dependenceDegree offAssignmentMixingSum
        simp_rw [Finset.sum_add_distrib]
        field_simp
  have hoff : offAssignmentMixingSum E ≤ externalMixingSum E θ := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left (hp i j)
    unfold dependenceIndicator
    split_ifs <;> norm_num
  refine ⟨hi, AronowAudit.P009.Wave1.t4_count_weighted (Bridge.toProjectExperiment E) k 2 1 hr b, ?_, ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hi i j
  · calc
      _ ≤ k^2/(n:ℝ)^2*((n:ℝ)*averageDependence E + offAssignmentMixingSum E) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by field_simp <;> ring
  · calc
      _ ≤ k^2/(n:ℝ)*averageDependence E + k^2/(n:ℝ)^2*externalMixingSum E θ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hoff
          (show (0:ℝ) ≤ k^2/(n:ℝ)^2 from div_nonneg (sq_nonneg _) (sq_nonneg _)))
      _ = _ := by unfold externalMixing externalMixingSum; field_simp <;> ring

/-- The two-arm variance inequality, before any fourth-moment bound is applied. -/
theorem variance_two_arms {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) :
    variance E.design (fun z => (n:ℝ)*bernoulliVarianceEstimate E z) ≤
      2/(n:ℝ)^2 * (∑ b : Bool, variance E.design (squareArmTotal E b)) := by
  let T := fun b : Bool => fun z : TreatmentVector n => squareArmTotal E b z/(n:ℝ)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (fun z => (n:ℝ)*bernoulliVarianceEstimate E z) = fun z => T true z-(-T false z) := by
    funext z
    let R := fun i =>
      (if z i then E.outcome i z^2 else 0)/armProbability E i true^2 +
      (if z i then 0 else E.outcome i z^2)/armProbability E i false^2
    calc
      _ = (∑ i, R i)/(n:ℝ) := by
        change (n:ℝ)*((∑ i, R i)/(n:ℝ)^2) = _
        field_simp
      _ = T true z+T false z := by
        dsimp [T, squareArmTotal]
        rw [← add_div, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        dsimp [R]
        cases hzi : z i <;> simp [armResponse, hzi]
      _ = _ := by ring
  have hneg : variance E.design (fun z => -T false z) = variance E.design (T false) := by
    change AronowAudit.P009.var (Bridge.toProjectDistribution E.design) (fun z => -T false z) =
      AronowAudit.P009.var (Bridge.toProjectDistribution E.design) (T false)
    simp only [AronowAudit.P009.variance_second_moment]
    have hm : AronowAudit.P009.mean (Bridge.toProjectDistribution E.design) (fun z => -T false z) =
        -AronowAudit.P009.mean (Bridge.toProjectDistribution E.design) (T false) := by
      simpa using AronowAudit.P009.mean_const_mul (Bridge.toProjectDistribution E.design) (-1) (T false)
    simp only [neg_sq, hm]
  rw [he]
  have hv := AronowAudit.P009.BernoulliCompletion.variance_sub_le
    (Bridge.toProjectDistribution E.design) (T true) (fun z => -T false z)
  change variance E.design (fun z => T true z-(-T false z)) ≤
    2*(variance E.design (T true)+variance E.design (fun z => -T false z)) at hv
  rw [hneg] at hv
  apply hv.trans_eq
  change 2*(AronowAudit.P009.var (Bridge.toProjectDistribution E.design)
      (fun z => squareArmTotal E true z/(n:ℝ)) +
    AronowAudit.P009.var (Bridge.toProjectDistribution E.design)
      (fun z => squareArmTotal E false z/(n:ℝ))) = _
  rw [AronowAudit.P009.BernoulliCompletion.variance_div,
    AronowAudit.P009.BernoulliCompletion.variance_div]
  change 2*(variance E.design (squareArmTotal E true)/(n:ℝ)^2 +
    variance E.design (squareArmTotal E false)/(n:ℝ)^2) = _
  simp only [Fintype.sum_bool]
  ring

/-- The whole target uses only the two new mathematical leaves above. -/
theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) : T4WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · exact weighted_variance_general
  · exact moment_covariance h1
  · intro n hn E k q s hr
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have r2 := regularity_lower h1 E k q s hr 2 (by norm_num) hr.2.1
    have hC (a : ℕ) (ha : a = 1 ∨ a = 2) (hqa : ((2*a:ℕ):ExtendedOrder) ≤ q) (b : Bool) :
        ∀ i j, |covariance E.design (armResponse E b a i) (armResponse E b a j)| ≤ k^(2*a) :=
      fun i j => moment_covariance h1 E k q hr.1 a ha hqa (hr.2.2.2.2.1) i j b
    have hc1 (b : Bool) (i j : Fin n) :
        |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ≤ k^2 := by
      simpa using hC 1 (Or.inl rfl) hr.2.1 b i j
    have cancel (hb : ProductDesign E) (b : Bool) (a : ℕ) :
        (∀ i j, (1-dependenceIndicator E i j)*
          covariance E.design (armResponse E b a i) (armResponse E b a j) = 0) ∧
        absoluteArmCovarianceSum E b a = dependentArmCovarianceSum E b a := by
      refine ⟨?_, AronowAudit.P009.Wave1.t4_covariance_cancellation (Bridge.toProjectExperiment E) hb b a⟩
      intro i j
      by_cases hij : SharesCause E i j
      · simp [dependenceIndicator, hij]
      · have hz := AronowAudit.P009.BernoulliCompletion.covariance_nonedge
          (Bridge.toProjectExperiment E) hb i j hij b a
        change covariance E.design (armResponse E b a i) (armResponse E b a j) = 0 at hz
        rw [hz, mul_zero]
    constructor
    · intro b
      refine ⟨?_, count_chains hn E k (wholeExternalExponent q) r2 (whole_exponent_le_one q hr.2.1) b⟩
      have hm := arm_mixing_extended h1 h2 E k q s hr b
      refine ⟨AronowAudit.P009.Wave1.t4_arm_weighted (Bridge.toProjectExperiment E) k 2 1 r2 b,
        ?_, (fun i j _ => hm i j), (fun i j _ => hc1 b i j), ?_, ?_⟩
      · intro hb
        refine ⟨(cancel hb b 1).1, (cancel hb b 1).2, ?_⟩
        calc
          _ ≤ k^2/(n:ℝ)^2*(k^2*(n:ℝ)*averageDependence E) :=
            mul_le_mul_of_nonneg_left (dependent_sum_bound hn E b 1 (k^2) (hc1 b)) (by positivity)
          _ = _ := by field_simp
      · calc
          _ ≤ k^2/(n:ℝ)^2*(k^2*(n:ℝ)*averageDependence E +
              10*k^2*externalMixingSum E (wholeExternalExponent q)) :=
            mul_le_mul_of_nonneg_left (mixed_sum_bound hn E b k _ (hc1 b) hm) (by positivity)
          _ = _ := by field_simp
      · unfold externalMixing externalMixingSum
        field_simp
    · intro hq4 hb
      have r4 := regularity_lower h1 E k q s hr 4 (by norm_num) hq4
      have hc2 (b : Bool) (i j : Fin n) :
          |covariance E.design (armResponse E b 2 i) (armResponse E b 2 j)| ≤ k^4 := by
        simpa using hC 2 (Or.inr rfl) hq4 b i j
      have hfin (b : Bool) : variance E.design (squareArmTotal E b) ≤ k^8*(n:ℝ)*averageDependence E :=
        AronowAudit.P009.Wave1.t4_square_variance hn (Bridge.toProjectExperiment E) k 4 1 r4 (by norm_num) hb b
      refine ⟨?_, variance_two_arms hn E, ?_⟩
      · intro b
        refine ⟨AronowAudit.P009.Wave1.t4_square_weighted (Bridge.toProjectExperiment E) k 4 1 r4 b,
          (cancel hb b 2).1, (cancel hb b 2).2, ?_⟩
        calc
          _ ≤ k^4*(k^4*(n:ℝ)*averageDependence E) :=
            mul_le_mul_of_nonneg_left (dependent_sum_bound hn E b 2 (k^4) (hc2 b)) (by positivity)
          _ = _ := by ring
      · calc
          _ ≤ 2/(n:ℝ)^2*(∑ _b : Bool, k^8*(n:ℝ)*averageDependence E) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hfin b) (by positivity)
          _ = _ := by simp only [Fintype.sum_bool]; field_simp <;> ring

end
end SAP.P009a.WH.W2
