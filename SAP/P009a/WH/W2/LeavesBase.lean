import SAP.P009a.WH.W2.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace SAP.P009a.WH.W2

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

/-- Lower finite moments from an admissible finite or infinite moment order.
For finite q repeat finite_moment_interpolation's concavity argument for real p,
then use monotonicity of rpow and
(rpow k q)^(p/q)=k^p. At infinity sum the support bound; zero-mass terms vanish.
This is a moment lemma only: there are no assignment or potential-outcome premises. -/
def T4_L1 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (P : FiniteDistribution Ω) (X : Ω → ℝ)
    (k p : ℝ) (q : ExtendedOrder), 0 < k → 0 < p → (p : ExtendedOrder) ≤ q →
    OrderBound P X k q → expectation P (fun ω => Real.rpow |X ω| p) ≤ Real.rpow k p

/-- Bounded covariance with bounds required only on positive-mass assignments.
Truncate f and g to [-M,M] and [-N,N]. Their compositions agree with the originals
on the support, so covariance is unchanged. Apply t4_bounded_covariance to the
truncated recodings. The statement includes zero M or N and arbitrary recoding ranges. -/
def T4_L2 : Prop :=
  ∀ {Ω A B : Type} [Fintype Ω] [Fintype A] [Fintype B]
    (P : FiniteDistribution Ω) (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (M N : ℝ), 0 ≤ M → 0 ≤ N →
    (∀ ω, 0 < P.mass ω → |f (X ω)| ≤ M) →
    (∀ ω, 0 < P.mass ω → |g (Y ω)| ≤ N) →
    |covariance P (fun ω => f (X ω)) (fun ω => g (Y ω))| ≤
      4*M*N*mixingCoefficient P X Y

/-- The printed limsup selection step fails in the complete explicit density witness. -/
theorem T5_assembly : T5WholeStatement := by
  have h0 : T5Statement := ⟨AronowAudit.P009.limsup_interference_counterexample,
    AronowAudit.P009.limsup_threshold_counterexample⟩
  have hlim := h0.1.2.2.1
  refine ⟨h0, ?_, by norm_num [clusterDensity, clusterSize],
    by norm_num [clusterDensity, clusterSize], by norm_num [clusterDensity, clusterSize],
    by norm_num [clusterDensity, clusterSize], ?_, ?_, hlim.limsup_eq, by norm_num, ?_, ?_⟩
  · intro n hn
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      change AronowAudit.P009.Interferes (AronowAudit.P009.limsupExperiment n hn) i j ↔ _
      rw [AronowAudit.P009.LimsupCompletion.limsup_interferes hn,
        AronowAudit.P009.OneSourceCompletion.source_interferes hn]
      change (i = j ∨ i.val = 0 ∧ 0 < j.val ∧ j.val < clusterSize n) ↔ _
      simp only [Fin.ext_iff]
      omega
    · intro i j
      change AronowAudit.P009.Dependent (AronowAudit.P009.limsupExperiment n hn) i j ↔ _
      unfold AronowAudit.P009.Dependent
      simp_rw [AronowAudit.P009.LimsupCompletion.limsup_interferes hn]
      exact AronowAudit.P009.OneSourceCompletion.source_dependent hn
        (clusterSize n) (by unfold clusterSize; omega) (fun _ => 0) i j
    · exact AronowAudit.P009.LimsupCompletion.limsup_density_exact n hn
  · intro m hm
    rw [h0.2.2.2.1 m hm]
    have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
    exact div_pos (by linarith) (by positivity)
  · intro m hm
    rw [h0.2.2.2.2 m hm]
    have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
    exact div_pos (by linarith) (by positivity)
  · intro hz
    have he := tendsto_nhds_unique hlim hz
    norm_num at he
  · apply (Set.finite_Iic (3:ℕ)).subset
    intro t ht
    have hn : (0:ℝ) < sampleSize clusterSequence t := by
      change (0:ℝ) < (t+1:ℕ)
      positivity
    have ha : (1/4:ℝ) ≤ averageDependence (clusterSequence.experiment t)/sampleSize clusterSequence t :=
      (le_div_iff₀ hn).2 (by simpa [mul_comm] using ht)
    have he := (h0.1.2.2.2 t).mp ha
    change t ≤ 3
    omega

/-- A regular restricted-interference sequence disproves guaranteed largest magnitude. -/
theorem T11_assembly : T11WholeStatement := by
  intro h
  obtain ⟨hr, hb, hs, hd, hv⟩ := star_sequence_facts
  have he := h wholeStarSequence 2 4 1 hr (by norm_num) hb hs hd
  obtain ⟨t, ht⟩ := he.exists
  have hz := (hv t).1
  have hp := (hv t).2.1
  have hh := ht.2
  rw [hz, abs_zero, abs_of_pos hp] at hh
  linarith

/-- Finite bias bounds, all ratio consequences, and a witness with B2 identically zero. -/
theorem T12_assembly : T12WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn E k q s hr hq hb
    have h := AronowAudit.P009.Wave1.corrected_bias_term_bounds_proof hn
      (Bridge.toProjectExperiment E) k q s hr hq hb
    have hd : 0 < averageDependence E := zero_lt_one.trans_le (graph_lower_bounds hn E).2
    refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
    apply (div_le_iff₀ hd).2
    nlinarith [show 0 ≤ k^4 by positivity]
  · intro S k q s hr hq hb hd
    have h := AronowAudit.P009.Wave1.corrected_bias_term_comparison_proof
      (Bridge.toProjectSequence S) k q s hr hq hb hd
    have hC (t : ℕ) : 1 ≤ averageOutgoing (S.experiment t) :=
      (graph_lower_bounds (S.positive t) _).1
    have hD (t : ℕ) : 0 < averageDependence (S.experiment t) :=
      zero_lt_one.trans_le (graph_lower_bounds (S.positive t) _).2
    have hdom (hnz : ∀ᶠ t in atTop, indirectBias (S.experiment t) ≠ 0)
        (hrel : Tendsto (fun t => averageOutgoing (S.experiment t)/
          (averageDependence (S.experiment t)*|indirectBias (S.experiment t)|)) atTop (nhds 0)) :
        WholeBiasDominance S := by
      exact ⟨reciprocal_consequence _ _ _ hC hD hnz hrel, h.2.2.2 hrel hnz⟩
    refine ⟨h.1, h.2.1, h.2.2.1, hdom, ?_⟩
    intro c hc hl
    have hh := ratio_from_lower_bound _ _ _ (fun t => (zero_lt_one.trans_le (hC t)).le)
      hD hd c hc hl
    exact ⟨hh.1, hh.2, hdom hh.1 hh.2⟩
  · exact ⟨wholeStarSequence, star_sequence_facts⟩

/-- Pointwise cancellation and bounded moments complete the three-unit refutation. -/
theorem T13_assembly : T13WholeStatement := by
  have h := AronowAudit.P009.direct_spillover_counterexample
  have hy (i : Fin 3) (z : TreatmentVector 3) : |cancellingPopulation.outcome i z| ≤ 1 := by
    by_cases hi : i = 1
    · subst i
      cases h0 : z 0 <;> cases h2 : z 2 <;>
        norm_num [cancellingPopulation, fairPopulation, treatmentValue, h0, h2]
    · simp [cancellingPopulation, fairPopulation, hi]
  have hall (q s : ℝ) (hq : 2 ≤ q) (hs : 1 ≤ s) : Regularity cancellingPopulation 2 q s :=
    fair_regular_all_orders _ 2 (by norm_num) (fun i z => (hy i z).trans (by norm_num)) q s hq hs
  refine ⟨h.1, ?_, ?_, hy, hall, ?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, ?_⟩
  · intro z
    norm_num [cancellingPopulation, fairPopulation, fairDistribution]
  · intro i z
    rfl
  · refine ⟨by norm_num, le_top, le_top, (hall 4 1 (by norm_num) (by norm_num)).2.2.2.1, ?_, ?_⟩
    · intro i
      simpa [OrderBound] using (fun z (_ : 0 < cancellingPopulation.design.mass z) =>
        (hy i z).trans (by norm_num : (1:ℝ) ≤ 2))
    · intro i b
      simpa [OrderBound, potentialResponse] using
        (fun z (_ : 0 < cancellingPopulation.design.mass z) =>
          (hy i (Function.update z i b)).trans (by norm_num : (1:ℝ) ≤ 2))
  · intro a z
    have he : cancellingPopulation.outcome 1 (Function.update (Function.update z 1 a) 0 true) -
      cancellingPopulation.outcome 1 (Function.update (Function.update z 1 a) 0 false) =
      2*treatmentValue (z 2)-1 := by
        simp [cancellingPopulation, fairPopulation, treatmentValue, Function.update_of_ne]
    refine ⟨he, ?_, ?_⟩ <;> cases z 2 <;> norm_num [treatmentValue]
  · intro hp
    exact hp cancellingPopulation h.1 (hall 4 1 (by norm_num) (by norm_num)) 0 1
      (by decide) h.2.2.1 h.2.2.2.2.2

/-- The general covariance identity needs no finite-support assumption. -/
theorem weighted_variance_general {Ω U : Type*} [MeasurableSpace Ω] [Fintype U]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : U → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (w : U → ℝ) (K : ℝ)
    (hw : ∀ i, 0 < w i ∧ w i ≤ K) :
    ProbabilityTheory.variance (fun ω => ∑ i, w i*X i ω) P =
      ∑ i, ∑ j, w i*w j*ProbabilityTheory.covariance (X i) (X j) P ∧
    ProbabilityTheory.variance (fun ω => ∑ i, w i*X i ω) P ≤
      K^2*(∑ i, ∑ j, |ProbabilityTheory.covariance (X i) (X j) P|) := by
  have he : ProbabilityTheory.variance (fun ω => ∑ i, w i*X i ω) P =
      ∑ i, ∑ j, w i*w j*ProbabilityTheory.covariance (X i) (X j) P := by
    rw [ProbabilityTheory.variance_fun_sum (fun i => (hX i).const_mul (w i))]
    simp_rw [ProbabilityTheory.covariance_const_mul_left, ProbabilityTheory.covariance_const_mul_right]
    congr 1
    funext i
    congr 1
    funext j
    ring
  refine ⟨he, ?_⟩
  rw [he]
  calc
    _ ≤ ∑ i, ∑ j, K^2*|ProbabilityTheory.covariance (X i) (X j) P| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hK : 0 ≤ K := (hw i).1.le.trans (hw i).2
      have hwK : w i*w j ≤ K^2 := by
        simpa only [pow_two] using mul_le_mul (hw i).2 (hw j).2 (hw j).1.le hK
      exact (mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (hw i).1.le (hw j).1.le)).trans
        (mul_le_mul_of_nonneg_right hwK (abs_nonneg _))
    _ = _ := by simp_rw [Finset.mul_sum]

/-- Moment-only A3, using the lower-moment leaf and the existing Cauchy–Schwarz theorem. -/
theorem moment_covariance (h1 : T4_L1) {n : ℕ} (E : FiniteExperiment n)
    (k : ℝ) (q : ExtendedOrder) (hk : 0 < k) (a : ℕ) (ha : a = 1 ∨ a = 2)
    (hqa : ((2*a:ℕ) : ExtendedOrder) ≤ q)
    (hm : ∀ i, OrderBound E.design (E.outcome i) k q) (i j : Fin n) (b : Bool) :
    |covariance E.design (armResponse E b a i) (armResponse E b a j)| ≤ k^(2*a) := by
  have ha0 : 0 < a := by omega
  have hlow (i : Fin n) : expectation E.design
      (fun z => Real.rpow |E.outcome i z| ((2*a:ℕ):ℝ)) ≤ Real.rpow k ((2*a:ℕ):ℝ) := by
    apply h1 E.design (E.outcome i) k ((2*a:ℕ):ℝ) q hk (by positivity) _ (hm i)
    rcases ha with rfl | rfl <;> norm_num at hqa ⊢ <;> exact hqa
  have htwo : (2:ℝ) ≤ ((2*a:ℕ):ℝ) := by
    exact_mod_cast (show 2 ≤ 2*a by omega)
  exact (AronowAudit.P009.corrected_moment_covariance (Bridge.toProjectExperiment E)
    k ((2*a:ℕ):ℝ) hk htwo hlow a (by norm_cast) i j b).2.2.2.2.2.2

/-- Lower moments turn the extended regularity predicate into ordinary finite regularity. -/
theorem regularity_lower (h1 : T4_L1) {n : ℕ} (E : FiniteExperiment n)
    (k : ℝ) (q s : ExtendedOrder) (hr : WholeRegularity E k q s)
    (p : ℝ) (hp : 2 ≤ p) (hpq : (p : ExtendedOrder) ≤ q) : Regularity E k p 1 := by
  refine ⟨hr.1, hp, by norm_num, hr.2.2.2.1, ?_, ?_⟩
  · intro i
    exact h1 E.design (E.outcome i) k p q hr.1 (by linarith) hpq (hr.2.2.2.2.1 i)
  · intro i b
    exact h1 E.design (potentialResponse E i b) k 1 s hr.1 (by norm_num)
      hr.2.2.1 (hr.2.2.2.2.2 i b)

/-- The external exponent is at most one, including both endpoints. -/
theorem whole_exponent_le_one (q : ExtendedOrder) (hq : 2 ≤ q) : wholeExternalExponent q ≤ 1 := by
  by_cases ht : q = ⊤
  · simp [wholeExternalExponent, ht]
  · lift q to ℝ using ht with r
    have hr : (2:ℝ) ≤ r := by exact WithTop.coe_le_coe.mp hq
    simp only [wholeExternalExponent, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe]
    exact (div_le_one (by linarith)).2 (by linarith)

/-- The extended-order arm mixing estimate: the finite branch is an existing theorem. -/
theorem arm_mixing_extended (h1 : T4_L1) (h2 : T4_L2) {n : ℕ}
    (E : FiniteExperiment n) (k : ℝ) (q s : ExtendedOrder)
    (hr : WholeRegularity E k q s) (b : Bool) (i j : Fin n) :
    |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ≤
      10*k^2*mixingPower (mixingCoefficient E.design
        (relevantTreatments E i) (relevantTreatments E j)) (wholeExternalExponent q) := by
  by_cases ht : q = ⊤
  · subst q
    have hmask (l : Fin n) : (fun z => armResponse E b 1 l (relevantTreatments E l z)) =
        armResponse E b 1 l := by
      funext z
      exact AronowAudit.P009.Wave1.t4_arm_mask (Bridge.toProjectExperiment E) b 1 l z
    have hbound (l : Fin n) (z : TreatmentVector n) (hz : 0 < E.design.mass z) :
        |armResponse E b 1 l (relevantTreatments E l z)| ≤ k := by
      rw [congrFun (hmask l) z]
      have ho : |E.outcome l z| ≤ k := by
        have hh := hr.2.2.2.2.1 l
        simpa only [OrderBound, ite_eq_left rfl] using hh z hz
      unfold armResponse
      split_ifs
      · simpa only [pow_one] using ho
      · simpa using hr.1.le
    have hh := h2 E.design (relevantTreatments E i) (relevantTreatments E j)
      (armResponse E b 1 i) (armResponse E b 1 j) k k hr.1.le hr.1.le (hbound i) (hbound j)
    rw [hmask i, hmask j] at hh
    have hα : 0 ≤ mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j) := by
      rw [Bridge.mixing_correspondence]
      exact AronowAudit.P009.MixingBasics.alpha_nonnegative _ _ _
    have he (x : ℝ) : mixingPower x 1 = x := by
      by_cases hx : x = 0 <;> simp [mixingPower, hx]
    simp only [wholeExternalExponent, ite_true, he]
    nlinarith [mul_nonneg (sq_nonneg k) hα]
  · lift q to ℝ using ht with r
    have hq : (2:ℝ) ≤ r := by exact WithTop.coe_le_coe.mp hr.2.1
    have hf : Regularity E k r 1 := regularity_lower h1 E k r s hr r hq le_rfl
    have hh := AronowAudit.P009.Wave1.t4_arm_mixing (Bridge.toProjectExperiment E) k r 1 hf b i j
    change |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ≤
      10*k^2*mixingPower (mixingCoefficient E.design
        (relevantTreatments E i) (relevantTreatments E j)) ((r-2)/r) at hh
    simpa only [wholeExternalExponent, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe] using hh

end
end SAP.P009a.WH.W2
