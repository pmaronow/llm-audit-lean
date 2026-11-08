import SAP.P009a.WH.W1.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SAP.P009a.WH.W1

open Filter MeasureTheory Bridge
open scoped BigOperators Topology Classical

noncomputable section

/-- Self-mixing of a Boolean random variable is its Bernoulli variance, including p=0 and p=1.
Use MixingBasics.alpha_le_of_event_bound. An event in Bool has four membership patterns;
enumerate the sixteen pairs of patterns using probability_complement and mean_const.
The singleton event attains p(1-p), by event_abs_le_alpha. No positive-marginal premise is needed. -/
def T16_L1 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (P : FiniteDistribution Ω) (X : Ω → Bool) (b : Bool),
    mixingCoefficient P X X =
      probability P (fun ω => X ω = b) * (1 - probability P (fun ω => X ω = b))

/-- Exact sparse scaled and centered error laws, and the finite zero lower-tail cutoff.
Use sparseCoverage_scaled_error, sparse_estimators_finite, sparse_moments_finite,
sparseCoverage_msq and sparseCoverage_inflations. Split the first Boolean coordinate;
fair_first_coordinate computes both atom probabilities. Positivity of n=t+1 separates the atoms.
For n>1/epsilon, both scaled-error values exceed -epsilon, so the event is empty. -/
def T1_L1 : Prop := W1SparseErrors

/-- Sparse dispersion limits and all Proposition-8/9A/10A rate checks, with Part B excluded.
Use sparseCoverage_sdSigmaSq and sparseCoverage_graph. Squeeze (n-1)/n² between 0 and 1/n,
then use continuity of sqrt. The two graph ratios equal 1/sqrt(n), which tends to zero.
Use sparseCoverage_msq and inv_size_zero to contradict an eventual positive lower bound. -/
def T1_L2 : Prop := W1SparseRates

/-- Sparse intervals at every alpha in (0,1), for all four estimates, and relative lower tails.
Rewrite sparse_estimators_finite, sparse_eate and sparseCoverage_inflations. On the first
coordinate false, the interval is [0,0]; on true, its squared error is 1/n² and the variance
ratio is 4/(alpha*n²). Use Real.abs_le_sqrt and fair_first_coordinate. The relative lower-tail
event is exactly the first coordinate being false. All statements are on the full cube. -/
def T1_L3 : Prop := W1SparseIntervals

theorem T16_assembly (h1 : T16_L1) : T16WholeStatement := by
  intro n hn E b k hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcov (i j : Fin n) :
      covariance E.design (fun z => if z i = b then 1 else 0)
        (fun z => if z j = b then 1 else 0) = assignmentGap E b i j := by
    rw [covariance_correspondence, AronowAudit.P009.BernoulliCompletion.covariance_product_formula]
    change expectation E.design (fun z => (if z i = b then 1 else 0) *
      (if z j = b then 1 else 0)) -
      expectation E.design (fun z => if z i = b then 1 else 0) *
      expectation E.design (fun z => if z j = b then 1 else 0) = _
    unfold assignmentGap armProbability probability
    congr 1
    · apply congrArg (expectation E.design)
      funext z
      by_cases hi : z i = b <;> by_cases hj : z j = b <;> simp [hi, hj]
    · congr 1 <;> apply congrArg (expectation E.design) <;>
        funext z <;> split_ifs <;> rfl
  have hdiag (i : Fin n) :
      assignmentMixing E i i = armProbability E i b * (1-armProbability E i b) :=
    h1 E.design (fun z => z i) b
  have hrest : (∑ i, ∑ j, assignmentMixing E i j) = restoredMixingSum E b := by
    have hs (i : Fin n) : (∑ j, assignmentMixing E i j) =
        (∑ j, if j = i then 0 else assignmentMixing E i j) + assignmentMixing E i i := by
      calc
        _ = ∑ j, ((if j = i then 0 else assignmentMixing E i j) +
            (if j = i then assignmentMixing E i i else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i <;> simp [hji]
        _ = _ := by simp [Finset.sum_add_distrib]
    simp_rw [hs, hdiag]
    exact Finset.sum_add_distrib
  have hold := AronowAudit.P009.corrected_full_pair_mixing_bound hn (toProjectExperiment E) b k hk
  have hsecond : k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentMixing E i j) ≤
      k^2*averageDependence E/(n:ℝ) + k^2/(n:ℝ)^2 *
        (∑ i, ∑ j, (1-dependenceIndicator E i j)*assignmentMixing E i j) := hold.2
  have hfirst : k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentGap E b i j) ≤
      k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentMixing E i j) := by
    have hh : k^2/(n:ℝ)^2 * (∑ i, ∑ j, covariance E.design
        (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)) ≤
        k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentMixing E i j) := hold.1
    simpa only [hcov] using hh
  refine ⟨?_, ?_, ?_, hfirst, hsecond, hrest, ?_, ?_⟩
  · intro i j
    refine ⟨hcov i j, ?_, ?_, ?_, by ring⟩
    · simpa only [assignmentGap, assignmentMixing, armProbability,
        probability_correspondence, mixing_correspondence, Set.mem_singleton_iff] using
        AronowAudit.P009.MixingBasics.event_abs_le_alpha
          (toProjectDistribution E.design) (fun z => z i) (fun z => z j) {b} {b}
    · exact AronowAudit.P009.MixingBasics.alpha_nonnegative
        (toProjectDistribution E.design) (fun z => z i) (fun z => z j)
    · exact AronowAudit.P009.Wave1.t9_alpha_le_quarter
        (toProjectDistribution E.design) (fun z => z i) (fun z => z j)
  · intro i
    refine ⟨ite_eq_left ⟨i, Or.inl rfl, Or.inl rfl⟩, ?_, hdiag i⟩
    simp only [assignmentGap, and_self, armProbability]
    ring
  · unfold averageDependence dependenceDegree
    field_simp
  · simpa only [hrest] using hfirst
  · simpa only [hrest] using hsecond

theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) (h3 : T1_L3) : T1WholeStatement := by
  refine ⟨retainedT1, sparse_all_orders, sparse_bounds, sparse_marginal, sparse_diagonal,
    ?_, h1, h2, h3, sparse_normalizations, sparse_bias_limit, sparse_variance_limit⟩
  intro t i
  exact AronowAudit.P009.Wave1.sparseCoverage_sigmaSq t i

/-- The counterexample part of corrected T2 needs only already certified finite sparse facts. -/
theorem coverage_counterexample : W1CoverageCounterexample := by
  rcases retainedT1.1 with ⟨hReg, hgraph, hRestricted, hfinite, hCons,
    hConsAvg, hConsMax, hConsSR, hEq, hCov, hNom⟩
  refine ⟨hReg, ?_, hCons, hEq, sparse_normalizations, sparse_bias_limit,
    sparse_variance_limit, hNom⟩
  intro t
  rcases hfinite t with ⟨heate, hadse, hmsq, hv, hm, hstrict, hest, hdisp⟩
  refine ⟨(hgraph t).1, (hgraph t).2.1, ?_, ?_, ?_, hstrict, hCov t⟩
  · rw [hv]
    have hn : 0 < sampleSize sparseSequence t := by
      change (0 : ℝ) < (t+1 : ℕ)
      positivity
    positivity
  · intro z
    rw [(hest z).2.1]
    have hb : 0 ≤ treatmentValue (z ⟨0, by simp [sparseSequence]⟩) := by
      unfold treatmentValue
      split <;> norm_num
    positivity
  · exact (retainedT1.2 t).trans heate.symm

theorem T2_assembly : T2WholeStatement := by
  exact ⟨retainedT2, @AronowAudit.P009.iterated_lower_tail_zero, coverage_counterexample⟩

theorem T3_assembly : T3WholeStatement := by
  exact ⟨signedWitness, countWitness, squareWitness, signed_base, signed_bounds,
    signed_all_orders, signed_table, count_table, square_table⟩

theorem T17_assembly : T17WholeStatement := by
  have h1 := hypergeom_first_facts
  have h2 := hypergeom_second
  refine ⟨@other_incoming_count, hypergeomWitness, hypergeomSecondWitness, ?_⟩
  have hr := AronowAudit.P009.hypergeometric_draw_counterexample
  have hc : incomingCount hypergeomWitness 0 = 2 := hr.2.2.1
  have hp := h1.1 0 true
  rcases h1.2.2 (0 : Fin 3) with ⟨hm, hpm, hcm, hpcm, hcf, hpcf⟩
  norm_num at hm hpm hcm hpcm
  refine ⟨(fun _ => rfl), (fun _ _ => rfl), hr.1, hr.2.1, h1.1,
    (fun j => AronowAudit.P009.hypergeom_interferes_zero j), hc, ?_, h1.2.1,
    h1.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h2⟩ <;>
    norm_num [hc, hp, hm, hpm, hcm, hpcm, printedIncomingRatio, treatmentValue]

end
end SAP.P009a.WH.W1
