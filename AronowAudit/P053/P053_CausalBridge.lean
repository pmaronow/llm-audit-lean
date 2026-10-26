import AronowAudit.P053.P053_Audit
import AronowAudit.External.Causalean.Experimentation.DesignBased.FinitePopulationVariance

/-! Exact bridges from the Causalean finite-population sampling theorems to
the complete-randomization definitions.
The imported Causalean proofs are by Jiyuan Tan, Apache-2.0; see NOTICE at the
repository root. -/

namespace AronowAudit.P053
open scoped BigOperators Topology
open Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

namespace CausalBridge

 theorem probability_eq_size (P : Population) (n : ℕ) (hn : n ≤ P.size)
    (A : Finset (Fin P.size) → Prop) :
    (Causalean.Experimentation.DesignBased.completeRandomization
      (V := Fin P.size) n (by simpa using hn)).Pr (fun S => A S.val) =
      (((support (ι := Fin P.size) n).filter A).card : ℝ) /
        (support (ι := Fin P.size) n).card := by
  classical
  have hcard : Fintype.card {S : Finset (Fin P.size) // S.card = n} =
      (support (ι := Fin P.size) n).card := by
    rw [Causalean.Experimentation.DesignBased.completeRandomization_card]
    simp [support]
  have hsum := Finset.sum_subtype (F := inferInstance)
    (p := fun S : Finset (Fin P.size) => S.card = n) (support (ι := Fin P.size) n)
    (fun S => by simp [support, Finset.mem_powersetCard])
    (fun S => if A S then (1 : ℝ) else 0)
  simp only [Causalean.Experimentation.DesignBased.FiniteDesign.Pr,
    Causalean.Experimentation.DesignBased.FiniteDesign.E,
    Causalean.Experimentation.DesignBased.FiniteDesign.ind,
    Causalean.Experimentation.DesignBased.completeRandomization]
  rw [← Finset.mul_sum, ← hsum, hcard]
  simp [← Finset.sum_filter, div_eq_mul_inv, mul_comm]

 theorem probability_eq (P : Population) (A : Finset (Fin P.size) → Prop) :
    (Causalean.Experimentation.DesignBased.completeRandomization
      (V := Fin P.size) P.n1 (by simp [Population.size])).Pr (fun S => A S.val) =
      randomizationProbability P A := by
  exact probability_eq_size P P.n1 (by simp [Population.size]) A

 theorem expectation_eq (P : Population) (X : Finset (Fin P.size) → ℝ) :
    (Causalean.Experimentation.DesignBased.completeRandomization
      (V := Fin P.size) P.n1 (by simp [Population.size])).E (fun S => X S.val) =
      randomizationMean P X := by
  classical
  have hcard : Fintype.card {S : Finset (Fin P.size) // S.card = P.n1} =
      (support (ι := Fin P.size) P.n1).card := by
    rw [Causalean.Experimentation.DesignBased.completeRandomization_card]
    simp [support]
  have hsum := Finset.sum_subtype (F := inferInstance)
    (p := fun S : Finset (Fin P.size) => S.card = P.n1) (support (ι := Fin P.size) P.n1)
    (fun S => by simp [support, Finset.mem_powersetCard]) X
  simp only [Causalean.Experimentation.DesignBased.FiniteDesign.E,
    Causalean.Experimentation.DesignBased.completeRandomization]
  rw [← Finset.mul_sum, ← hsum, hcard]
  simp [randomizationMean, div_eq_mul_inv, mul_comm]

 theorem variance_eq (P : Population) (X : Finset (Fin P.size) → ℝ) :
    (Causalean.Experimentation.DesignBased.completeRandomization
      (V := Fin P.size) P.n1 (by simp [Population.size])).Var (fun S => X S.val) =
      randomizationVariance P X := by
  simp only [Causalean.Experimentation.DesignBased.FiniteDesign.Var, expectation_eq,
    randomizationVariance]
  exact expectation_eq P (fun z => (X z - randomizationMean P X)^2)

 theorem probability_control_eq (P : Population) (A : Finset (Fin P.size) → Prop) :
    (Causalean.Experimentation.DesignBased.completeRandomization
      (V := Fin P.size) P.n0 (by simp [Population.size])).Pr (fun S => A S.val) =
      randomizationProbability P (fun z => A zᶜ) := by
  classical
  rw [probability_eq_size P P.n0 (by simp [Population.size])]
  have hcard : (support (ι := Fin P.size) P.n0).card =
      (support (ι := Fin P.size) P.n1).card := by
    simp only [support, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact Nat.choose_symm_add.symm
  have hnum : ((support (ι := Fin P.size) P.n1).filter (fun z => A zᶜ)).card =
      ((support (ι := Fin P.size) P.n0).filter A).card := by
    apply Finset.card_bij (fun z _ => zᶜ)
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hz, ha⟩
      refine Finset.mem_filter.mpr ⟨?_, ha⟩
      simp only [support, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact (arm_cards P z hz).2
    · intro z hz w hw he
      exact compl_injective he
    · intro w hw
      rcases Finset.mem_filter.mp hw with ⟨hw, ha⟩
      refine ⟨wᶜ, Finset.mem_filter.mpr ⟨?_, by simpa⟩, by simp⟩
      simp only [support, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hw ⊢
      rw [Finset.card_compl, Fintype.card_fin, hw]
      dsimp [Population.size]
      omega
  simp only [randomizationProbability, hcard, hnum]

 theorem sampleMean_eq (P : Population) (n : ℕ) (y : Fin P.size → ℝ)
    (S : {S : Finset (Fin P.size) // S.card = n}) :
    Causalean.Experimentation.FinitePopulationMoments.sampleMean n y S =
      sampleMean S.val y := by
  simp [Causalean.Experimentation.FinitePopulationMoments.sampleMean,
    sampleMean, ← Finset.sum_filter, S.property]

 theorem populationMean_eq (P : Population) (y : Fin P.size → ℝ) :
    Causalean.Experimentation.FinitePopulationMoments.popMean y = populationMean P y := by
  simp [Causalean.Experimentation.FinitePopulationMoments.popMean, populationMean, sampleMean]

 theorem sampleVariance_eq (P : Population) (n : ℕ) (y : Fin P.size → ℝ)
    (S : {S : Finset (Fin P.size) // S.card = n}) :
    Causalean.Experimentation.FinitePopulationMoments.sampleVariance n y S =
      sampleVariance S.val y := by
  simp [Causalean.Experimentation.FinitePopulationMoments.sampleVariance,
    sampleVariance, centeredSS, sampleMean_eq P, ← Finset.sum_filter, S.property]

 theorem populationVariance_eq (P : Population) (y : Fin P.size → ℝ) :
    Causalean.Experimentation.FinitePopulationMoments.popVar y = populationVariance P y := by
  simp [Causalean.Experimentation.FinitePopulationMoments.popVar,
    populationVariance, sampleVariance, centeredSS, populationMean_eq P,
    populationMean, sampleMean]

 theorem limit_transport {Ω : ℕ → Type*} [∀ k, Fintype (Ω k)]
    (E : ℕ → Population)
    (D : ∀ k, Causalean.Experimentation.DesignBased.FiniteDesign (Ω k))
    (f : ∀ k, Ω k → Finset (Fin (E k).size))
    (X : ∀ k, Finset (Fin (E k).size) → ℝ) (a : ℕ → ℝ) (c : ℝ)
    (hPr : ∀ k (A : Finset (Fin (E k).size) → Prop),
      (D k).Pr (fun w => A (f k w)) = randomizationProbability (E k) A)
    (hX : Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb D
      (fun k w => X k (f k w)) a)
    (ha : Tendsto a atTop (𝓝 c)) : InProbability E X c := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hclose : ∀ᶠ k in atTop, |a k-c| < ε/2 := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.mp ha (ε/2) hhalf)
  refine squeeze_zero' (.of_forall fun k => ?_) ?_ (hX (ε/2) hhalf)
  · unfold randomizationProbability
    positivity
  · filter_upwards [hclose] with k hk
    rw [← hPr k]
    apply (D k).Pr_mono
    intro w hw
    have htri := abs_sub_le (X k (f k w)) (a k) c
    by_contra hn
    have hn' : |X k (f k w) - a k| < ε/2 := lt_of_not_ge hn
    linarith

/-- Chebyshev consistency under complete randomization, with no
asymptotic sampling theorem assumed. The premises are actual finite expectation
and variance limits. -/
 theorem chebyshev_limit (E : ℕ → Population)
    (X : ∀ k, Finset (Fin (E k).size) → ℝ) (c : ℝ)
    (hvar : Tendsto (fun k => randomizationVariance (E k) (X k)) atTop (𝓝 0))
    (hmean : Tendsto (fun k => randomizationMean (E k) (X k)) atTop (𝓝 c)) :
    InProbability E X c := by
  let D := fun k => Causalean.Experimentation.DesignBased.completeRandomization
    (V := Fin (E k).size) (E k).n1 (by simp [Population.size])
  apply limit_transport (Ω := fun k => {S : Finset (Fin (E k).size) // S.card = (E k).n1})
    E D (fun _ S => S.val) X (fun k => randomizationMean (E k) (X k)) c
    (fun k A => probability_eq (E k) A) ?_ hmean
  have hv : Tendsto (fun k => (D k).Var (fun S => X k S.val)) atTop (𝓝 0) := by
    simpa only [D, variance_eq] using hvar
  have h := Causalean.Experimentation.DesignBased.FiniteDesign.tendstoInProb_of_var
    D (fun k S => X k S.val) hv
  simpa only [D, expectation_eq] using h

 theorem treated_limit (E : ℕ → Population)
    (X : ∀ k, Finset (Fin (E k).size) → ℝ) (a : ℕ → ℝ) (c : ℝ)
    (hX : Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb
      (fun k => Causalean.Experimentation.DesignBased.completeRandomization
        (V := Fin (E k).size) (E k).n1 (by simp [Population.size]))
      (fun k S => X k S.val) a)
    (ha : Tendsto a atTop (𝓝 c)) : InProbability E X c :=
  limit_transport (Ω := fun k => {S : Finset (Fin (E k).size) // S.card = (E k).n1}) E
    (fun k => Causalean.Experimentation.DesignBased.completeRandomization
      (V := Fin (E k).size) (E k).n1 (by simp [Population.size]))
    (fun _ S => S.val) X a c
    (fun k A => probability_eq (E k) A) hX ha

 theorem control_limit (E : ℕ → Population)
    (X : ∀ k, Finset (Fin (E k).size) → ℝ) (a : ℕ → ℝ) (c : ℝ)
    (hX : Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb
      (fun k => Causalean.Experimentation.DesignBased.completeRandomization
        (V := Fin (E k).size) (E k).n0 (by simp [Population.size]))
      (fun k S => X k S.val) a)
    (ha : Tendsto a atTop (𝓝 c)) :
      InProbability E (fun k z => X k zᶜ) c := by
  apply limit_transport (Ω := fun k => {S : Finset (Fin (E k).size) // S.card = (E k).n0}) E
    (fun k => Causalean.Experimentation.DesignBased.completeRandomization
      (V := Fin (E k).size) (E k).n0 (by simp [Population.size]))
    (fun _ S => S.valᶜ) (fun k z => X k zᶜ) a c
    (fun k A => ?_) (by simpa using hX) ha
  simpa using probability_control_eq (E k) (fun z => A zᶜ)

instance witness_nonempty (k : ℕ) : Nonempty (Fin (heterogeneousWitness k).size) :=
  ⟨⟨0, by dsimp [heterogeneousWitness, Population.size]; omega⟩⟩

def witnessOutcome (b : Bool) (k : ℕ) : Fin (heterogeneousWitness k).size → ℝ :=
  if b then (heterogeneousWitness k).Y1 else (heterogeneousWitness k).Y0

def witnessVariance (b : Bool) : ℝ := if b then 4 else 1

 theorem witness_source_mean (b : Bool) (k : ℕ) :
    Causalean.Experimentation.FinitePopulationMoments.popMean (witnessOutcome b k) = 0 := by
  rw [populationMean_eq (heterogeneousWitness k)]
  cases b
  · exact (witness_potential_moments k).1
  · exact (witness_potential_moments k).2.1

 theorem witness_source_variance (b : Bool) :
    Tendsto (fun k => Causalean.Experimentation.FinitePopulationMoments.popVar
      (witnessOutcome b k)) atTop (𝓝 (witnessVariance b)) := by
  simp only [populationVariance_eq (heterogeneousWitness _)]
  cases b
  · exact witness_regular.variance0
  · exact witness_regular.variance1

 theorem witness_source_max (b : Bool) (k : ℕ) :
    Causalean.Experimentation.FinitePopulationMoments.popMaxSqDev
      (witnessOutcome b k) = witnessVariance b := by
  unfold Causalean.Experimentation.FinitePopulationMoments.popMaxSqDev
  rw [witness_source_mean]
  have he : (fun i : Fin (heterogeneousWitness k).size => (witnessOutcome b k i - 0)^2) =
      fun _ => witnessVariance b := by
    funext i
    cases b <;> dsimp [witnessOutcome, witnessVariance, heterogeneousWitness]
    all_goals split_ifs <;> norm_num
  rw [he, Finset.sup'_const]

 theorem witness_arm_diverges (b : Bool) :
    Tendsto (fun k => if b then (heterogeneousWitness k).n1 else
      (heterogeneousWitness k).n0) atTop atTop := by
  apply tendsto_atTop.2
  intro a
  filter_upwards [eventually_ge_atTop a] with k hk
  cases b <;> dsimp [heterogeneousWitness] <;> omega

 theorem witness_variance_source_limit (b : Bool) (n : ℕ → ℕ)
    (hn2 : ∀ k, 2 ≤ n k) (hnle : ∀ k, n k ≤ (heterogeneousWitness k).size)
    (hnTop : Tendsto n atTop atTop) :
    Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb
      (fun k => Causalean.Experimentation.DesignBased.completeRandomization
        (V := Fin (heterogeneousWitness k).size) (n k) (by simpa using hnle k))
      (fun k => Causalean.Experimentation.FinitePopulationMoments.sampleVariance
        (n k) (witnessOutcome b k))
      (fun k => Causalean.Experimentation.FinitePopulationMoments.popVar (witnessOutcome b k)) := by
  apply Causalean.Experimentation.FinitePopulationMoments.SampleVarianceConsistency.sampleVariance_tendstoInProb
    n hn2 (fun k => by simpa using hnle k) (witnessOutcome b) (witnessVariance b)
    hnTop (witness_source_variance b)
  have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hnTop
  simpa only [witness_source_max, div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnR) :
      Tendsto (fun k => witnessVariance b * (n k : ℝ)⁻¹) atTop (𝓝 (witnessVariance b * 0)))

/-- Actual treated and control sample variances of the heterogeneous witness
converge under the full complete-randomization law. No sampling LLN
or variance-estimator limit is assumed. -/
 theorem witness_arm_variance_limits :
    InProbability heterogeneousWitness
      (fun k z => sampleVariance z (observed (heterogeneousWitness k) z)) 4 ∧
    InProbability heterogeneousWitness
      (fun k z => sampleVariance zᶜ (observed (heterogeneousWitness k) z)) 1 := by
  have ht := witness_variance_source_limit true (fun k => (heterogeneousWitness k).n1)
    (fun k => by dsimp [heterogeneousWitness]; omega)
    (fun k => by dsimp [Population.size]; omega) (witness_arm_diverges true)
  have hc := witness_variance_source_limit false (fun k => (heterogeneousWitness k).n0)
    (fun k => by dsimp [heterogeneousWitness]; omega)
    (fun k => by dsimp [Population.size]; omega) (witness_arm_diverges false)
  have ht' : InProbability heterogeneousWitness
      (fun k z => sampleVariance z (heterogeneousWitness k).Y1) 4 := by
    apply treated_limit heterogeneousWitness _
      (fun k => Causalean.Experimentation.FinitePopulationMoments.popVar (witnessOutcome true k)) 4
      (by simpa only [Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb,
        witnessOutcome, if_true, sampleVariance_eq] using ht)
      (by simpa [witnessVariance] using witness_source_variance true)
  have hc' : InProbability heterogeneousWitness
      (fun k z => sampleVariance zᶜ (heterogeneousWitness k).Y0) 1 := by
    apply control_limit heterogeneousWitness
      (fun k z => sampleVariance z (heterogeneousWitness k).Y0)
      (fun k => Causalean.Experimentation.FinitePopulationMoments.popVar (witnessOutcome false k)) 1
      (by simpa only [Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb,
        witnessOutcome, Bool.false_eq_true, if_false, sampleVariance_eq] using hc)
      (by simpa [witnessVariance] using witness_source_variance false)
  simpa only [treated_variance_observed, control_variance_observed] using And.intro ht' hc'

end CausalBridge
end
end AronowAudit.P053
