import SAP.P001g.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w z u1 v1

def T118Statement : Prop :=
  (¬ PluginPositiveNormalLimit.{u}) ∧
  (¬ ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    ∃ L : KolmogorovSpace →L[ℝ] ℝ,
      HadamardAt {F | finiteSecondCDF F} Set.univ cdfMeanFunctional
        (kolmogorovEmbed (cdf ν id)) L)

def T120Statement : Prop :=
  ¬ FixedCovariateKLMLEPositiveSupport.{u}

def T121Statement : Prop :=
  ¬ (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → Fin 4) (hiid : IID μ X) (b0 : ℝ) (hb : b0∈Set.Icc (1/4 : ℝ) (3/4))
   (hlaw : μ.map (X 0)=∑ j : Fin 4,ENNReal.ofReal (disjointMixture 1 (1/3) b0 j) • Measure.dirac j)
   (that : ∀ n : ℕ,(Fin n → Fin 4) → Fin 3 → ℝ)
   (hvalid : ∀ n s,that n s 0∈Set.Icc (0 : ℝ) 1 ∧ that n s 1∈Set.Icc (0 : ℝ) 1 ∧
      that n s 2∈Set.Icc (1/4 : ℝ) (3/4))
   (hmax : ∀ n s p a b,p∈Set.Icc (0 : ℝ) 1 → a∈Set.Icc (0 : ℝ) 1 → b∈Set.Icc (1/4 : ℝ) (3/4) →
     (∏ i,disjointMixture p a b (s i)) ≤ 
       ∏ i,disjointMixture (that n s 0) (that n s 1) (that n s 2) (s i)),
    CP μ (fun n ω => that n (firstSample X n ω)) (![1,1/3,b0] : Fin 3 → ℝ))

end

end SAP.P001g
