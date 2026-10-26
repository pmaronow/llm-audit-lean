import AronowAudit.P037.P037_VaryingLindeberg
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments
import AronowAudit.External.Causalean.Stat.FiniteDesign.FiniteDesignMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.DeriveFintype
import Lean.Elab.Tactic.Omega

namespace AronowAudit.P037
open scoped BigOperators
set_option autoImplicit false

/-- SI pp. 16--17: "An experimental design is a plan for randomly
selecting a particular value of z with predetermined probability p_z."
A finite nonnegative normalized law; zero-mass states can be retained. -/
structure FiniteDesign (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ w, 0 ≤ weight w
  total : ∑ w, weight w = 1

/-- SI p. 18: π_i(d_k) = sum over assignments of their probabilities
times the exposure indicator. Expectations use the same finite sum. -/
noncomputable def designMean {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) : ℝ := ∑ w, d.weight w * X w

/-- Variance over randomization, computed as E[X²] - E[X]². For the
normalized finite design this equals E[(X-E[X])²], proved below. -/
noncomputable def designVariance {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) : ℝ :=
  designMean d (fun w => (X w)^2) - (designMean d X)^2

/-- Randomization covariance of two school assignment indicators,
used in P037-T10 to test the SI p. 19 independence assertion. -/
noncomputable def designCovariance {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X Y : Ω → ℝ) : ℝ :=
  designMean d (fun w => X w*Y w) - designMean d X * designMean d Y

/-- Exact finite-sum linearity supporting SI's randomization expectations. -/
theorem designMean_add {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω)
    (X Y : Ω → ℝ) :
    designMean d (fun w => X w + Y w) = designMean d X + designMean d Y := by
  simp [designMean, mul_add, Finset.sum_add_distrib]

/-- Exact finite-sum subtraction supporting SI's randomization expectations. -/
theorem designMean_sub {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω)
    (X Y : Ω → ℝ) :
    designMean d (fun w => X w - Y w) = designMean d X - designMean d Y := by
  simp [designMean, mul_sub, Finset.sum_sub_distrib]

/-- A constant has its constant value under the normalized design law. -/
theorem designMean_const {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω) (c : ℝ) :
    designMean d (fun _ => c) = c := by
  rw [designMean, ← Finset.sum_mul, d.total, one_mul]

/-- A fixed coefficient factors out of the finite design expectation. -/
theorem designMean_mul {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω)
    (c : ℝ) (X : Ω → ℝ) :
    designMean d (fun w => c * X w) = c * designMean d X := by
  simp [designMean, Finset.mul_sum, mul_left_comm]

/-- Finite sums of school or student contributions commute with expectation. -/
theorem designMean_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (X : I → Ω → ℝ) :
    designMean d (fun w => ∑ i, X i w) = ∑ i, designMean d (X i) := by
  simp only [designMean, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The second-moment expression is the actual centered variance of
the finite randomization distribution, rather than a surrogate. -/
theorem designVariance_centered {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) :
    designVariance d X = designMean d (fun w => (X w - designMean d X)^2) := by
  have hp : (fun w => (X w - designMean d X)^2) =
      (fun w => (X w)^2 - (2*designMean d X)*X w + (designMean d X)^2) := by
    funext w; ring
  rw [hp, designMean_add, designMean_sub, designMean_mul, designMean_const]
  unfold designVariance
  ring

/-- SI p. 5 and Fig. S1 p. 24: "Within each of the 14 school blocks,
two schools were assigned to control ... and two to treatment". One
uniform block has these six treatment pairs (schools indexed 0--3). -/
def treatedPair (w : Fin 6) : Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)] w

/-- The school-level assignment D_ij of SI Eqs. (1)--(6), for one
uniformly randomized block; 1 denotes a treated school. -/
noncomputable def blockTreatment (w : Fin 6) (i : Fin 4) : ℝ :=
  if i = (treatedPair w).1 ∨ i = (treatedPair w).2 then 1 else 0

/-- Uniform two-of-four block randomization; each of its six
allocations has mass 1/6. -/
noncomputable def oneBlockDesign : FiniteDesign (Fin 6) where
  weight := fun _ => 1/6
  nonneg := fun _ => by norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- P037-T10's witness obeys both design constraints: each assignment
indicator is binary and exactly two of the four schools are treated. -/
theorem block_design_constraints :
    (∀ w i, blockTreatment w i = 0 ∨ blockTreatment w i = 1) ∧
    (∀ w, ∑ i, blockTreatment w i = 2) := by
  constructor
  · intro w i; unfold blockTreatment; split_ifs <;> simp
  · intro w; fin_cases w <;>
      norm_num [Fin.sum_univ_four, blockTreatment, treatedPair]

/-- P037-T10(i)--(iii): every school has treatment probability 1/2,
every distinct within-block pair has joint treatment probability 1/6
and covariance -1/12; control exposures have the same covariance.
The nonfactorizing joint probability proves dependence. -/
theorem within_block_dependence :
    (∀ i, designMean oneBlockDesign (fun w => blockTreatment w i) = 1/2) ∧
    (∀ i j, i ≠ j →
      designMean oneBlockDesign (fun w => blockTreatment w i*blockTreatment w j) = 1/6 ∧
      designCovariance oneBlockDesign (fun w => blockTreatment w i)
        (fun w => blockTreatment w j) = -1/12 ∧
      designCovariance oneBlockDesign (fun w => 1-blockTreatment w i)
        (fun w => 1-blockTreatment w j) = -1/12 ∧
      designMean oneBlockDesign (fun w => blockTreatment w i*blockTreatment w j) ≠
        designMean oneBlockDesign (fun w => blockTreatment w i) *
        designMean oneBlockDesign (fun w => blockTreatment w j)) := by
  constructor
  · intro i; fin_cases i <;>
      norm_num [designMean, oneBlockDesign, blockTreatment, treatedPair, Fin.sum_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | norm_num [designCovariance, designMean, oneBlockDesign, blockTreatment,
        treatedPair, Fin.sum_univ_succ] at hij ⊢

/-- P037-T10(v): two independently randomized blocks have the product
law, with 36 allocations each of probability 1/36. -/
noncomputable def twoBlockDesign : FiniteDesign (Fin 6 × Fin 6) where
  weight := fun _ => 1/36
  nonneg := fun _ => by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- P037-T10(v): the two whole allocation vectors are independent,
and any two school-treatment indicators from different blocks have
zero covariance. The probability factorization concerns whole blocks. -/
theorem between_block_independence :
    (∀ u v, twoBlockDesign.weight (u,v) =
      oneBlockDesign.weight u * oneBlockDesign.weight v) ∧
    (∀ i j, designCovariance twoBlockDesign
      (fun w => blockTreatment w.1 i) (fun w => blockTreatment w.2 j) = 0) := by
  constructor
  · intro u v; norm_num [twoBlockDesign, oneBlockDesign]
  · intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [designCovariance, designMean, twoBlockDesign, blockTreatment,
        treatedPair, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- SI p. 17: s_i denotes a treated school, z_i direct seed invitation,
t_i = z'θ_i the seed-peer count and r_i = (z∘γ)'θ_i the referent-seed-peer
count. Integer indicators and natural counts preserve the printed products. -/
structure ExposureConfiguration where
  school : ℕ
  seed : ℕ
  peers : ℕ
  referentPeers : ℕ

/-- Design-feasible exposure configurations: binary school/seed indicators,
seeds only in treated schools, and referent seed peers a subset of seed peers.
These are SI pp. 16--17's design and adjacency-vector constraints. -/
def ExposureConfiguration.Feasible (x : ExposureConfiguration) : Prop :=
  x.school ≤ 1 ∧ x.seed ≤ x.school ∧ x.referentPeers ≤ x.peers

/-- SI p. 17: "Control exposure", "School exposure", "Non social
referent seed exposure", "Social referent seed exposure", "Direct treatment
condition". Distinct constructors preserve distinct potential outcomes. -/
inductive Exposure | control | school | nonreferent | referent | direct
  deriving DecidableEq

/-- The five exposure conditions literally printed on SI p. 17.
The nonreferent line omits (1-z_i) and I(t_i>0). -/
def printedExposureCondition (x : ExposureConfiguration) : Exposure → Prop
  | .control => x.school = 0
  | .school => x.school = 1 ∧ x.seed = 0 ∧ x.peers = 0
  | .nonreferent => x.school = 1 ∧ x.referentPeers = 0
  | .referent => x.school = 1 ∧ x.seed = 0 ∧ 0 < x.referentPeers
  | .direct => x.seed = 1

/-- P037-T8 repairs the SI p. 17 nonreferent line by adding both missing
factors. On feasible configurations these predicates express the corrected indicator products. -/
def correctedExposureCondition (x : ExposureConfiguration) : Exposure → Prop
  | .control => x.school = 0
  | .school => x.school = 1 ∧ x.seed = 0 ∧ x.peers = 0
  | .nonreferent => x.school = 1 ∧ x.seed = 0 ∧ 0 < x.peers ∧ x.referentPeers = 0
  | .referent => x.school = 1 ∧ x.seed = 0 ∧ 0 < x.referentPeers
  | .direct => x.seed = 1

/-- P037-T7: the explicit feasible configurations (1,0,0,0) and
(1,1,0,0) each activate two different printed exposure cases. -/
theorem printed_exposure_counterexamples :
    ExposureConfiguration.Feasible ⟨1,0,0,0⟩ ∧
    printedExposureCondition ⟨1,0,0,0⟩ .school ∧
    printedExposureCondition ⟨1,0,0,0⟩ .nonreferent ∧
    Exposure.school ≠ Exposure.nonreferent ∧
    ExposureConfiguration.Feasible ⟨1,1,0,0⟩ ∧
    printedExposureCondition ⟨1,1,0,0⟩ .nonreferent ∧
    printedExposureCondition ⟨1,1,0,0⟩ .direct ∧
    Exposure.nonreferent ≠ Exposure.direct := by
  simp [ExposureConfiguration.Feasible, printedExposureCondition]

/-- P037-T7(iii): every printed school-exposure configuration also
satisfies the nonreferent condition; a seed with no referent seed peers
likewise activates both nonreferent and direct conditions. -/
theorem printed_exposure_overlaps (x : ExposureConfiguration)
    (hx : x.Feasible) :
    (printedExposureCondition x .school → printedExposureCondition x .nonreferent) ∧
    (x.school = 1 → x.seed = 1 → x.referentPeers = 0 →
      printedExposureCondition x .nonreferent ∧ printedExposureCondition x .direct) := by
  simp only [ExposureConfiguration.Feasible] at hx
  simp only [printedExposureCondition]
  constructor
  · rintro ⟨hs, _, ht⟩; exact ⟨hs, by omega⟩
  · intro hs hz hr; exact ⟨⟨hs, hr⟩, hz⟩

/-- P037-T7's conclusion: the printed conditions cannot all be
the cases of a single-valued mapping on design-feasible configurations. -/
theorem printed_exposure_not_single_valued :
    ¬ ∃ f : ExposureConfiguration → Exposure,
      ∀ x, x.Feasible → ∀ e, printedExposureCondition x e → f x=e := by
  rintro ⟨f, hf⟩
  have hS := hf ⟨1,0,0,0⟩ (by simp [ExposureConfiguration.Feasible])
    .school (by simp [printedExposureCondition])
  have hN := hf ⟨1,0,0,0⟩ (by simp [ExposureConfiguration.Feasible])
    .nonreferent (by simp [printedExposureCondition])
  have hbad : Exposure.school=Exposure.nonreferent := hS.symm.trans hN
  cases hbad

/-- P037-T8: for all design-feasible configurations, the five repaired
exposure cases are exhaustive and pairwise disjoint, with no peer-count cap. -/
theorem corrected_exposure_partition (x : ExposureConfiguration) (hx : x.Feasible) :
    ∃! e : Exposure, correctedExposureCondition x e := by
  rcases hx with ⟨hs, hz, hr⟩
  by_cases h0 : x.school = 0
  · refine ⟨.control, h0, ?_⟩
    intro e he; cases e <;> simp_all [correctedExposureCondition] <;> omega
  have h1 : x.school = 1 := by omega
  by_cases hd : x.seed = 1
  · refine ⟨.direct, hd, ?_⟩
    intro e he; cases e <;> simp_all [correctedExposureCondition]
  have hz0 : x.seed = 0 := by omega
  by_cases ht : x.peers = 0
  · refine ⟨.school, ⟨h1, hz0, ht⟩, ?_⟩
    intro e he; cases e <;> simp_all [correctedExposureCondition] <;> omega
  by_cases hrr : x.referentPeers = 0
  · refine ⟨.nonreferent, ⟨h1, hz0, by omega, hrr⟩, ?_⟩
    intro e he; cases e <;> simp_all [correctedExposureCondition]
  · refine ⟨.referent, ⟨h1, hz0, by omega⟩, ?_⟩
    intro e he; cases e <;> simp_all [correctedExposureCondition]

/-- SI pp. 14,18, corrected P037-T9: "1/J sum I[f(z^ell,θ_i)=d_k]".
The mean is over indicators of the individual draws, not their category labels. -/
noncomputable def exposureFrequency {A : Type*} [DecidableEq A]
    (J : ℕ) (draws : Fin J → A) (target : A) : ℝ :=
  (∑ j, if draws j = target then (1:ℝ) else 0) / J

/-- P037-T9(iii): two coded exposures 0 and 1 give corrected frequency
1/2, the printed repeated-last-draw formula 1, and the formula repaired
only in the superscript 0. The coding is only for this arithmetic example. -/
theorem exposure_frequency_printed_example :
    exposureFrequency 2 (![0,1] : Fin 2 → ℕ) 1 = 1/2 ∧
    (if ((1:ℝ)+1)/2 = 1 then (1:ℝ) else 0) = 1 ∧
    (if ((0:ℝ)+1)/2 = 1 then (1:ℝ) else 0) = 0 := by
  unfold exposureFrequency
  rw [Fin.sum_univ_two]
  norm_num

/-- P037-T9(iii): under any real coding of exposures, the printed
constant-summand average is just the last draw's single 0/1 indicator. -/
theorem printed_monte_carlo_last_draw (J : ℕ) (hJ : 0 < J) (v target : ℝ) :
    (if (∑ _ : Fin J, v)/(J:ℝ)=target then (1:ℝ) else 0) =
      (if v=target then (1:ℝ) else 0) := by
  have hJ0 : (J:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hJ
  have hmean : (∑ _ : Fin J, v)/(J:ℝ)=v := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hmean]

/-- P037-T9(i): the indicator of any exposure event has expectation
its exposure probability and variance π(1-π). No independence is needed
for this individual-draw identity. -/
theorem exposure_indicator_moments {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (event : Ω → Prop) [DecidablePred event] :
    let X := fun w => if event w then (1:ℝ) else 0
    designVariance d X = designMean d X * (1-designMean d X) := by
  dsimp
  have hx : (fun w => (if event w then (1:ℝ) else 0)^2) =
      (fun w => if event w then (1:ℝ) else 0) := by
    funext w; split_ifs <;> norm_num
  rw [designVariance, hx]
  ring

/-- P037-T11(1): SI p. 19's regression-augmented inverse-probability
term, with fixed prediction g and exact exposure probability π. -/
noncomputable def augmentedContribution (I pi y g : ℝ) : ℝ :=
  g + I/pi*(y-g)

/-- P037-T11(1): exact unbiasedness of each fixed-prediction contribution.
The hypothesis E[I]=π is the exposure probability in SI p. 18. -/
theorem augmented_contribution_unbiased {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (I : Ω → ℝ) (pi y g : ℝ)
    (hpi : pi ≠ 0) (hI : designMean d I = pi) :
    designMean d (fun w => augmentedContribution (I w) pi y g) = y := by
  have hi : (fun w => augmentedContribution (I w) pi y g) =
      (fun w => g + ((y-g)/pi)*I w) := by
    funext w; unfold augmentedContribution; ring
  rw [hi, designMean_add, designMean_const, designMean_mul, hI]
  field_simp
  ring

/-- P037-T11(3): uniform outcome/prediction bounds and a probability
lower bound imply the bound H=K+2K/η for every realization. -/
theorem augmented_contribution_bound (I pi y g K eta : ℝ)
    (hI : I=0 ∨ I=1) (heta : 0 < eta) (hpi : eta ≤ pi)
    (hy : |y| ≤ K) (hg : |g| ≤ K) :
    |augmentedContribution I pi y g| ≤ K + 2*K/eta := by
  have hpi0 : 0 < pi := lt_of_lt_of_le heta hpi
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hy
  have hdiff : |y-g| ≤ 2*K := by
    calc |y-g| ≤ |y|+|g| := abs_sub _ _
         _ ≤ 2*K := by linarith
  rcases hI with hI | hI
  · simp [augmentedContribution, hI]
    have : 0 ≤ 2*K/eta := by positivity
    linarith
  · have hd : |y-g|/pi ≤ 2*K/eta := by
      exact div_le_div₀ (by positivity) hdiff heta hpi
    calc
      |augmentedContribution I pi y g| ≤ |g| + |(y-g)/pi| := by
        simpa [augmentedContribution, hI, div_eq_mul_inv, mul_comm] using
          abs_add_le g ((y-g)/pi)
      _ = |g| + |y-g|/pi := by rw [abs_div, abs_of_pos hpi0]
      _ ≤ K+2*K/eta := by linarith

/-- Variance of a finite sum is the sum of all ordered covariances.
This exact identity permits unrestricted within-block dependence. -/
theorem designVariance_sum_covariances {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (X : I → Ω → ℝ) :
    designVariance d (fun w => ∑ i, X i w) = ∑ i, ∑ j, designCovariance d (X i) (X j) := by
  have hs : (fun w => (∑ i, X i w)^2) = (fun w => ∑ i, ∑ j, X i w*X j w) := by
    funext w; rw [pow_two, Finset.sum_mul]; simp_rw [Finset.mul_sum]
  unfold designVariance designCovariance
  rw [hs, designMean_sum, designMean_sum]
  simp_rw [designMean_sum]
  simp only [Finset.sum_sub_distrib, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [mul_comm]

/-- Exact product-of-sums factorization for finite block assignment
spaces. This is the normalization and independence of the product law. -/
theorem finite_product_factorization {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (f : ∀ i, Ω i → ℝ) :
    (∑ w : ∀ i, Ω i, ∏ i, f i (w i)) = ∏ i, ∑ z, f i z := by
  classical
  symm
  simpa using Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Ω i))) f

/-- Product finite design of entire blocks; arbitrary dependence
inside each block is encoded by that block's own finite law. -/
noncomputable def productDesign {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (d : ∀ i, FiniteDesign (Ω i)) :
    FiniteDesign (∀ i, Ω i) where
  weight := fun w => ∏ i, (d i).weight (w i)
  nonneg := fun w => Finset.prod_nonneg (fun i _ => (d i).nonneg (w i))
  total := by rw [finite_product_factorization]; simp_rw [FiniteDesign.total]; simp

/-- Products of block-specific random quantities have factorizing
expectations under independently randomized block laws. -/
theorem product_design_mean_product {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (d : ∀ i, FiniteDesign (Ω i))
    (X : ∀ i, Ω i → ℝ) :
    designMean (productDesign d) (fun w => ∏ i, X i (w i)) =
      ∏ i, designMean (d i) (X i) := by
  unfold designMean
  change (∑ w : ∀ i, Ω i, (∏ i, (d i).weight (w i))*(∏ i, X i (w i))) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact finite_product_factorization (fun i z => (d i).weight z * X i z)

/-- A block-specific factor extended by one to the other block
coordinates; dependent assignment types are transported only on equality. -/
noncomputable def coordinateFactor {I : Type*} {Ω : I → Type*}
    (j : I) (X : Ω j → ℝ) : ∀ i, Ω i → ℝ := by
  classical
  exact fun i z => if h : i=j then X (h ▸ z) else 1

/-- Extending a block factor leaves its own coordinate function
unchanged; this is only the representation of a block variable. -/
theorem coordinateFactor_self {I : Type*} {Ω : I → Type*}
    (j : I) (X : Ω j → ℝ) : coordinateFactor j X j = X := by
  funext z
  simp [coordinateFactor]

/-- An extended block factor is the constant one on every other
coordinate, so it introduces no extra random contribution. -/
theorem coordinateFactor_other {I : Type*} {Ω : I → Type*}
    (j : I) (X : Ω j → ℝ) (i : I) (h : i≠j) :
    coordinateFactor j X i = fun _ => (1:ℝ) := by
  funext z
  simp [coordinateFactor, h]

/-- The product of the extended coordinate factors recovers the
original block variable, rather than replacing it by an independent copy. -/
theorem coordinateFactor_product {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} (j : I) (X : Ω j → ℝ) (w : ∀ i, Ω i) :
    (∏ i, coordinateFactor j X i (w i))=X (w j) := by
  classical
  rw [Finset.prod_eq_single j]
  · simp [coordinateFactor]
  · intro i _ hij; simp [coordinateFactor, hij]
  · simp

/-- A block variable's marginal mean under the joint product law
is its original block-law mean. -/
theorem product_design_coordinate_mean {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (d : ∀ i, FiniteDesign (Ω i))
    (j : I) (X : Ω j → ℝ) :
    designMean (productDesign d) (fun w => X (w j)) = designMean (d j) X := by
  classical
  have hf : (fun w : ∀ i, Ω i => X (w j)) =
      (fun w => ∏ i, coordinateFactor j X i (w i)) := by
    funext w; exact (coordinateFactor_product j X w).symm
  rw [hf, product_design_mean_product]
  have hm : ∀ i, designMean (d i) (coordinateFactor j X i) =
      if i=j then designMean (d j) X else 1 := by
    intro i; by_cases h : i=j
    · subst i; simp [coordinateFactor_self]
    · rw [coordinateFactor_other j X i h, designMean_const, if_neg h]
  simp_rw [hm]
  simp

/-- P037-T11(2): independent block assignments give independent
block-specific totals; all mixed products have factorizing means. -/
theorem product_design_coordinate_pair {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (d : ∀ i, FiniteDesign (Ω i))
    (j k : I) (hjk : j≠k) (X : Ω j → ℝ) (Y : Ω k → ℝ) :
    designMean (productDesign d) (fun w => X (w j)*Y (w k)) =
      designMean (d j) X*designMean (d k) Y := by
  classical
  have hf : (fun w : ∀ i, Ω i => X (w j)*Y (w k)) =
      (fun w => ∏ i, coordinateFactor j X i (w i)*coordinateFactor k Y i (w i)) := by
    funext w
    rw [Finset.prod_mul_distrib, coordinateFactor_product, coordinateFactor_product]
  rw [hf, product_design_mean_product d (fun i z => coordinateFactor j X i z*coordinateFactor k Y i z)]
  have hi : ∀ i, designMean (d i)
      (fun z => coordinateFactor j X i z*coordinateFactor k Y i z) =
      designMean (d i) (coordinateFactor j X i)*designMean (d i) (coordinateFactor k Y i) := by
    intro i
    by_cases hij : i=j
    · subst i
      simp only [coordinateFactor_self, coordinateFactor_other k Y j hjk,
        mul_one, designMean_const]
    by_cases hik : i=k
    · subst i
      simp only [coordinateFactor_self, coordinateFactor_other j X k (Ne.symm hjk),
        one_mul, designMean_const]
    · simp only [coordinateFactor_other j X i hij, coordinateFactor_other k Y i hik,
        one_mul, designMean_const]
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  have hj : (∏ i, designMean (d i) (coordinateFactor j X i)) = designMean (d j) X := by
    rw [← product_design_mean_product]
    simp_rw [coordinateFactor_product]
    exact product_design_coordinate_mean d j X
  have hk : (∏ i, designMean (d i) (coordinateFactor k Y i)) = designMean (d k) Y := by
    rw [← product_design_mean_product]
    simp_rw [coordinateFactor_product]
    exact product_design_coordinate_mean d k Y
  rw [hj,hk]

/-- P037-T11(4): variance of the sum of independent block-specific
totals is the sum of their variances, under the actual product law. -/
theorem product_design_sum_variance {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (d : ∀ i, FiniteDesign (Ω i))
    (X : ∀ i, Ω i → ℝ) :
    designVariance (productDesign d) (fun w => ∑ i, X i (w i)) =
      ∑ i, designVariance (d i) (X i) := by
  classical
  rw [designVariance_sum_covariances]
  apply Finset.sum_congr rfl; intro i _
  calc
    _ = ∑ j, if j=i then designVariance (d i) (X i) else 0 := by
      apply Finset.sum_congr rfl; intro j _
      by_cases h : j=i
      · subst j
        simp only [if_true, designCovariance, designVariance, pow_two]
        rw [product_design_coordinate_mean d i (fun z => X i z*X i z),
          product_design_coordinate_mean d i (X i)]
      · simp only [if_neg h, designCovariance]
        rw [product_design_coordinate_pair d i j (Ne.symm h),
          product_design_coordinate_mean, product_design_coordinate_mean]
        ring
    _ = _ := by simp

/-- P037-T1's fixed eligible referent fractions for SI Eq. (2), pp. 13--14:
q=(1/10,1/10,3/10,3/10). Every school has four strata of ten eligibles,
with one or three referents per stratum. -/
noncomputable def witnessEligibleFraction (i : Fin 4) : ℝ :=
  if i.val < 2 then 1/10 else 3/10

/-- Exact hypergeometric seed draw in one stratum: choose five of ten
uniformly without replacement, r of the ten being referents. The Fin 4
count range is sufficient for the witness's r=1 or r=3.
This implements the SI p. 6 half-of-eligibles draw. -/
noncomputable def stratumCountMass (r : ℕ) (k : Fin 4) : ℝ :=
  (r.choose k.val : ℝ) * ((10-r).choose (5-k.val) : ℝ) / (10:ℕ).choose 5

/-- P037-T1(i), structured seed-law certificate: the two stratum
hypergeometric laws are normalized and have their exact first and second
moments. The four-stratum convolution is proved in `school_count_moments`. -/
theorem stratum_moment_certificates :
    (∑ k, stratumCountMass 1 k)=1 ∧
    (∑ k, stratumCountMass 1 k*(k.val:ℝ))=1/2 ∧
    (∑ k, stratumCountMass 1 k*(k.val:ℝ)^2)=1/2 ∧
    (∑ k, stratumCountMass 3 k)=1 ∧
    (∑ k, stratumCountMass 3 k*(k.val:ℝ))=3/2 ∧
    (∑ k, stratumCountMass 3 k*(k.val:ℝ)^2)=17/6 ∧
    (1/10:ℝ)*(1-1/10)/36=1/400 ∧
    (3/10:ℝ)*(1-3/10)/36=7/1200 := by
  norm_num [Fin.sum_univ_four, stratumCountMass, Nat.choose]

/-- Sum the four independent stratum counts to obtain the number K
of referent seeds in one school. The seed-group fraction is K/20.
This is an exact finite convolution, not a fitted or postulated moment law. -/
noncomputable def schoolCountMass (r : ℕ) (k : Fin 13) : ℝ :=
  ∑ c : Fin 4 → Fin 4,
    if (∑ s, (c s).val) = k.val then ∏ s, stratumCountMass r (c s) else 0

/-- P037-T1(i), finite convolution identity for the exact five-of-ten
seed law: summing a function of the total count against its
quotient law equals summing over the four actual stratum counts. -/
theorem school_count_pushforward (r : ℕ) (f : ℝ → ℝ) :
    (∑ k, schoolCountMass r k * f (k.val:ℝ)) =
      ∑ c : Fin 4 → Fin 4, (∏ s, stratumCountMass r (c s)) *
        f (∑ s, ((c s).val:ℝ)) := by
  classical
  unfold schoolCountMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  have hbound : (∑ s, (c s).val) < 13 := by
    rw [Fin.sum_univ_four]
    have h0 := (c 0).isLt
    have h1 := (c 1).isLt
    have h2 := (c 2).isLt
    have h3 := (c 3).isLt
    omega
  let total : Fin 13 := ⟨∑ s, (c s).val, hbound⟩
  have heq : ∀ k : Fin 13, (∑ s, (c s).val) = k.val ↔ k = total := by
    intro k
    exact ⟨fun h => Fin.ext h.symm, fun h => by subst k; rfl⟩
  simp_rw [heq, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [total, Nat.cast_sum]

/-- Nonnegativity of every hypergeometric stratum mass in the witness;
this is an elementary property of the binomial-count formula. -/
theorem stratum_count_nonneg (r : ℕ) (k : Fin 4) :
    0 ≤ stratumCountMass r k := by
  unfold stratumCountMass
  positivity

/-- The true one-stratum law, used for the product calculation in
P037-T1(i). Only the witness's r=1 or r=3 is used with this truncated support. -/
noncomputable def witnessStratumDesign (r : ℕ) (hr : r=1 ∨ r=3) :
    FiniteDesign (Fin 4) where
  weight := stratumCountMass r
  nonneg := stratum_count_nonneg r
  total := by
    rcases hr with rfl | rfl
    · exact stratum_moment_certificates.1
    · exact stratum_moment_certificates.2.2.2.1

/-- P037-T1(i): four independent genuine hypergeometric strata give
normalized total-count masses, means 2 and 6, and second moments 5 and
115/3. The proof factors the product law and passes through the count quotient. -/
theorem school_count_moments (r : ℕ) (hr : r=1 ∨ r=3) :
    (∑ k, schoolCountMass r k) = 1 ∧
    (∑ k, schoolCountMass r k*(k.val:ℝ)) = 2*r ∧
    (∑ k, schoolCountMass r k*(k.val:ℝ)^2) =
      if r=1 then 5 else 115/3 := by
  let d := witnessStratumDesign r hr
  let ds := fun _ : Fin 4 => d
  have hm : designMean d (fun k => (k.val:ℝ)) = (r:ℝ)/2 := by
    rcases hr with rfl | rfl
    · simpa [d, designMean, witnessStratumDesign] using stratum_moment_certificates.2.1
    · simpa [d, designMean, witnessStratumDesign] using stratum_moment_certificates.2.2.2.2.1
  have hv : designVariance d (fun k => (k.val:ℝ)) =
      if r=1 then 1/4 else 7/12 := by
    unfold designVariance
    rw [hm]
    rcases hr with rfl | rfl
    · change (∑ k, stratumCountMass 1 k * (k.val:ℝ)^2) - _ = _
      rw [stratum_moment_certificates.2.2.1]
      norm_num
    · change (∑ k, stratumCountMass 3 k * (k.val:ℝ)^2) - _ = _
      rw [stratum_moment_certificates.2.2.2.2.2.1]
      norm_num
  have hmean : designMean (productDesign ds)
      (fun c => ∑ s, ((c s).val:ℝ)) = 2*r := by
    rw [designMean_sum]
    simp only [product_design_coordinate_mean ds (X := fun k => (k.val:ℝ)),
      ds, hm, Fin.sum_univ_four]
    ring
  have hvar : designVariance (productDesign ds)
      (fun c => ∑ s, ((c s).val:ℝ)) =
        if r=1 then 1 else 7/3 := by
    rw [product_design_sum_variance ds (fun _ k => (k.val:ℝ))]
    simp only [ds, hv, Fin.sum_univ_four]
    rcases hr with rfl | rfl <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · have hh := school_count_pushforward r (fun _ => (1:ℝ))
    simp only [mul_one] at hh
    rw [hh]
    exact (productDesign ds).total
  · rw [school_count_pushforward r (fun x => x)]
    exact hmean
  · rw [school_count_pushforward r (fun x => x^2)]
    change designMean (productDesign ds) (fun c => (∑ s, ((c s).val:ℝ))^2) = _
    unfold designVariance at hvar
    rw [hmean] at hvar
    rcases hr with rfl | rfl <;> norm_num at hvar ⊢ <;> linarith

/-- P037-T1's count quotient has no negative mass, since each retained
summand is a product of nonnegative hypergeometric probabilities. -/
theorem school_count_nonneg (r : ℕ) (k : Fin 13) :
    0 ≤ schoolCountMass r k := by
  unfold schoolCountMass
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact Finset.prod_nonneg (fun s _ => stratum_count_nonneg r (c s))
  · exact le_rfl

/-- P037-T1(ii): every count 0,...,4 is feasible in both eligible-pool
types. An explicit stratum-count tuple using only zeros and ones has positive
mass, so this is common support under the genuine hypergeometric design. -/
theorem school_count_common_support (r : ℕ) (hr : r=1 ∨ r=3)
    (k : Fin 13) (hk : k.val ≤ 4) : 0 < schoolCountMass r k := by
  let c : Fin 4 → Fin 4 := fun s => if s.val < k.val then 1 else 0
  have hcount : (∑ s, (c s).val) = k.val := by
    fin_cases k <;> norm_num at hk <;> norm_num [c, Fin.sum_univ_four]
  have hpos : 0 < ∏ s, stratumCountMass r (c s) := by
    apply Finset.prod_pos
    intro s _
    dsimp [c]
    split_ifs <;> rcases hr with rfl | rfl <;>
      norm_num [stratumCountMass, Nat.choose]
  have hle : (∏ s, stratumCountMass r (c s)) ≤ schoolCountMass r k := by
    unfold schoolCountMass
    have hh := Finset.single_le_sum (f := fun v : Fin 4 → Fin 4 =>
      if (∑ s, (v s).val) = k.val then ∏ s, stratumCountMass r (v s) else 0)
      (s := Finset.univ) (a := c) (fun v _ => by
        split_ifs
        · exact Finset.prod_nonneg (fun s _ => stratum_count_nonneg r (v s))
        · exact le_rfl) (Finset.mem_univ c)
    simpa only [hcount, ite_true] using hh
  exact lt_of_lt_of_le hpos hle

/-- Conditional expectation over the two independently drawn treated-school
seed counts in P037-T1, before averaging the six school allocations. -/
noncomputable def pairCountMean (r s : ℕ) (f : Fin 13 → Fin 13 → ℝ) : ℝ :=
  ∑ k, ∑ l, schoolCountMass r k * schoolCountMass s l * f k l

/-- Finite independence certificate used to evaluate P037-T1's pair law:
the mean of a product of separate count functions is the product of means. -/
theorem pair_count_factorization (r s : ℕ) (f g : Fin 13 → ℝ) :
    pairCountMean r s (fun k l => f k*g l) =
      (∑ k, schoolCountMass r k*f k)*(∑ l, schoolCountMass s l*g l) := by
  unfold pairCountMean
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The two-school count law is normalized, so constants retain their
value; P037-T1(i), conditional on its school-treatment allocation. -/
theorem pair_count_mean_const (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3)
    (a : ℝ) : pairCountMean r s (fun _ _ => a) = a := by
  have hh := pair_count_factorization r s (fun _ => a) (fun _ => (1:ℝ))
  simpa [← Finset.sum_mul, (school_count_moments r hr).1,
    (school_count_moments s hs).1] using hh

/-- P037-T1(i): the marginal treated composition is q=r/10 or s/10,
because each school's four independent seed strata draw half the eligibles. -/
theorem pair_count_mean_first (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun k _ => (k.val:ℝ)/20) = (r:ℝ)/10 := by
  have hh := pair_count_factorization r s (fun k => (k.val:ℝ)/20) (fun _ => (1:ℝ))
  simp only [mul_one, ← mul_div_assoc, ← Finset.sum_div,
    (school_count_moments r hr).2.1, (school_count_moments s hs).1] at hh
  exact hh.trans (by ring)

/-- The second treated school's composition has mean q=s/10 in the
same exact product law; P037-T1(i). -/
theorem pair_count_mean_second (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun _ l => (l.val:ℝ)/20) = (s:ℝ)/10 := by
  have hh := pair_count_factorization r s (fun _ => (1:ℝ)) (fun l => (l.val:ℝ)/20)
  simp only [one_mul, mul_one, ← mul_div_assoc, ← Finset.sum_div,
    (school_count_moments s hs).2.1, (school_count_moments r hr).1] at hh
  exact hh.trans (by ring)

/-- P037-T1(i): first-school composition second moment, derived from
the actual four-stratum convolution: 1/80 or 23/240. -/
theorem pair_count_mean_first_sq (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun k _ => ((k.val:ℝ)/20)^2) =
      if r=1 then 1/80 else 23/240 := by
  have hh := pair_count_factorization r s (fun k => (k.val:ℝ)^2/400) (fun _ => (1:ℝ))
  have heq : (fun (k _l : Fin 13) => ((k.val:ℝ)/20)^2) =
      (fun k _l => (k.val:ℝ)^2/400) := by funext k l; ring
  rw [heq]
  have hc := (school_count_moments r hr).2.2
  simp only [mul_one, ← mul_div_assoc, ← Finset.sum_div, hc,
    (school_count_moments s hs).1] at hh
  rcases hr with rfl | rfl <;> norm_num at hh ⊢ <;> exact hh

/-- P037-T1(i): the second treated school's analogous second moment. -/
theorem pair_count_mean_second_sq (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun _ l => ((l.val:ℝ)/20)^2) =
      if s=1 then 1/80 else 23/240 := by
  have hh := pair_count_factorization r s (fun _ => (1:ℝ)) (fun l => (l.val:ℝ)^2/400)
  have heq : (fun (_k l : Fin 13) => ((l.val:ℝ)/20)^2) =
      (fun _k l => (l.val:ℝ)^2/400) := by funext k l; ring
  rw [heq]
  have hc := (school_count_moments s hs).2.2
  simp only [one_mul, mul_one, ← mul_div_assoc, ← Finset.sum_div, hc,
    (school_count_moments r hr).1] at hh
  rcases hs with rfl | rfl <;> norm_num at hh ⊢ <;> exact hh

/-- Conditional independence of the two treated-school seed draws:
their composition cross moment is the product of their means (T1(i),(iii)). -/
theorem pair_count_mean_product (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun k l => (k.val:ℝ)/20*((l.val:ℝ)/20)) =
      ((r:ℝ)/10)*((s:ℝ)/10) := by
  rw [pair_count_factorization]
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div,
    (school_count_moments r hr).2.1, (school_count_moments s hs).2.1]
  ring

/-- Product form of the first composition's second moment, T1(i),(iii). -/
theorem pair_count_mean_first_self (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun k _ => (k.val:ℝ)/20*((k.val:ℝ)/20)) =
      if r=1 then 1/80 else 23/240 := by
  simpa only [pow_two] using pair_count_mean_first_sq r s hr hs

/-- Product form of the second composition's second moment, T1(i),(iii). -/
theorem pair_count_mean_second_self (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun _ l => (l.val:ℝ)/20*((l.val:ℝ)/20)) =
      if s=1 then 1/80 else 23/240 := by
  simpa only [pow_two] using pair_count_mean_second_sq r s hr hs

/-- Reversing the product of the independent composition draws has the
same cross moment; the indices remain the two actual treated schools. -/
theorem pair_count_mean_reverse_product (r s : ℕ) (hr : r=1 ∨ r=3) (hs : s=1 ∨ s=3) :
    pairCountMean r s (fun k l => (l.val:ℝ)/20*((k.val:ℝ)/20)) =
      ((r:ℝ)/10)*((s:ℝ)/10) := by
  have heq : (fun (k l : Fin 13) => (l.val:ℝ)/20*((k.val:ℝ)/20)) =
      (fun k l => (k.val:ℝ)/20*((l.val:ℝ)/20)) := by funext k l; ring
  rw [heq, pair_count_mean_product r s hr hs]

/-- Number of referents among ten eligibles in each stratum of the
low/high-q schools; all eligible pools are fixed. -/
def witnessStratumReferents (i : Fin 4) : ℕ := if i.val < 2 then 1 else 3

/-- Collapse full seed assignments to their two treated-school counts.
Zero-weight counts are retained. SI's school and seed randomizations are
independent; seed draws are independent across strata and treated schools. -/
abbrev CompositionState := Fin 6 × Fin 13 × Fin 13

/-- Probability of a treatment pair and its two composition counts in
P037-T1; the hypergeometric convolutions derive the exact quotient law. -/
noncomputable def witnessStateMass (w : CompositionState) : ℝ :=
  (1/6) * schoolCountMass (witnessStratumReferents (treatedPair w.1).1) w.2.1 *
    schoolCountMass (witnessStratumReferents (treatedPair w.1).2) w.2.2

/-- C_iD_i in SI Eq. (2), zero for a control school and K_i/20 for
either treated school in the counterexample. -/
noncomputable def witnessInteraction (w : CompositionState) (i : Fin 4) : ℝ :=
  if i = (treatedPair w.1).1 then (w.2.1.val:ℝ)/20 else
  if i = (treatedPair w.1).2 then (w.2.2.val:ℝ)/20 else 0

/-- P037-T1's fixed school potential outcomes: control 3/10; treated
3/10-q_i for every seed set/composition c. The school-level paper does
not supply potential-outcome notation. -/
noncomputable def witnessPotentialOutcome (i : Fin 4) (treated : Bool) (_c : ℝ) : ℝ :=
  if treated then 3/10-witnessEligibleFraction i else 3/10

/-- Observed outcome of that fixed schedule under the school assignment. -/
noncomputable def witnessObservedOutcome (w : CompositionState) (i : Fin 4) : ℝ :=
  3/10 - blockTreatment w.1 i*witnessEligibleFraction i

/-- The profiled cross-product x'My for one block, M=I_4-11'/4.
This removes a block intercept in each realized assignment, not after
replacing random regressors by their expectations. -/
noncomputable def blockCross (x y : Fin 4 → ℝ) : ℝ :=
  (∑ i, x i*y i) - (∑ i, x i)*(∑ i, y i)/4

/-- Columns (D,q,DC) in the expected normal equations for SI Eq. (2).
The column order (D,q,DC) is explicit. -/
noncomputable def witnessColumns (w : CompositionState) (k : Fin 3) : Fin 4 → ℝ :=
  ![blockTreatment w.1, witnessEligibleFraction, witnessInteraction w] k

/-- Exact expectation over P037-T1's finite count-collapsed law. -/
noncomputable def witnessMean (X : CompositionState → ℝ) : ℝ :=
  ∑ w, witnessStateMass w * X w

/-- G=E[X'MX] and h=E[X'MY], the population
normal equations of the printed composition regression. -/
noncomputable def witnessGram : Matrix (Fin 3) (Fin 3) ℝ :=
  fun k l => witnessMean (fun w => blockCross (witnessColumns w k) (witnessColumns w l))

/-- Right-hand side h of the same expected, block-profiled equations. -/
noncomputable def witnessRhs : Fin 3 → ℝ :=
  fun k => witnessMean (fun w => blockCross (witnessColumns w k) (witnessObservedOutcome w))

/-- P037-T1(i),(iii): split the exact count-quotient expectation into
the six school allocations and their independent treated-school count laws. -/
theorem witness_mean_split (X : CompositionState → ℝ) :
    witnessMean X = ∑ p : Fin 6, (1/6:ℝ) *
      pairCountMean (witnessStratumReferents (treatedPair p).1)
        (witnessStratumReferents (treatedPair p).2) (fun k l => X (p,k,l)) := by
  simp [witnessMean, witnessStateMass, Fintype.sum_prod_type,
    pairCountMean, Finset.mul_sum, mul_assoc]

/-- The witness is a genuine normalized randomization law,
not merely a list of asserted regression moments (P037-T1(i)). -/
theorem witness_state_probability_law :
    (∀ w, 0 ≤ witnessStateMass w) ∧ (∑ w, witnessStateMass w) = 1 := by
  constructor
  · intro w
    exact mul_nonneg (mul_nonneg (by norm_num)
      (school_count_nonneg _ _)) (school_count_nonneg _ _)
  · have hh := witness_mean_split (fun _ => (1:ℝ))
    simp only [witnessMean, mul_one] at hh
    rw [hh]
    norm_num [Fin.sum_univ_succ, treatedPair, witnessStratumReferents,
      pair_count_mean_const]

/-- Addition is linear under P037-T1's actual finite witness law. -/
theorem witness_mean_add (X Y : CompositionState → ℝ) :
    witnessMean (fun w => X w+Y w) = witnessMean X+witnessMean Y := by
  simp [witnessMean, mul_add, Finset.sum_add_distrib]

/-- Subtraction is linear under P037-T1's actual finite witness law. -/
theorem witness_mean_sub (X Y : CompositionState → ℝ) :
    witnessMean (fun w => X w-Y w) = witnessMean X-witnessMean Y := by
  simp [witnessMean, mul_sub, Finset.sum_sub_distrib]

/-- A fixed scalar factors out of P037-T1's actual witness expectation. -/
theorem witness_mean_mul (a : ℝ) (X : CompositionState → ℝ) :
    witnessMean (fun w => a*X w) = a*witnessMean X := by
  simp [witnessMean, Finset.mul_sum, mul_left_comm]

/-- A fixed scalar on the right also factors out of witness expectation. -/
theorem witness_mean_mul_right (X : CompositionState → ℝ) (a : ℝ) :
    witnessMean (fun w => X w*a) = witnessMean X*a := by
  simp [witnessMean, Finset.sum_mul, mul_assoc]

/-- A constant's witness expectation equals itself by genuine normalization. -/
theorem witness_mean_const (a : ℝ) : witnessMean (fun _ => a) = a := by
  rw [witnessMean, ← Finset.sum_mul, witness_state_probability_law.2, one_mul]

/-- Finite sums commute with the exact witness expectation, T1(iii). -/
theorem witness_mean_sum {I : Type*} [Fintype I] (X : I → CompositionState → ℝ) :
    witnessMean (fun w => ∑ i, X i w) = ∑ i, witnessMean (X i) := by
  simp only [witnessMean, Finset.mul_sum]
  rw [Finset.sum_comm]

set_option maxHeartbeats 2000000 in
/-- P037-T1(i),(iii): all school assignment and composition first and
cross moments, obtained by conditioning on the six allocations and factoring
the two actual count laws. The diagonal retains seed variance. -/
theorem witness_coordinate_moments :
    (∀ i, witnessMean (fun w => blockTreatment w.1 i) = 1/2 ∧
      witnessMean (fun w => witnessInteraction w i) = witnessEligibleFraction i/2) ∧
    (∀ i j,
      witnessMean (fun w => blockTreatment w.1 i*blockTreatment w.1 j) =
        if i=j then 1/2 else 1/6) ∧
    (∀ i j,
      witnessMean (fun w => blockTreatment w.1 i*witnessInteraction w j) =
        (if i=j then 1/2 else 1/6)*witnessEligibleFraction j) ∧
    (∀ i j,
      witnessMean (fun w => witnessInteraction w i*witnessInteraction w j) =
        (if i=j then 1/2 else 1/6)*witnessEligibleFraction i*witnessEligibleFraction j +
        if i=j then witnessEligibleFraction i*(1-witnessEligibleFraction i)/72 else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> constructor <;>
      norm_num [witness_mean_split, Fin.sum_univ_succ, treatedPair,
        witnessStratumReferents, blockTreatment, witnessInteraction,
        witnessEligibleFraction, pair_count_mean_const, pair_count_mean_first,
        pair_count_mean_second]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witness_mean_split, Fin.sum_univ_succ, treatedPair,
        witnessStratumReferents, blockTreatment, pair_count_mean_const]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witness_mean_split, Fin.sum_univ_succ, treatedPair,
        witnessStratumReferents, blockTreatment, witnessInteraction,
        witnessEligibleFraction, pair_count_mean_const, pair_count_mean_first,
        pair_count_mean_second]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witness_mean_split, Fin.sum_univ_succ, treatedPair,
        witnessStratumReferents, witnessInteraction, witnessEligibleFraction,
        pair_count_mean_const, pair_count_mean_product, pair_count_mean_first_self,
        pair_count_mean_second_self, pair_count_mean_reverse_product]

/-- Profile block effects in each realized block, then take expectations:
the cross-product is the diagonal moment sum minus a quarter of all ordered
cross moments. This is the actual M=I-11'/4 of P037-T1(iii). -/
theorem witness_mean_block_cross (X Y : CompositionState → Fin 4 → ℝ) :
    witnessMean (fun w => blockCross (X w) (Y w)) =
      (∑ i, witnessMean (fun w => X w i*Y w i)) -
        (1/4:ℝ)*(∑ i, ∑ j, witnessMean (fun w => X w i*Y w j)) := by
  have hp : (fun w => blockCross (X w) (Y w)) =
      (fun w => (∑ i, X w i*Y w i) - (1/4:ℝ)*(∑ i, ∑ j, X w i*Y w j)) := by
    funext w
    have hsum : (∑ i, X w i)*(∑ j, Y w j) = ∑ i, ∑ j, X w i*Y w j := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    rw [blockCross, hsum]
    ring
  rw [hp, witness_mean_sub, witness_mean_mul, witness_mean_sum,
    witness_mean_sum]
  simp_rw [witness_mean_sum]

/-- Reversing a school assignment/composition product preserves its mean;
the indices refer to the same witness assignment, not independent copies. -/
theorem witness_mean_composition_treatment (i j : Fin 4) :
    witnessMean (fun w => witnessInteraction w i*blockTreatment w.1 j) =
      (if i=j then 1/2 else 1/6)*witnessEligibleFraction i := by
  have heq : (fun w => witnessInteraction w i*blockTreatment w.1 j) =
      (fun w => blockTreatment w.1 j*witnessInteraction w i) := by
    funext w
    ring
  rw [heq, witness_coordinate_moments.2.2.1 j i]
  by_cases h : i=j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Division by a fixed scalar factors out of the finite witness mean. -/
theorem witness_mean_div (X : CompositionState → ℝ) (a : ℝ) :
    witnessMean (fun w => X w/a) = witnessMean X/a := by
  simp only [div_eq_mul_inv, witness_mean_mul_right]

/-- P037-T1(iii): cross moments with Y_j=3/10-D_jq_j retain the
school-treatment interaction; only the fixed constant factors out. -/
theorem witness_mean_observed_product (X : CompositionState → ℝ) (j : Fin 4) :
    witnessMean (fun w => X w*witnessObservedOutcome w j) =
      (3/10:ℝ)*witnessMean X - witnessEligibleFraction j*
        witnessMean (fun w => X w*blockTreatment w.1 j) := by
  have heq : (fun w => X w*witnessObservedOutcome w j) =
      (fun w => (3/10:ℝ)*X w - witnessEligibleFraction j*(X w*blockTreatment w.1 j)) := by
    funext w
    unfold witnessObservedOutcome
    ring
  rw [heq, witness_mean_sub, witness_mean_mul, witness_mean_mul]

/-- P037-T1(iii): every entry of the population Gram matrix and RHS is
derived from actual design moments after centering each realized block. -/
theorem witness_expected_normal_equations :
    witnessGram = !![1,0,1/5; 0,1/25,1/50; 1/5,1/50,151/2400] ∧
    witnessRhs = ![-1/5,-1/50,-17/300] := by
  constructor
  · ext k l
    fin_cases k <;> fin_cases l <;>
      norm_num [witnessGram, witnessColumns, witness_mean_block_cross,
        Fin.sum_univ_four, witnessEligibleFraction, witness_mean_const,
        witness_mean_mul, witness_mean_mul_right, witness_mean_div,
        witness_coordinate_moments.1, witness_coordinate_moments.2.1,
        witness_coordinate_moments.2.2.1, witness_coordinate_moments.2.2.2,
        witness_mean_composition_treatment]
  · funext k
    fin_cases k <;>
      norm_num [witnessRhs, witnessColumns, witness_mean_block_cross,
        Fin.sum_univ_four, witness_mean_observed_product,
        witness_mean_mul, witness_mean_mul_right, witness_mean_div,
        witness_mean_const, witnessEligibleFraction,
        witness_coordinate_moments.1, witness_coordinate_moments.2.1,
        witness_coordinate_moments.2.2.1, witness_mean_composition_treatment]

/-- P037-T1(ii): composition has no effect in any school; the average
causal effect is exactly -1/5 for every c, including every feasible c. -/
theorem witness_zero_composition_effect :
    (∀ i c c', witnessPotentialOutcome i true c - witnessPotentialOutcome i true c' = 0) ∧
    (∀ c : ℝ, (∑ i : Fin 4, (witnessPotentialOutcome i true c - witnessPotentialOutcome i false c))/4 = -1/5) := by
  constructor
  · intro i c c'; simp [witnessPotentialOutcome]
  · intro c
    have hq : (∑ i : Fin 4, witnessEligibleFraction i) = 4/5 := by
      rw [Fin.sum_univ_four]
      norm_num [witnessEligibleFraction]
    have hf : (fun i : Fin 4 => witnessPotentialOutcome i true c - witnessPotentialOutcome i false c) =
        (fun i => -witnessEligibleFraction i) := by
      funext i; simp [witnessPotentialOutcome]
    have hs : (∑ i : Fin 4, (witnessPotentialOutcome i true c-witnessPotentialOutcome i false c)) =
        -4/5 := by
      calc
        _ = ∑ i : Fin 4, -witnessEligibleFraction i := Finset.sum_congr rfl (fun i _ => congrFun hf i)
        _ = -4/5 := by rw [Finset.sum_neg_distrib, hq]; ring
    rw [hs]
    norm_num

/-- P037-T1(i),(iii): normalization, school marginals, treated-composition
mean and variance, and every expected cross-product of the actual
hypergeometric design. These are expectations under the actual hierarchical law. -/
theorem composition_witness_design_moments :
    (∀ w, 0 ≤ witnessStateMass w) ∧ (∑ w, witnessStateMass w) = 1 ∧
    (∀ i, witnessMean (fun w => blockTreatment w.1 i) = 1/2 ∧
      2*witnessMean (fun w => witnessInteraction w i) = witnessEligibleFraction i ∧
      2*witnessMean (fun w =>
        (witnessInteraction w i - blockTreatment w.1 i*witnessEligibleFraction i)^2) =
        witnessEligibleFraction i*(1-witnessEligibleFraction i)/36) ∧
    (∀ i k, k.val ≤ 4 → 0 < schoolCountMass (witnessStratumReferents i) k) ∧
    witnessGram = !![1,0,1/5; 0,1/25,1/50; 1/5,1/50,151/2400] ∧
      witnessRhs = ![-1/5,-1/50,-17/300] := by
  refine ⟨witness_state_probability_law.1, witness_state_probability_law.2,
    ?_, ?_, witness_expected_normal_equations.1, witness_expected_normal_equations.2⟩
  · intro i
    refine ⟨(witness_coordinate_moments.1 i).1, ?_, ?_⟩
    · rw [(witness_coordinate_moments.1 i).2]
      ring
    · have heq : (fun w =>
          (witnessInteraction w i-blockTreatment w.1 i*witnessEligibleFraction i)^2) =
        (fun w => witnessInteraction w i*witnessInteraction w i -
          (2*witnessEligibleFraction i)*(blockTreatment w.1 i*witnessInteraction w i) +
          witnessEligibleFraction i^2*(blockTreatment w.1 i*blockTreatment w.1 i)) := by
        funext w
        ring
      rw [heq, witness_mean_add, witness_mean_sub, witness_mean_mul, witness_mean_mul,
        witness_coordinate_moments.2.2.2 i i, witness_coordinate_moments.2.2.1 i i,
        witness_coordinate_moments.2.1 i i]
      simp only [ite_true]
      ring
  · intro i k hk
    apply school_count_common_support _ _ k hk
    fin_cases i <;> norm_num [witnessStratumReferents]

/-- P037-T1(iii): exact algebraic certificate for the printed Gram
matrix. Its determinant is nonzero and the unique normal-equation
solution is (-3/31,-15/62,-16/31). Connecting this matrix to the actual
design is the separate proved `composition_witness_design_moments`. -/
theorem witness_normal_equation_certificate (t g b : ℝ) :
    (1*(1/25*(151/2400)-1/50*(1/50)) +
       (1/5)*(0*(1/50)-(1/25)*(1/5)) : ℝ) = 31/60000 ∧
    (31/60000:ℝ) ≠ 0 ∧
    (t+b/5 = -1/5 ∧ g/25+b/50 = -1/50 ∧
      t/5+g/50+151*b/2400 = -17/300 ↔
      t = -3/31 ∧ g = -15/62 ∧ b = -16/31) ∧
    (-16/31:ℝ) ≠ 0 := by
  refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩
  constructor
  · rintro ⟨h1,h2,h3⟩
    refine ⟨?_,?_,?_⟩ <;> linarith
  · rintro ⟨rfl,rfl,rfl⟩; norm_num

/-- P037-T1(iv): the general fixed schedule
“a + τD + b₁D(C-q) + b₂D(q-1/5) + gq”, as potential outcomes. -/
noncomputable def witnessMixturePotentialOutcome (a tau b1 b2 g : ℝ)
    (i : Fin 4) (treated : Bool) (c : ℝ) : ℝ :=
  a+g*witnessEligibleFraction i +
    if treated then tau+b1*(c-witnessEligibleFraction i)+b2*(witnessEligibleFraction i-1/5) else 0

/-- P037-T1(iv): the observed general schedule
uses the realized columns D and Z=DC, with its fixed eligible fraction q. -/
noncomputable def witnessMixtureObservedOutcome (a tau b1 b2 g : ℝ)
    (w : CompositionState) (i : Fin 4) : ℝ :=
  a+tau*blockTreatment w.1 i+
    b1*(witnessInteraction w i-blockTreatment w.1 i*witnessEligibleFraction i)+
    b2*blockTreatment w.1 i*(witnessEligibleFraction i-1/5)+g*witnessEligibleFraction i

/-- P037-T1(iv): the general schedule has within-school composition
slope b₁ and the average causal curve τ+b₁(c-1/5), even when b₂ differs. -/
theorem witness_mixture_causal_curve (a tau b1 b2 g : ℝ) :
    (∀ i c c', witnessMixturePotentialOutcome a tau b1 b2 g i true c-
      witnessMixturePotentialOutcome a tau b1 b2 g i true c'=b1*(c-c')) ∧
    (∀ c : ℝ, (∑ i : Fin 4,
      (witnessMixturePotentialOutcome a tau b1 b2 g i true c-
       witnessMixturePotentialOutcome a tau b1 b2 g i false c))/4=tau+b1*(c-1/5)) := by
  constructor
  · intro i c c'
    simp only [witnessMixturePotentialOutcome, Bool.true_eq, ite_true]
    ring
  · intro c
    rw [Fin.sum_univ_four]
    norm_num [witnessMixturePotentialOutcome, witnessEligibleFraction]
    ring

/-- P037-T1(iv): linear expansion of the actual mixture outcome's
coordinate cross moment. All coefficients are fixed before randomization. -/
theorem witness_mean_mixture_product (a tau b1 b2 g : ℝ)
    (X : CompositionState → ℝ) (j : Fin 4) :
    witnessMean (fun w => X w*witnessMixtureObservedOutcome a tau b1 b2 g w j) =
      a*witnessMean X + (tau-b2/5)*witnessMean (fun w => X w*blockTreatment w.1 j) +
      b1*witnessMean (fun w => X w*witnessInteraction w j) +
      ((b2-b1)*witnessEligibleFraction j)*witnessMean (fun w => X w*blockTreatment w.1 j) +
      (g*witnessEligibleFraction j)*witnessMean X := by
  have heq : (fun w => X w*witnessMixtureObservedOutcome a tau b1 b2 g w j) =
      (fun w => a*X w + (tau-b2/5)*(X w*blockTreatment w.1 j) +
        b1*(X w*witnessInteraction w j) +
        ((b2-b1)*witnessEligibleFraction j)*(X w*blockTreatment w.1 j) +
        (g*witnessEligibleFraction j)*X w) := by
    funext w
    unfold witnessMixtureObservedOutcome
    ring
  rw [heq]
  simp only [witness_mean_add, witness_mean_mul]

/-- P037-T1(iv): the expected normal-equation RHS for the general
schedule is (τ, g/25+b₂/50, τ/5+g/50+b₁/160+b₂/60). The constant a
vanishes only because block effects are profiled in each realized block. -/
theorem witness_mixture_rhs (a tau b1 b2 g : ℝ) :
    (fun k => witnessMean (fun w => blockCross (witnessColumns w k)
      (witnessMixtureObservedOutcome a tau b1 b2 g w))) =
      ![tau, g/25+b2/50, tau/5+g/50+b1/160+b2/60] := by
  funext k
  fin_cases k <;>
    norm_num [witnessColumns, witness_mean_block_cross, Fin.sum_univ_four,
      witness_mean_mixture_product, witness_mean_mul, witness_mean_mul_right,
      witness_mean_div, witness_mean_const, witnessEligibleFraction,
      witness_coordinate_moments.1, witness_coordinate_moments.2.1,
      witness_coordinate_moments.2.2.1, witness_coordinate_moments.2.2.2,
      witness_mean_composition_treatment] <;> ring

/-- P037-T1(iv): under the exact witness design, for the
general outcome schedule the population DC coefficient mixes b_1 and b_2
with weights 15/31 and 16/31, although its causal composition slope is b_1.
Existence and uniqueness of the population solution are explicit.
This is a population projection, not E of finite-sample OLS. -/
theorem composition_witness_mixture (a tau b1 b2 g : ℝ) :
    ∃ theta : Fin 3 → ℝ,
      (witnessGram.mulVec theta = fun k => witnessMean (fun w =>
        blockCross (witnessColumns w k) (witnessMixtureObservedOutcome a tau b1 b2 g w))) ∧
      (∀ theta' : Fin 3 → ℝ,
        (witnessGram.mulVec theta' = fun k => witnessMean (fun w =>
          blockCross (witnessColumns w k) (witnessMixtureObservedOutcome a tau b1 b2 g w))) →
        theta' = theta) ∧
      theta 2 = (15*b1+16*b2)/31 ∧ (theta 2 = b1 ↔ b1=b2) := by
  rw [witness_expected_normal_equations.1, witness_mixture_rhs]
  let theta : Fin 3 → ℝ := ![tau-b2/5+3*(b2-b1)/31,
    g+15*(b2-b1)/62, (15*b1+16*b2)/31]
  refine ⟨theta, ?_, ?_, by simp [theta], ?_⟩
  · funext k
    fin_cases k <;> norm_num [theta, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  · intro theta' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
    funext k
    fin_cases k <;> norm_num [theta] <;> linarith
  · change ((15*b1+16*b2)/31 = b1 ↔ b1=b2)
    constructor <;> intro h <;> linarith

/-- P037-T1(ii),(iii): a complete finite design counterexample to the
randomization-only causal interpretation of SI Eq. (2), pp. 13--14.
The actual expected equations have the unique slope -16/31, whereas every
school and the common-support average causal curve have composition slope zero.
The separate probability-limit claim T1(v) is not a premise or conclusion here. -/
theorem composition_witness_counterexample :
    (∀ w, 0 ≤ witnessStateMass w) ∧ (∑ w, witnessStateMass w) = 1 ∧
    (∀ i, witnessMean (fun w => blockTreatment w.1 i) = 1/2 ∧
      2*witnessMean (fun w => witnessInteraction w i) = witnessEligibleFraction i ∧
      2*witnessMean (fun w =>
        (witnessInteraction w i-blockTreatment w.1 i*witnessEligibleFraction i)^2) =
        witnessEligibleFraction i*(1-witnessEligibleFraction i)/36) ∧
    (∀ i k, k.val ≤ 4 → 0 < schoolCountMass (witnessStratumReferents i) k) ∧
    (∀ i c c', witnessPotentialOutcome i true c-witnessPotentialOutcome i true c'=0) ∧
    (∀ c : ℝ, (∑ i : Fin 4,
      (witnessPotentialOutcome i true c-witnessPotentialOutcome i false c))/4 = -1/5) ∧
    (∀ theta : Fin 3 → ℝ, witnessGram.mulVec theta = witnessRhs ↔
      theta = ![-3/31,-15/62,-16/31]) ∧ (-16/31:ℝ) ≠ 0 := by
  refine ⟨witness_state_probability_law.1, witness_state_probability_law.2,
    composition_witness_design_moments.2.2.1,
    composition_witness_design_moments.2.2.2.1,
    witness_zero_composition_effect.1, witness_zero_composition_effect.2, ?_, by norm_num⟩
  intro theta
  rw [witness_expected_normal_equations.1, witness_expected_normal_equations.2]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
    funext k
    fin_cases k <;> norm_num <;> linarith
  · intro h
    rw [h]
    ext k
    fin_cases k <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Pooled OLS after profiling block indicators for B independent
copies of the witness block. Singular Gram matrices use Mathlib's zero
inverse; nonsingularity in probability is handled by the proved limit below. -/
noncomputable def pooledWitnessCoefficient (B : ℕ) (w : Fin B → CompositionState) : ℝ :=
  let G : Matrix (Fin 3) (Fin 3) ℝ := fun k l =>
    ∑ b, blockCross (witnessColumns (w b) k) (witnessColumns (w b) l)
  let h : Fin 3 → ℝ := fun k =>
    ∑ b, blockCross (witnessColumns (w b) k) (witnessObservedOutcome (w b))
  (G⁻¹.mulVec h) 2

/-- A finite collection of the paper's four-school blocks. The
centering kernel is I_4-11'/4 inside each block and zero across blocks. -/
noncomputable def withinBlocksCross {B : ℕ}
    (x y : (Fin B × Fin 4) → ℝ) : ℝ :=
  ∑ b, ∑ i, ∑ j, (if i=j then (3/4:ℝ) else -1/4) * x (b,i) * y (b,j)

/-- Finite bilinearity of the block-centering cross-product in the
second argument; this is the linear algebra of SI's block fixed effects. -/
theorem withinBlocksCross_add {B : ℕ} (x y z : (Fin B × Fin 4) → ℝ) :
    withinBlocksCross x (fun i => y i+z i) =
      withinBlocksCross x y + withinBlocksCross x z := by
  simp [withinBlocksCross, mul_add, Finset.sum_add_distrib]

/-- Finite bilinearity with a constant coefficient in the second argument. -/
theorem withinBlocksCross_mul {B : ℕ} (x y : (Fin B × Fin 4) → ℝ) (c : ℝ) :
    withinBlocksCross x (fun i => c*y i) = c*withinBlocksCross x y := by
  simp [withinBlocksCross, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Sums of columns are handled by finite bilinearity. -/
theorem withinBlocksCross_sum {B : ℕ} {K : Type*} [Fintype K]
    (x : (Fin B × Fin 4) → ℝ) (v : K → (Fin B × Fin 4) → ℝ) :
    withinBlocksCross x (fun i => ∑ k, v k i) = ∑ k, withinBlocksCross x (v k) := by
  simp only [withinBlocksCross, Finset.mul_sum]
  calc
    _ = ∑ b, ∑ i, ∑ k, ∑ j,
        (if i=j then (3/4:ℝ) else -1/4)*x (b,i)*v k (b,j) := by
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ k, ∑ i, ∑ j,
        (if i=j then (3/4:ℝ) else -1/4)*x (b,i)*v k (b,j) := by
      apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- Conditional mean zero in P037-T2(R), represented by orthogonality
to every function of the finite treatment vector. This is exactly the
finite-space E[R_i|D]=0 condition, including zero-probability cells. -/
def RandomizedComposition {Ω : Type*} [Fintype Ω] {B : ℕ}
    (d : FiniteDesign Ω) (D : Ω → (Fin B × Fin 4) → Bool)
    (R : Ω → (Fin B × Fin 4) → ℝ) : Prop :=
  ∀ (f : ((Fin B × Fin 4) → Bool) → ℝ) i,
    designMean d (fun w => f (D w)*R w i) = 0

/-- Block fixed effects are annihilated by the actual centering kernel. -/
theorem withinBlocksCross_block_constant {B : ℕ} (x : (Fin B × Fin 4) → ℝ)
    (alpha : Fin B → ℝ) : withinBlocksCross x (fun i => alpha i.1) = 0 := by
  have hc : ∀ i : Fin 4, (∑ j : Fin 4, if i=j then (3/4:ℝ) else -1/4) = 0 := by
    intro i; fin_cases i <;> norm_num [Fin.sum_univ_four]
  unfold withinBlocksCross
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro i _
  calc
    _ = (∑ j : Fin 4, if i=j then (3/4:ℝ) else -1/4)*(x (b,i)*alpha b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    _ = 0 := by rw [hc]; ring

/-- Expected profiled normal equations of SI Eq. (2), with arbitrary
additional fixed columns as allowed by Eq. (6). Column order is explicit. -/
def ExpectedNormalEquations {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (X : K → Ω → (Fin B × Fin 4) → ℝ)
    (Y : Ω → (Fin B × Fin 4) → ℝ) (theta : K → ℝ) : Prop :=
  ∀ k, designMean d (fun w => withinBlocksCross (X k w) (Y w)) =
    ∑ l, theta l * designMean d (fun w => withinBlocksCross (X k w) (X l w))

/-- P037-T2(A): correct conditional-model specification plus the
explicit orthogonality E[X'Mε]=0 makes its coefficient vector solve the
expected equations; an injective Gram operator (nonsingularity) makes
the solution unique. This assumption is stronger than an average curve. -/
theorem correctly_specified_composition_model {Ω K : Type*}
    [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (X : K → Ω → (Fin B × Fin 4) → ℝ)
    (alpha : Fin B → ℝ) (theta : K → ℝ)
    (err Y : Ω → (Fin B × Fin 4) → ℝ)
    (hY : ∀ w i, Y w i = alpha i.1 + (∑ k, theta k*X k w i) + err w i)
    (he : ∀ k, designMean d (fun w => withinBlocksCross (X k w) (err w)) = 0) :
    ExpectedNormalEquations d X Y theta ∧
    (Function.Injective (fun v : K → ℝ => fun k =>
      ∑ l, v l * designMean d (fun w => withinBlocksCross (X k w) (X l w))) →
      ∀ v, ExpectedNormalEquations d X Y v → v=theta) := by
  have hN : ExpectedNormalEquations d X Y theta := by
    intro k
    have hyfun : Y = fun w i => alpha i.1+(∑ l, theta l*X l w i)+err w i := by
      funext w i; exact hY w i
    rw [hyfun]
    simp_rw [withinBlocksCross_add, withinBlocksCross_sum, withinBlocksCross_mul,
      withinBlocksCross_block_constant]
    rw [designMean_add, designMean_add, designMean_const, he, designMean_sum]
    simp_rw [designMean_mul]
    ring
  refine ⟨hN, ?_⟩
  intro hInjective v hv
  apply hInjective
  funext k
  exact (hv k).symm.trans (hN k)

/-- P037-T2(B1): the randomized composition innovation R=D(C-μ)
separates the common within-school slope b from arbitrary fixed school
baselines a_i and treatment-effect intercepts t_i. -/
theorem composition_innovation_decomposition (a t b D C μ : ℝ) :
    a+D*t+b*D*C = a+D*(t+b*μ)+b*(D*(C-μ)) := by ring

/-- P037-T2(B2): conditional mean-zero composition innovations are
orthogonal after block centering to every nuisance vector that depends
only on school assignment and fixed attributes. -/
theorem composition_innovation_orthogonality {Ω : Type*} [Fintype Ω] {B : ℕ}
    (d : FiniteDesign Ω) (D : Ω → (Fin B × Fin 4) → Bool)
    (R : Ω → (Fin B × Fin 4) → ℝ) (hR : RandomizedComposition d D R)
    (V : ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ) :
    designMean d (fun w => withinBlocksCross (R w) (V (D w))) = 0 := by
  unfold withinBlocksCross
  simp_rw [designMean_sum]
  apply Finset.sum_eq_zero; intro b _
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  have h := hR (fun t => V t (b,j)) (b,i)
  have heq : (fun w =>
      (if i=j then (3/4:ℝ) else -1/4)*R w (b,i)*V (D w) (b,j)) =
      (fun w => (if i=j then (3/4:ℝ) else -1/4)*(V (D w) (b,j)*R w (b,i))) := by
    funext w; ring
  rw [heq, designMean_mul, h, mul_zero]

/-- Split expected normal equations for nuisance columns W and the
last composition column R or Z. This is exactly the partitioned Gram
system, not an extra identification assumption. -/
def AugmentedNormalEquations {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (W : K → Ω → (Fin B × Fin 4) → ℝ)
    (R Y : Ω → (Fin B × Fin 4) → ℝ) (delta : K → ℝ) (beta : ℝ) : Prop :=
  (∀ k, designMean d (fun w => withinBlocksCross (W k w) (Y w)) =
    (∑ l, delta l*designMean d (fun w => withinBlocksCross (W k w) (W l w))) +
      beta*designMean d (fun w => withinBlocksCross (W k w) (R w))) ∧
  designMean d (fun w => withinBlocksCross (R w) (Y w)) =
    (∑ l, delta l*designMean d (fun w => withinBlocksCross (R w) (W l w))) +
      beta*designMean d (fun w => withinBlocksCross (R w) (R w))

/-- Subtraction is linear in the block-centered outcome argument. -/
theorem withinBlocksCross_sub {B : ℕ} (x y z : (Fin B × Fin 4) → ℝ) :
    withinBlocksCross x (fun i => y i-z i) = withinBlocksCross x y-withinBlocksCross x z := by
  simp [withinBlocksCross, mul_sub, Finset.sum_sub_distrib]

/-- Addition is linear in the block-centered regressor argument. -/
theorem withinBlocksCross_left_add {B : ℕ} (x y z : (Fin B × Fin 4) → ℝ) :
    withinBlocksCross (fun i => x i+y i) z = withinBlocksCross x z+withinBlocksCross y z := by
  simp [withinBlocksCross, mul_add, add_mul, Finset.sum_add_distrib]

/-- The normal equations assert orthogonality of each regressor to
the residual, an exact reformulation used for the invertible repair. -/
theorem augmented_normal_iff_residual {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (W : K → Ω → (Fin B × Fin 4) → ℝ)
    (R Y : Ω → (Fin B × Fin 4) → ℝ) (delta : K → ℝ) (beta : ℝ) :
    AugmentedNormalEquations d W R Y delta beta ↔
      (∀ k, designMean d (fun w => withinBlocksCross (W k w)
        (fun i => Y w i-((∑ l, delta l*W l w i)+beta*R w i))) = 0) ∧
      designMean d (fun w => withinBlocksCross (R w)
        (fun i => Y w i-((∑ l, delta l*W l w i)+beta*R w i))) = 0 := by
  have hres : ∀ V : Ω → (Fin B × Fin 4) → ℝ,
      designMean d (fun w => withinBlocksCross (V w)
        (fun i => Y w i-((∑ l, delta l*W l w i)+beta*R w i))) =
      designMean d (fun w => withinBlocksCross (V w) (Y w)) -
        ((∑ l, delta l*designMean d (fun w => withinBlocksCross (V w) (W l w))) +
          beta*designMean d (fun w => withinBlocksCross (V w) (R w))) := by
    intro V
    simp_rw [withinBlocksCross_sub, withinBlocksCross_add,
      withinBlocksCross_sum, withinBlocksCross_mul]
    rw [designMean_sub, designMean_add, designMean_sum, designMean_mul]
    simp_rw [designMean_mul]
  unfold AugmentedNormalEquations
  simp_rw [hres, sub_eq_zero]

/-- P037-T2(B3): with a common composition slope b, seed-independent
nuisance controls, arbitrary fixed baselines/intercepts and E[R|D]=0,
every population normal-equation solution has β=b when E[R'MR]>0. -/
theorem centered_composition_identifies_common_slope {Ω K : Type*}
    [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (D : Ω → (Fin B × Fin 4) → Bool)
    (R : Ω → (Fin B × Fin 4) → ℝ) (hR : RandomizedComposition d D R)
    (A : ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ)
    (W : K → ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ)
    (b beta : ℝ) (delta : K → ℝ)
    (hN : AugmentedNormalEquations d (fun k w => W k (D w)) R
      (fun w i => A (D w) i + b*R w i) delta beta)
    (hv : 0 < designMean d (fun w => withinBlocksCross (R w) (R w))) :
    beta=b := by
  have hA := composition_innovation_orthogonality d D R hR A
  have hW : ∀ l, designMean d (fun w => withinBlocksCross (R w) (W l (D w))) = 0 := by
    intro l; exact composition_innovation_orthogonality d D R hR (W l)
  have hrow := hN.2
  simp_rw [withinBlocksCross_add, withinBlocksCross_mul] at hrow
  rw [designMean_add, designMean_mul, hA] at hrow
  simp_rw [hW, mul_zero] at hrow
  simp only [Finset.sum_const_zero, zero_add] at hrow
  nlinarith

/-- P037-T2(B4): adding Dμ to the original DC model is the invertible
column transformation Z=R+Dμ; Dq is the μ=q case. The coefficient on DC
is the coefficient on the innovation in the equivalent centered parameterization. -/
theorem adding_eligible_interaction_equivalent {Ω K : Type*}
    [Fintype Ω] [Fintype K] [DecidableEq K] {B : ℕ}
    (d : FiniteDesign Ω) (W : K → Ω → (Fin B × Fin 4) → ℝ)
    (R Z Y : Ω → (Fin B × Fin 4) → ℝ) (e : K)
    (hZ : ∀ w i, Z w i=R w i+W e w i)
    (delta : K → ℝ) (beta : ℝ) :
    AugmentedNormalEquations d W Z Y delta beta ↔
    AugmentedNormalEquations d W R Y
      (fun k => delta k + if k=e then beta else 0) beta := by
  have hpred : ∀ w i, (∑ l, delta l*W l w i)+beta*Z w i =
      (∑ l, (delta l + if l=e then beta else 0)*W l w i)+beta*R w i := by
    intro w i
    rw [hZ]
    simp [add_mul, Finset.sum_add_distrib, ite_mul]
    ring
  rw [augmented_normal_iff_residual, augmented_normal_iff_residual]
  simp_rw [hpred]
  let residual := fun w i => Y w i-
    ((∑ l, (delta l + if l=e then beta else 0)*W l w i)+beta*R w i)
  have hlast : designMean d (fun w => withinBlocksCross (Z w) (residual w)) =
      designMean d (fun w => withinBlocksCross (R w) (residual w)) +
      designMean d (fun w => withinBlocksCross (W e w) (residual w)) := by
    have hzfun : Z = fun w i => R w i+W e w i := by funext w i; exact hZ w i
    rw [hzfun]
    simp_rw [withinBlocksCross_left_add]
    rw [designMean_add]
  change ((∀ k, designMean d (fun w => withinBlocksCross (W k w) (residual w)) = 0) ∧
      designMean d (fun w => withinBlocksCross (Z w) (residual w)) = 0) ↔
    ((∀ k, designMean d (fun w => withinBlocksCross (W k w) (residual w)) = 0) ∧
      designMean d (fun w => withinBlocksCross (R w) (residual w)) = 0)
  constructor
  · rintro ⟨hW, hZr⟩
    rw [hlast, hW e, add_zero] at hZr
    exact ⟨hW, hZr⟩
  · rintro ⟨hW, hRr⟩
    refine ⟨hW, ?_⟩
    rw [hlast, hRr, hW e, add_zero]

/-- P037-T2(C): the centered or expanded witness regressors. The
centered innovation R=DC-Dq is not replaced by an identically zero variable. -/
noncomputable def witnessInnovation (w : CompositionState) (i : Fin 4) : ℝ :=
  witnessInteraction w i - blockTreatment w.1 i*witnessEligibleFraction i

/-- The repaired expanded columns (D,q,DC,Dq), preserving both DC and Dq. -/
noncomputable def witnessExpandedColumns (w : CompositionState) (k : Fin 4) : Fin 4 → ℝ :=
  ![blockTreatment w.1, witnessEligibleFraction, witnessInteraction w,
    (fun i => blockTreatment w.1 i*witnessEligibleFraction i)] k

/-- The repaired centered columns (D,q,R), retaining the eligible main effect. -/
noncomputable def witnessCenteredColumns (w : CompositionState) (k : Fin 3) : Fin 4 → ℝ :=
  ![blockTreatment w.1, witnessEligibleFraction, witnessInnovation w] k

/-- Exact expected normal equations for any named witness column set. -/
def WitnessEquations {n : ℕ} (X : CompositionState → Fin n → Fin 4 → ℝ)
    (Y : CompositionState → Fin 4 → ℝ) (theta : Fin n → ℝ) : Prop :=
  ∀ k, (∑ l, theta l*witnessMean (fun w => blockCross (X w k) (X w l))) =
    witnessMean (fun w => blockCross (X w k) (Y w))

/-- A fixed school attribute multiplying the left factor can be taken
outside the exact cross moment; used for P037-T2(C)'s Dq columns. -/
theorem witness_mean_left_scaled_product (X Y : CompositionState → ℝ) (a : ℝ) :
    witnessMean (fun w => (X w*a)*Y w) =
      a*witnessMean (fun w => X w*Y w) := by
  have heq : (fun w => (X w*a)*Y w) = (fun w => a*(X w*Y w)) := by
    funext w
    ring
  rw [heq, witness_mean_mul]

/-- The corresponding fixed-attribute factorization on the right,
for P037-T2(C)'s exact school-treatment/composition cross moments. -/
theorem witness_mean_right_scaled_product (X Y : CompositionState → ℝ) (a : ℝ) :
    witnessMean (fun w => X w*(Y w*a)) =
      a*witnessMean (fun w => X w*Y w) := by
  have heq : (fun w => X w*(Y w*a)) = (fun w => a*(X w*Y w)) := by
    funext w
    ring
  rw [heq, witness_mean_mul]

/-- The same exact cross-moment scaling when the scalar is written
before the right factor; this is the 1/5 common slope in P037-T2(C). -/
theorem witness_mean_scalar_right_factor (X Y : CompositionState → ℝ) (a : ℝ) :
    witnessMean (fun w => X w*(a*Y w)) =
      a*witnessMean (fun w => X w*Y w) := by
  have heq : (fun w => X w*(a*Y w)) = (fun w => a*(X w*Y w)) := by
    funext w
    ring
  rw [heq, witness_mean_mul]

set_option maxHeartbeats 2000000 in
/-- P037-T2(C): the expected Gram matrices and outcome RHS for the
expanded (D,q,DC,Dq) and centered (D,q,R) regressions under the genuine
counterexample design. The centered innovation has variance 1/160. -/
theorem witness_repaired_moments :
    (fun k l => witnessMean (fun w => blockCross (witnessExpandedColumns w k)
      (witnessExpandedColumns w l))) =
      !![1,0,1/5,1/5; 0,1/25,1/50,1/50;
        1/5,1/50,151/2400,17/300; 1/5,1/50,17/300,17/300] ∧
    (fun k l => witnessMean (fun w => blockCross (witnessCenteredColumns w k)
      (witnessCenteredColumns w l))) = !![1,0,0; 0,1/25,0; 0,0,1/160] ∧
    (fun k => witnessMean (fun w => blockCross (witnessExpandedColumns w k)
      (witnessObservedOutcome w))) = ![-1/5,-1/50,-17/300,-17/300] ∧
    (fun k => witnessMean (fun w => blockCross (witnessCenteredColumns w k)
      (witnessObservedOutcome w))) = ![-1/5,-1/50,0] := by
  refine ⟨?_,?_,?_,?_⟩
  · ext k l
    fin_cases k <;> fin_cases l <;>
      norm_num [witnessExpandedColumns, witness_mean_block_cross, Fin.sum_univ_four,
        witnessEligibleFraction, witness_mean_left_scaled_product,
        witness_mean_right_scaled_product, witness_mean_mul, witness_mean_mul_right,
        witness_mean_div, witness_mean_const, witness_coordinate_moments.1,
        witness_coordinate_moments.2.1, witness_coordinate_moments.2.2.1,
        witness_coordinate_moments.2.2.2, witness_mean_composition_treatment]
  · ext k l
    fin_cases k <;> fin_cases l <;>
      norm_num [witnessCenteredColumns, witnessInnovation, witness_mean_block_cross,
        Fin.sum_univ_four, mul_sub, sub_mul, witness_mean_add, witness_mean_sub,
        witness_mean_left_scaled_product, witness_mean_right_scaled_product,
        witness_mean_mul, witness_mean_mul_right, witness_mean_div, witness_mean_const,
        witnessEligibleFraction, witness_coordinate_moments.1,
        witness_coordinate_moments.2.1, witness_coordinate_moments.2.2.1,
        witness_coordinate_moments.2.2.2, witness_mean_composition_treatment]
  · funext k
    fin_cases k <;>
      norm_num [witnessExpandedColumns, witness_mean_block_cross, Fin.sum_univ_four,
        witness_mean_observed_product, witness_mean_left_scaled_product,
        witness_mean_right_scaled_product, witness_mean_mul, witness_mean_mul_right,
        witness_mean_div, witness_mean_const, witnessEligibleFraction,
        witness_coordinate_moments.1, witness_coordinate_moments.2.1,
        witness_coordinate_moments.2.2.1, witness_mean_composition_treatment]
  · funext k
    fin_cases k <;>
      norm_num [witnessCenteredColumns, witnessInnovation, witness_mean_block_cross,
        Fin.sum_univ_four, witness_mean_observed_product, mul_sub, sub_mul,
        witness_mean_add, witness_mean_sub, witness_mean_left_scaled_product,
        witness_mean_right_scaled_product, witness_mean_mul, witness_mean_mul_right,
        witness_mean_div, witness_mean_const, witnessEligibleFraction,
        witness_coordinate_moments.1, witness_coordinate_moments.2.1,
        witness_coordinate_moments.2.2.1, witness_mean_composition_treatment]

set_option maxHeartbeats 2000000 in
/-- P037-T2(C): actual expected RHS vectors for the nonzero common
slope 1/5 example and for the correctly specified printed regression.
The randomization law, covariates, and block profiling are unchanged. -/
theorem witness_repaired_rhs :
    (fun k => witnessMean (fun w => blockCross (witnessColumns w k)
      (fun i => witnessObservedOutcome w i+(1/5)*witnessInteraction w i))) =
      ![-4/25,-2/125,-529/12000] ∧
    (fun k => witnessMean (fun w => blockCross (witnessCenteredColumns w k)
      (fun i => witnessObservedOutcome w i+(1/5)*witnessInteraction w i))) =
      ![-4/25,-2/125,1/800] ∧
    (fun k => witnessMean (fun w => blockCross (witnessExpandedColumns w k)
      (fun i => witnessObservedOutcome w i+(1/5)*witnessInteraction w i))) =
      ![-4/25,-2/125,-529/12000,-17/375] ∧
    (fun k => witnessMean (fun w => blockCross (witnessColumns w k)
      (fun i => 3/10-(1/5)*blockTreatment w.1 i-(1/2)*witnessEligibleFraction i+
        (1/5)*witnessInteraction w i))) = ![-4/25,-2/125,-449/12000] := by
  refine ⟨?_,?_,?_,?_⟩ <;> funext k <;> fin_cases k <;>
    norm_num [witnessColumns, witnessExpandedColumns, witnessCenteredColumns,
      witnessInnovation, witnessObservedOutcome, witness_mean_block_cross,
      Fin.sum_univ_four, mul_sub, sub_mul, mul_add, add_mul,
      witness_mean_add, witness_mean_sub, witness_mean_left_scaled_product,
      witness_mean_right_scaled_product, witness_mean_scalar_right_factor,
      witness_mean_mul, witness_mean_mul_right,
      witness_mean_div, witness_mean_const, witnessEligibleFraction,
      witness_coordinate_moments.1, witness_coordinate_moments.2.1,
      witness_coordinate_moments.2.2.1, witness_coordinate_moments.2.2.2,
      witness_mean_composition_treatment]

/-- Matrix form of P037-T2(C)'s expected normal equations. This is an
equivalent notation, with no existence or nonsingularity assumption added. -/
theorem witness_equations_matrix_iff {n : ℕ}
    (X : CompositionState → Fin n → Fin 4 → ℝ)
    (Y : CompositionState → Fin 4 → ℝ) (theta : Fin n → ℝ) :
    WitnessEquations X Y theta ↔
      (Matrix.of (fun k l => witnessMean (fun w => blockCross (X w k) (X w l)))).mulVec theta =
        fun k => witnessMean (fun w => blockCross (X w k) (Y w)) := by
  simp only [WitnessEquations, funext_iff, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm]

/-- P037-T2(C): all the exact corrected and printed
normal-equation comparisons, including the nonzero common slope 1/5.
These connect the actual finite design to unique coefficients. -/
theorem witness_repaired_regression_comparisons :
    witnessMean (fun w => blockCross (witnessInnovation w) (witnessInnovation w)) = 1/160 ∧
    (∀ theta, WitnessEquations witnessExpandedColumns witnessObservedOutcome theta ↔
      theta = ![0,0,0,-1]) ∧
    (∀ theta, WitnessEquations witnessCenteredColumns witnessObservedOutcome theta ↔
      theta = ![-1/5,-1/2,0]) ∧
    (∀ theta, WitnessEquations witnessColumns
      (fun w i => witnessObservedOutcome w i+(1/5)*witnessInteraction w i) theta ↔
      theta = ![-3/31,-15/62,-49/155]) ∧
    (∀ theta, WitnessEquations witnessCenteredColumns
      (fun w i => witnessObservedOutcome w i+(1/5)*witnessInteraction w i) theta ↔
      theta = ![-4/25,-2/5,1/5]) ∧
    (∀ theta, WitnessEquations witnessExpandedColumns
      (fun w i => witnessObservedOutcome w i+(1/5)*witnessInteraction w i) theta ↔
      theta = ![0,0,1/5,-1]) ∧
    (∀ theta, WitnessEquations witnessColumns
      (fun w i => 3/10-(1/5)*blockTreatment w.1 i-(1/2)*witnessEligibleFraction i+
        (1/5)*witnessInteraction w i) theta ↔ theta = ![-1/5,-1/2,1/5]) := by
  have hv := congrFun (congrFun witness_repaired_moments.2.1 2) 2
  have hvar : witnessMean (fun w => blockCross (witnessInnovation w) (witnessInnovation w)) = 1/160 := by
    simpa [witnessCenteredColumns] using hv
  refine ⟨hvar, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro theta
    rw [witness_equations_matrix_iff, witness_repaired_moments.1, witness_repaired_moments.2.2.1]
    change ((!![1,0,1/5,1/5; 0,1/25,1/50,1/50;
      1/5,1/50,151/2400,17/300; 1/5,1/50,17/300,17/300] :
      Matrix (Fin 4) (Fin 4) ℝ).mulVec theta = _) ↔ _
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      have h3 := congrFun h 3
      norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_four] at h0 h1 h2 h3
      funext k
      fin_cases k <;> norm_num <;> linarith
    · intro h
      rw [h]
      funext k
      fin_cases k <;> norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_four]
  · intro theta
    rw [witness_equations_matrix_iff, witness_repaired_moments.2.1, witness_repaired_moments.2.2.2]
    change ((!![1,0,0; 0,1/25,0; 0,0,1/160] :
      Matrix (Fin 3) (Fin 3) ℝ).mulVec theta = _) ↔ _
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three] at h0 h1 h2
      funext k
      fin_cases k <;> norm_num <;> linarith
    · intro h
      rw [h]
      funext k
      fin_cases k <;> norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three]
  · intro theta
    rw [witness_equations_matrix_iff]
    change (witnessGram.mulVec theta = _) ↔ _
    rw [witness_expected_normal_equations.1, witness_repaired_rhs.1]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three] at h0 h1 h2
      funext k
      fin_cases k <;> norm_num <;> linarith
    · intro h
      rw [h]
      funext k
      fin_cases k <;> norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three]
  · intro theta
    rw [witness_equations_matrix_iff, witness_repaired_moments.2.1, witness_repaired_rhs.2.1]
    change ((!![1,0,0; 0,1/25,0; 0,0,1/160] :
      Matrix (Fin 3) (Fin 3) ℝ).mulVec theta = _) ↔ _
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three] at h0 h1 h2
      funext k
      fin_cases k <;> norm_num <;> linarith
    · intro h
      rw [h]
      funext k
      fin_cases k <;> norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three]
  · intro theta
    rw [witness_equations_matrix_iff, witness_repaired_moments.1, witness_repaired_rhs.2.2.1]
    change ((!![1,0,1/5,1/5; 0,1/25,1/50,1/50;
      1/5,1/50,151/2400,17/300; 1/5,1/50,17/300,17/300] :
      Matrix (Fin 4) (Fin 4) ℝ).mulVec theta = _) ↔ _
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      have h3 := congrFun h 3
      norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_four] at h0 h1 h2 h3
      funext k
      fin_cases k <;> norm_num <;> linarith
    · intro h
      rw [h]
      funext k
      fin_cases k <;> norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_four]
  · intro theta
    rw [witness_equations_matrix_iff]
    change (witnessGram.mulVec theta = _) ↔ _
    rw [witness_expected_normal_equations.1, witness_repaired_rhs.2.2.2]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three] at h0 h1 h2
      funext k
      fin_cases k <;> norm_num <;> linarith
    · intro h
      rw [h]
      funext k
      fin_cases k <;> norm_num [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_three]

/-- Probability of an event under the finite randomization law. -/
noncomputable def designProbability {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (event : Ω → Prop) : ℝ := by
  classical
  exact designMean d (fun w => if event w then (1:ℝ) else 0)

/-- Finite Chebyshev bound supporting P037-T9(ii) and P037-T11(5).
This is about the actual finite design law, not an assumed tail bound. -/
theorem finite_chebyshev {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) (eps : ℝ) (heps : 0 < eps) :
    designProbability d (fun w => eps < |X w-designMean d X|) ≤
      designVariance d X / eps^2 := by
  classical
  have hp : 0 < eps^2 := sq_pos_of_pos heps
  rw [le_div_iff₀ hp, designVariance_centered]
  unfold designProbability designMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w _
  change (d.weight w * if eps < |X w-designMean d X| then 1 else 0)*eps^2 ≤
    d.weight w*(X w-designMean d X)^2
  by_cases h : eps < |X w-designMean d X|
  · simp only [if_pos h, mul_one]
    apply mul_le_mul_of_nonneg_left _ (d.nonneg w)
    nlinarith [sq_abs (X w-designMean d X)]
  · simp only [if_neg h, mul_zero, zero_mul]
    exact mul_nonneg (d.nonneg w) (sq_nonneg _)

/-- P037-T9(ii): independent design-draw exposure indicators have
the stated unbiased frequency, variance π(1-π)/J and finite tail bound.
Only pairwise independence of the binary indicators is needed; hpair
is its exact moment factorization, so this also covers all iid draws. -/
theorem monte_carlo_frequency_moments {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (J : ℕ) (hJ : 0 < J)
    (X : Fin J → Ω → ℝ) (pi : ℝ)
    (hbinary : ∀ j w, X j w=0 ∨ X j w=1)
    (hmean : ∀ j, designMean d (X j)=pi)
    (hpair : ∀ j k, j≠k → designMean d (fun w => X j w*X k w)=pi^2) :
    designMean d (fun w => (∑ j, X j w)/J)=pi ∧
    designVariance d (fun w => (∑ j, X j w)/J)=pi*(1-pi)/J ∧
    designVariance d (fun w => (∑ j, X j w)/J) ≤ 1/(4*J) ∧
    (∀ eps : ℝ, 0 < eps →
      designProbability d (fun w => eps < |(∑ j, X j w)/J-pi|) ≤ 1/(4*J*eps^2)) := by
  have hJ0 : (J:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hJ
  have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
  have hsumMean : designMean d (fun w => ∑ j, X j w) = J*pi := by
    rw [designMean_sum]; simp [hmean]
  have hprod : ∀ j k, designMean d (fun w => X j w*X k w) =
      if j=k then pi else pi^2 := by
    intro j k; by_cases hjk : j=k
    · subst k
      have heq : (fun w => X j w*X j w) = X j := by
        funext w; rcases hbinary j w with h | h <;> simp [h]
      simp [heq, hmean]
    · simp [hjk, hpair j k hjk]
  have hsumSquare : designMean d (fun w => (∑ j, X j w)^2) =
      J*(pi-pi^2+(J:ℝ)*pi^2) := by
    have hexpand : (fun w => (∑ j, X j w)^2) =
        (fun w => ∑ j, ∑ k, X j w*X k w) := by
      funext w
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    rw [hexpand, designMean_sum]
    simp_rw [designMean_sum, hprod]
    have hrow : ∀ j : Fin J, (∑ k : Fin J, if j=k then pi else pi^2) =
        pi-pi^2+(J:ℝ)*pi^2 := by
      intro j
      have heq : (fun k : Fin J => if j=k then pi else pi^2) =
          (fun k => (if k=j then pi-pi^2 else 0)+pi^2) := by
        funext k; by_cases hk : k=j
        · subst k; simp
        · simp [hk, Ne.symm hk]
      rw [heq, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [hrow]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : designMean d (fun w => (∑ j, X j w)/(J:ℝ))=pi := by
    have heq : (fun w => (∑ j, X j w)/(J:ℝ)) =
        (fun w => (1/(J:ℝ))*(∑ j, X j w)) := by funext w; ring
    rw [heq, designMean_mul, hsumMean]; field_simp
  have hvar : designVariance d (fun w => (∑ j, X j w)/(J:ℝ))=pi*(1-pi)/J := by
    have heq : (fun w => ((∑ j, X j w)/(J:ℝ))^2) =
        (fun w => (1/(J:ℝ)^2)*(∑ j, X j w)^2) := by funext w; ring
    rw [designVariance, hm, heq, designMean_mul, hsumSquare]
    field_simp
    <;> ring
  have hvarbound : designVariance d (fun w => (∑ j, X j w)/(J:ℝ)) ≤ 1/(4*J) := by
    rw [hvar]
    have hquadratic : pi*(1-pi) ≤ 1/4 := by nlinarith [sq_nonneg (pi-1/2)]
    calc
      pi*(1-pi)/(J:ℝ) ≤ (1/4)/(J:ℝ) := div_le_div_of_nonneg_right hquadratic hJpos.le
      _ = 1/(4*J) := by ring
  refine ⟨hm, hvar, hvarbound, ?_⟩
  intro eps heps
  have ht := finite_chebyshev d (fun w => (∑ j, X j w)/(J:ℝ)) eps heps
  rw [hm] at ht
  calc
    _ ≤ designVariance d (fun w => (∑ j, X j w)/(J:ℝ))/eps^2 := ht
    _ ≤ (1/(4*J))/eps^2 := div_le_div_of_nonneg_right hvarbound (sq_nonneg eps)
    _ = 1/(4*J*eps^2) := by ring

/-- P037-T9(ii)'s consistency remark, stated on a growing sequence
of independent design draws. Exposure means and pair factorization
are the same exact finite hypotheses as the previous theorem. -/
theorem monte_carlo_frequency_consistent (Ω : ℕ → Type*)
    [∀ J, Fintype (Ω J)] (d : ∀ J, FiniteDesign (Ω J))
    (X : ∀ J, Fin (J+1) → Ω J → ℝ) (pi : ℝ)
    (hbinary : ∀ J j w, X J j w=0 ∨ X J j w=1)
    (hmean : ∀ J j, designMean (d J) (X J j)=pi)
    (hpair : ∀ J j k, j≠k → designMean (d J) (fun w => X J j w*X J k w)=pi^2)
    (eps : ℝ) (heps : 0 < eps) :
    Filter.Tendsto (fun J => designProbability (d J)
      (fun w => eps < |(∑ j, X J j w)/(J+1)-pi|)) Filter.atTop (nhds 0) := by
  classical
  have hn : ∀ J, 0 ≤ designProbability (d J)
      (fun w => eps < |(∑ j, X J j w)/(J+1)-pi|) := by
    intro J
    unfold designProbability designMean
    apply Finset.sum_nonneg; intro w _
    apply mul_nonneg ((d J).nonneg w)
    dsimp
    split_ifs <;> norm_num
  have hb : ∀ J, designProbability (d J)
      (fun w => eps < |(∑ j, X J j w)/(J+1)-pi|) ≤ 1/(4*(J+1)*eps^2) := by
    intro J
    simpa only [Nat.cast_add, Nat.cast_one] using
      (monte_carlo_frequency_moments (d J) (J+1) (Nat.succ_pos _)
      (X J) pi (hbinary J) (hmean J) (hpair J)).2.2.2 eps heps
  have hl : Filter.Tendsto (fun J : ℕ => 1/(4*((J:ℝ)+1)*eps^2))
      Filter.atTop (nhds 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (1/(4*eps^2))
    convert ht using 1
    · funext J; field_simp <;> ring
    · simp
  exact squeeze_zero hn hb hl

/-- P037-T10(iv): fixed-count dependence without a uniform allocation law. -/
theorem fixed_count_forces_dependence {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (T : Fin 4 → Ω → ℝ)
    (hbinary : ∀ i w, T i w=0 ∨ T i w=1)
    (hcount : ∀ w, ∑ i, T i w=2)
    (hmarginal : ∀ i, designMean d (T i)=1/2) :
    designVariance d (fun w => ∑ i, T i w)=0 ∧
    (∑ i, designVariance d (T i))=1 ∧
    (∑ i, ∑ j, if i=j then (0:ℝ) else designCovariance d (T i) (T j)) = -1 ∧
    (∃ i j, i≠j ∧ designCovariance d (T i) (T j) < 0) := by
  classical
  have ht : (fun w => ∑ i, T i w) = (fun _ => (2:ℝ)) := by funext w; exact hcount w
  have hv : designVariance d (fun w => ∑ i, T i w)=0 := by
    rw [ht, designVariance, designMean_const, designMean_const]; norm_num
  have hd : ∀ i, designVariance d (T i)=1/4 := by
    intro i
    have hs : (fun w => (T i w)^2) = T i := by
      funext w; rcases hbinary i w with h | h <;> simp [h]
    rw [designVariance, hs, hmarginal]; norm_num
  have hdiag : (∑ i, designVariance d (T i))=1 := by simp [hd]
  have hcd : ∀ i, designCovariance d (T i) (T i)=designVariance d (T i) := by
    intro i; simp [designCovariance, designVariance, pow_two]
  have hsplit : (∑ i, ∑ j, designCovariance d (T i) (T j)) =
      (∑ i, designVariance d (T i)) +
      (∑ i, ∑ j, if i=j then (0:ℝ) else designCovariance d (T i) (T j)) := by
    have heq : ∀ i j, designCovariance d (T i) (T j) =
        (if i=j then designVariance d (T i) else 0) +
        (if i=j then 0 else designCovariance d (T i) (T j)) := by
      intro i j; by_cases hij : i=j
      · subst j; simp [hcd]
      · simp [hij]
    calc
      _ = ∑ i, ∑ j, ((if i=j then designVariance d (T i) else 0) +
          (if i=j then 0 else designCovariance d (T i) (T j))) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _; exact heq i j
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hoff : (∑ i, ∑ j, if i=j then (0:ℝ) else designCovariance d (T i) (T j)) = -1 := by
    have hall := designVariance_sum_covariances d T
    rw [hv, hsplit, hdiag] at hall
    linarith
  refine ⟨hv, hdiag, hoff, ?_⟩
  by_contra hnone
  have hnonneg : ∀ i j, i≠j → 0 ≤ designCovariance d (T i) (T j) := by
    intro i j hij; by_contra hneg
    exact hnone ⟨i,j,hij,lt_of_not_ge hneg⟩
  have hsum : 0 ≤ ∑ i, ∑ j, if i=j then (0:ℝ) else designCovariance d (T i) (T j) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    split_ifs with hij
    · exact le_rfl
    · exact hnonneg i j hij
  linarith

/-- Finite variance scales quadratically with a deterministic coefficient. -/
theorem designVariance_mul {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω)
    (X : Ω → ℝ) (c : ℝ) :
    designVariance d (fun w => c*X w)=c^2*designVariance d X := by
  have hf : (fun w => (c*X w)^2) = (fun w => c^2*(X w)^2) := by
    funext w; ring
  rw [designVariance, designMean_mul, hf, designMean_mul]
  unfold designVariance
  ring

/-- P037-T11, sufficient setting: B independently randomized
four-school blocks, fixed retained students/outcomes/predictions, and
block-local exposures with their exact positive probabilities. The
assignment index encodes both school and within-school seed draws; it
may also carry auxiliary finite simulation randomness unused by exposures. -/
structure RetainedBlockRow (B : ℕ) where
  students : Fin B → ℕ
  assignments : Fin B → ℕ
  law : (b : Fin B) → FiniteDesign (Fin (assignments b))
  exposed : (b : Fin B) → Fin (assignments b) → Fin (students b) → Bool
  y : (b : Fin B) → Fin (students b) → ℝ
  g : (b : Fin B) → Fin (students b) → ℝ
  pi : (b : Fin B) → Fin (students b) → ℝ
  pi_def : ∀ b i, pi b i = designMean (law b)
    (fun z => if exposed b z i then (1:ℝ) else 0)
  pi_pos : ∀ b i, 0 < pi b i

/-- N_B is the number of retained students, SI p. 19's N_s: sum of
the retained counts, conditional on fixed eligible groups and networks. -/
def retainedSize {B : ℕ} (r : RetainedBlockRow B) : ℕ := ∑ b, r.students b

/-- Joint block sample space; dependence inside a block is unrestricted. -/
abbrev BlockSample {B : ℕ} (r : RetainedBlockRow B) := (b : Fin B) → Fin (r.assignments b)

/-- Independent block randomizations have product probability. This
is independence of entire four-school blocks, not of their schools. -/
noncomputable def blockRowProbability {B : ℕ} (r : RetainedBlockRow B)
    (event : BlockSample r → Prop) : ℝ := by
  classical
  exact ∑ w, (∏ b, (r.law b).weight (w b)) * if event w then 1 else 0

/-- P037-T11's oracle block total X_b=sum_{i in S_b} h_i, with fixed
prediction g and true exposure probability π. -/
noncomputable def oracleBlockTotal {B : ℕ} (r : RetainedBlockRow B)
    (b : Fin B) (z : Fin (r.assignments b)) : ℝ :=
  ∑ i, augmentedContribution (if r.exposed b z i then 1 else 0)
    (r.pi b i) (r.y b i) (r.g b i)

/-- Oracle finite-population mean estimator, the fixed-g exact-π version
of SI p. 19's μ̂_R(d_k), on the unchanged retained population. -/
noncomputable def oracleRowMean {B : ℕ} (r : RetainedBlockRow B) (w : BlockSample r) : ℝ :=
  (∑ b, oracleBlockTotal r b (w b)) / retainedSize r

/-- SI p. 18's μ(d_k), restricted to the retained students per p. 19;
y_i(d_k) are fixed finite-population potential outcomes. -/
noncomputable def retainedPotentialMean {B : ℕ} (r : RetainedBlockRow B) : ℝ :=
  (∑ b, ∑ i, r.y b i) / retainedSize r

/-- s_B² is the sum of the independent block-total variances.
Its square root is the normalizing SD in P037-T11(6). -/
noncomputable def rowTotalVariance {B : ℕ} (r : RetainedBlockRow B) : ℝ :=
  ∑ b, designVariance (r.law b) (oracleBlockTotal r b)

/-- Sufficient regularity in P037-T11(3)--(6), not conditions
verified for the 56 empirical schools. Uniform block size, population
growth, positivity and bounded outcomes/predictions are explicit. -/
def UniformBlockBounds (r : ∀ B, RetainedBlockRow (B+1)) (m : ℕ) (c eta K : ℝ) : Prop :=
  0 < c ∧ 0 < eta ∧ 0 ≤ K ∧
  ∀ B, c*(B+1) ≤ retainedSize (r B) ∧
    ∀ b, (r B).students b ≤ m ∧
      ∀ i, eta ≤ (r B).pi b i ∧ |(r B).y b i| ≤ K ∧ |(r B).g b i| ≤ K

/-- P037-T11(1): exact finite unbiasedness of every oracle block total.
Exposures inside the block may be arbitrarily dependent. -/
theorem oracle_block_unbiased {B : ℕ} (r : RetainedBlockRow B) (b : Fin B) :
    designMean (r.law b) (oracleBlockTotal r b) = ∑ i, r.y b i := by
  unfold oracleBlockTotal
  rw [designMean_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact augmented_contribution_unbiased (r.law b) _ _ _ _
    (ne_of_gt (r.pi_pos b i)) (r.pi_def b i).symm

/-- P037-T11(1),(4): unbiasedness and the exact variance identity for
the retained-population oracle mean under independent block laws. -/
theorem oracle_row_unbiased {B : ℕ} (r : RetainedBlockRow B) :
    designMean (productDesign r.law) (oracleRowMean r) = retainedPotentialMean r ∧
    designVariance (productDesign r.law) (oracleRowMean r) =
      rowTotalVariance r/(retainedSize r:ℝ)^2 := by
  have hm : (oracleRowMean r) =
      (fun w => (1/(retainedSize r:ℝ))*(∑ b, oracleBlockTotal r b (w b))) := by
    funext w; unfold oracleRowMean; ring
  constructor
  · rw [hm, designMean_mul, designMean_sum]
    simp_rw [product_design_coordinate_mean, oracle_block_unbiased]
    unfold retainedPotentialMean
    ring
  · rw [hm, designVariance_mul, product_design_sum_variance]
    unfold rowTotalVariance
    ring

/-- Nonnegativity of the actual centered finite design variance. -/
theorem designVariance_nonneg {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) : 0 ≤ designVariance d X := by
  rw [designVariance_centered]
  unfold designMean
  apply Finset.sum_nonneg; intro w _
  exact mul_nonneg (d.nonneg w) (sq_nonneg _)

/-- P037-T11(3)'s finite variance lemma: a bounded variable has
variance at most the square of its bound under a normalized design. -/
theorem bounded_design_variance {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hx : ∀ w, |X w| ≤ A) : designVariance d X ≤ A^2 := by
  have hsq : ∀ w, (X w)^2 ≤ A^2 := by
    intro w; nlinarith [hx w, abs_nonneg (X w), sq_abs (X w)]
  have hmean : designMean d (fun w => (X w)^2) ≤ A^2 := by
    rw [← designMean_const d (A^2)]
    unfold designMean
    apply Finset.sum_le_sum; intro w _
    exact mul_le_mul_of_nonneg_left (hsq w) (d.nonneg w)
  unfold designVariance
  nlinarith [sq_nonneg (designMean d X)]

/-- P037-T11(3): exact bound on the retained-student oracle block
total, then its variance; no within-block independence is required. -/
theorem oracle_block_bounds {B : ℕ} (r : RetainedBlockRow B)
    (m : ℕ) (eta K : ℝ) (heta : 0 < eta) (hK : 0 ≤ K)
    (hn : ∀ b, r.students b ≤ m)
    (hb : ∀ b i, eta ≤ r.pi b i ∧ |r.y b i| ≤ K ∧ |r.g b i| ≤ K) :
    (∀ b z, |oracleBlockTotal r b z| ≤ m*(K+2*K/eta)) ∧
    (∀ b, designVariance (r.law b) (oracleBlockTotal r b) ≤ (m:ℝ)^2*(K+2*K/eta)^2) := by
  have hH : 0 ≤ K+2*K/eta := by positivity
  have hs : ∀ b z, |oracleBlockTotal r b z| ≤ m*(K+2*K/eta) := by
    intro b z
    have hi : ∀ i, |augmentedContribution (if r.exposed b z i then 1 else 0)
        (r.pi b i) (r.y b i) (r.g b i)| ≤ K+2*K/eta := by
      intro i
      exact augmented_contribution_bound _ _ _ _ _ _
        (by split_ifs <;> simp) heta (hb b i).1 (hb b i).2.1 (hb b i).2.2
    calc
      _ ≤ ∑ i, |augmentedContribution (if r.exposed b z i then 1 else 0)
          (r.pi b i) (r.y b i) (r.g b i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin (r.students b), (K+2*K/eta) := Finset.sum_le_sum (fun i _ => hi i)
      _ = (r.students b:ℝ)*(K+2*K/eta) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ m*(K+2*K/eta) := mul_le_mul_of_nonneg_right (by exact_mod_cast hn b) hH
  refine ⟨hs, ?_⟩
  intro b
  have hv := bounded_design_variance (r.law b) (oracleBlockTotal r b)
    ((m:ℝ)*(K+2*K/eta)) (by positivity) (hs b)
  simpa [mul_pow] using hv

/-- P037-T11(4): the independent-block variance bound of order 1/B,
derived from the actual block variances and the retained-population size. -/
theorem oracle_variance_rate_bound (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K : ℝ) (h : UniformBlockBounds r m c eta K) (B : ℕ) :
    rowTotalVariance (r B)/(retainedSize (r B):ℝ)^2 ≤
      (m:ℝ)^2*(K+2*K/eta)^2/(c^2*((B:ℝ)+1)) := by
  rcases h with ⟨hc, he, hK, hrows⟩
  have hb := oracle_block_bounds (r B) m eta K he hK
    (fun b => ((hrows B).2 b).1) (fun b i => ((hrows B).2 b).2 i)
  let A : ℝ := (m:ℝ)^2*(K+2*K/eta)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs : rowTotalVariance (r B) ≤ ((B:ℝ)+1)*A := by
    unfold rowTotalVariance
    calc
      _ ≤ ∑ _ : Fin (B+1), A := Finset.sum_le_sum (fun b _ => hb.2 b)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hN : c*((B:ℝ)+1) ≤ retainedSize (r B) := (hrows B).1
  have hcb : 0 < c*((B:ℝ)+1) := by positivity
  have hNpos : (0:ℝ) < retainedSize (r B) := lt_of_lt_of_le hcb hN
  have hsq : (c*((B:ℝ)+1))^2 ≤ (retainedSize (r B):ℝ)^2 := by
    nlinarith
  calc
    _ ≤ (((B:ℝ)+1)*A)/(retainedSize (r B):ℝ)^2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ ≤ A/(c^2*((B:ℝ)+1)) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hNpos) (by positivity)]
      convert mul_le_mul_of_nonneg_left hsq hA using 1 <;> ring

/-- P037-T11(3)--(5): finite block bounds and Chebyshev probability bound. -/
theorem oracle_row_finite_bounds (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K : ℝ) (h : UniformBlockBounds r m c eta K)
    (B : ℕ) (eps : ℝ) (heps : 0 < eps) :
    (∀ b z, |oracleBlockTotal (r B) b z| ≤ m*(K+2*K/eta)) ∧
    (∀ b, designVariance ((r B).law b) (oracleBlockTotal (r B) b) ≤
      (m:ℝ)^2*(K+2*K/eta)^2) ∧
    rowTotalVariance (r B)/(retainedSize (r B):ℝ)^2 ≤
      (m:ℝ)^2*(K+2*K/eta)^2/(c^2*(B+1)) ∧
    blockRowProbability (r B) (fun w => eps < |oracleRowMean (r B) w-retainedPotentialMean (r B)|) ≤
      (m:ℝ)^2*(K+2*K/eta)^2/(c^2*(B+1)*eps^2) := by
  rcases h with ⟨hc, he, hK, hrows⟩
  have hb := oracle_block_bounds (r B) m eta K he hK
    (fun b => ((hrows B).2 b).1) (fun b i => ((hrows B).2 b).2 i)
  have hr := oracle_variance_rate_bound r m c eta K ⟨hc,he,hK,hrows⟩ B
  refine ⟨hb.1, hb.2, hr, ?_⟩
  have ht := finite_chebyshev (productDesign (r B).law) (oracleRowMean (r B)) eps heps
  rw [(oracle_row_unbiased (r B)).1, (oracle_row_unbiased (r B)).2] at ht
  have htail : blockRowProbability (r B)
      (fun w => eps < |oracleRowMean (r B) w-retainedPotentialMean (r B)|) ≤
      (rowTotalVariance (r B)/(retainedSize (r B):ℝ)^2)/eps^2 := by
    simpa only [blockRowProbability, designProbability, designMean, productDesign] using ht
  calc
    _ ≤ (rowTotalVariance (r B)/(retainedSize (r B):ℝ)^2)/eps^2 := htail
    _ ≤ ((m:ℝ)^2*(K+2*K/eta)^2/(c^2*((B:ℝ)+1)))/eps^2 :=
      div_le_div_of_nonneg_right hr (sq_nonneg eps)
    _ = _ := by rw [div_div]

/-- P037-T11(5): design consistency as the number of independently
randomized blocks grows, preserving the retained-population estimand. -/
theorem independent_blocks_oracle_consistent (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K : ℝ) (h : UniformBlockBounds r m c eta K)
    (eps : ℝ) (heps : 0 < eps) :
    Filter.Tendsto (fun B => blockRowProbability (r B)
      (fun w => eps < |oracleRowMean (r B) w-retainedPotentialMean (r B)|))
      Filter.atTop (nhds 0) := by
  classical
  have hn : ∀ B, 0 ≤ blockRowProbability (r B)
      (fun w => eps < |oracleRowMean (r B) w-retainedPotentialMean (r B)|) := by
    intro B
    unfold blockRowProbability
    apply Finset.sum_nonneg; intro w _
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun b _ => ((r B).law b).nonneg (w b))
    · dsimp; split_ifs <;> norm_num
  have hb : ∀ B, blockRowProbability (r B)
      (fun w => eps < |oracleRowMean (r B) w-retainedPotentialMean (r B)|) ≤
      (m:ℝ)^2*(K+2*K/eta)^2/(c^2*((B:ℝ)+1)*eps^2) := by
    intro B; exact (oracle_row_finite_bounds r m c eta K h B eps heps).2.2.2
  have ht : Filter.Tendsto (fun B : ℕ =>
      (m:ℝ)^2*(K+2*K/eta)^2/(c^2*((B:ℝ)+1)*eps^2)) Filter.atTop (nhds 0) := by
    have hz := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((m:ℝ)^2*(K+2*K/eta)^2/(c^2*eps^2))
    convert hz using 1
    · funext B; field_simp <;> ring
    · simp
  exact squeeze_zero hn hb ht

/-- A bounded finite random variable has a mean within the same
absolute bound. This supports the centered-block bound in T11(6). -/
theorem bounded_design_mean {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) (A : ℝ)
    (hx : ∀ z, |X z| ≤ A) : |designMean d X| ≤ A := by
  unfold designMean
  calc
    _ ≤ ∑ z, |d.weight z * X z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, d.weight z * |X z| := by
      apply Finset.sum_congr rfl; intro z _
      rw [abs_mul, abs_of_nonneg (d.nonneg z)]
    _ ≤ ∑ z, d.weight z * A := Finset.sum_le_sum
      (fun z _ => mul_le_mul_of_nonneg_left (hx z) (d.nonneg z))
    _ = A := by rw [← Finset.sum_mul, d.total, one_mul]

/-- P037-T11(6)'s exact finite bound: centering a block total doubles
the bound mH, with H=K+2K/η. No independence inside a block is required. -/
theorem oracle_block_centered_bound {B : ℕ} (r : RetainedBlockRow B)
    (m : ℕ) (eta K : ℝ) (heta : 0 < eta) (hK : 0 ≤ K)
    (hn : ∀ b, r.students b ≤ m)
    (hb : ∀ b i, eta ≤ r.pi b i ∧ |r.y b i| ≤ K ∧ |r.g b i| ≤ K) :
    ∀ b z, |oracleBlockTotal r b z-designMean (r.law b) (oracleBlockTotal r b)| ≤
      2*m*(K+2*K/eta) := by
  have h := (oracle_block_bounds r m eta K heta hK hn hb).1
  intro b z
  have hm := bounded_design_mean (r.law b) (oracleBlockTotal r b)
    (m*(K+2*K/eta)) (h b)
  calc
    _ ≤ |oracleBlockTotal r b z|+|designMean (r.law b) (oracleBlockTotal r b)| :=
      abs_sub _ _
    _ ≤ 2*m*(K+2*K/eta) := by linarith [h b z]

/-- P037-T11(6): the finite Lindeberg numerator is exactly zero once
ε sqrt(σ₀² B)>2mH; division by the positive total variance then also
gives zero. This finite lemma does not require a central limit theorem. -/
theorem oracle_lindeberg_vanish (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K sigmaSquared : ℝ)
    (h : UniformBlockBounds r m c eta K)
    (hv : ∀ B, sigmaSquared*(B+1) ≤ rowTotalVariance (r B))
    (B : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hsmall : 2*m*(K+2*K/eta) < eps*Real.sqrt (sigmaSquared*(B+1))) :
    (∑ b, designMean ((r B).law b) (fun z =>
      let U := oracleBlockTotal (r B) b z - designMean ((r B).law b) (oracleBlockTotal (r B) b)
      U^2 * if eps*Real.sqrt (rowTotalVariance (r B)) < |U| then 1 else 0)) = 0 := by
  rcases h with ⟨_, he, hK, hrows⟩
  have hbound := oracle_block_centered_bound (r B) m eta K he hK
    (fun b => ((hrows B).2 b).1) (fun b i => ((hrows B).2 b).2 i)
  have hcut : 2*m*(K+2*K/eta) < eps*Real.sqrt (rowTotalVariance (r B)) :=
    lt_of_lt_of_le hsmall (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hv B)) (le_of_lt heps))
  apply Finset.sum_eq_zero; intro b _
  unfold designMean
  apply Finset.sum_eq_zero; intro z _
  have hno : ¬ eps*Real.sqrt (rowTotalVariance (r B)) <
      |oracleBlockTotal (r B) b z-designMean ((r B).law b) (oracleBlockTotal (r B) b)| := by
    linarith [hbound b z]
  simp only [designMean] at hno
  simp only [hno, ite_false, mul_zero]

/-!
Finite product-law Lindeberg-Feller theorem. The general analytic CLT is
adapted from the Apache-2.0 StatLean development in
`AronowAudit.P037.P037_VaryingLindeberg`.
All finite-law, independence, moment and standardization identities below
are proved from the finite-design definitions.
-/
namespace BlockCLT
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
 def causalDesign {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω) :
    Causalean.Experimentation.DesignBased.FiniteDesign Ω :=
  ⟨d.weight, d.nonneg, d.total⟩

 def finiteMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (d : FiniteDesign Ω) : Measure Ω := (causalDesign d).toMeasure

instance finiteMeasure_probability {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (d : FiniteDesign Ω) : IsProbabilityMeasure (finiteMeasure d) := by
  unfold finiteMeasure
  infer_instance

 theorem integral_finite {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (d : FiniteDesign Ω) (f : Ω → ℝ) :
    ∫ x, f x ∂finiteMeasure d = designMean d f := by
  exact (causalDesign d).integral_toMeasure f

 theorem probability_finite {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (d : FiniteDesign Ω) (A : Ω → Prop) :
    (finiteMeasure d).real {z | A z} = designProbability d A := by
  exact (causalDesign d).toMeasure_real_setOf A

 theorem singleton_finite {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (d : FiniteDesign Ω) (z : Ω) :
    finiteMeasure d {z} = ENNReal.ofReal (d.weight z) := by
  classical
  simp [finiteMeasure, Causalean.Experimentation.DesignBased.FiniteDesign.toMeasure_apply,
    Measure.dirac_apply', causalDesign, eq_comm, Pi.single_apply]

 theorem product_finite {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (d : ∀ i, FiniteDesign (Ω i)) :
    finiteMeasure (productDesign d) = Measure.pi (fun i => finiteMeasure (d i)) := by
  apply Measure.ext_of_singleton
  intro w
  rw [singleton_finite, Measure.pi_singleton]
  simp only [productDesign]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    exact (singleton_finite (d i) (w i)).symm
  · intro i _
    exact (d i).nonneg (w i)

 theorem variance_finite {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (d : FiniteDesign Ω) (f : Ω → ℝ) :
    variance f (finiteMeasure d) = designVariance d f := by
  rw [finiteMeasure, Causalean.Experimentation.DesignBased.FiniteDesign.variance_toMeasure]
  exact (designVariance_centered d f).symm

/-- A bounded centered triangular array on its actual varying finite product
spaces has a Gaussian limit once total variance grows linearly. -/
 theorem finite_bounded_array_normal
    {m : ℕ → ℕ} {Ω : (n : ℕ) → Fin (m n) → Type*}
    [∀ n i, Fintype (Ω n i)] [∀ n i, MeasurableSpace (Ω n i)]
    [∀ n i, MeasurableSingletonClass (Ω n i)]
    (d : ∀ n i, FiniteDesign (Ω n i)) (X : ∀ n i, Ω n i → ℝ)
    (A sigma : ℝ) (hs : 0 < sigma)
    (hmean : ∀ n i, designMean (d n i) (X n i) = 0)
    (hbound : ∀ n i z, |X n i z| ≤ A)
    (hv : ∀ n : ℕ, sigma*((n:ℝ)+1) ≤ ∑ i, designVariance (d n i) (X n i)) :
    ∀ x : ℝ, Tendsto (fun n => designProbability (productDesign (d n)) (fun w =>
      (∑ i, X n i (w i)) / Real.sqrt (∑ i, designVariance (d n i) (X n i)) ≤ x))
      atTop (𝓝 ((gaussianReal 0 1 (Set.Iic x)).toReal)) := by
  let S := fun n => ∑ i, designVariance (d n i) (X n i)
  let P := fun n => finiteMeasure (productDesign (d n))
  let W := fun n (i : Fin (m n)) (w : ∀ j, Ω n j) =>
    (Real.sqrt (S n))⁻¹ * X n i (w i)
  have hSpos : ∀ n, 0 < S n := by
    intro n
    exact lt_of_lt_of_le (by positivity) (hv n)
  have hsqrt : ∀ n, 0 < Real.sqrt (S n) := fun n => Real.sqrt_pos.2 (hSpos n)
  have hS_top : Tendsto S atTop atTop := by
    have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_atTop_mono hv (hn.const_mul_atTop hs)
  have hsmall : Tendsto (fun n => A / Real.sqrt (S n)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp hS_top)) :
        Tendsto (fun n => A * (Real.sqrt (S n))⁻¹) atTop (𝓝 (A*0)))
  have hmeas : ∀ n i, Measurable (W n i) := fun n i => measurable_of_finite _
  have hindep : ∀ n, iIndepFun (W n) (P n) := by
    intro n
    rw [show P n = Measure.pi (fun i => finiteMeasure (d n i)) from product_finite (d n)]
    exact iIndepFun_pi (fun i => (measurable_of_finite
      (fun z => (Real.sqrt (S n))⁻¹ * X n i z)).aemeasurable)
  have hzero : ∀ n i, ∫ w, W n i w ∂P n = 0 := by
    intro n i
    rw [show P n = Measure.pi (fun j => finiteMeasure (d n j)) from product_finite (d n)]
    rw [integral_comp_eval ((measurable_of_finite
      (fun z => (Real.sqrt (S n))⁻¹ * X n i z)).aestronglyMeasurable)]
    rw [integral_const_mul, integral_finite, hmean n i, mul_zero]
  have hvar : ∀ n i, variance (W n i) (P n) =
      (Real.sqrt (S n))⁻¹ ^ 2 * designVariance (d n i) (X n i) := by
    intro n i
    rw [show P n = Measure.pi (fun j => finiteMeasure (d n j)) from product_finite (d n)]
    rw [(measurePreserving_eval (fun j => finiteMeasure (d n j)) i).variance_fun_comp
      (f := fun z => (Real.sqrt (S n))⁻¹ * X n i z) (measurable_of_finite _).aemeasurable]
    rw [variance_const_mul, variance_finite]
  have hsumvar : ∀ n, ∑ i, variance (W n i) (P n) = 1 := by
    intro n
    simp_rw [hvar]
    rw [← Finset.mul_sum]
    change (Real.sqrt (S n))⁻¹ ^ 2 * S n = 1
    rw [inv_pow, Real.sq_sqrt (hSpos n).le]
    exact inv_mul_cancel₀ (ne_of_gt (hSpos n))
  have hb : ∀ n i w, |W n i w| ≤ A / Real.sqrt (S n) := by
    intro n i w
    dsimp [W]
    rw [abs_mul, abs_inv, abs_of_pos (hsqrt n)]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (hbound n i (w i)) (inv_nonneg.mpr (hsqrt n).le)
  have hCLT := LindebergCompletion.lindeberg_clt_of_bounded
    (P := P) (P' := gaussianReal 0 1) (Z := id) hmeas hindep hzero
    (by simp only [hsumvar]; exact tendsto_const_nhds) hb hsmall
    (show HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) from
      ⟨aemeasurable_id, Measure.map_id⟩)
  intro x
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hfront : (gaussianReal 0 1).map (id : ℝ → ℝ) (frontier (Set.Iic x)) = 0 := by
    simp [frontier_Iic]
  have hCDF := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hCLT.tendsto hfront
  have hCDF' : Tendsto (fun n => (P n).map (fun w => ∑ i, W n i w) (Set.Iic x))
      atTop (𝓝 (gaussianReal 0 1 (Set.Iic x))) := by
    simpa using hCDF
  have hreal := (ENNReal.tendsto_toReal
    (measure_ne_top (gaussianReal 0 1) (Set.Iic x))).comp hCDF' 
  have hsum : ∀ n w, (∑ i, W n i w) =
      (∑ i, X n i (w i))/Real.sqrt (S n) := by
    intro n w
    dsimp only [W]
    rw [← Finset.mul_sum]
    ring
  have hEq : ∀ n, ((P n).map (fun w => ∑ i, W n i w) (Set.Iic x)).toReal =
      designProbability (productDesign (d n)) (fun w =>
        (∑ i, X n i (w i))/Real.sqrt (S n) ≤ x) := by
    intro n
    rw [Measure.map_apply_of_aemeasurable (hCLT.forall_aemeasurable n) measurableSet_Iic]
    change (P n).real {w | (∑ i, W n i w) ≤ x} = _
    simp_rw [hsum]
    exact probability_finite (productDesign (d n)) _
  simpa only [Function.comp_def, hEq] using hreal

 theorem designVariance_sub_constant {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (f : Ω → ℝ) (c : ℝ) :
    designVariance d (fun z => f z-c) = designVariance d f := by
  rw [designVariance_centered, designMean_sub, designMean_const]
  convert (designVariance_centered d f).symm using 1
  congr 1
  funext z
  ring

 theorem finite_centered_blocks_normal
    {m : ℕ → ℕ} {Ω : (n : ℕ) → Fin (m n) → Type*}
    [∀ n i, Fintype (Ω n i)] [∀ n i, MeasurableSpace (Ω n i)]
    [∀ n i, MeasurableSingletonClass (Ω n i)]
    (d : ∀ n i, FiniteDesign (Ω n i)) (X : ∀ n i, Ω n i → ℝ)
    (A sigma : ℝ) (hs : 0 < sigma)
    (hbound : ∀ n i z, |X n i z| ≤ A)
    (hv : ∀ n : ℕ, sigma*((n:ℝ)+1) ≤ ∑ i, designVariance (d n i) (X n i)) :
    ∀ x : ℝ, Tendsto (fun n => designProbability (productDesign (d n)) (fun w =>
      (∑ i, (X n i (w i)-designMean (d n i) (X n i))) /
        Real.sqrt (∑ i, designVariance (d n i) (X n i)) ≤ x))
      atTop (𝓝 ((gaussianReal 0 1 (Set.Iic x)).toReal)) := by
  have h := finite_bounded_array_normal d
    (fun n i z => X n i z-designMean (d n i) (X n i)) (2*A) sigma hs
    (fun n i => by rw [designMean_sub, designMean_const, sub_self])
    (fun n i z => by
      have hm := bounded_design_mean (d n i) (X n i) A (hbound n i)
      calc
        _ ≤ |X n i z|+|designMean (d n i) (X n i)| := abs_sub _ _
        _ ≤ 2*A := by linarith [hbound n i z])
    (by simpa only [designVariance_sub_constant] using hv)
  simpa only [designVariance_sub_constant] using h

local instance finite_measurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤
local instance finite_singleton (n : ℕ) : MeasurableSingletonClass (Fin n) :=
  ⟨fun _ => trivial⟩

 theorem oracle_normal_completed (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K sigmaSquared : ℝ)
    (h : UniformBlockBounds r m c eta K) (hs : 0 < sigmaSquared)
    (hv : ∀ B, sigmaSquared*(B+1) ≤ rowTotalVariance (r B)) :
    ∀ x : ℝ, Tendsto (fun B => blockRowProbability (r B) (fun w =>
      (retainedSize (r B):ℝ)*(oracleRowMean (r B) w-retainedPotentialMean (r B)) /
        Real.sqrt (rowTotalVariance (r B)) ≤ x)) atTop
      (𝓝 ((gaussianReal 0 1 (Set.Iic x)).toReal)) := by
  have hb := fun B => (oracle_block_bounds (r B) m eta K h.2.1 h.2.2.1
    (fun b => ((h.2.2.2 B).2 b).1) (fun b i => ((h.2.2.2 B).2 b).2 i)).1
  have hnormal := finite_centered_blocks_normal
    (fun B b => (r B).law b) (fun B b => oracleBlockTotal (r B) b)
    ((m:ℝ)*(K+2*K/eta)) sigmaSquared hs hb hv
  intro x
  apply (hnormal x).congr
  intro B
  have hN : (retainedSize (r B):ℝ) ≠ 0 := by
    have hsize := (h.2.2.2 B).1
    have hc : 0 < c := h.1
    have hp : 0 < c*((B:ℝ)+1) := by positivity
    exact ne_of_gt (lt_of_lt_of_le hp hsize)
  have hstat : ∀ w, (∑ i, (oracleBlockTotal (r B) i (w i) -
      designMean ((r B).law i) (oracleBlockTotal (r B) i))) /
        Real.sqrt (∑ i, designVariance ((r B).law i) (oracleBlockTotal (r B) i)) =
      (retainedSize (r B):ℝ)*(oracleRowMean (r B) w-retainedPotentialMean (r B)) /
        Real.sqrt (rowTotalVariance (r B)) := by
    intro w
    congr 1
    simp only [Finset.sum_sub_distrib, oracle_block_unbiased]
    unfold oracleRowMean retainedPotentialMean
    field_simp
  simp_rw [hstat]
  rfl


end
end BlockCLT

/-- P037-T11(6): bounded independent block totals satisfy the Lindeberg
condition and their standardized sum converges in distribution to N(0,1)
under a linear variance lower bound. Distribution convergence is stated
by CDFs at every real x (the Gaussian CDF is continuous everywhere). -/
theorem independent_blocks_oracle_normal (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K sigmaSquared : ℝ)
    (h : UniformBlockBounds r m c eta K) (hs : 0 < sigmaSquared)
    (hv : ∀ B, sigmaSquared*(B+1) ≤ rowTotalVariance (r B)) :
    (∀ (B : ℕ) (eps : ℝ), 0 < eps → 2*m*(K+2*K/eta) < eps*Real.sqrt (sigmaSquared*(B+1)) →
      (∑ b, designMean ((r B).law b) (fun z =>
        let U := oracleBlockTotal (r B) b z - designMean ((r B).law b) (oracleBlockTotal (r B) b)
        U^2 * if eps*Real.sqrt (rowTotalVariance (r B)) < |U| then 1 else 0)) = 0) ∧
    (∀ x : ℝ, Filter.Tendsto (fun B => blockRowProbability (r B) (fun w =>
      (retainedSize (r B):ℝ)*(oracleRowMean (r B) w-retainedPotentialMean (r B)) /
        Real.sqrt (rowTotalVariance (r B)) ≤ x)) Filter.atTop
      (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal))) := by
  constructor
  · intro B eps heps hsmall
    exact oracle_lindeberg_vanish r m c eta K sigmaSquared h hv B eps heps hsmall
  · exact BlockCLT.oracle_normal_completed r m c eta K sigmaSquared h hs hv

/-- A second exposure measured on the *same* retained students and
randomized block assignments, for the contrasts of SI p. 19 and T11(7).
No independence between the two exposure indicators is postulated. -/
structure SecondRowExposure {B : ℕ} (r : RetainedBlockRow B) where
  exposed : (b : Fin B) → Fin (r.assignments b) → Fin (r.students b) → Bool
  y : (b : Fin B) → Fin (r.students b) → ℝ
  g : (b : Fin B) → Fin (r.students b) → ℝ
  pi : (b : Fin B) → Fin (r.students b) → ℝ
  pi_def : ∀ b i, pi b i = designMean (r.law b)
    (fun z => if exposed b z i then (1:ℝ) else 0)
  pi_pos : ∀ b i, 0 < pi b i

/-- The second exposure's μ̂_R(d_l) and μ(d_l), SI p. 19 / T11(7),
on the same retained students and block assignment laws as the first. -/
abbrev secondExposureRow {B : ℕ} (r : RetainedBlockRow B)
    (s : SecondRowExposure r) : RetainedBlockRow B where
  students := r.students
  assignments := r.assignments
  law := r.law
  exposed := s.exposed
  y := s.y
  g := s.g
  pi := s.pi
  pi_def := s.pi_def
  pi_pos := s.pi_pos

/-- Block total for the difference of two regression-augmented exposure
means, using the same block assignment in both terms. -/
noncomputable def oracleContrastBlock {B : ℕ} (r : RetainedBlockRow B)
    (s : SecondRowExposure r) (b : Fin B) (z : Fin (r.assignments b)) : ℝ :=
  oracleBlockTotal r b z - ∑ i, augmentedContribution
    (if s.exposed b z i then 1 else 0) (s.pi b i) (s.y b i) (s.g b i)

/-- Retained-population average causal exposure contrast μ(d_k)-μ(d_l). -/
noncomputable def retainedContrast {B : ℕ} (r : RetainedBlockRow B)
    (s : SecondRowExposure r) : ℝ :=
  (∑ b, ∑ i, (r.y b i-s.y b i)) / retainedSize r

/-- The contrast estimator from the two paired oracle means. -/
noncomputable def oracleRowContrast {B : ℕ} (r : RetainedBlockRow B)
    (s : SecondRowExposure r) (w : BlockSample r) : ℝ :=
  (∑ b, oracleContrastBlock r s b (w b)) / retainedSize r

/-- P037-T11(7)'s finite identities: the paired oracle contrast is
unbiased for μ(d_k)-μ(d_l), its variance is the sum of contrast block
variances divided by N², and the contribution bound doubles to 2mH.
The two exposure-specific estimates are not assumed independent. -/
theorem oracle_contrast_finite_facts {B : ℕ} (r : RetainedBlockRow B)
    (s : SecondRowExposure r) (m : ℕ) (eta K : ℝ)
    (heta : 0 < eta) (hK : 0 ≤ K) (hn : ∀ b, r.students b ≤ m)
    (hb : ∀ b i, eta ≤ r.pi b i ∧ |r.y b i| ≤ K ∧ |r.g b i| ≤ K)
    (h2 : ∀ b i, eta ≤ s.pi b i ∧ |s.y b i| ≤ K ∧ |s.g b i| ≤ K) :
    designMean (productDesign r.law) (oracleRowContrast r s)=retainedContrast r s ∧
    designVariance (productDesign r.law) (oracleRowContrast r s)=
      (∑ b, designVariance (r.law b) (oracleContrastBlock r s b))/(retainedSize r:ℝ)^2 ∧
    (∀ b z, |oracleContrastBlock r s b z| ≤ 2*m*(K+2*K/eta)) ∧
    (∀ b, designVariance (r.law b) (oracleContrastBlock r s b) ≤
      (2*m*(K+2*K/eta))^2) := by
  have hmu : ∀ b, designMean (r.law b) (oracleContrastBlock r s b)=
      ∑ i, (r.y b i-s.y b i) := by
    intro b
    change designMean (r.law b) (fun z =>
      oracleBlockTotal r b z-oracleBlockTotal (secondExposureRow r s) b z)=_
    rw [designMean_sub, oracle_block_unbiased r b,
      oracle_block_unbiased (secondExposureRow r s) b, Finset.sum_sub_distrib]
  have hm : oracleRowContrast r s =
      fun w => (1/(retainedSize r:ℝ))*(∑ b, oracleContrastBlock r s b (w b)) := by
    funext w; unfold oracleRowContrast; ring
  have hfirst := (oracle_block_bounds r m eta K heta hK hn hb).1
  have hsecond := (oracle_block_bounds (secondExposureRow r s) m eta K heta hK hn h2).1
  have hbound : ∀ b z, |oracleContrastBlock r s b z| ≤ 2*m*(K+2*K/eta) := by
    intro b z
    change |oracleBlockTotal r b z-oracleBlockTotal (secondExposureRow r s) b z| ≤ _
    calc
      _ ≤ |oracleBlockTotal r b z|+|oracleBlockTotal (secondExposureRow r s) b z| := abs_sub _ _
      _ ≤ _ := by linarith [hfirst b z, hsecond b z]
  refine ⟨?_, ?_, hbound, ?_⟩
  · rw [hm, designMean_mul, designMean_sum]
    simp_rw [product_design_coordinate_mean, hmu]
    unfold retainedContrast
    ring
  · rw [hm, designVariance_mul, product_design_sum_variance]
    ring
  · intro b
    exact bounded_design_variance (r.law b) (oracleContrastBlock r s b)
      (2*m*(K+2*K/eta)) (by positivity) (hbound b)

namespace BlockCLT
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] finite_measurable finite_singleton
 theorem finite_consistency {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (X : ∀ n, Ω n → ℝ) (mu : ℕ → ℝ)
    (hm : ∀ n, designMean (d n) (X n) = mu n)
    (hv : Tendsto (fun n => designVariance (d n) (X n)) atTop (𝓝 0)) :
    ∀ eps : ℝ, 0 < eps → Tendsto (fun n => designProbability (d n)
      (fun w => eps < |X n w-mu n|)) atTop (𝓝 0) := by
  intro eps heps
  have hu : ∀ n, designProbability (d n) (fun w => eps < |X n w-mu n|) ≤
      designVariance (d n) (X n)/eps^2 := by
    intro n
    simpa only [hm n] using finite_chebyshev (d n) (X n) eps heps
  have hn : ∀ n, 0 ≤ designProbability (d n) (fun w => eps < |X n w-mu n|) := by
    intro n
    unfold designProbability designMean
    apply Finset.sum_nonneg
    intro w _
    apply mul_nonneg ((d n).nonneg w)
    dsimp
    split_ifs <;> norm_num
  exact squeeze_zero hn hu (by simpa using hv.div_const (eps^2))

 theorem contrast_variance_bound (r : ∀ B, RetainedBlockRow (B+1))
    (s : ∀ B, SecondRowExposure (r B)) (m : ℕ) (c eta K : ℝ)
    (h : UniformBlockBounds r m c eta K)
    (h2 : ∀ B b i, eta ≤ (s B).pi b i ∧ |(s B).y b i| ≤ K ∧ |(s B).g b i| ≤ K)
    (B : ℕ) :
    designVariance (productDesign (r B).law) (oracleRowContrast (r B) (s B)) ≤
      (2*m*(K+2*K/eta))^2/(c^2*((B:ℝ)+1)) := by
  have hf := oracle_contrast_finite_facts (r B) (s B) m eta K h.2.1 h.2.2.1
    (fun b => ((h.2.2.2 B).2 b).1) (fun b i => ((h.2.2.2 B).2 b).2 i) (h2 B)
  rw [hf.2.1]
  let A : ℝ := (2*m*(K+2*K/eta))^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs : (∑ b, designVariance ((r B).law b) (oracleContrastBlock (r B) (s B) b)) ≤
      ((B:ℝ)+1)*A := by
    calc
      _ ≤ ∑ _ : Fin (B+1), A := Finset.sum_le_sum (fun b _ => hf.2.2.2 b)
      _ = _ := by simp [A, Nat.cast_add, Nat.cast_one]
  have hc : 0 < c := h.1
  have hN := (h.2.2.2 B).1
  have hcb : 0 < c*((B:ℝ)+1) := by positivity
  have hNp : 0 < (retainedSize (r B):ℝ) := lt_of_lt_of_le hcb hN
  have hsq : (c*((B:ℝ)+1))^2 ≤ (retainedSize (r B):ℝ)^2 := by nlinarith
  calc
    _ ≤ (((B:ℝ)+1)*A)/(retainedSize (r B):ℝ)^2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ ≤ A/(c^2*((B:ℝ)+1)) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hNp) (by positivity)]
      convert mul_le_mul_of_nonneg_left hsq hA using 1 <;> ring

 theorem contrast_consistent (r : ∀ B, RetainedBlockRow (B+1))
    (s : ∀ B, SecondRowExposure (r B)) (m : ℕ) (c eta K : ℝ)
    (h : UniformBlockBounds r m c eta K)
    (h2 : ∀ B b i, eta ≤ (s B).pi b i ∧ |(s B).y b i| ≤ K ∧ |(s B).g b i| ≤ K) :
    ∀ eps : ℝ, 0 < eps → Tendsto (fun B => blockRowProbability (r B)
      (fun w => eps < |oracleRowContrast (r B) (s B) w-retainedContrast (r B) (s B)|))
      atTop (𝓝 0) := by
  have hm := fun B => (oracle_contrast_finite_facts (r B) (s B) m eta K h.2.1 h.2.2.1
    (fun b => ((h.2.2.2 B).2 b).1) (fun b i => ((h.2.2.2 B).2 b).2 i) (h2 B)).1
  have hv : Tendsto (fun B => designVariance (productDesign (r B).law)
      (oracleRowContrast (r B) (s B))) atTop (𝓝 0) := by
    apply squeeze_zero (fun B => designVariance_nonneg _ _)
      (contrast_variance_bound r s m c eta K h h2)
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((2*m*(K+2*K/eta))^2/c^2)
    convert ht using 1
    · funext B
      field_simp <;> ring
    · simp
  simpa only [blockRowProbability, designProbability, designMean, productDesign] using
    finite_consistency (fun B => productDesign (r B).law)
      (fun B => oracleRowContrast (r B) (s B)) (fun B => retainedContrast (r B) (s B)) hm hv

 theorem contrast_normal (r : ∀ B, RetainedBlockRow (B+1))
    (s : ∀ B, SecondRowExposure (r B)) (m : ℕ) (c eta K : ℝ)
    (h : UniformBlockBounds r m c eta K)
    (h2 : ∀ B b i, eta ≤ (s B).pi b i ∧ |(s B).y b i| ≤ K ∧ |(s B).g b i| ≤ K)
    (v : ℝ) (hvpos : 0 < v)
    (hv : ∀ B, v*(B+1) ≤ ∑ b, designVariance ((r B).law b) (oracleContrastBlock (r B) (s B) b)) :
    ∀ x : ℝ, Tendsto (fun B => blockRowProbability (r B) (fun w =>
      (retainedSize (r B):ℝ)*(oracleRowContrast (r B) (s B) w-retainedContrast (r B) (s B)) /
        Real.sqrt (∑ b, designVariance ((r B).law b) (oracleContrastBlock (r B) (s B) b)) ≤ x))
      atTop (𝓝 ((gaussianReal 0 1 (Set.Iic x)).toReal)) := by
  have hb := fun B => (oracle_contrast_finite_facts (r B) (s B) m eta K h.2.1 h.2.2.1
    (fun b => ((h.2.2.2 B).2 b).1) (fun b i => ((h.2.2.2 B).2 b).2 i) (h2 B)).2.2.1
  have hnormal := finite_centered_blocks_normal
    (fun B b => (r B).law b) (fun B b => oracleContrastBlock (r B) (s B) b)
    (2*m*(K+2*K/eta)) v hvpos hb hv
  intro x
  apply (hnormal x).congr
  intro B
  have hN : (retainedSize (r B):ℝ) ≠ 0 := by
    have hsize := (h.2.2.2 B).1
    have hc : 0 < c := h.1
    have hp : 0 < c*((B:ℝ)+1) := by positivity
    exact ne_of_gt (lt_of_lt_of_le hp hsize)
  have hmu : ∀ b, designMean ((r B).law b) (oracleContrastBlock (r B) (s B) b) =
      ∑ i, ((r B).y b i-(s B).y b i) := by
    intro b
    change designMean ((r B).law b) (fun z => oracleBlockTotal (r B) b z -
      oracleBlockTotal (secondExposureRow (r B) (s B)) b z) = _
    rw [designMean_sub, oracle_block_unbiased (r B) b,
      oracle_block_unbiased (secondExposureRow (r B) (s B)) b, Finset.sum_sub_distrib]
  have hstat : ∀ w, (∑ i, (oracleContrastBlock (r B) (s B) i (w i) -
      designMean ((r B).law i) (oracleContrastBlock (r B) (s B) i))) =
      (retainedSize (r B):ℝ)*(oracleRowContrast (r B) (s B) w-retainedContrast (r B) (s B)) := by
    intro w
    simp only [Finset.sum_sub_distrib, hmu]
    unfold oracleRowContrast retainedContrast
    simp only [Finset.sum_sub_distrib]
    field_simp
  simp_rw [hstat]
  rfl

end
end BlockCLT

/-- P037-T11(7): the same independent-block consistency and Gaussian
CLT for exposure contrasts, with H doubled and the lower variance bound
imposed on contrast totals, without assuming the two estimates independent. -/
theorem independent_blocks_exposure_contrasts (r : ∀ B, RetainedBlockRow (B+1))
    (s : ∀ B, SecondRowExposure (r B)) (m : ℕ) (c eta K : ℝ)
    (h : UniformBlockBounds r m c eta K)
    (h2 : ∀ B b i, eta ≤ (s B).pi b i ∧ |(s B).y b i| ≤ K ∧ |(s B).g b i| ≤ K) :
    (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => blockRowProbability (r B)
      (fun w => eps < |oracleRowContrast (r B) (s B) w-retainedContrast (r B) (s B)|))
      Filter.atTop (nhds 0)) ∧
    (∀ v : ℝ, 0 < v →
      (∀ B, v*(B+1) ≤ ∑ b, designVariance ((r B).law b) (oracleContrastBlock (r B) (s B) b)) →
      ∀ x : ℝ, Filter.Tendsto (fun B => blockRowProbability (r B) (fun w =>
        (retainedSize (r B):ℝ)*(oracleRowContrast (r B) (s B) w-retainedContrast (r B) (s B)) /
          Real.sqrt (∑ b, designVariance ((r B).law b) (oracleContrastBlock (r B) (s B) b)) ≤ x))
        Filter.atTop (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal))) := by
  constructor
  · exact BlockCLT.contrast_consistent r s m c eta K h h2
  · intro v hvpos hv x
    exact BlockCLT.contrast_normal r s m c eta K h h2 v hvpos hv x

/-- P037-T11(8)'s coefficient and probability subtraction identities
at the individual contribution level; the population versions are finite
sums of these exact algebraic equalities. -/
theorem augmented_subtraction_certificates (I pi p y gh gs : ℝ) :
    augmentedContribution I pi y gh-augmentedContribution I pi y gs =
      (1-I/pi)*(gh-gs) ∧
    augmentedContribution I p y gh-augmentedContribution I pi y gh =
      I*(y-gh)*(p⁻¹-pi⁻¹) := by
  unfold augmentedContribution
  simp only [div_eq_mul_inv]
  constructor <;> ring

/-- Fixed-dimensional covariate vector x_i in SI p. 19's regression;
linear fitted specification g(x_i,ξ)=x_i'ξ is a sufficient
case, rather than a claim that the paper specified g this narrowly. -/
abbrev RowCovariates {B : ℕ} (r : RetainedBlockRow B) (q : ℕ) :=
  (b : Fin B) → Fin (r.students b) → Fin q → ℝ

/-- The fitted linear version of μ̂_R(d_k) of SI p. 19, evaluated at
an arbitrary coefficient β and positive exposure weights p. -/
noncomputable def fittedRowMean {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q) (beta : Fin q → ℝ)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r) : ℝ :=
  (∑ b, ∑ i, augmentedContribution (if r.exposed b (w b) i then 1 else 0)
    (p b i) (r.y b i) (∑ k, x b i k*beta k)) / retainedSize r

/-- The SI p. 19 IPW least-squares coefficient: inverse weighted Gram
times weighted outcome cross-products. On singular samples the zero
inverse is used. An asymptotic conclusion for this coefficient requires
singular samples to have vanishing probability. -/
noncomputable def fittedRowCoefficient {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r) : Fin q → ℝ :=
  let G : Matrix (Fin q) (Fin q) ℝ := fun k l => ∑ b, ∑ i,
    (if r.exposed b (w b) i then 1 else 0)/p b i * x b i k*x b i l
  let v : Fin q → ℝ := fun k => ∑ b, ∑ i,
    (if r.exposed b (w b) i then 1 else 0)/p b i * x b i k*r.y b i
  G⁻¹.mulVec v

/-- P037-T11(8): the exact two subtraction identities separating
coefficient-fitting error from simulated-probability error, for every
fixed population and realization. These identities contain no asymptotics. -/
theorem fitted_mean_subtraction_identities {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q) (betaHat betaStar : Fin q → ℝ)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r)
    (hp : ∀ b i, 0 < p b i) :
    fittedRowMean r x betaHat r.pi w-fittedRowMean r x betaStar r.pi w =
      (∑ k, ((∑ b, ∑ i,
        (1-(if r.exposed b (w b) i then 1 else 0)/r.pi b i)*x b i k) / retainedSize r)*
        (betaHat k-betaStar k)) ∧
    fittedRowMean r x betaHat p w-fittedRowMean r x betaHat r.pi w =
      (∑ b, ∑ i, (if r.exposed b (w b) i then 1 else 0)*
        (r.y b i-(∑ k, x b i k*betaHat k)) * ((p b i)⁻¹-(r.pi b i)⁻¹)) / retainedSize r := by
  have hterm : ∀ b i,
      augmentedContribution (if r.exposed b (w b) i then 1 else 0) (r.pi b i) (r.y b i)
        (∑ k, x b i k*betaHat k) -
      augmentedContribution (if r.exposed b (w b) i then 1 else 0) (r.pi b i) (r.y b i)
        (∑ k, x b i k*betaStar k) =
      ∑ k, (1-(if r.exposed b (w b) i then 1 else 0)/r.pi b i)*x b i k*(betaHat k-betaStar k) := by
    intro b i
    rw [(augmented_subtraction_certificates _ _ (p b i) _ _ _).1]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  constructor
  · calc
      _ = (∑ b, ∑ i,
          (augmentedContribution (if r.exposed b (w b) i then 1 else 0) (r.pi b i) (r.y b i)
            (∑ k, x b i k*betaHat k) -
          augmentedContribution (if r.exposed b (w b) i then 1 else 0) (r.pi b i) (r.y b i)
            (∑ k, x b i k*betaStar k))) / retainedSize r := by
        unfold fittedRowMean
        rw [← sub_div, ← Finset.sum_sub_distrib]
        simp_rw [← Finset.sum_sub_distrib]
      _ = (∑ b, ∑ i, ∑ k,
          (1-(if r.exposed b (w b) i then 1 else 0)/r.pi b i)*x b i k*(betaHat k-betaStar k)) /
            retainedSize r := by simp_rw [hterm]
      _ = (∑ k, ∑ b, ∑ i,
          (1-(if r.exposed b (w b) i then 1 else 0)/r.pi b i)*x b i k*(betaHat k-betaStar k)) /
            retainedSize r := by
        congr 1
        calc
          _ = ∑ b, ∑ k, ∑ i,
              (1-(if r.exposed b (w b) i then 1 else 0)/r.pi b i)*x b i k*(betaHat k-betaStar k) := by
            apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro k _
        simp only [← Finset.sum_mul]
        ring
  · unfold fittedRowMean
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro b _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    exact (augmented_subtraction_certificates _ _ _ _ _ (0:ℝ)).2

/-- P037-T11(8): population covariate Gram matrix on the retained set. -/
noncomputable def populationRowGram {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q) : Matrix (Fin q) (Fin q) ℝ :=
  fun k l => (∑ b, ∑ i, x b i k*x b i l) / retainedSize r

/-- P037-T11(8): population covariate-outcome cross-product on the
same retained set. It is deterministic under design-based randomization. -/
noncomputable def populationRowRhs {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q) : Fin q → ℝ :=
  fun k => (∑ b, ∑ i, x b i k*r.y b i) / retainedSize r


/-- T2(DM): “mu_i = sum_h n_ih(K_ih/N_ih)/sum_h n_ih”.
Stratum sizes N, referent counts K and fixed seed counts n are integers
fixed before randomization. -/
noncomputable def stratifiedCompositionMean {H : ℕ} (N K n : Fin H → ℕ) : ℝ :=
  (∑ h, (n h:ℝ)*((K h:ℝ)/N h))/(∑ h, (n h:ℝ))

/-- SI Eq. (2)'s C^E: the fraction of all eligibles who are referents,
q=ΣK/ΣN. Unlike μ, this does not weight strata by their fixed seed counts. -/
noncomputable def stratifiedEligibleFraction {H : ℕ} (N K : Fin H → ℕ) : ℝ :=
  (∑ h, (K h:ℝ))/(∑ h, (N h:ℝ))

/-- T2(DM): each stratum is uniformly sampled without replacement,
independently. The product subtype contains precisely its allowed seed sets. -/
abbrev StratifiedSeedState {H : ℕ} (N n : Fin H → ℕ) :=
  (h : Fin H) → {s : Finset (Fin (N h)) // s.card=n h}

/-- Actual seed-group referent composition, SI pp. 6,13: the number of
referents selected, divided by the fixed total number of seeds. -/
noncomputable def stratifiedSeedComposition {H : ℕ} (N n : Fin H → ℕ)
    (refs : (h : Fin H) → Finset (Fin (N h))) (z : StratifiedSeedState N n) : ℝ :=
  (∑ h, ((refs h∩(z h).val).card:ℝ))/(∑ h, (n h:ℝ))

/-! Exact product-stratum hypergeometric count moments, including empty samples. -/
namespace StratifiedCompletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

open Causalean.Experimentation.DesignBased (completeRandomization completeRandomization_card)
open Causalean.Experimentation.FinitePopulationMoments (sampleMean popMean popVar E_sampleMean Var_sampleMean)

def design (N n : ℕ) (hn : n ≤ N) :
    FiniteDesign {S : Finset (Fin N) // S.card = n} :=
  let d := @completeRandomization (Fin N) inferInstance n (by simpa using hn)
  ⟨d.p,d.p_nonneg,d.p_sum⟩

theorem design_weight (N n : ℕ) (hn : n ≤ N)
    (S : {S : Finset (Fin N) // S.card = n}) :
    (design N n hn).weight S = (Nat.choose N n:ℝ)⁻¹ := by
  simp [design,completeRandomization,completeRandomization_card]

theorem variance_source (N n : ℕ) (hn : n ≤ N)
    (X : {S : Finset (Fin N) // S.card = n} → ℝ) :
    designVariance (design N n hn) X =
      (@completeRandomization (Fin N) inferInstance n (by simpa using hn)).Var X := by
  rw [designVariance_centered]
  rfl

def count {N n : ℕ} (refs : Finset (Fin N))
    (S : {S : Finset (Fin N) // S.card = n}) : ℝ := (refs ∩ S.val).card

theorem indicator_sum {N : ℕ} (refs : Finset (Fin N)) :
    (∑ i : Fin N, if i ∈ refs then (1:ℝ) else 0) = (refs.card:ℝ) := by
  simp

theorem count_sum {N n : ℕ} (refs : Finset (Fin N))
    (S : {S : Finset (Fin N) // S.card = n}) :
    count refs S = ∑ i : Fin N, if i ∈ S.val then (if i ∈ refs then (1:ℝ) else 0) else 0 := by
  simp only [count,Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [Finset.sum_ite_mem]
  simp [Finset.sum_ite_mem,Finset.inter_comm]

theorem indicator_popMean {N : ℕ} (refs : Finset (Fin N)) :
    popMean (fun i => if i ∈ refs then (1:ℝ) else 0) = (refs.card:ℝ)/N := by
  simp [popMean]

theorem indicator_popVar {N : ℕ} (refs : Finset (Fin N)) (hN : 2 ≤ N) :
    popVar (fun i => if i ∈ refs then (1:ℝ) else 0) =
      (N:ℝ)/((N:ℝ)-1)*((refs.card:ℝ)/N)*(1-(refs.card:ℝ)/N) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn1 : (N:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold popVar
  rw [indicator_popMean]
  have hid : ∀ i : Fin N,
      ((if i ∈ refs then (1:ℝ) else 0)-(refs.card:ℝ)/N)^2 =
      (if i ∈ refs then (1:ℝ) else 0)-
        2*((refs.card:ℝ)/N)*(if i ∈ refs then (1:ℝ) else 0)+((refs.card:ℝ)/N)^2 := by
    intro i; split_ifs <;> ring
  simp_rw [hid]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,indicator_sum]
  simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  <;> ring

theorem stratum_moments (N n : ℕ) (refs : Finset (Fin N))
    (hN : 0 < N) (hn : n ≤ N) :
    designMean (design N n hn) (count refs) = (n:ℝ)*((refs.card:ℝ)/N) ∧
    designVariance (design N n hn) (count refs) =
      if N=1 then 0 else
        (n:ℝ)*((refs.card:ℝ)/N)*(1-(refs.card:ℝ)/N)*(((N:ℝ)-n)/((N:ℝ)-1)) := by
  by_cases hn0 : n=0
  · subst n
    have hc : count refs = fun _ : {S : Finset (Fin N) // S.card=0} => (0:ℝ) := by
      funext S
      have hs : S.val = ∅ := Finset.card_eq_zero.mp S.property
      simp only [count,hs,Finset.inter_empty,Finset.card_empty,Nat.cast_zero]
    rw [hc,designMean_const]
    simp [designVariance,designMean_const]
  have hnpos : 0<n := Nat.pos_of_ne_zero hn0
  have hnr : (n:ℝ) ≠ 0 := by exact_mod_cast hn0
  have hc : count refs = fun S => (n:ℝ)*sampleMean n
      (fun i => if i ∈ refs then (1:ℝ) else 0) S := by
    funext S
    rw [count_sum]
    unfold sampleMean
    field_simp
  have hm : designMean (design N n hn) (count refs) = (n:ℝ)*((refs.card:ℝ)/N) := by
    rw [hc,designMean_mul]
    change (n:ℝ)*(@completeRandomization (Fin N) inferInstance n (by simpa using hn)).E _ = _
    rw [E_sampleMean n (by simpa using hn) hnpos,indicator_popMean]
  refine ⟨hm,?_⟩
  by_cases hN1 : N=1
  · subst N
    have hn1 : n=1 := by omega
    subst n
    have hc : count refs = fun _ : {S : Finset (Fin 1) // S.card=1} => (refs.card:ℝ) := by
      funext S
      have hs : S.val = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simpa using le_of_eq S.property.symm
      simp only [count,hs,Finset.inter_univ]
    rw [hc]
    simp [designVariance,designMean_const]
  · rw [if_neg hN1,hc,designVariance_mul,variance_source,
      Var_sampleMean n (by simpa using hn) hnpos (by simp only [Fintype.card_fin]; omega),
      indicator_popVar refs (by omega)]
    have hnR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hn1R : (N:ℝ)-1 ≠ 0 := by
      have : (2:ℝ) ≤ N := by exact_mod_cast (show 2≤N by omega)
      linarith
    simp only [Fintype.card_fin]
    field_simp
    <;> ring

theorem completed {H : ℕ} (N n : Fin H → ℕ)
    (refs : (h : Fin H) → Finset (Fin (N h)))
    (hN : ∀ h, 0<N h) (hn : ∀ h, n h≤N h) (ht : 0<∑ h,n h) :
    let K := fun h => (refs h).card
    let μ := stratifiedCompositionMean N K n
    let mass := (∏ h, (Nat.choose (N h) (n h):ℝ))⁻¹
    (∑ z : StratifiedSeedState N n, mass)=1 ∧
    (∑ z : StratifiedSeedState N n, mass*stratifiedSeedComposition N n refs z)=μ ∧
    (∑ z : StratifiedSeedState N n, mass*(stratifiedSeedComposition N n refs z-μ)^2)=
      (∑ h, if N h=1 then 0 else
        (n h:ℝ)*((K h:ℝ)/N h)*(1-(K h:ℝ)/N h)*
          (((N h:ℝ)-n h)/((N h:ℝ)-1)))/(∑ h,(n h:ℝ))^2 := by
  dsimp
  let d := productDesign (fun h => design (N h) (n h) (hn h))
  have hw : ∀ z, d.weight z = (∏ h,(Nat.choose (N h) (n h):ℝ))⁻¹ := by
    intro z
    dsimp [d,productDesign]
    simp_rw [design_weight]
    simp only [Finset.prod_inv_distrib]
  have hmean : designMean d (stratifiedSeedComposition N n refs) =
      stratifiedCompositionMean N (fun h => (refs h).card) n := by
    have he : stratifiedSeedComposition N n refs =
        fun z => (1/(∑ h,(n h:ℝ)))*(∑ h,count (refs h) (z h)) := by
      funext z
      simp [stratifiedSeedComposition,count,div_eq_mul_inv,mul_comm]
    dsimp only [d]
    rw [he,designMean_mul,designMean_sum]
    simp_rw [product_design_coordinate_mean, (stratum_moments _ _ _ (hN _) (hn _)).1]
    unfold stratifiedCompositionMean
    ring
  have hvar : designVariance d (stratifiedSeedComposition N n refs) =
      (∑ h, if N h=1 then 0 else
        (n h:ℝ)*((refs h).card/N h)*(1-(refs h).card/N h)*
          (((N h:ℝ)-n h)/((N h:ℝ)-1)))/(∑ h,(n h:ℝ))^2 := by
    have he : stratifiedSeedComposition N n refs =
        fun z => (1/(∑ h,(n h:ℝ)))*(∑ h,count (refs h) (z h)) := by
      funext z
      simp [stratifiedSeedComposition,count,div_eq_mul_inv,mul_comm]
    dsimp only [d]
    rw [he,designVariance_mul,product_design_sum_variance]
    simp_rw [(stratum_moments _ _ _ (hN _) (hn _)).2]
    ring
  refine ⟨?_,?_,?_⟩
  · simpa only [hw] using d.total
  · simpa only [designMean,hw] using hmean
  · rw [designVariance_centered,hmean] at hvar
    simpa only [designMean,hw] using hvar

end
end StratifiedCompletion

/-- T2(DM): full exact mean and variance under the uniform product
seed design; singleton strata have zero variance. Independence of this law
from school assignment gives the treated-school conditional moments and (R). -/
theorem stratified_composition_design_moments {H : ℕ} (N n : Fin H → ℕ)
    (refs : (h : Fin H) → Finset (Fin (N h)))
    (hN : ∀ h, 0<N h) (hn : ∀ h, n h≤N h) (ht : 0<∑ h, n h) :
    let K := fun h => (refs h).card
    let μ := stratifiedCompositionMean N K n
    let mass := (∏ h, (Nat.choose (N h) (n h):ℝ))⁻¹
    (∑ z : StratifiedSeedState N n, mass)=1 ∧
    (∑ z : StratifiedSeedState N n, mass*stratifiedSeedComposition N n refs z)=μ ∧
    (∑ z : StratifiedSeedState N n, mass*(stratifiedSeedComposition N n refs z-μ)^2)=
      (∑ h, if N h=1 then 0 else
        (n h:ℝ)*((K h:ℝ)/N h)*(1-(K h:ℝ)/N h)*
          (((N h:ℝ)-n h)/((N h:ℝ)-1)))/(∑ h, (n h:ℝ))^2 := by
  exact StratifiedCompletion.completed N n refs hN hn ht

/-- T2(DM),(B5): equal sampling fractions across every stratum
make the design mean equal the eligible fraction. Nonzero total seeds and
nonempty strata are actual design conditions, not conclusions assumed. -/
theorem design_mean_equal_sampling_fraction {H : ℕ} (N K n : Fin H → ℕ)
    (f : ℝ) (hN : ∀ h, N h≠0) (hn : (∑ h, (n h:ℝ))≠0)
    (hfraction : ∀ h, (n h:ℝ)=f*(N h:ℝ)) :
    stratifiedCompositionMean N K n=stratifiedEligibleFraction N K := by
  have hs : (∑ h, (n h:ℝ))=f*(∑ h, (N h:ℝ)) := by
    simp_rw [hfraction]; rw [Finset.mul_sum]
  have hf : f≠0 := by intro he; rw [hs,he,zero_mul] at hn; exact hn rfl
  have hk : (∑ h, (n h:ℝ)*((K h:ℝ)/N h))=f*(∑ h, (K h:ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _
    rw [hfraction]
    have hNh : (N h:ℝ)≠0 := by exact_mod_cast hN h
    field_simp
  unfold stratifiedCompositionMean stratifiedEligibleFraction
  rw [hk,hs,mul_div_mul_left _ _ hf]

/-- T2(DM): four strata (13,2,7),(14,1,7),(14,0,7),(14,0,7)
give q=3/55, μ=41/728 and μ-q=71/40040. This is an exact arithmetic
certificate for supplied counts; their empirical provenance is not proved here. -/
theorem unequal_strata_design_mean_certificate :
    stratifiedEligibleFraction ![13,14,14,14] ![2,1,0,0]=3/55 ∧
    stratifiedCompositionMean ![13,14,14,14] ![2,1,0,0] ![7,7,7,7]=41/728 ∧
    (41/728:ℝ)-3/55=71/40040 ∧ (41/728:ℝ)≠3/55 := by
  norm_num [stratifiedEligibleFraction,stratifiedCompositionMean,Fin.sum_univ_succ]

/-- T2(B5): q-centered composition contains a nonzero design-mean
shift in general; q can replace μ in both repaired columns when μ=q. -/
theorem composition_centering_special_case (D C μ q : ℝ) :
    D*(C-q)=D*(C-μ)+D*(μ-q) ∧
    (μ=q → D*(C-μ)=D*(C-q) ∧ D*μ=D*q) := by
  constructor
  · ring
  · intro h; simp [h]

/-- T2(B1)--(B3): the actual arbitrary-baseline/common-slope
potential outcome schedule identifies b using R=D(C-μ), under the stated
conditional mean-zero seed design, seed-independent nuisance columns and
positive block-centered seed variance. Finite-sample unbiasedness is not claimed. -/
theorem design_mean_centered_common_slope {Ω K : Type*} [Fintype Ω] [Fintype K]
    {B : ℕ} (d : FiniteDesign Ω) (D : Ω → (Fin B × Fin 4) → Bool)
    (C : Ω → (Fin B × Fin 4) → ℝ) (μ a t : (Fin B × Fin 4) → ℝ)
    (W : K → ((Fin B × Fin 4) → Bool) → (Fin B × Fin 4) → ℝ)
    (b beta : ℝ) (delta : K → ℝ)
    (hR : RandomizedComposition d D (fun w i => (if D w i then (1:ℝ) else 0)*(C w i-μ i)))
    (hN : AugmentedNormalEquations d (fun k w => W k (D w))
      (fun w i => (if D w i then (1:ℝ) else 0)*(C w i-μ i))
      (fun w i => a i+(if D w i then (1:ℝ) else 0)*t i+
        b*(if D w i then (1:ℝ) else 0)*C w i) delta beta)
    (hv : 0<designMean d (fun w => withinBlocksCross
      (fun i => (if D w i then (1:ℝ) else 0)*(C w i-μ i))
      (fun i => (if D w i then (1:ℝ) else 0)*(C w i-μ i)))) : beta=b := by
  have hy : (fun w i => a i+(if D w i then (1:ℝ) else 0)*t i+
      b*(if D w i then (1:ℝ) else 0)*C w i)=
      (fun w i => (a i+(if D w i then (1:ℝ) else 0)*(t i+b*μ i))+
        b*((if D w i then (1:ℝ) else 0)*(C w i-μ i))) := by
    funext w i; ring
  rw [hy] at hN
  exact centered_composition_identifies_common_slope d D _ hR
    (fun dv i => a i+(if dv i then (1:ℝ) else 0)*(t i+b*μ i)) W b beta delta hN hv

/-! Independent-repetition LLNs and the actual pooled OLS probability limit. -/
namespace WitnessCompletion
open Filter
open scoped Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem probability_nonneg {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (A : Ω → Prop) : 0 ≤ designProbability d A := by
  unfold designProbability designMean
  exact Finset.sum_nonneg (fun w _ => mul_nonneg (d.nonneg w) (by dsimp; split_ifs <;> norm_num))

theorem probability_mono {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (A B : Ω → Prop) (h : ∀ w, A w → B w) :
    designProbability d A ≤ designProbability d B := by
  unfold designProbability designMean
  apply Finset.sum_le_sum
  intro w _
  apply mul_le_mul_of_nonneg_left _ (d.nonneg w)
  dsimp
  split_ifs with ha hb hb
  · norm_num
  · exact False.elim (hb (h w ha))
  · norm_num
  · norm_num

theorem probability_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (A : I → Ω → Prop) :
    designProbability d (fun w => ∃ i, A i w) ≤ ∑ i, designProbability d (A i) := by
  classical
  unfold designProbability designMean
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro w _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (d.nonneg w)
  dsimp
  by_cases h : ∃ i, A i w
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    calc
      1 = (if A i w then (1:ℝ) else 0) := (if_pos hi).symm
      _ ≤ ∑ j, if A j w then (1:ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if A j w then (1:ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · simp only [if_neg h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem iid_average_consistent {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (g : Ω → ℝ) :
    ∀ eps : ℝ, 0 < eps → Tendsto (fun n =>
      designProbability (productDesign (fun _ : Fin (n+1) => d))
        (fun w => eps < |(∑ b, g (w b))/(n+1)-designMean d g|)) atTop (𝓝 0) := by
  apply BlockCLT.finite_consistency
    (fun n => productDesign (fun _ : Fin (n+1) => d))
    (fun n w => (∑ b, g (w b))/(n+1)) (fun _ => designMean d g)
  · intro n
    simp_rw [div_eq_mul_inv]
    rw [show (fun w : Fin (n+1) → Ω => (∑ b, g (w b))*((n:ℝ)+1)⁻¹) =
      (fun w => ((n:ℝ)+1)⁻¹*(∑ b, g (w b))) by funext w; ring,
      designMean_mul, designMean_sum]
    simp_rw [product_design_coordinate_mean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  · have heq : ∀ n : ℕ, designVariance (productDesign (fun _ : Fin (n+1) => d))
        (fun w => (∑ b, g (w b))/((n:ℝ)+1)) = designVariance d g/((n:ℝ)+1) := by
      intro n
      rw [show (fun w : Fin (n+1) → Ω => (∑ b, g (w b))/((n:ℝ)+1)) =
        (fun w => (1/((n:ℝ)+1))*(∑ b, g (w b))) by funext w; ring,
        designVariance_mul, product_design_sum_variance]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have hn : (n:ℝ)+1 ≠ 0 := by positivity
      field_simp
      <;> ring
    simp_rw [heq]
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (designVariance d g)

theorem finite_continuous_map {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    {I : Type*} [Fintype I] (d : ∀ n, FiniteDesign (Ω n))
    (X : ∀ n, Ω n → I → ℝ) (a : I → ℝ) (f : (I → ℝ) → ℝ)
    (hX : ∀ i eps, 0 < eps → Tendsto (fun n =>
      designProbability (d n) (fun w => eps < |X n w i-a i|)) atTop (𝓝 0))
    (hf : ContinuousAt f a) :
    ∀ eps, 0 < eps → Tendsto (fun n =>
      designProbability (d n) (fun w => eps < |f (X n w)-f a|)) atTop (𝓝 0) := by
  intro eps heps
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hf eps heps
  have hd : 0 < δ/2 := by positivity
  have hsum : Tendsto (fun n => ∑ i, designProbability (d n)
      (fun w => δ/2 < |X n w i-a i|)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ => hX i (δ/2) hd)
  refine squeeze_zero (fun n => probability_nonneg _ _) (fun n => ?_) hsum
  apply le_trans (probability_mono (d n) _ (fun w => ∃ i, δ/2 < |X n w i-a i|) ?_)
    (probability_exists_le_sum (d n) _)
  intro w hw
  by_contra hn
  push_neg at hn
  have hdist : dist (X n w) a < δ := (dist_pi_lt_iff hδ).mpr (fun i => by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hn i) (by linarith))
  have h := hclose hdist
  rw [Real.dist_eq] at h
  exact (not_lt_of_ge hw.le) h

theorem matrix_inv_smul {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (k : ℝ)
    (hk : k ≠ 0) : (k • A)⁻¹ = k⁻¹ • A⁻¹ := by
  by_cases hA : IsUnit A.det
  · letI : Invertible k := invertibleOfNonzero hk
    simpa only [invOf_eq_inv] using Matrix.inv_smul A k hA
  · have ha : A.det = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hA
    rw [Matrix.nonsing_inv_apply_not_isUnit A hA]
    rw [Matrix.nonsing_inv_apply_not_isUnit (k • A) (by simp [Matrix.det_smul,ha])]
    simp

abbrev Coordinate := Fin 3 × Fin 4

def witnessDesign : FiniteDesign CompositionState :=
  ⟨witnessStateMass,witness_state_probability_law.1,witness_state_probability_law.2⟩

def feature (w : CompositionState) (i : Coordinate) : ℝ :=
  if h : i.2.val < 3 then
    blockCross (witnessColumns w i.1) (witnessColumns w ⟨i.2.val,h⟩)
  else blockCross (witnessColumns w i.1) (witnessObservedOutcome w)

def featureMean : Coordinate → ℝ := fun i => designMean witnessDesign (fun w => feature w i)

def gram (a : Coordinate → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun k l => a (k,l.castSucc)
def rhs (a : Coordinate → ℝ) : Fin 3 → ℝ := fun k => a (k,3)
def coefficient (a : Coordinate → ℝ) : ℝ := ((gram a)⁻¹.mulVec (rhs a)) 2

theorem featureMean_gram : gram featureMean = witnessGram := by
  ext k l
  simp [gram,featureMean,feature,witnessDesign,designMean,witnessGram,witnessMean]

theorem featureMean_rhs : rhs featureMean = witnessRhs := by
  ext k
  simp [rhs,featureMean,feature,witnessDesign,designMean,witnessRhs,witnessMean]

theorem witness_det : witnessGram.det ≠ 0 := by
  rw [witness_expected_normal_equations.1]
  norm_num [Matrix.det_fin_three]

theorem coefficient_continuous : ContinuousAt coefficient featureMean := by
  have hG : Continuous gram := continuous_pi (fun k => continuous_pi (fun l => continuous_apply _))
  have hR : Continuous rhs := continuous_pi (fun k => continuous_apply _)
  have hi : ContinuousAt (fun a => (gram a)⁻¹) featureMean := by
    apply ContinuousAt.comp (continuousAt_matrix_inv _ _) hG.continuousAt
    rw [featureMean_gram]
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ witness_det
  unfold coefficient Matrix.mulVec dotProduct
  exact tendsto_finsetSum _ (fun j _ => ((continuous_apply j).continuousAt.comp
    ((continuous_apply 2).continuousAt.comp hi)).mul
      ((continuous_apply j).continuousAt.comp hR.continuousAt))

theorem coefficient_mean : coefficient featureMean = (-16/31:ℝ) := by
  unfold coefficient
  rw [featureMean_gram,featureMean_rhs]
  have h := (composition_witness_counterexample.2.2.2.2.2.2.1 ![-3/31,-15/62,-16/31]).mpr rfl
  have hu : IsUnit witnessGram.det := isUnit_iff_ne_zero.mpr witness_det
  rw [← h,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hu,Matrix.one_mulVec]
  norm_num

theorem coefficient_average (n : ℕ) (w : Fin (n+1) → CompositionState) :
    coefficient (fun i => (∑ b,feature (w b) i)/((n:ℝ)+1)) =
      pooledWitnessCoefficient (n+1) w := by
  let G : Matrix (Fin 3) (Fin 3) ℝ := fun k l =>
    ∑ b, blockCross (witnessColumns (w b) k) (witnessColumns (w b) l)
  let h : Fin 3 → ℝ := fun k =>
    ∑ b, blockCross (witnessColumns (w b) k) (witnessObservedOutcome (w b))
  have hG : gram (fun i => (∑ b,feature (w b) i)/((n:ℝ)+1)) =
      (1/((n:ℝ)+1)) • G := by
    ext k l
    change (∑ b, feature (w b) (k,l.castSucc))/((n:ℝ)+1) =
      (1/((n:ℝ)+1))*(∑ b, blockCross (witnessColumns (w b) k) (witnessColumns (w b) l))
    simp [feature,div_eq_mul_inv,mul_comm]
  have hR : rhs (fun i => (∑ b,feature (w b) i)/((n:ℝ)+1)) =
      (1/((n:ℝ)+1)) • h := by
    ext k
    simp [rhs,feature,h,div_eq_mul_inv,mul_comm]
  unfold coefficient
  rw [hG,hR,matrix_inv_smul _ _ (by positivity),Matrix.smul_mulVec,Matrix.mulVec_smul]
  simp only [one_div, inv_inv, smul_smul]
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hn,one_smul]
  rfl

theorem completed (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun B : ℕ => ∑ w : Fin B → CompositionState,
      (∏ b, witnessStateMass (w b)) *
      (if |pooledWitnessCoefficient B w-(-16/31)| > eps then (1:ℝ) else 0))
      atTop (𝓝 0) := by
  have h := finite_continuous_map
    (fun n => productDesign (fun _ : Fin (n+1) => witnessDesign))
    (fun n w i => (∑ b,feature (w b) i)/((n:ℝ)+1)) featureMean coefficient
    (fun i => iid_average_consistent witnessDesign (fun w => feature w i))
    coefficient_continuous eps heps
  simp_rw [coefficient_average,coefficient_mean] at h
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact h

end
end WitnessCompletion

/-- P037-T1(v): the actual block-OLS coefficient converges in
probability to -16/31 along independent repetitions of this witness.
The finite law is specified, and no limit conclusion is assumed. -/
theorem witness_ols_probability_limit (eps : ℝ) (heps : 0 < eps) :
    Filter.Tendsto (fun B : ℕ =>
      ∑ w : Fin B → CompositionState,
        (∏ b, witnessStateMass (w b)) *
        (if |pooledWitnessCoefficient B w - (-16/31)| > eps then (1:ℝ) else 0))
      Filter.atTop (nhds 0) := by
  exact WitnessCompletion.completed eps heps

end AronowAudit.P037

