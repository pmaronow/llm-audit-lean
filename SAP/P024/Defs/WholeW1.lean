import Mathlib
import SAP.P024.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
open Filter
noncomputable section

/-- Twenty-four clusters, with 46 individuals in cluster zero and one in each
other cluster. Only treatment in cluster zero changes outcomes, from zero to one. -/
def fewDozenPopulation : ClusterPopulation 24 where
  size := fun j => if j = 0 then 46 else 1
  positive := fun j => by split_ifs <;> norm_num
  y0 := fun _ _ => 0
  y1 := fun j _ => if j = 0 then 1 else 0

/-- Uniform treatment of twelve of the twenty-four clusters. -/
def fewDozenDesign : Design {s : Finset (Fin 24) // s.card = 12} := halfClusterDesign 11

/-- P024-T5; corrected consistency sentence, p. 171 (PDF p. 5).
Uniformly bounded individual potential outcomes, a common cluster treatment
probability uniformly bounded away from zero and one, and a vanishing largest
cluster share imply consistency: one fixed eta > 0 satisfies
eta <= p_K <= 1-eta for every K. This holds under
independent assignment or complete cluster randomization. The squared-share
condition is equivalent. Bias can still be appreciable with a few dozen unequal
clusters: a 24-cluster, 12-treated example with outcomes in [0,1] has effect 2/3,
mean estimate 23/57 and bias -5/19, of magnitude greater than 1/4. Without no
dominance, bounded outcomes and interior independent assignment do not suffice:
the dominant-cluster sequence has error probability tending to one for every
empty-arm extension. Populations, effects, and probabilities may change, while
the outcome bound and probability margin remain uniform over the sequence. -/
def T5WholeStatement : Prop :=
  T5Statement ∧
  ((∀ j i, 0 ≤ fewDozenPopulation.y0 j i ∧ fewDozenPopulation.y0 j i ≤ 1 ∧
      0 ≤ fewDozenPopulation.y1 j i ∧ fewDozenPopulation.y1 j i ≤ 1) ∧
    fewDozenPopulation.size 0 = 46 ∧
    (∀ j : Fin 24, j ≠ 0 → fewDozenPopulation.size j = 1) ∧
    (∑ j, (fewDozenPopulation.size j : ℝ)) = 69 ∧
    populationEffect fewDozenPopulation = 2/3 ∧
    (∀ empty : Finset (Fin 24) → ℝ,
      expectation fewDozenDesign
        (fun s => populationEstimator fewDozenPopulation empty s.val) = 23/57) ∧
    (23/57 : ℝ) - 2/3 = -5/19 ∧ (1/4 : ℝ) < |(23/57 : ℝ) - 2/3|) ∧
  ((∀ k, independentClusterLaw (uniformDesign (Finset (Fin (k+2)))) (1/2)) ∧
    (∀ k j i, |(dominantPopulation k).y0 j i| ≤ 1 ∧
      |(dominantPopulation k).y1 j i| ≤ 1) ∧
    (∀ k, populationEffect (dominantPopulation k) = 1/4) ∧
    Tendsto (fun k => maxClusterWeight (dominantPopulation k)) atTop (nhds 1) ∧
    (∀ empty : (k : ℕ) → Finset (Fin (k+2)) → ℝ,
      Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
        (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s -
          populationEffect (dominantPopulation k)|)) atTop (nhds 1) ∧
      ¬ Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
        (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s -
          populationEffect (dominantPopulation k)|)) atTop (nhds 0)))

/-- Six nonempty proper individual assignments, in the order
{0}, {1,2}, {1}, {2}, {0,1}, {0,2}. -/
def sixExposure : Fin 6 → Fin 3 → Bool :=
  ![![true, false, false], ![false, true, true], ![false, true, false],
    ![false, false, true], ![true, true, false], ![true, false, true]]

/-- A common-marginal individual law whose treatment count is random. -/
def unequalSixDesign : Design (Fin 6) where
  mass := ![1/4, 1/4, 1/8, 1/8, 1/8, 1/8]
  nonneg := fun ω => by fin_cases ω <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- P024-T6; between-subjects design, p. 170 (PDF p. 4).
The printed claim is false: identical individual treatment probabilities alone
do not ensure unbiased observed difference in means. Three subjects with fixed
control outcomes (0,0,0) and treatment outcomes (1,0,0) have common probability
1/2 under the six explicitly weighted assignments. Both arms are always nonempty,
but the treatment count varies and the mean estimate is 3/8 rather than effect
1/3. Assignment is the only randomness and outcomes depend only on own treatment.
This refutes the unrestricted equal-probability assertion; it does not assert
bias under independent Bernoulli assignment conditioned on nonempty arms. -/
def T6WholeStatement : Prop :=
  (∀ ω, 0 < unequalSixDesign.mass ω) ∧
  (∀ ω, 0 < treatedCount (sixExposure ω) ∧ treatedCount (sixExposure ω) < 3) ∧
  treatedCount (sixExposure 0) = 1 ∧ treatedCount (sixExposure 1) = 2 ∧
  (∀ i, exposureProbability unequalSixDesign sixExposure i = 1/2) ∧
  expectation unequalSixDesign
    (fun ω => clusterDIM (fun _ => 1) (fun _ => 0) ![1,0,0] (sixExposure ω)) = 3/8 ∧
  averageEffect Finset.univ (fun _ : Fin 3 => 0) ![1,0,0] = 1/3 ∧
  expectation unequalSixDesign
    (fun ω => clusterDIM (fun _ => 1) (fun _ => 0) ![1,0,0] (sixExposure ω)) ≠
      averageEffect Finset.univ (fun _ : Fin 3 => 0) ![1,0,0]

/-- The individual-level realization of T7's unequal-size two-cluster witness. -/
def unequalPairPopulation : ClusterPopulation 2 where
  size := ![1,2]
  positive := fun j => by fin_cases j <;> norm_num
  y0 := fun _ _ => 0
  y1 := fun j _ => if j = 0 then 0 else 1

/-- P024-T7; corrected conditional clustering component, p. 171 (PDF p. 5),
with the individual-level estimand on p. 172 (PDF p. 6).
For K >= 2 independent common-p Bernoulli cluster assignments, 0 < p < 1,
the nonempty-arm event has probability 1-p^K-(1-p)^K > 0, for arbitrary
positive cluster sizes. Conditional masses are the actual parent masses divided
by that probability. Equal positive cluster sizes give unbiased individual
difference in means conditionally on this event, and each allocation equals
the difference of the two cluster means. For sizes (1,2), zero control outcomes
and treatment outcomes zero in the small cluster and one in the large cluster,
the fair parent law instead gives effect 2/3 and conditional mean 1/2, with the
two conditional allocations equiprobable and estimates zero and one. Every
empty-arm extension is allowed. Independence refers to the parent law. -/
def T7WholeStatement : Prop :=
  (∀ (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1),
    independentClusterLaw (bernoulliDesign (k+2) p hp.le hp1.le) p ∧
    probability (bernoulliDesign (k+2) p hp.le hp1.le)
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 1-p^(k+2)-(1-p)^(k+2) ∧
    0 < 1-p^(k+2)-(1-p)^(k+2) ∧
    (∀ s : NonemptyAllocations k, bernoulliConditionalMass k p s =
      (bernoulliDesign (k+2) p hp.le hp1.le).mass s.val /
        (1-p^(k+2)-(1-p)^(k+2))) ∧
    (∑ s : NonemptyAllocations k, bernoulliConditionalMass k p s) = 1) ∧
  T7Statement ∧
  (unequalPairPopulation.size = ![1,2] ∧
    (∀ j i, unequalPairPopulation.y0 j i = 0 ∧
      unequalPairPopulation.y1 j i = if j = 0 then 0 else 1) ∧
    clusterMean0 unequalPairPopulation = ![0,0] ∧
    clusterMean1 unequalPairPopulation = ![0,1] ∧
    populationEffect unequalPairPopulation = 2/3 ∧
    (∀ empty : Finset (Fin 2) → ℝ,
      expectation (conditionalNonemptyDesign 0)
        (fun s => populationEstimator unequalPairPopulation empty s.val) = 1/2) ∧
    (∀ s : NonemptyAllocations 0, (conditionalNonemptyDesign 0).mass s = 1/2))

/-- Overall HT contrast using actual unit propensities, for a finite partition
into blocks. Used here only with positive block population and propensities in (0,1). -/
def actualBlockedHT {B Ω : Type*} [Fintype B] [Fintype Ω]
    (I : B → Type*) [∀ b, Fintype (I b)] (d : Design Ω)
    (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ) (ω : Ω) : ℝ :=
  (∑ b, ∑ i, if z ω b i then
    y1 b i / exposureProbability d (fun υ => z υ b) i else
    -(y0 b i / (1 - exposureProbability d (fun υ => z υ b) i))) / blockPopulation I

/-- The population-share weighted raw differences of observed means in blocks.
Used below only with nonempty arms in every block. -/
def weightedBlockDIM {B Ω : Type*} [Fintype B]
    (I : B → Type*) [∀ b, Fintype (I b)]
    (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ) (ω : Ω) : ℝ :=
  ∑ b, (Fintype.card (I b) : ℝ) / blockPopulation I *
    clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b)

/-- One block containing three individuals, with six possible assignments. -/
def oneBlockThreeExposure (ω : Fin 6) (_ : Fin 1) : Fin 3 → Bool := sixExposure ω

/-- One treated individual out of two, with unequal individual propensities. -/
def unequalTwoDesign : Design (Fin 2) where
  mass := ![1/4, 3/4]
  nonneg := fun ω => by fin_cases ω <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def oneBlockTwoExposure : Fin 2 → Fin 1 → Fin 2 → Bool :=
  fun ω _ => (![![true,false], ![false,true]] : Fin 2 → Fin 2 → Bool) ω

/-- P024-T8; weighted blocked estimation, p. 173 (PDF p. 7), and Note 4,
p. 177 (PDF p. 11).
The printed claim is false: under the canonical interpretation of each block
estimate as its raw difference in means, the overall actual-probability HT
contrast need not equal their population-share weighted average. In one block
of three units, uniformly randomizing over all six nonempty proper treated
sets gives actual propensities 1/2; with control outcomes zero and treatment
outcomes one, a one-treated allocation gives HT 2/3 and block mean 1.
In one block of two units with exactly one treated, assignment probabilities
(1/4,3/4), control outcomes (0,0) and treatment outcomes (1,0), HT is 2 and
the raw mean is 1 on the first allocation. Expected HT equals effect 1/2,
whereas the expected raw mean is 1/4. All means exist on every assignment. -/
def T8WholeStatement : Prop :=
  ((∀ i : Fin 3, exposureProbability (uniformDesign (Fin 6)) sixExposure i = 1/2) ∧
    (∀ ω, 0 < treatedCount (sixExposure ω) ∧ treatedCount (sixExposure ω) < 3) ∧
    actualBlockedHT (fun _ : Fin 1 => Fin 3) (uniformDesign (Fin 6))
      oneBlockThreeExposure (fun _ _ => 0) (fun _ _ => 1) 0 = 2/3 ∧
    weightedBlockDIM (fun _ : Fin 1 => Fin 3)
      oneBlockThreeExposure (fun _ _ => 0) (fun _ _ => 1) 0 = 1 ∧
    actualBlockedHT (fun _ : Fin 1 => Fin 3) (uniformDesign (Fin 6))
      oneBlockThreeExposure (fun _ _ => 0) (fun _ _ => 1) 0 ≠
    weightedBlockDIM (fun _ : Fin 1 => Fin 3)
      oneBlockThreeExposure (fun _ _ => 0) (fun _ _ => 1) 0) ∧
  ((∀ i : Fin 2, exposureProbability unequalTwoDesign
      (fun ω => oneBlockTwoExposure ω 0) i = (![1/4,3/4] : Fin 2 → ℝ) i) ∧
    (∀ ω, treatedCount (oneBlockTwoExposure ω 0) = 1) ∧
    actualBlockedHT (fun _ : Fin 1 => Fin 2) unequalTwoDesign
      oneBlockTwoExposure (fun _ _ => 0) (fun _ => ![1,0]) 0 = 2 ∧
    weightedBlockDIM (fun _ : Fin 1 => Fin 2)
      oneBlockTwoExposure (fun _ _ => 0) (fun _ => ![1,0]) 0 = 1 ∧
    expectation unequalTwoDesign
      (actualBlockedHT (fun _ : Fin 1 => Fin 2) unequalTwoDesign
        oneBlockTwoExposure (fun _ _ => 0) (fun _ => ![1,0])) = 1/2 ∧
    averageEffect Finset.univ (fun _ : Fin 2 => 0) ![1,0] = 1/2 ∧
    expectation unequalTwoDesign
      (weightedBlockDIM (fun _ : Fin 1 => Fin 2)
        oneBlockTwoExposure (fun _ _ => 0) (fun _ => ![1,0])) = 1/4 ∧
    expectation unequalTwoDesign
      (weightedBlockDIM (fun _ : Fin 1 => Fin 2)
        oneBlockTwoExposure (fun _ _ => 0) (fun _ => ![1,0])) ≠
      averageEffect Finset.univ (fun _ : Fin 2 => 0) ![1,0])

end
end SAP.P024
