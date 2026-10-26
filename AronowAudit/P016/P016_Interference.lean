import AronowAudit.P016.P016_RankCompletion
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Powerset

/-!
P016: Bowers, Fredrickson and Aronow (2016), pp. 395–403.
All population and exact-design quantities below are genuine finite sums.
General exchangeable-reference statements use probability measures of total mass one.
-/

namespace AronowAudit.P016

open scoped BigOperators
open Finset MeasureTheory

/-- "observed outcome" and hypothesis-adjusted outcome vectors, p. 396,
represented as real coordinates indexed from zero. -/
abbrev Outcome (n : ℕ) := Fin n → ℝ
/-- "treatment assignment vector", p. 395, binary assignment to n units. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- "binary treatment", p. 397: the real 0/1 indicator of own assignment. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- "n_g = #{i : z_i = g} > 0", correction P016-E002 to (1), p. 397. -/
def groupSize {n : ℕ} (z : Assignment n) (g : Bool) : ℕ :=
  ∑ i, if z i = g then 1 else 0

/-- The group sum in "bar u_g = n_g⁻¹ sum_{i:z_i=g} u_i", P016-E002, p. 397. -/
noncomputable def groupSum {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : ℝ :=
  ∑ i, if z i = g then u i else 0

/-- "bar u_g = n_g⁻¹ sum_{i:z_i=g} u_i", correction P016-E002, p. 397. -/
noncomputable def groupMean {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : ℝ :=
  groupSum u z g / groupSize z g

/-- Fixed-outcome pooled mean; the pooled reading of the undefined bar in (1), p. 397. -/
noncomputable def pooledMean {n : ℕ} (u : Outcome n) : ℝ := (∑ i, u i) / n

/-- "sum_i (u_i - bar u)^2", pooled interpretation of (1), p. 397; P016-E002. -/
noncomputable def tss {n : ℕ} (u : Outcome n) : ℝ := ∑ i, (u i - pooledMean u)^2

/-- "sums the squared differences ... from the respective assignment-group means",
correction P016-E002 to (1), p. 397; the intercept-and-treatment SSR. -/
noncomputable def rss {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  ∑ i, (u i - groupMean u z (z i))^2

/-- Difference of the two means of the uniformity outcomes, corrected p. 397 (P016-N002). -/
noncomputable def meanDifference {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  groupMean u z true - groupMean u z false

/-- "F_g(t) = n_g⁻¹ sum_{i:z_i=g} I(u_i ≤ t)", correction to footnote 3, p. 396. -/
noncomputable def ecdf {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (t : ℝ) : ℝ :=
  (∑ i, if z i = g ∧ u i ≤ t then (1 : ℝ) else 0) / groupSize z g

/-- "F(x) = (1/n) sum_i I(x_i ≤ x)", footnote 3, p. 396; P016-E011(b). -/
noncomputable def sampleECDF {n : ℕ} (u : Outcome n) (t : ℝ) : ℝ :=
  (∑ i, if u i ≤ t then (1 : ℝ) else 0) / n

/-- "max_i |F_1(u_i) - F_0(u_i)|", correction P016-E002 to footnote 3, p. 396.
The fold takes the maximum of the n sample-point distances and 0; the distances
are nonnegative, so this is exactly the sample maximum whenever n > 0. -/
noncomputable def ks {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  (List.ofFn fun i => |ecdf u z true (u i) - ecdf u z false (u i)|).foldr max 0

/-- "max_i [F_1(u_i) - F_0(u_i)]", footnote 3 AS PRINTED, p. 396.
The extra 0 in the fold has no effect for nonempty groups: at the largest
sample point both ECDFs equal 1. -/
noncomputable def signedKS {n : ℕ} (u : Outcome n) (z : Assignment n) : ℝ :=
  (List.ofFn fun i => ecdf u z true (u i) - ecdf u z false (u i)).foldr max 0

/-- "tilde y_{i,Z_i=0} = Y_i - Z_i tau_0", p. 396, step (2). -/
noncomputable def additiveAdjust {n : ℕ} (Y : Outcome n) (Z : Assignment n) (t : ℝ) : Outcome n :=
  fun i => Y i - bit (Z i) * t

/-- "constant additive effects ... y_{i,1} = y_{i,0} + tau", p. 397. -/
noncomputable def additiveGenerate {n : ℕ} (y : Outcome n) (z : Assignment n) (t : ℝ) : Outcome n :=
  fun i => y i + bit (z i) * t

/-- "constant multiplicative effects ... y_{i,1} = y_{i,0} · tau", p. 397;
the implied uniformity adjustment, for a nonzero multiplicative parameter. -/
noncomputable def multiplicativeAdjust {n : ℕ} (Y : Outcome n) (Z : Assignment n) (a : ℝ) : Outcome n :=
  fun i => Y i / (1 + bit (Z i) * (a - 1))

/-- The multiplicative forward outcomes y_i[1+z_i(a−1)], p. 397 and P016-N003 calibration. -/
noncomputable def multiplicativeGenerate {n : ℕ} (y : Outcome n) (z : Assignment n) (a : ℝ) : Outcome n :=
  fun i => y i * (1 + bit (z i) * (a - 1))

/-- The known "treatment assignment process", p. 396, step (3): nonnegative
weights on a finite assignment space, summing to 1. Zero-weight points are
allowed; strict positivity is separately stated where target T12 requires it. -/
structure FiniteLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

/-- Exact randomization probability: the sum of assignment weights over an event,
the "distribution ... from repetitions of the treatment assignment process", p. 396. -/
noncomputable def mass {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (E : Ω → Prop) : ℝ :=
  by classical exact ∑ ω, if E ω then P.weight ω else 0

/-- Expectation over the fixed randomization design (p. 396; P016-E004). -/
noncomputable def expectation {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, P.weight ω * f ω

/-- Design-based covariance of the group summaries, P016-E004, p. 397. -/
noncomputable def covariance {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f g : Ω → ℝ) : ℝ :=
  expectation P (fun ω => f ω * g ω) - expectation P f * expectation P g

/-- Design-based variance, P016-E004, p. 397. -/
noncomputable def variance {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  covariance P f f

/-- Inclusive exact upper tail, corrected sharp-null validity text, p. 397 (P016-E005). -/
noncomputable def upperP {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) : ℝ :=
  mass P (fun w => s z ≤ s w)

/-- Inclusive exact lower tail, corrected sharp-null validity text, p. 397 (P016-E005). -/
noncomputable def lowerP {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) : ℝ :=
  mass P (fun w => s w ≤ s z)

/-- "min{1,2 min(p_U,p_L)}", simulations' two-tail convention (P016-E006/P016-E008), p. 400. -/
noncomputable def doubledP (L U : ℝ) : ℝ := min 1 (2 * min L U)

/-- "completely at random", p. 397: the uniform law on a nonempty finite design. -/
noncomputable def uniformLaw (Ω : Type) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight := fun _ => 1 / Fintype.card Ω
  nonneg := fun _ => by positivity
  total := by simp [div_eq_mul_inv, Fintype.card_ne_zero]

/-- Six assignments with two of four treated; the complete randomization
design in P016-E004 and P016-E001 witnesses (not paper data). -/
def complete4 : Fin 6 → Assignment 4 :=
  ![![true,true,false,false], ![true,false,true,false], ![true,false,false,true],
    ![false,true,true,false], ![false,true,false,true], ![false,false,true,true]]

/-- Four assignments treating one in each block {1,3},{2,4}, P016-E004 witness. -/
def blocked4 : Fin 4 → Assignment 4 :=
  ![![true,true,false,false], ![true,false,false,true],
    ![false,true,true,false], ![false,false,true,true]]

/-- Fixed outcomes (0,1,2,3) of the exact P016-E004/P016-E001/P016-E002/P016-E005 witnesses, not the paper's data. -/
def u4 : Outcome 4 := ![0,1,2,3]

/-- "sum_i {u_i - (X b)_i}²", corrected equation (2), p. 399; P016-E002. -/
noncomputable def lsObjective {n k : ℕ} (u : Outcome n) (X : Fin n → Fin k → ℝ)
    (b : Fin k → ℝ) : ℝ := ∑ i, (u i - ∑ j, X i j * b j)^2

/-- Least-squares fitted vector (X b)_i, corrected equation (2), p. 399. -/
noncomputable def fitted {n k : ℕ} (X : Fin n → Fin k → ℝ) (b : Fin k → ℝ) : Outcome n :=
  fun i => ∑ j, X i j * b j

/-- "min_b ‖u−Xb‖²", correction P016-E002 to (2), p. 399. The infimum formulation
does not impose full rank; attainment is stated in T10(b). -/
noncomputable def lsRSS {n k : ℕ} (u : Outcome n) (X : Fin n → Fin k → ℝ) : ℝ :=
  sInf (Set.range (lsObjective u X))

/-- "z^T S ... number of directly connected nodes assigned treatment", p. 399. -/
noncomputable def treatedNeighbors {n : ℕ} (S : Fin n → Fin n → ℝ)
    (z : Assignment n) (i : Fin n) : ℝ := ∑ j, bit (z j) * S j i

/-- "1^T S ... degree of the node", p. 399, §2.1. -/
noncomputable def degree {n : ℕ} (S : Fin n → Fin n → ℝ) (i : Fin n) : ℝ := ∑ j, S j i

/-- "X ... Z_i, z^T S, 1^T S", p. 399, (2), with the intercept made explicit by P016-E002. -/
noncomputable def networkX {n : ℕ} (S : Fin n → Fin n → ℝ) (z : Assignment n) :
    Fin n → Fin 4 → ℝ := fun i => ![1,bit (z i),treatedNeighbors S z i,degree S i]

/-- Rows (1,z_i) of the simple regression, corrected (1), p. 397. -/
noncomputable def basicX {n : ℕ} (z : Assignment n) : Fin n → Fin 2 → ℝ :=
  fun i => ![1,bit (z i)]

/-- Two group multisets, P016-E004 correction to the information contrast, p. 397. -/
noncomputable def groupValues {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) : Multiset ℝ :=
  ((Finset.univ.filter (fun i => z i = g)).val).map u

/-- "same multiset of treated values ... and ... control values", P016-E004 correction. -/
def sameMargins {n : ℕ} (u : Outcome n) (z : Assignment n) (v : Outcome n) (w : Assignment n) : Prop :=
  ∀ g, groupValues u z g = groupValues v w g

set_option maxRecDepth 2048

macro "audit_num" : tactic => `(tactic|
  (simp only [u4, complete4, blocked4, rss, tss, pooledMean, meanDifference,
    groupMean, groupSum, groupSize, ecdf, sampleECDF, ks, signedKS,
    additiveAdjust, additiveGenerate, multiplicativeAdjust, multiplicativeGenerate,
    bit, mass, uniformLaw, expectation, covariance, variance, upperP, lowerP, doubledP,
    Fin.sum_univ_succ, Fin.sum_univ_zero, List.ofFn_succ, List.ofFn_zero,
    List.foldr_cons, List.foldr_nil]
   norm_num))


/-- Monotonicity of probability for the finite assignment law, p. 396. -/
theorem mass_mono {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) {E F : Ω → Prop}
    (h : ∀ i, E i → F i) : mass P E ≤ mass P F := by
  classical
  unfold mass
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : E i
  · simp [hi, h i hi]
  · simp only [hi, ↓reduceIte]
    split_ifs <;> simp [P.nonneg]

/-- The finite assignment distribution has total probability 1, p. 396. -/
theorem mass_all {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) :
    mass P (fun _ => True) = 1 := by simp [mass, P.total]

/-- The union bound for exact randomization events, P016-E005 validity. -/
theorem mass_or_le {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (E F : Ω → Prop) :
    mass P (fun i => E i ∨ F i) ≤ mass P E + mass P F := by
  classical
  rw [mass, mass, mass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hE : E i <;> by_cases hF : F i <;> simp [hE,hF,P.nonneg]

/-- Inclusive upper-tail calibration for any statistic under a sharp null,
p. 397, validity sentence, corrected P016-E005; T12(iii), upper tail. -/
theorem upper_tail_bound {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) : mass P (fun z => upperP P s z ≤ α) ≤ α := by
  classical
  let A := Finset.univ.filter (fun z => upperP P s z ≤ α)
  by_cases hA : A.Nonempty
  · obtain ⟨z, hz, hmin⟩ := A.exists_min_image s hA
    have hzα : upperP P s z ≤ α := (Finset.mem_filter.mp hz).2
    calc
      mass P (fun w => upperP P s w ≤ α) ≤ upperP P s z := by
        apply mass_mono P
        intro w hw
        exact hmin w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)
      _ ≤ α := hzα
  · have hnone : ∀ z, ¬ upperP P s z ≤ α := by
      intro z hz
      exact hA ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩⟩
    simpa [mass,hnone] using hα

/-- Inclusive lower-tail calibration for any statistic, p. 397, P016-E005;
T12(iii), lower tail. No effect-increasing premise is imposed. -/
theorem lower_tail_bound {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) : mass P (fun z => lowerP P s z ≤ α) ≤ α := by
  have heq : lowerP P s = upperP P (fun z => -s z) := by
    funext z
    simp [lowerP, upperP, mass]
  rw [heq]
  exact upper_tail_bound P _ α hα

/-- The capped doubled minimum of inclusive exact tails is valid, p. 397,
corrected P016-E005; T12(iii), including ties and nonuniform assignment weights. -/
theorem two_tail_bound {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    mass P (fun z => doubledP (lowerP P s z) (upperP P s z) ≤ α) ≤ α := by
  by_cases ha : α = 1
  · subst α
    calc
      _ ≤ mass P (fun _ => True) := mass_mono P (fun _ _ => trivial)
      _ = 1 := mass_all P
  · have hlt : α < 1 := lt_of_le_of_ne hα1 ha
    have hsub : ∀ z, doubledP (lowerP P s z) (upperP P s z) ≤ α →
        lowerP P s z ≤ α/2 ∨ upperP P s z ≤ α/2 := by
      intro z hz
      unfold doubledP at hz
      rcases (min_le_iff.mp hz) with h | h
      · exact False.elim (not_le_of_gt hlt h)
      · rcases le_total (lowerP P s z) (upperP P s z) with hLU | hUL
        · rw [min_eq_left hLU] at h
          exact Or.inl (by linarith)
        · rw [min_eq_right hUL] at h
          exact Or.inr (by linarith)
    calc
      _ ≤ mass P (fun z => lowerP P s z ≤ α/2 ∨ upperP P s z ≤ α/2) := mass_mono P hsub
      _ ≤ mass P (fun z => lowerP P s z ≤ α/2) + mass P (fun z => upperP P s z ≤ α/2) :=
        mass_or_le P _ _
      _ ≤ α/2 + α/2 := add_le_add (lower_tail_bound P s _ (by linarith))
        (upper_tail_bound P s _ (by linarith))
      _ = α := by ring

/-- T12(iii): the corrected upper-tail level bound on a finite assignment
support with strictly positive probabilities and alpha in [0,1], p. 397 (P016-E005). -/
theorem t12_upper_valid {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (hP : ∀ z, 0 < P.weight z) (s : Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    mass P (fun z => upperP P s z ≤ α) ≤ α :=
  upper_tail_bound P s α hα

/-- T12(iii): the corrected lower-tail level bound with strictly positive
support probabilities and alpha in [0,1], p. 397 (P016-E005). -/
theorem t12_lower_valid {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (hP : ∀ z, 0 < P.weight z) (s : Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    mass P (fun z => lowerP P s z ≤ α) ≤ α :=
  lower_tail_bound P s α hα

/-- T12(iii): the corrected capped doubled-minimum level bound with strictly
positive support probabilities and alpha in [0,1], p. 397 (P016-E005). -/
theorem t12_two_tail_valid {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (hP : ∀ z, 0 < P.weight z) (s : Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    mass P (fun z => doubledP (lowerP P s z) (upperP P s z) ≤ α) ≤ α :=
  two_tail_bound P s α hα hα1


/-- Listed-order covariance with divisor two, P016-E004 witness (not a paper definition). -/
noncomputable def pairedCovariance2 (t c : Outcome 2) : ℝ :=
  ((t 0 - (t 0+t 1)/2)*(c 0 - (c 0+c 1)/2) +
    (t 1 - (t 0+t 1)/2)*(c 1 - (c 0+c 1)/2))/2

/-- T1(i): reversing the listed control pairing reverses covariance but leaves
the simple SSR and KS unchanged; P016-E004 exact witness, p. 397 contrast. -/
theorem t1_pairing_witness :
    pairedCovariance2 ![0,2] ![1,3] = 1 ∧
    pairedCovariance2 ![0,2] ![3,1] = -1 ∧
    rss ![0,2,1,3] (complete4 0) = 4 ∧ rss ![0,2,3,1] (complete4 0) = 4 ∧
    ks ![0,2,1,3] (complete4 0) = 1/2 ∧ ks ![0,2,3,1] (complete4 0) = 1/2 := by
  norm_num [pairedCovariance2]
  audit_num

/-- T1(ii): exact values of both statistics under complete and blocked designs,
P016-E004, not a printed data set. -/
theorem t1_design_tables :
    (∀ k, rss u4 (complete4 k) = (![1,4,5,5,4,1] : Fin 6 → ℝ) k ∧
      ks u4 (complete4 k) = (![1,1/2,1/2,1/2,1/2,1] : Fin 6 → ℝ) k) ∧
    (∀ k, rss u4 (blocked4 k) = (![1,5,5,1] : Fin 4 → ℝ) k ∧
      ks u4 (blocked4 k) = (![1,1/2,1/2,1] : Fin 4 → ℝ) k) := by
  constructor <;> intro k <;> fin_cases k <;> audit_num

/-- T1(ii): changing only the design changes both tail probabilities and the
covariance of the two means; P016-E004, p. 397 information contrast. -/
theorem t1_design_probabilities :
    mass (uniformLaw (Fin 6)) (fun k => rss u4 (complete4 k) ≤ rss u4 (complete4 0)) = 1/3 ∧
    mass (uniformLaw (Fin 6)) (fun k => ks u4 (complete4 0) ≤ ks u4 (complete4 k)) = 1/3 ∧
    covariance (uniformLaw (Fin 6)) (fun k => groupMean u4 (complete4 k) true)
      (fun k => groupMean u4 (complete4 k) false) = -5/12 ∧
    mass (uniformLaw (Fin 4)) (fun k => rss u4 (blocked4 k) ≤ rss u4 (blocked4 0)) = 1/2 ∧
    mass (uniformLaw (Fin 4)) (fun k => ks u4 (blocked4 0) ≤ ks u4 (blocked4 k)) = 1/2 ∧
    covariance (uniformLaw (Fin 4)) (fun k => groupMean u4 (blocked4 k) true)
      (fun k => groupMean u4 (blocked4 k) false) = -1/2 := by audit_num

/-- T2(G): a scalar KS distance does not determine SSR, P016-E004 corrected explanation. -/
theorem t2_scalar_ks_witness :
    ks u4 (complete4 1) = 1/2 ∧ ks u4 (complete4 2) = 1/2 ∧
    rss u4 (complete4 1) = 4 ∧ rss u4 (complete4 2) = 5 := by audit_num

/-- T9(i): the literal signed footnote-3 statistic is different from two-sided
KS and changes on swapping labels, p. 396; P016-E002 exact witness. -/
theorem t9_signed_ks_witness :
    (∀ i : Fin 4, ecdf u4 (complete4 5) true (u4 i) - ecdf u4 (complete4 5) false (u4 i) =
      (![-1/2,-1,-1/2,0] : Outcome 4) i) ∧
    signedKS u4 (complete4 5) = 0 ∧ ks u4 (complete4 5) = 1 ∧
    signedKS u4 (complete4 0) = 1 ∧ ks u4 (complete4 0) = 1 := by
  constructor
  · intro i; fin_cases i <;> audit_num
  · audit_num

/-- T9(ii): the pooled reading of (1) has a point-mass reference distribution,
whereas the intended group-mean SSR is nonconstant; P016-E002, p. 397. -/
theorem t9_pooled_witness : tss u4 = 5 ∧
    lowerP (uniformLaw (Fin 6)) (fun _ => tss u4) 0 = 1 ∧
    upperP (uniformLaw (Fin 6)) (fun _ => tss u4) 0 = 1 ∧
    lowerP (uniformLaw (Fin 6)) (fun k => rss u4 (complete4 k)) 0 = 1/3 := by audit_num

/-- T11(i)–(ii): KS decreases when treated responses rise and control responses
fall (also with strict changes in both groups), P016-E005, p. 397. -/
theorem t11_ks_witness :
    (∀ i : Fin 4, if complete4 0 i then u4 i ≤ (![2,3,2,3] : Outcome 4) i
      else (![2,3,2,3] : Outcome 4) i ≤ u4 i) ∧
    ks u4 (complete4 0) = 1 ∧ ks ![2,3,2,3] (complete4 0) = 0 ∧
    signedKS u4 (complete4 0) = 1 ∧ signedKS ![2,3,2,3] (complete4 0) = 0 ∧
    (∀ i : Fin 4, if complete4 0 i then (![0,1,4,5] : Outcome 4) i < (![2,3,2,3] : Outcome 4) i
      else (![2,3,2,3] : Outcome 4) i < (![0,1,4,5] : Outcome 4) i) ∧
    ks ![0,1,4,5] (complete4 0) = 1 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | (intro i; fin_cases i <;> audit_num) | audit_num

/-- T11(iii): raising a treated response can decrease or increase SSR,
so neither orientation is effect increasing; P016-E005 witness, p. 397. -/
theorem t11_rss_witness :
    rss ![0,2,0,2] (complete4 0) = 4 ∧
    rss ![1,2,0,2] (complete4 0) = 5/2 ∧
    rss ![0,3,0,2] (complete4 0) = 13/2 ∧
    (∀ i : Fin 4, (![0,2,0,2] : Outcome 4) i ≤ (![1,2,0,2] : Outcome 4) i ∧
      (![0,2,0,2] : Outcome 4) i ≤ (![0,3,0,2] : Outcome 4) i) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals first | (intro i; fin_cases i <;> audit_num) | audit_num

/-- T8(a): the corrected adjusted vector equals y0+(tau−tau0)Z and is fixed
at the true additive hypothesis, p. 396, steps (1)–(2); P016-E001. -/
theorem t8_additive_mapping {n : ℕ} (y : Outcome n) (z : Assignment n) (t t0 : ℝ) :
    additiveAdjust (additiveGenerate y z t) z t0 = additiveGenerate y z (t-t0) ∧
    additiveAdjust (additiveGenerate y z t) z t = y := by
  constructor <;> funext i <;> simp [additiveAdjust,additiveGenerate] <;> ring

/-- T7(i): all six raw observed mean differences are far outside the adjusted
reference distribution under the true additive effect 10; P016-E001 exact witness. -/
theorem t7_mean_witness :
    (∀ k : Fin 6, meanDifference u4 (complete4 k) = (![-2,-1,0,0,1,2] : Fin 6 → ℝ) k ∧
      meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k) =
        (![8,9,10,10,11,12] : Fin 6 → ℝ) k ∧
      mass (uniformLaw (Fin 6)) (fun j => |meanDifference u4 (complete4 j)| ≥
        |meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)|) = 0 ∧
      mass (uniformLaw (Fin 6)) (fun j => meanDifference u4 (complete4 j) ≥
        meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)) = 0 ∧
      mass (uniformLaw (Fin 6)) (fun j => |meanDifference u4 (complete4 j)| ≥
        |meanDifference u4 (complete4 k)|) = (![1/3,2/3,1,1,2/3,1/3] : Fin 6 → ℝ) k) := by
  intro k; fin_cases k <;> audit_num

/-- T7(i): the printed raw-versus-adjusted comparison rejects the true
hypothesis with probability one at every positive level; P016-E001, step (4), p. 396. -/
theorem t7_mean_rejects_truth (α : ℝ) (hα : 0 < α) :
    mass (uniformLaw (Fin 6)) (fun k =>
      mass (uniformLaw (Fin 6)) (fun j => |meanDifference u4 (complete4 j)| ≥
        |meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)|) < α) = 1 := by
  have hzero : ∀ k : Fin 6, mass (uniformLaw (Fin 6)) (fun j => |meanDifference u4 (complete4 j)| ≥
      |meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)|) = 0 :=
    fun k => (t7_mean_witness k).2.2.1
  simp only [hzero]
  simpa only [hα] using mass_all (uniformLaw (Fin 6))

/-- T12(iv): the non-effect-increasing KS nevertheless has valid exact
upper-tail p values on the six-assignment example, P016-E005 validity check. -/
theorem t12_ks_p_table : ∀ k : Fin 6,
    upperP (uniformLaw (Fin 6)) (fun j => ks u4 (complete4 j)) k =
      (![1/3,1,1,1,1,1/3] : Fin 6 → ℝ) k := by
  intro k; fin_cases k <;> audit_num

/-- T12(iv): the exact rejection probability is 0, 1/3 or 1 according to the
printed threshold ranges in the P016-E005 six-assignment check, p. 397. -/
theorem t12_ks_size (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    mass (uniformLaw (Fin 6)) (fun k => upperP (uniformLaw (Fin 6))
      (fun j => ks u4 (complete4 j)) k ≤ α) =
      if α < 1/3 then 0 else if α < 1 then 1/3 else 1 := by
  classical
  simp only [t12_ks_p_table]
  unfold mass
  simp only [t12_ks_p_table,uniformLaw,Fin.sum_univ_succ,Fin.sum_univ_zero]
  by_cases hsmall : α < 1/3
  · have hnot1 : ¬ (1 : ℝ) ≤ α := by linarith
    have hnot3 : ¬ (1/3 : ℝ) ≤ α := not_le_of_gt hsmall
    norm_num [hsmall,hnot1,hnot3]
  · by_cases hmid : α < 1
    · have hnot1 : ¬ (1 : ℝ) ≤ α := not_le_of_gt hmid
      have hyes3 : (1/3 : ℝ) ≤ α := le_of_not_gt hsmall
      norm_num [hsmall,hmid,hnot1,hyes3]
    · have hyes1 : (1 : ℝ) ≤ α := le_of_not_gt hmid
      have hyes3 : (1/3 : ℝ) ≤ α := by linarith
      norm_num [hsmall,hmid,hyes1,hyes3]

/-- The row-oriented application exposure (Sz)_i, p. 400; P016-E006 correction. -/
noncomputable def exposureSum {n : ℕ} (S : Fin n → Fin n → ℝ) (z : Assignment n)
    (i : Fin n) : ℝ := ∑ j, S i j * bit (z j)

/-- "S_ij=1−|s_i−s_j|/2 ... diagonal and undefined entries zero", P016-E006
corrected application model, p. 400. Optional scores model undefined coordinates. -/
noncomputable def similarity {n : ℕ} (s : Fin n → Option ℝ) (i j : Fin n) : ℝ :=
  if i = j then 0 else match s i, s j with
  | some a, some b => 1 - |a-b|/2
  | _, _ => 0

/-- The raw distance matrix "Gamma", p. 400, under the ordinary distance reading. -/
noncomputable def distance {n : ℕ} (s : Outcome n) (i j : Fin n) : ℝ := |s i-s j|

/-- "mu_ia ... mean of (Sz')_i among saved ... assignments with z'_i=a",
P016-E006 correction to the application, p. 400. The theorem premises require both
conditioning sets to be nonempty. -/
noncomputable def conditionalMean {n : ℕ} {Ω : Type} [Fintype Ω] (S : Fin n → Fin n → ℝ)
    (bank : Ω → Assignment n) (i : Fin n) (a : Bool) : ℝ :=
  (∑ b, if bank b i = a then exposureSum S (bank b) i else 0) /
    (∑ b, if bank b i = a then (1 : ℝ) else 0)

/-- "h_i(z)=(Sz)_i−z_i mu_i1−(1−z_i)mu_i0", P016-E006 correction, p. 400. -/
noncomputable def centeredExposure {n : ℕ} {Ω : Type} [Fintype Ω] (S : Fin n → Fin n → ℝ)
    (bank : Ω → Assignment n) (z : Assignment n) : Outcome n :=
  fun i => exposureSum S z i - bit (z i)*conditionalMean S bank i true -
    (1-bit (z i))*conditionalMean S bank i false

/-- "s_h(z)^2=(n−1)⁻¹ sum_i(h_i−bar h)^2", P016-E006 correction, p. 400.
The subtraction is in ℝ; all uses of sample variance have n ≥ 2. -/
noncomputable def sampleVariance {n : ℕ} (h : Outcome n) : ℝ :=
  (∑ i, (h i-pooledMean h)^2) / ((n : ℝ)-1)

/-- "sample standard deviation across all units", P016-E006 correction, p. 400. -/
noncomputable def sampleSD {n : ℕ} (h : Outcome n) : ℝ := Real.sqrt (sampleVariance h)

/-- "e_i(z)=(h_i(z)−bar h(z))/s_h(z)", positive denominator,
P016-E006 corrected application model, p. 400. -/
noncomputable def standardize {n : ℕ} (h : Outcome n) : Outcome n :=
  fun i => (h i-pooledMean h) / sampleSD h

/-- Bank-centered, standardized exposure in the released application, P016-E006, p. 400. -/
noncomputable def codedExposure {n N : ℕ} (S : Fin n → Fin n → ℝ)
    (bank : Fin N → Assignment n) (z : Assignment n) : Outcome n :=
  standardize (centeredExposure S bank z)

/-- "u=Y−beta1 Z−beta2 e(Z), held fixed", P016-E006 correction, p. 400. -/
noncomputable def applicationAdjust {n : ℕ} (Y : Outcome n) (Z : Assignment n)
    (e : Outcome n) (b1 b2 : ℝ) : Outcome n := fun i => Y i-bit (Z i)*b1-b2*e i

/-- "u ~ 1+z+e(z)", application regression, P016-E006 correction, p. 400. -/
noncomputable def applicationX {n : ℕ} (z : Assignment n) (e : Outcome n) :
    Fin n → Fin 3 → ℝ := fun i => ![1,bit (z i),e i]


/-- "p values ... less than .05", AS PRINTED, pp. 398, 400 and Fig. 3, p. 401. -/
def printedReject (p : ℝ) : Prop := p < 1/20

/-- "p <= .05", the released simulations, explicitly specified by P016-E006, p. 400. -/
def codedReject (p : ℝ) : Prop := p ≤ 1/20

/-- The four matched-pair bank assignments of P016-E006 T3(i), not paper data. -/
def matchedBank4 : Fin 4 → Assignment 4 :=
  ![![false,true,false,true], ![false,true,true,false],
    ![true,false,false,true], ![true,false,true,false]]

/-- The eight matched-pair assignments of P016-E006 T3(ii), indexed by three bits. -/
def matchedBank6 (b : Fin 3 → Bool) : Assignment 6 :=
  ![b 0, !(b 0), b 1, !(b 1), b 2, !(b 2)]

/-- Scores of the four-unit P016-E006 witness, not the legislative data. -/
noncomputable def scores4 : Outcome 4 := ![-1,-1/2,1/2,1]

/-- Scores of the six-unit P016-E006 witness, not the legislative data. -/
noncomputable def scores6 : Outcome 6 := ![-1,-3/4,-1/2,0,1/4,1]

/-- T3(i): the exposure at equal raw exposures for two treated units is unequal,
so no changed intercept/direct coefficient/rescaling recovers it; P016-E006, p. 400. -/
theorem t3_four_unit_exposure :
    (∀ i j : Fin 4, similarity (fun k => some (scores4 k)) i j =
      (!![0,3/4,1/4,0; 3/4,0,1/2,1/4; 1/4,1/2,0,3/4; 0,1/4,3/4,0] :
        Matrix (Fin 4) (Fin 4) ℝ) i j) ∧
    (∀ i : Fin 4, conditionalMean (similarity (fun k => some (scores4 k))) matchedBank4 i false =
      (![7/8,9/8,9/8,7/8] : Outcome 4) i ∧
      conditionalMean (similarity (fun k => some (scores4 k))) matchedBank4 i true =
      (![1/8,3/8,3/8,1/8] : Outcome 4) i) ∧
    (∀ i : Fin 4, exposureSum (similarity (fun k => some (scores4 k))) (complete4 1) i =
      (![1/4,5/4,1/4,3/4] : Outcome 4) i ∧
      exposureSum (distance scores4) (complete4 1) i = (![3/2,3/2,3/2,5/2] : Outcome 4) i ∧
      centeredExposure (similarity (fun k => some (scores4 k))) matchedBank4 (complete4 1) i =
        (![1/8,1/8,-1/8,-1/8] : Outcome 4) i) ∧
    (¬ ∃ A B C : ℝ, ∀ i : Fin 4, (![1/8,1/8,-1/8,-1/8] : Outcome 4) i =
      A+B*bit (complete4 1 i)+C*(![1/4,5/4,1/4,3/4] : Outcome 4) i) ∧
    (¬ ∃ A B C : ℝ, ∀ i : Fin 4, (![1/8,1/8,-1/8,-1/8] : Outcome 4) i =
      A+B*bit (complete4 1 i)+C*(![3/2,3/2,3/2,5/2] : Outcome 4) i) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [similarity,scores4]
  · intro i; fin_cases i <;>
      simp only [conditionalMean,exposureSum,matchedBank4,similarity,scores4,bit,
        Fin.sum_univ_succ,Fin.sum_univ_zero] <;> norm_num
  · intro i; fin_cases i <;>
      simp only [centeredExposure,conditionalMean,exposureSum,matchedBank4,similarity,distance,
        scores4,complete4,bit,Fin.sum_univ_succ,Fin.sum_univ_zero] <;> norm_num
  · rintro ⟨A,B,C,h⟩
    have h0 := h 0; have h2 := h 2
    norm_num [complete4,bit] at h0 h2
    linarith
  · rintro ⟨A,B,C,h⟩
    have h0 := h 0; have h2 := h 2
    norm_num [complete4,bit] at h0 h2
    linarith

/-- T3(i),(iii): exact nonzero determinant certificates, P016-E006. The second matrix
uses the first four table rows as exact recorded rationals, not rounded estimates. -/
theorem t3_determinants :
    Matrix.det (!![1,1,1/4,1/8; 1,0,5/4,1/8; 1,1,1/4,-1/8; 1,0,3/4,-1/8] :
      Matrix (Fin 4) (Fin 4) ℝ) = 1/8 ∧
    Matrix.det (!![1,0,216630956840236/10000000000000,370753999962044/1000000000000000;
      1,0,191947426509578/10000000000000,240866262449021/1000000000000000;
      1,1,208676713418681/10000000000000,286925998351727/1000000000000000;
      1,1,225467332911212/10000000000000,-193126413625389/1000000000000000] :
      Matrix (Fin 4) (Fin 4) ℝ) = -14030283848669586515272953541/10^28 := by
  simp only [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_unique,Matrix.submatrix_apply]
  norm_num [Fin.succAbove]

/-- T3(iii): in the four exact recorded application rows h is not an affine
function of own treatment and raw exposure, P016-E006, p. 400. -/
theorem t3_table_not_affine :
    ¬ ∃ A B C : ℝ, ∀ i : Fin 4,
      (![370753999962044/10^15,240866262449021/10^15,
        286925998351727/10^15,-193126413625389/10^15] : Outcome 4) i =
      A+B*(![0,0,1,1] : Outcome 4) i + C*
        (![216630956840236/10^13,191947426509578/10^13,
          208676713418681/10^13,225467332911212/10^13] : Outcome 4) i := by
  rintro ⟨A,B,C,h⟩
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  norm_num at h0 h1 h2 h3
  linarith

/-- T4(a): the corrected application adjustment is fixed under a true model,
P016-E006 corrected model, p. 400. -/
theorem t4_application_mapping {n N : ℕ} (hn : 2 ≤ n)
    (S : Fin n → Fin n → ℝ) (hS : ∀ i j, S i j = S j i) (hdiag : ∀ i, S i i = 0)
    (bank : Fin N → Assignment n) (hbank : ∀ i a, ∃ b, bank b i = a)
    (Ω : Finset (Assignment n)) (hsd : ∀ z ∈ Ω, 0 < sampleSD (centeredExposure S bank z))
    (y0 : Outcome n) (y : Assignment n → Outcome n) (b1 b2 : ℝ)
    (hmodel : ∀ z ∈ Ω, ∀ i, y z i = y0 i+bit (z i)*b1+b2*codedExposure S bank z i) :
    ∀ z ∈ Ω, applicationAdjust (y z) z (codedExposure S bank z) b1 b2 = y0 := by
  intro z hz
  funext i
  simp only [applicationAdjust,hmodel z hz i]
  ring

/-- A distance matrix on the units, Section 3, p. 400: nonnegative symmetric
distances, zero self-distance, and the triangle inequality. Distinct units can
have identical scores, hence zero distance between them is allowed. -/
def IsDistanceMatrix {n : ℕ} (Γ : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ Γ i j) ∧ (∀ i j, Γ i j = Γ j i) ∧
  (∀ i, Γ i i = 0) ∧ (∀ i j k, Γ i k ≤ Γ i j + Γ j k)

/-- T6: consistency of the AS-PRINTED raw-distance model with any normalizing
function g that gives unit variance on this assignment, Section 3, p. 400.
The unspecified g is not identified with the coded bank-centered exposure.
Unit variance uses the across-unit sample-variance convention. -/
theorem t6_printed_model_consistency {n : ℕ} (hn : 2 ≤ n) (Γ : Fin n → Fin n → ℝ)
    (hΓ : IsDistanceMatrix Γ) (z : Assignment n) (g : Outcome n → Outcome n)
    (hg : sampleVariance (g (exposureSum Γ z)) = 1) (y0 : Outcome n) (b1 b2 : ℝ) :
    applicationAdjust (fun i => y0 i+bit (z i)*b1+b2*g (exposureSum Γ z) i)
      z (g (exposureSum Γ z)) b1 b2 = y0 := by
  funext i
  simp only [applicationAdjust]
  ring

/-- T6: the printed strict rejection convention on pp. 398, 400 and in the
Fig. 3 caption, p. 401, is rejection exactly when p < .05. -/
theorem t6_printed_cutoff (p : ℝ) : printedReject p ↔ p < 1/20 := Iff.rfl

/-- T6: the printed model with its unspecified normalizing FUNCTION g left
as a parameter. On any finite nonempty design, the true printed parameters
recover the same uniformity outcomes under every assignment. The algebra
holds for every g satisfying the printed unit-variance requirement on the
design and every distance matrix. Section 3, p. 400. Across-unit variance uses
the sample-variance convention; g is otherwise unspecified. -/
theorem t6_printed_general_model_consistency {n : ℕ} (hn : 2 ≤ n)
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (assign : Ω → Assignment n)
    (Γ : Fin n → Fin n → ℝ) (hΓ : IsDistanceMatrix Γ) (g : Outcome n → Outcome n)
    (hg : ∀ ω, sampleVariance (g (exposureSum Γ (assign ω))) = 1)
    (y0 : Outcome n) (y : Ω → Outcome n) (b1 b2 : ℝ)
    (hy : ∀ ω i, y ω i = y0 i+b1*bit (assign ω i)+b2*g (exposureSum Γ (assign ω)) i) :
    ∀ ω, applicationAdjust (y ω) (assign ω) (g (exposureSum Γ (assign ω))) b1 b2 = y0 := by
  intro ω
  funext i
  simp only [applicationAdjust,hy]
  ring

/-- T4(e): weak and strict cutoffs differ exactly at equality, P016-E006,
pp. 398, 400 and Fig. 3. -/
theorem t4_cutoff_difference (p α : ℝ) : (p ≤ α ∧ ¬ p < α) ↔ p = α := by
  constructor
  · intro h
    exact le_antisymm h.1 (le_of_not_gt h.2)
  · rintro rfl
    exact ⟨le_rfl,lt_irrefl _⟩

/-- Sum of squared residuals at a least-squares minimizer really is the minimum,
corrected (2), p. 399 (P016-E002). -/
theorem lsRSS_of_minimizer {n k : ℕ} (u : Outcome n) (X : Fin n → Fin k → ℝ)
    (b : Fin k → ℝ) (hb : ∀ c, lsObjective u X b ≤ lsObjective u X c) :
    lsRSS u X = lsObjective u X b := by
  apply IsLeast.csInf_eq
  exact ⟨⟨b,rfl⟩,fun x ⟨c,hc⟩ => hc ▸ hb c⟩

/-- A finite OLS minimum can be certified by its exact excess sum of squares;
this avoids numerical inversion and is used for P016-E002/P016-E004/P016-E006 witnesses. -/
theorem lsRSS_of_square_certificate {n k : ℕ} (u : Outcome n) (X : Fin n → Fin k → ℝ)
    (b : Fin k → ℝ) (hcert : ∀ c, lsObjective u X c = lsObjective u X b +
      ∑ i, (fitted X c i-fitted X b i)^2) : lsRSS u X = lsObjective u X b := by
  apply lsRSS_of_minimizer
  intro c
  rw [hcert c]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (fitted X c i-fitted X b i))

/-- Both groups' sums together give the full population sum, P016-E004 decomposition. -/
theorem group_sums {n : ℕ} (u : Outcome n) (z : Assignment n) :
    groupSum u z false + groupSum u z true = ∑ i, u i := by
  classical
  rw [groupSum,groupSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> simp

/-- Group sizes partition the population, P016-E004, p. 397. -/
theorem group_sizes {n : ℕ} (z : Assignment n) : groupSize z false + groupSize z true = n := by
  classical
  rw [groupSize,groupSize,← Finset.sum_add_distrib]
  convert Finset.sum_const (s := Finset.univ (α := Fin n)) (b := (1 : ℕ)) using 1
  · apply Finset.sum_congr rfl
    intro i _
    cases z i <;> simp
  · simp

/-- The mean times the nonempty group's size equals its sum, P016-E004. -/
theorem group_mean_sum {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool)
    (hg : 0 < groupSize z g) : (groupSize z g : ℝ) * groupMean u z g = groupSum u z g := by
  have hne : (groupSize z g : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hg)
  unfold groupMean
  field_simp

/-- Expanding squares about an arbitrary group center, P016-E004 finite identity. -/
theorem group_square_expansion {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (c : ℝ) :
    groupSum (fun i => (u i-c)^2) z g = groupSum (fun i => (u i)^2) z g -
      2*c*groupSum u z g + (groupSize z g : ℝ)*c^2 := by
  classical
  have hcard : (groupSize z g : ℝ) = ∑ i, if z i = g then (1 : ℝ) else 0 := by
    simp [groupSize,Nat.cast_sum,Nat.cast_ite]
  rw [hcard]
  unfold groupSum
  calc
    _ = ∑ i, ((if z i = g then (u i)^2 else 0) -
      2*c*(if z i = g then u i else 0) + (if z i = g then (1 : ℝ) else 0)*c^2) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]

/-- Centering a nonempty group at its mean gives the square decomposition,
P016-E004, finite lemma supporting corrected equation (1), p. 397. -/
theorem group_center_decomposition {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool)
    (hg : 0 < groupSize z g) (c : ℝ) :
    groupSum (fun i => (u i-c)^2) z g =
      groupSum (fun i => (u i-groupMean u z g)^2) z g +
      (groupSize z g : ℝ)*(c-groupMean u z g)^2 := by
  rw [group_square_expansion,group_square_expansion,← group_mean_sum u z g hg]
  ring

/-- The corrected group SSR is the sum of the two group objectives, P016-E004. -/
theorem rss_groups {n : ℕ} (u : Outcome n) (z : Assignment n) :
    rss u z = groupSum (fun i => (u i-groupMean u z false)^2) z false +
      groupSum (fun i => (u i-groupMean u z true)^2) z true := by
  classical
  unfold rss groupSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hz : z i <;> simp [hz]

/-- Splitting the intercept-and-treatment objective into the two groups,
P016-E004, correction of equation (1), p. 397. -/
theorem basic_objective_groups {n : ℕ} (u : Outcome n) (z : Assignment n) (a b : ℝ) :
    lsObjective u (basicX z) ![a,b] = groupSum (fun i => (u i-a)^2) z false +
      groupSum (fun i => (u i-(a+b))^2) z true := by
  classical
  unfold lsObjective basicX groupSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hz : z i <;> simp [hz,bit,Fin.sum_univ_succ] <;> ring

/-- Exact excess of any coefficient objective above the group-mean objective,
P016-E004, finite lemma supporting corrected (1), p. 397. -/
theorem basic_objective_decomposition {n : ℕ} (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (a b : ℝ) :
    lsObjective u (basicX z) ![a,b] = rss u z +
      (groupSize z false : ℝ)*(a-groupMean u z false)^2 +
      (groupSize z true : ℝ)*(a+b-groupMean u z true)^2 := by
  rw [basic_objective_groups,group_center_decomposition u z false h0 a,
    group_center_decomposition u z true h1 (a+b),rss_groups]
  ring

/-- The exact second-moment expression of within-group SSR, P016-E004. -/
theorem rss_second_moments {n : ℕ} (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) :
    rss u z = (∑ i, (u i)^2) - (groupSize z false : ℝ)*(groupMean u z false)^2 -
      (groupSize z true : ℝ)*(groupMean u z true)^2 := by
  rw [rss_groups,group_square_expansion,group_square_expansion,
    ← group_mean_sum u z false h0,← group_mean_sum u z true h1,
    ← group_sums (fun i => (u i)^2) z]
  ring

/-- T2(A),T10(a): the simple regression has the unique coefficient minimum
alpha=m0, beta=m1−m0; its value is the sum of within-group squared residuals
and the second-moment expression, corrected (1), p. 397 (P016-E004/P016-E002). -/
theorem t2_least_squares {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) :
    lsRSS u (basicX z) = rss u z ∧
    (∀ a b : ℝ, lsObjective u (basicX z) ![a,b] = rss u z ↔
      a = groupMean u z false ∧ b = meanDifference u z) ∧
    rss u z = (∑ i, (u i)^2) - (groupSize z false : ℝ)*(groupMean u z false)^2 -
      (groupSize z true : ℝ)*(groupMean u z true)^2 := by
  have hn0 : (0 : ℝ) < groupSize z false := Nat.cast_pos.mpr h0
  have hn1 : (0 : ℝ) < groupSize z true := Nat.cast_pos.mpr h1
  have hopt : lsObjective u (basicX z) ![groupMean u z false,meanDifference u z] = rss u z := by
    rw [basic_objective_decomposition u z h0 h1]
    simp [meanDifference]
  refine ⟨?_,?_,rss_second_moments u z h0 h1⟩
  · rw [← hopt]
    apply lsRSS_of_minimizer
    intro c
    have hc : c = ![c 0,c 1] := by funext i; fin_cases i <;> rfl
    rw [hc,hopt,basic_objective_decomposition u z h0 h1]
    have hq0 := mul_nonneg hn0.le (sq_nonneg (c 0-groupMean u z false))
    have hq1 := mul_nonneg hn1.le (sq_nonneg (c 0+c 1-groupMean u z true))
    linarith
  · intro a b
    rw [basic_objective_decomposition u z h0 h1]
    constructor
    · intro h
      have hq0 := mul_nonneg hn0.le (sq_nonneg (a-groupMean u z false))
      have hq1 := mul_nonneg hn1.le (sq_nonneg (a+b-groupMean u z true))
      have hz0 : (groupSize z false : ℝ)*(a-groupMean u z false)^2 = 0 := by linarith
      have hz1 : (groupSize z true : ℝ)*(a+b-groupMean u z true)^2 = 0 := by linarith
      have ha := sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz0).resolve_left hn0.ne'))
      have hb := sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz1).resolve_left hn1.ne'))
      exact ⟨ha,by unfold meanDifference; linarith⟩
    · rintro ⟨rfl,rfl⟩
      simp [meanDifference]

/-- Centering the whole population: TSS has the exact second-moment form,
P016-E004, finite lemma supporting the decomposition in corrected (1), p. 397. -/
theorem tss_second_moments {n : ℕ} (hn : 0 < n) (u : Outcome n) :
    tss u = (∑ i, (u i)^2)-(n : ℝ)*(pooledMean u)^2 := by
  have hsum : (n : ℝ)*pooledMean u = ∑ i, u i := by
    unfold pooledMean
    field_simp
  unfold tss
  calc
    _ = (∑ i, (u i)^2)-2*pooledMean u*(∑ i, u i)+(n : ℝ)*(pooledMean u)^2 := by
      calc
        _ = ∑ i, ((u i)^2-2*pooledMean u*u i+(pooledMean u)^2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    _ = _ := by rw [← hsum]; ring

/-- T2(B): within-group SSR equals TSS minus the scaled squared mean difference,
corrected explanation of (1), p. 397 (P016-E004). -/
theorem t2_decomposition {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) :
    rss u z = tss u - (groupSize z false : ℝ)*groupSize z true/n*(meanDifference u z)^2 := by
  have hnr : (n : ℝ) = (groupSize z false : ℝ)+groupSize z true := by
    exact_mod_cast (group_sizes z).symm
  have hm : pooledMean u = ((groupSize z false : ℝ)*groupMean u z false+
      (groupSize z true : ℝ)*groupMean u z true)/n := by
    rw [group_mean_sum u z false h0,group_mean_sum u z true h1,group_sums]
    rfl
  rw [rss_second_moments u z h0 h1,tss_second_moments (by omega) u,hm,meanDifference,hnr]
  have hden : (groupSize z false : ℝ)+groupSize z true ≠ 0 := by
    have : (0 : ℝ) < groupSize z false := Nat.cast_pos.mpr h0
    have : (0 : ℝ) < groupSize z true := Nat.cast_pos.mpr h1
    positivity
  field_simp
  ring

/-- T2(C): for the SAME fixed outcomes and positive fixed group sizes, ordering
SSR reverses ordering of absolute differences of means; P016-E004, p. 397. -/
theorem t2_tail_equivalence {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z w : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true)
    (hw : groupSize w true = groupSize z true) :
    rss u w ≤ rss u z ↔ |meanDifference u z| ≤ |meanDifference u w| := by
  have hw0 : groupSize w false = groupSize z false := by
    have hz := group_sizes z; have hh := group_sizes w; omega
  have wh0 : 0 < groupSize w false := by simpa [hw0] using h0
  have wh1 : 0 < groupSize w true := by simpa [hw] using h1
  rw [t2_decomposition hn u w wh0 wh1,t2_decomposition hn u z h0 h1,hw0,hw]
  have hc : (0 : ℝ) < (groupSize z false : ℝ)*groupSize z true/n := by
    have : (0 : ℝ) < groupSize z false := Nat.cast_pos.mpr h0
    have : (0 : ℝ) < groupSize z true := Nat.cast_pos.mpr h1
    have : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    positivity
  have horder : ∀ a b : ℝ, tss u-((groupSize z false : ℝ)*groupSize z true/n)*b ≤
      tss u-((groupSize z false : ℝ)*groupSize z true/n)*a ↔ a ≤ b := by
    intro a b
    constructor
    · intro h
      apply (mul_le_mul_iff_right₀ hc).mp
      linarith
    · intro h
      have hh := (mul_le_mul_iff_right₀ hc).mpr h
      linarith
  rw [horder,sq_le_sq]

/-- T2(C), probability consequence: the lower SSR tail and the absolute mean-
difference upper tail are identical for every fixed-size finite design; P016-E004. -/
theorem t2_tail_probability {n : ℕ} {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (hn : 2 ≤ n) (u : Outcome n) (zobs : Assignment n) (assign : Ω → Assignment n)
    (h0 : 0 < groupSize zobs false) (h1 : 0 < groupSize zobs true)
    (hsize : ∀ ω, groupSize (assign ω) true = groupSize zobs true) :
    mass P (fun ω => rss u (assign ω) ≤ rss u zobs) =
      mass P (fun ω => |meanDifference u zobs| ≤ |meanDifference u (assign ω)|) := by
  classical
  unfold mass
  apply Finset.sum_congr rfl
  intro ω _
  simp only [t2_tail_equivalence hn u zobs (assign ω) h0 h1 (hsize ω)]

/-- T2(D): the basic SSR uses only the first two empirical group moments,
P016-E004 corrected information contrast, p. 397. -/
theorem t2_group_moments {n : ℕ} (hn : 2 ≤ n) (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) :
    rss u z = (groupSize z false : ℝ) * (groupMean (fun i => (u i)^2) z false -
      (groupMean u z false)^2) + (groupSize z true : ℝ) *
      (groupMean (fun i => (u i)^2) z true - (groupMean u z true)^2) := by
  have h := (t2_least_squares hn u z h0 h1).2.2
  have hs := group_sums (fun i => (u i)^2) z
  have hm0 := group_mean_sum (fun i => (u i)^2) z false h0
  have hm1 := group_mean_sum (fun i => (u i)^2) z true h1
  nlinarith

/-- Group-multiset cardinality is the group size, P016-E004, p. 397. -/
theorem group_values_card {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) :
    (groupValues u z g).card = groupSize z g := by
  classical
  simp only [groupValues,Multiset.card_map]
  change (Finset.univ.filter (fun i => z i = g)).card = groupSize z g
  rw [Finset.card_filter]
  rfl

/-- Summing the empirical group multiset gives the group outcome sum,
P016-E004, p. 397. -/
theorem group_values_sum {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) :
    (groupValues u z g).sum = groupSum u z g := by
  classical
  change (∑ i ∈ Finset.univ.filter (fun i => z i = g), u i) = groupSum u z g
  simp only [Finset.sum_filter,groupSum]

/-- The exact second moment is also a sum over the empirical group multiset,
P016-E004, p. 397. -/
theorem group_values_square {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) :
    ((groupValues u z g).map (fun x => x^2)).sum = groupSum (fun i => (u i)^2) z g := by
  classical
  simp only [groupValues,Multiset.map_map]
  change (∑ i ∈ Finset.univ.filter (fun i => z i = g), (u i)^2) = groupSum (fun i => (u i)^2) z g
  simp only [Finset.sum_filter,groupSum]

/-- The simple SSR is determined by the two group multisets, P016-E004 correction,
p. 397; finite portion of T2(D), also refuting the AS-PRINTED T5 claim. -/
theorem t2_rss_margin_invariance {n : ℕ} (hn : 2 ≤ n) (u v : Outcome n) (z w : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (hm : sameMargins u z v w) :
    rss u z = rss v w := by
  have hsz : ∀ g, groupSize z g = groupSize w g := by
    intro g
    rw [← group_values_card u z g,← group_values_card v w g,hm g]
  have hsum : ∀ g, groupSum u z g = groupSum v w g := by
    intro g
    rw [← group_values_sum u z g,← group_values_sum v w g,hm g]
  have hsq : ∀ g, groupSum (fun i => (u i)^2) z g = groupSum (fun i => (v i)^2) w g := by
    intro g
    rw [← group_values_square u z g,← group_values_square v w g,hm g]
  have hmn : ∀ g, groupMean u z g = groupMean v w g := by
    intro g; simp only [groupMean,hsum,hsz]
  have w0 : 0 < groupSize w false := by simpa [hsz] using h0
  have w1 : 0 < groupSize w true := by simpa [hsz] using h1
  rw [rss_second_moments u z h0 h1,rss_second_moments v w w0 w1,
    ← group_sums (fun i => (u i)^2) z,← group_sums (fun i => (v i)^2) w,hsz false,hsz true,
    hmn false,hmn true,hsq false,hsq true]
/-- Bounding a finite maximum with initial value zero, finite KS lemma for
the correction of footnote 3, p. 396. -/
theorem fold_max_le (l : List ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ x ∈ l, x ≤ c) :
    l.foldr max 0 ≤ c := by
  induction l with
  | nil => exact hc
  | cons a l ih =>
    exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- Each entry is bounded by the finite maximum, KS sample maximum,
footnote 3, p. 396. -/
theorem le_fold_max (l : List ℝ) (x : ℝ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

/-- The sample KS distance bounds the ECDF difference at EVERY real threshold,
including ties; finite lemma for corrected footnote 3, p. 396 (P016-E002). -/
theorem ks_threshold_bound {n : ℕ} (u : Outcome n) (z : Assignment n) (t : ℝ) :
    |ecdf u z true t-ecdf u z false t| ≤ ks u z := by
  classical
  let A := Finset.univ.filter (fun i => u i ≤ t)
  by_cases hA : A.Nonempty
  · obtain ⟨i,hi,hmax⟩ := A.exists_max_image u hA
    have hui : u i ≤ t := (Finset.mem_filter.mp hi).2
    have hiff : ∀ j, u j ≤ t ↔ u j ≤ u i := by
      intro j
      exact ⟨fun hj => hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩),fun hj => hj.trans hui⟩
    have hCDF : ∀ g, ecdf u z g t = ecdf u z g (u i) := by
      intro g
      simp only [ecdf,hiff]
    rw [hCDF true,hCDF false]
    apply le_fold_max
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · have hn : ∀ i, ¬ u i ≤ t := by
      intro i hi
      exact hA ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    have he0 : ∀ g, ecdf u z g t = 0 := by intro g; simp [ecdf,hn]
    rw [he0 true,he0 false]
    simp only [sub_self,abs_zero]
    unfold ks
    generalize List.ofFn (fun i => |ecdf u z true (u i)-ecdf u z false (u i)|) = l
    induction l with
    | nil => exact le_rfl
    | cons a l ih => exact ih.trans (le_max_right _ _)

/-- The sample-point maximum is the supremum over all thresholds, including
ties; correction to footnote 3, p. 396 (P016-E002), without any full-rank or untied-
outcome premise. -/
theorem ks_threshold_sup {n : ℕ} (u : Outcome n) (z : Assignment n) :
    ks u z = sSup (Set.range (fun t : ℝ => |ecdf u z true t-ecdf u z false t|)) := by
  let R := Set.range (fun t : ℝ => |ecdf u z true t-ecdf u z false t|)
  have hb : BddAbove R := ⟨ks u z,fun x ⟨t,ht⟩ => ht ▸ ks_threshold_bound u z t⟩
  have hne : R.Nonempty := ⟨_,⟨0,rfl⟩⟩
  apply le_antisymm
  · apply fold_max_le
    · exact (abs_nonneg _).trans (le_csSup hb ⟨0,rfl⟩)
    · intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact le_csSup hb ⟨u i,rfl⟩
  · exact csSup_le hne (fun x ⟨t,ht⟩ => ht ▸ ks_threshold_bound u z t)

/-- Each group ECDF lies between zero and one when the group is nonempty,
footnote 3, p. 396 (P016-E002). -/
theorem ecdf_range {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (t : ℝ)
    (hg : 0 < groupSize z g) : 0 ≤ ecdf u z g t ∧ ecdf u z g t ≤ 1 := by
  classical
  have hd : (0 : ℝ) < groupSize z g := Nat.cast_pos.mpr hg
  have hc : (groupSize z g : ℝ) = ∑ i, if z i = g then (1 : ℝ) else 0 := by simp [groupSize]
  have hn : 0 ≤ ∑ i, if z i = g ∧ u i ≤ t then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have hle : (∑ i, if z i = g ∧ u i ≤ t then (1 : ℝ) else 0) ≤ groupSize z g := by
    rw [hc]
    apply Finset.sum_le_sum
    intro i _
    by_cases hz : z i = g <;> by_cases hy : u i ≤ t <;> simp [hz,hy]
  exact ⟨div_nonneg hn hd.le,(div_le_iff₀ hd).mpr (by simpa using hle)⟩

/-- Group ECDFs are interchanged by swapping binary labels, correction to
footnote 3, p. 396 (P016-E002). -/
theorem ecdf_swap_labels {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (t : ℝ) :
    ecdf u (fun i => !(z i)) g t = ecdf u z (!g) t := by
  have hb : ∀ i, (Bool.not (z i) = g) ↔ z i = Bool.not g := by
    intro i; cases z i <;> cases g <;> decide
  simp only [ecdf,groupSize,hb]

/-- Integrating an arbitrary function of empirical group values gives its
group sum, P016-E004 margin-invariance correction, p. 397. -/
theorem group_values_function {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (f : ℝ → ℝ) :
    ((groupValues u z g).map f).sum = groupSum (fun i => f (u i)) z g := by
  classical
  simp only [groupValues,Multiset.map_map]
  change (∑ i ∈ Finset.univ.filter (fun i => z i = g), f (u i)) = groupSum (fun i => f (u i)) z g
  simp only [Finset.sum_filter,groupSum]

/-- Each empirical group CDF is the group mean of threshold indicators,
footnote 3, p. 396 and P016-E004 covariance correction. -/
theorem ecdf_indicator_mean {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (x : ℝ) :
    ecdf u z g x = groupMean (fun i => if u i ≤ x then 1 else 0) z g := by
  classical
  unfold ecdf groupMean groupSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z i = g <;> by_cases hu : u i ≤ x <;> simp [hi,hu]

/-- T2(D): neither simple SSR nor KS uses information beyond the two group
multisets; corrected P016-E004 information contrast, p. 397. -/
theorem t2_margin_invariance {n : ℕ} (hn : 2 ≤ n) (u v : Outcome n) (z w : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (hm : sameMargins u z v w) :
    rss u z = rss v w ∧ ks u z = ks v w := by
  have hsz : ∀ g, groupSize z g = groupSize w g := by
    intro g
    rw [← group_values_card u z g,← group_values_card v w g,hm g]
  have hCDF : ∀ g t, ecdf u z g t = ecdf v w g t := by
    intro g t
    rw [ecdf_indicator_mean,ecdf_indicator_mean]
    unfold groupMean
    rw [← group_values_function u z g (fun x => if x ≤ t then 1 else 0),
      ← group_values_function v w g (fun x => if x ≤ t then 1 else 0),hm g,hsz g]
  refine ⟨t2_rss_margin_invariance hn u v z w h0 h1 hm,?_⟩
  rw [ks_threshold_sup,ks_threshold_sup]
  simp only [hCDF]


/-- Under a deterministic affine relation, covariance is the corresponding
multiple of variance; P016-E004, finite randomization lemma. -/
theorem covariance_affine {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (f g : Ω → ℝ) (C k : ℝ) (hg : ∀ ω, g ω = C-k*f ω) :
    covariance P f g = -k*variance P f := by
  have heg : expectation P g = C-k*expectation P f := by
    unfold expectation
    simp_rw [hg,mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,P.total,one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hefg : expectation P (fun ω => f ω*g ω) =
      C*expectation P f-k*expectation P (fun ω => f ω*f ω) := by
    unfold expectation
    simp_rw [hg,mul_sub]
    rw [Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro ω _ <;> ring
  unfold covariance variance
  rw [heg,hefg]
  unfold covariance
  ring

/-- The fixed-size two means obey a deterministic linear constraint under
every realized assignment, P016-E004, p. 397. -/
theorem design_mean_constraint {n : ℕ} {Ω : Type} [Fintype Ω] (hn : 0 < n)
    (u : Outcome n) (assign : Ω → Assignment n) (n0 n1 : ℕ) (h0 : 0 < n0) (h1 : 0 < n1)
    (hsize : ∀ ω, groupSize (assign ω) false = n0 ∧ groupSize (assign ω) true = n1) :
    ∀ ω, (n1 : ℝ)*groupMean u (assign ω) true + (n0 : ℝ)*groupMean u (assign ω) false =
      n*pooledMean u := by
  intro ω
  have hg0 : 0 < groupSize (assign ω) false := by simpa [(hsize ω).1] using h0
  have hg1 : 0 < groupSize (assign ω) true := by simpa [(hsize ω).2] using h1
  have hm0 := group_mean_sum u (assign ω) false hg0
  have hm1 := group_mean_sum u (assign ω) true hg1
  rw [(hsize ω).1] at hm0
  rw [(hsize ω).2] at hm1
  rw [hm0,hm1,add_comm,group_sums]
  unfold pooledMean
  field_simp

/-- A fixed-size linear constraint entails the finite-design covariance
identity, P016-E004, p. 397. -/
theorem covariance_from_constraint {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (f g : Ω → ℝ) (n0 n1 C : ℝ) (h0 : n0 ≠ 0)
    (hrel : ∀ ω, n1*f ω+n0*g ω = C) : covariance P f g = -n1/n0*variance P f := by
  have hg : ∀ ω, g ω = C/n0-(n1/n0)*f ω := by
    intro ω
    field_simp
    linarith [hrel ω]
  simpa only [neg_div] using covariance_affine P f g (C/n0) (n1/n0) hg

/-- T2(E): both means AND ECDFs have the design-induced linear dependence and
covariance identity, P016-E004 corrected explanation, p. 397. -/
theorem t2_design_dependence {n : ℕ} {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (hn : 2 ≤ n) (u : Outcome n) (assign : Ω → Assignment n) (n0 n1 : ℕ)
    (h0 : 0 < n0) (h1 : 0 < n1)
    (hsize : ∀ ω, groupSize (assign ω) false = n0 ∧ groupSize (assign ω) true = n1) :
    (∀ ω, (n1 : ℝ)*groupMean u (assign ω) true + (n0 : ℝ)*groupMean u (assign ω) false =
      n*pooledMean u) ∧
    covariance P (fun ω => groupMean u (assign ω) true) (fun ω => groupMean u (assign ω) false) =
      -(n1 : ℝ)/n0 * variance P (fun ω => groupMean u (assign ω) true) ∧
    (∀ x : ℝ, (∀ ω, (n1 : ℝ)*ecdf u (assign ω) true x + (n0 : ℝ)*ecdf u (assign ω) false x =
      ∑ i, if u i ≤ x then (1 : ℝ) else 0) ∧
      covariance P (fun ω => ecdf u (assign ω) true x) (fun ω => ecdf u (assign ω) false x) =
        -(n1 : ℝ)/n0 * variance P (fun ω => ecdf u (assign ω) true x)) := by
  have hn0 : 0 < n := by omega
  have hne : (n0 : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr h0)
  have hmean := design_mean_constraint hn0 u assign n0 n1 h0 h1 hsize
  refine ⟨hmean,?_,?_⟩
  · exact covariance_from_constraint P _ _ n0 n1 (n*pooledMean u) hne hmean
  · intro x
    have hCDF := design_mean_constraint hn0 (fun i => if u i ≤ x then 1 else 0)
      assign n0 n1 h0 h1 hsize
    have hsum : (n : ℝ)*pooledMean (fun i => if u i ≤ x then 1 else 0) =
        ∑ i, if u i ≤ x then (1 : ℝ) else 0 := by unfold pooledMean; field_simp
    simp only [← ecdf_indicator_mean,hsum] at hCDF
    exact ⟨hCDF,covariance_from_constraint P _ _ n0 n1 _ hne hCDF⟩

/-- T2(F): extra network degree carries alignment information beyond group
margins; P016-E004 four-node path witness (not a paper data set), p. 399. -/
theorem t2_network_alignment :
    let z := complete4 1
    let S : Fin 4 → Fin 4 → ℝ := !![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0]
    let X := fun i : Fin 4 => (![1,bit (z i),degree S i] : Fin 3 → ℝ)
    sameMargins u4 z ![2,1,0,3] z ∧
    rss u4 z = 4 ∧ rss ![2,1,0,3] z = 4 ∧ ks u4 z = 1/2 ∧ ks ![2,1,0,3] z = 1/2 ∧
    (∀ i, degree S i = (![1,1,2,2] : Outcome 4) i) ∧
    lsObjective u4 X ![-1,-1,2] = 0 ∧ lsRSS u4 X = 0 ∧
    lsObjective ![2,1,0,3] X ![2,-1,0] = 4 ∧ lsRSS ![2,1,0,3] X = 4 := by
  dsimp
  have hc0 : ∀ c : Fin 3 → ℝ,
      lsObjective u4 (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) c =
      lsObjective u4 (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) ![-1,-1,2] +
      ∑ i, (fitted (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) c i -
        fitted (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) ![-1,-1,2] i)^2 := by
    intro c
    simp [lsObjective,fitted,degree,complete4,bit,u4,Fin.sum_univ_succ]
    ring
  have hc1 : ∀ c : Fin 3 → ℝ,
      lsObjective (![2,1,0,3] : Outcome 4) (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) c =
      lsObjective (![2,1,0,3] : Outcome 4) (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) ![2,-1,0] +
      ∑ i, (fitted (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) c i -
        fitted (fun i => ![1,bit (complete4 1 i),degree
        (!![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0] : Matrix (Fin 4) (Fin 4) ℝ) i]) ![2,-1,0] i)^2 := by
    intro c
    simp [lsObjective,fitted,degree,complete4,bit,Fin.sum_univ_succ]
    ring
  rw [lsRSS_of_square_certificate _ _ _ hc0,lsRSS_of_square_certificate _ _ _ hc1]
  have huniv : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by ext i; fin_cases i <;> simp
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro g; cases g <;> norm_num [sameMargins,groupValues,complete4,u4,huniv,
      Multiset.filter_cons,Multiset.filter_singleton,Multiset.map_cons,Multiset.map_singleton]
    exact Multiset.cons_swap _ _ _
  all_goals first
    | (intro i; fin_cases i <;> norm_num [degree,Fin.sum_univ_succ])
    | (simp only [lsObjective,degree,Fin.sum_univ_succ,Fin.sum_univ_zero]; audit_num)
    | audit_num




/-- Refutation of T5's AS-PRINTED information contrast: identical empirical
group margins force identical simple SSR, P016-E004 correction, p. 397. -/
theorem t5_printed_contrast_refuted :
    ¬ (∃ n : ℕ, ∃ u v : Outcome n, ∃ z w : Assignment n,
      2 ≤ n ∧ 0 < groupSize z false ∧ 0 < groupSize z true ∧
      sameMargins u z v w ∧ ks u z = ks v w ∧ rss u z ≠ rss v w) := by
  rintro ⟨n,u,v,z,w,hn,h0,h1,hm,_,hne⟩
  exact hne (t2_rss_margin_invariance hn u v z w h0 h1 hm)

/-- T10(b): least squares attains its minimum even for rank-deficient X, and
all minimizers have the same fitted vector, corrected (2), p. 399 (P016-E002). -/
theorem least_squares_attained {n k : ℕ} (u : Outcome n) (X : Fin n → Fin k → ℝ) :
    (∃ b, lsObjective u X b = lsRSS u X) ∧
    (∀ b c, lsObjective u X b = lsRSS u X → lsObjective u X c = lsRSS u X → fitted X b = fitted X c) := by
  classical
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin X
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.range L
  let U : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u
  have hsq : ∀ c : EuclideanSpace ℝ (Fin k),
      ‖U-L c‖^2 = lsObjective u X (WithLp.ofLp c) := by
    intro c
    have hL : L c = WithLp.toLp 2 (fun i => ∑ j, X i j*WithLp.ofLp c j) := rfl
    rw [hL,EuclideanSpace.real_norm_sq_eq]
    rfl
  obtain ⟨v,hv,hmin⟩ := K.exists_norm_eq_iInf_of_complete_subspace
    K.closed_of_finiteDimensional.isComplete U
  obtain ⟨b,rfl⟩ := hv
  have hbest : ∀ c : Fin k → ℝ, lsObjective u X (WithLp.ofLp b) ≤ lsObjective u X c := by
    intro c
    have hnorm : ‖U-L b‖ ≤ ‖U-L (WithLp.toLp 2 c)‖ := by
      have hbdd : BddBelow (Set.range (fun w : (K : Set (EuclideanSpace ℝ (Fin n))) => ‖U-w.val‖)) := by
        refine ⟨0,?_⟩
        rintro x ⟨w,rfl⟩
        exact norm_nonneg _
      have hle := ciInf_le hbdd (⟨L (WithLp.toLp 2 c),⟨WithLp.toLp 2 c,rfl⟩⟩ : (K : Set (EuclideanSpace ℝ (Fin n))))
      rw [← hmin] at hle
      exact hle
    have hsqb := hsq b
    have hsqc := hsq (WithLp.toLp 2 c)
    simp only [WithLp.ofLp_toLp] at hsqc
    nlinarith [norm_nonneg (U-L b),norm_nonneg (U-L (WithLp.toLp 2 c))]
  have hval := lsRSS_of_minimizer u X (WithLp.ofLp b) hbest
  refine ⟨⟨WithLp.ofLp b,hval.symm⟩,?_⟩
  intro b c hb hc
  have hlower : ∀ d : Fin k → ℝ, lsRSS u X ≤ lsObjective u X d := by
    intro d
    apply csInf_le
    · refine ⟨0,?_⟩
      rintro x ⟨e,rfl⟩
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    · exact ⟨d,rfl⟩
  let d : Fin k → ℝ := fun j => (b j+c j)/2
  have hfit : ∀ i, fitted X d i = (fitted X b i+fitted X c i)/2 := by
    intro i
    simp only [fitted,d,← mul_div_assoc,mul_add,← Finset.sum_div,Finset.sum_add_distrib]
  have hmid : lsObjective u X d = (lsObjective u X b+lsObjective u X c)/2 -
      (∑ i, (fitted X b i-fitted X c i)^2)/4 := by
    change (∑ i, (u i-fitted X d i)^2) = _
    simp_rw [hfit]
    have hpoint : ∀ i, (u i-(fitted X b i+fitted X c i)/2)^2 =
        ((u i-fitted X b i)^2+(u i-fitted X c i)^2)/2-(fitted X b i-fitted X c i)^2/4 := by
      intro i; ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_div,Finset.sum_add_distrib]
    rfl
  have hnonneg : 0 ≤ ∑ i, (fitted X b i-fitted X c i)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hzero : (∑ i, (fitted X b i-fitted X c i)^2) = 0 := by
    have hd := hlower d
    rw [hmid,hb,hc] at hd
    linarith
  funext i
  have heach := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (fitted X b i-fitted X c i))).mp hzero i (Finset.mem_univ _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp heach)

/-- T10(b): on the correction's outcome/assignment domain with both groups
nonempty, every real design matrix has an attained least-squares minimum and
all minimizers yield the same fitted vector, corrected (2), p. 399 (P016-E002). -/
theorem t10_general_least_squares {n k : ℕ} (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true)
    (X : Fin n → Fin k → ℝ) :
    (∃ b, lsObjective u X b = lsRSS u X) ∧
    (∀ b c, lsObjective u X b = lsRSS u X → lsObjective u X c = lsRSS u X → fitted X b = fitted X c) :=
  least_squares_attained u X

/-- T10(c): the sample maximum equals the real-threshold supremum, with ties;
KS is label-symmetric and in [0,1], corrected footnote 3, p. 396 (P016-E002). -/
theorem t10_ks_supremum {n : ℕ} (u : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) :
    ks u z = sSup (Set.range (fun t : ℝ => |ecdf u z true t - ecdf u z false t|)) ∧
    ks u z = ks u (fun i => !(z i)) ∧ 0 ≤ ks u z ∧ ks u z ≤ 1 := by
  have hlo : 0 ≤ ks u z := by
    rw [ks_threshold_sup]
    have hb : BddAbove (Set.range (fun t : ℝ => |ecdf u z true t-ecdf u z false t|)) :=
      ⟨ks u z,fun x ⟨t,ht⟩ => ht ▸ ks_threshold_bound u z t⟩
    exact (abs_nonneg _).trans (le_csSup hb ⟨0,rfl⟩)
  refine ⟨ks_threshold_sup u z,?_,hlo,?_⟩
  · rw [ks_threshold_sup,ks_threshold_sup]
    simp only [ecdf_swap_labels,Bool.not_true,Bool.not_false,abs_sub_comm]
  · apply fold_max_le _ _ (by norm_num)
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    have hg0 := ecdf_range u z false (u i) h0
    have hg1 := ecdf_range u z true (u i) h1
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- T10(d): for the undirected graph the column formulas in (2) are the row
formulas for numbers of treated neighbors and degree, p. 399 (P016-E002). -/
theorem t10_symmetric_network {n : ℕ} (S : Fin n → Fin n → ℝ)
    (hS : ∀ i j, S i j = S j i) (hbin : ∀ i j, S i j = 0 ∨ S i j = 1)
    (hdiag : ∀ i, S i i = 0) (z : Assignment n) (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (i : Fin n) :
    treatedNeighbors S z i = ∑ j, S i j*bit (z j) ∧ degree S i = ∑ j, S i j := by
  constructor <;> apply Finset.sum_congr rfl <;> intro j _
  · rw [hS j i,mul_comm]
  · exact hS j i

/-- Inclusive lower count among B reference values, simulations described on
p. 400; P016-E006/P016-E008 make the tail convention explicit. -/
noncomputable def lowerCount {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℕ :=
  ∑ b, if ref b ≤ obs then 1 else 0

/-- Inclusive upper count among B reference values, p. 400; P016-E006/P016-E008. -/
noncomputable def upperCount {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℕ :=
  ∑ b, if obs ≤ ref b then 1 else 0

/-- "min{1,2 min(L,U)/B}", simulation raw p value, P016-E008, p. 400. -/
noncomputable def rawP {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℝ :=
  doubledP ((lowerCount ref obs : ℝ)/B) ((upperCount ref obs : ℝ)/B)

/-- T4(e): inclusive lower and upper sampled tails sum to at least one,
P016-E006 corrected test specification, p. 400 (ties are counted in both). -/
theorem t4_tail_coverage {B : ℕ} (hB : 0 < B) (ref : Fin B → ℝ) (obs : ℝ) :
    (lowerCount ref obs : ℝ)/B + (upperCount ref obs : ℝ)/B ≥ 1 := by
  have h : B ≤ lowerCount ref obs + upperCount ref obs := by
    rw [lowerCount,upperCount,← Finset.sum_add_distrib]
    calc
      B = ∑ _ : Fin B, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ => by
        rcases le_total (ref b) obs with h | h <;> simp [h] <;> split_ifs <;> omega)
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hc : (B : ℝ) ≤ lowerCount ref obs + upperCount ref obs := by exact_mod_cast h
  rw [← add_div]
  exact (le_div_iff₀ hb).mpr (by simpa using hc)

/-- Inclusive counts for the bank 1,...,B, without expanding a thousand terms,
finite lemma for P016-E006 cutoff/tail witness, p. 400. -/
theorem consecutive_counts {B : ℕ} (k : Fin B) :
    lowerCount (fun b : Fin B => (b.val : ℝ)+1) ((k.val : ℝ)+1) = k.val+1 ∧
    upperCount (fun b : Fin B => (b.val : ℝ)+1) ((k.val : ℝ)+1) = B-k.val := by
  classical
  have hlo : ∀ b : Fin B, ((b.val : ℝ)+1 ≤ (k.val : ℝ)+1) ↔ b ≤ k := by
    intro b
    rw [Fin.le_def]
    exact (add_le_add_iff_right (1 : ℝ)).trans Nat.cast_le
  have hup : ∀ b : Fin B, ((k.val : ℝ)+1 ≤ (b.val : ℝ)+1) ↔ k ≤ b := by
    intro b
    rw [Fin.le_def]
    exact (add_le_add_iff_right (1 : ℝ)).trans Nat.cast_le
  constructor
  · simp only [lowerCount,hlo]
    rw [← Finset.card_filter]
    have hset : Finset.univ.filter (fun b : Fin B => b ≤ k) = Finset.Iic k := by ext b; simp
    rw [hset,Fin.card_Iic]
  · simp only [upperCount,hup]
    rw [← Finset.card_filter]
    have hset : Finset.univ.filter (fun b : Fin B => k ≤ b) = Finset.Ici k := by ext b; simp
    rw [hset,Fin.card_Ici]

/-- T3(iv): at the specified observed values in the 1000-point reference bank,
the code and printed cutoff differ and the two tail rules are incomparable;
P016-E006 witness, pp. 398, 400. -/
theorem t3_cutoff_witness :
    let ref : Fin 1000 → ℝ := fun b => (b.val : ℝ)+1
    (lowerCount ref 25 = 25 ∧ upperCount ref 25 = 976 ∧ rawP ref 25 = 1/20 ∧
      codedReject (rawP ref 25) ∧ ¬ printedReject (rawP ref 25)) ∧
    (lowerCount ref 40 = 40 ∧ rawP ref 40 = 2/25 ∧
      (lowerCount ref 40 : ℝ)/1000 ≤ 1/20 ∧ ¬ codedReject (rawP ref 40)) ∧
    (lowerCount ref 980 = 980 ∧ rawP ref 980 = 21/500 ∧
      ¬ (lowerCount ref 980 : ℝ)/1000 ≤ 1/20 ∧ codedReject (rawP ref 980)) := by
  dsimp
  have h25 := consecutive_counts (⟨24,by decide⟩ : Fin 1000)
  have h40 := consecutive_counts (⟨39,by decide⟩ : Fin 1000)
  have h980 := consecutive_counts (⟨979,by decide⟩ : Fin 1000)
  norm_num only at h25 h40 h980
  simp only [rawP,h25.1,h25.2,h40.1,h40.2,h980.1,h980.2]
  norm_num [doubledP,codedReject,printedReject]

/-- Expanding a finite Boolean assignment bank by its first bit; finite
calculation lemma for the six-unit P016-E006 witness, p. 400. -/
theorem sum_bool_fin_succ (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    (∑ b, f b) = ∑ a : Bool, ∑ t : Fin n → Bool, f (Fin.cons a t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

/-- Three-bit bank indices written as explicit binary vectors; finite
enumeration lemma for the matched-pair P016-E006 witness, p. 400. -/
theorem bool_cons_vec_three (a b c : Bool) (v : Fin 0 → Bool) :
    Fin.cons a (Fin.cons b (Fin.cons c v)) = ![a,b,c] := by
  funext i; fin_cases i <;> rfl

/-- T4(b): centering/scaling produces mean zero and sample variance one and
preserves OLS SSR with intercept and own treatment, P016-E006 correction, p. 400. -/
theorem t4_standardization {n : ℕ} (hn : 2 ≤ n) (h u : Outcome n) (z : Assignment n)
    (hs : 0 < sampleSD h) :
    (∑ i, standardize h i) = 0 ∧ (∑ i, (standardize h i)^2)/((n : ℝ)-1) = 1 ∧
    lsRSS u (applicationX z (standardize h)) = lsRSS u (applicationX z h) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by
    have hcast : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hs0 : sampleSD h ≠ 0 := ne_of_gt hs
  have hmean : (n : ℝ)*pooledMean h = ∑ i, h i := by unfold pooledMean; field_simp
  have hc : (∑ i, (h i-pooledMean h)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [hmean]
    ring
  have hvar : 0 ≤ sampleVariance h :=
    div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hn1.le
  have hs2 : (sampleSD h)^2 = sampleVariance h := Real.sq_sqrt hvar
  refine ⟨?_,?_,?_⟩
  · unfold standardize
    rw [← Finset.sum_div,hc]
    simp
  · simp only [standardize,div_pow,← Finset.sum_div]
    have hsumsq : (∑ i, (h i-pooledMean h)^2) = ((n : ℝ)-1)*(sampleSD h)^2 := by
      unfold sampleVariance at hs2
      exact ((eq_div_iff (ne_of_gt hn1)).mp hs2).symm.trans (by ring)
    rw [hsumsq]
    field_simp [hs0,ne_of_gt hn1]
  · have hf : ∀ c : Fin 3 → ℝ, lsObjective u (applicationX z (standardize h)) c =
        lsObjective u (applicationX z h)
          ![c 0-c 2*pooledMean h/sampleSD h,c 1,c 2/sampleSD h] := by
      intro c
      unfold lsObjective applicationX
      apply Finset.sum_congr rfl
      intro i _
      simp only [standardize,Fin.sum_univ_succ,Fin.sum_univ_zero]
      simp
      field_simp [hs0]
      <;> ring
    have hb : ∀ c : Fin 3 → ℝ, lsObjective u (applicationX z h) c =
        lsObjective u (applicationX z (standardize h))
          ![c 0+c 2*pooledMean h,c 1,c 2*sampleSD h] := by
      intro c
      unfold lsObjective applicationX
      apply Finset.sum_congr rfl
      intro i _
      simp only [standardize,Fin.sum_univ_succ,Fin.sum_univ_zero]
      simp
      field_simp [hs0]
      <;> ring
    unfold lsRSS
    congr 1
    ext v
    constructor
    · rintro ⟨c,rfl⟩
      exact ⟨_,(hf c).symm⟩
    · rintro ⟨c,rfl⟩
      exact ⟨_,(hb c).symm⟩

/-- T3(ii): the full six-unit centered-similarity witness, including its
three exact least-squares minima, P016-E006 correction, p. 400. -/
theorem t3_six_unit_exposure :
    let S := similarity (fun k => some (scores6 k))
    let z : Assignment 6 := ![true,false,true,false,true,false]
    let h := centeredExposure S matchedBank6 z
    let x := exposureSum S z
    let y : Outcome 6 := ![0,1,0,1,1,0]
    (∀ i j : Fin 6, S i j =
      (!![0,7,6,4,3,0; 7,0,7,5,4,1; 6,7,0,6,5,2;
        4,5,6,0,7,4; 3,4,5,7,0,5; 0,1,2,4,5,0] : Matrix (Fin 6) (Fin 6) ℝ) i j/8) ∧
    (∀ i, x i = (![9/8,9/4,11/8,17/8,1,7/8] : Outcome 6) i ∧
      conditionalMean S matchedBank6 i (z i) = (![13/16,31/16,5/4,2,19/16,17/16] : Outcome 6) i ∧
      h i = (![5/16,5/16,1/8,1/8,-3/16,-3/16] : Outcome 6) i ∧
      degree S i = (![5/2,3,13/4,13/4,3,3/2] : Outcome 6) i) ∧
    pooledMean h = 1/12 ∧ sampleVariance h = 49/960 ∧
    (∀ i, standardize h i = Real.sqrt 15/42 * (![11,11,2,2,-13,-13] : Outcome 6) i) ∧
    (¬ ∃ A C : ℝ, ∀ i, h i = A+C*x i) ∧
    (¬ ∃ A B C : ℝ, ∀ i, h i = A+B*bit (z i)+C*x i) ∧
    lsRSS y (applicationX z h) = 4/3 ∧ lsRSS y (applicationX z (standardize h)) = 4/3 ∧
    lsRSS y (applicationX z x) = 655/708 ∧
    lsRSS y (fun i => (![1,bit (z i),x i,degree S i] : Fin 4 → ℝ)) = 515/859 := by
  classical
  let S := similarity (fun k => some (scores6 k))
  let z : Assignment 6 := ![true,false,true,false,true,false]
  let h := centeredExposure S matchedBank6 z
  let x := exposureSum S z
  let y : Outcome 6 := ![0,1,0,1,1,0]
  have hmatrix : ∀ i j : Fin 6, S i j =
      (!![0,7,6,4,3,0; 7,0,7,5,4,1; 6,7,0,6,5,2;
        4,5,6,0,7,4; 3,4,5,7,0,5; 0,1,2,4,5,0] : Matrix (Fin 6) (Fin 6) ℝ) i j/8 := by
    intro i j; fin_cases i <;> fin_cases j <;> norm_num [S,similarity,scores6]
  have hvals : ∀ i, x i = (![9/8,9/4,11/8,17/8,1,7/8] : Outcome 6) i ∧
      conditionalMean S matchedBank6 i (z i) = (![13/16,31/16,5/4,2,19/16,17/16] : Outcome 6) i ∧
      h i = (![5/16,5/16,1/8,1/8,-3/16,-3/16] : Outcome 6) i ∧
      degree S i = (![5/2,3,13/4,13/4,3,3/2] : Outcome 6) i := by
    intro i; fin_cases i <;>
      simp only [x,h,z,centeredExposure,conditionalMean,sum_bool_fin_succ,
        Fintype.sum_bool,bool_cons_vec_three,matchedBank6,Fin.cons_zero,Fin.cons_succ,
        exposureSum,degree,hmatrix,Fin.sum_univ_succ,Fin.sum_univ_zero] <;>
      norm_num [bit]
  have hh : h = ![5/16,5/16,1/8,1/8,-3/16,-3/16] := by
    funext i; exact (hvals i).2.2.1
  have hx : x = ![9/8,9/4,11/8,17/8,1,7/8] := by
    funext i; exact (hvals i).1
  have hd : degree S = ![5/2,3,13/4,13/4,3,3/2] := by
    funext i; exact (hvals i).2.2.2
  have hmean : pooledMean h = 1/12 := by norm_num [hh,pooledMean,Fin.sum_univ_succ]
  have hvar : sampleVariance h = 49/960 := by
    rw [sampleVariance,hmean,hh]
    norm_num [Fin.sum_univ_succ]
  have hsd : sampleSD h = 7/(8*Real.sqrt 15) := by
    unfold sampleSD
    rw [hvar]
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
    have h15 : Real.sqrt 15 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [h15]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  have he : ∀ i, standardize h i = Real.sqrt 15/42 * (![11,11,2,2,-13,-13] : Outcome 6) i := by
    intro i
    rw [standardize,hmean,hsd,hh]
    fin_cases i <;> norm_num <;> field_simp <;> ring
  have hn : ¬ ∃ A B C : ℝ, ∀ i, h i = A+B*bit (z i)+C*x i := by
    rintro ⟨A,B,C,hfit⟩
    have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2; have h3 := hfit 3
    norm_num [hh,hx,z,bit] at h0 h1 h2 h3
    linarith
  have hc : lsRSS y (applicationX z h) = 4/3 := by
    have hcert := lsRSS_of_square_certificate y (applicationX z h) (![2/3,-1/3,0] : Fin 3 → ℝ) (by
      intro c
      simp only [lsObjective,fitted,applicationX,hh,y,z,Fin.sum_univ_succ,Fin.sum_univ_zero]
      norm_num [bit]
      ring)
    rw [hcert]
    norm_num [lsObjective,applicationX,hh,y,z,bit,Fin.sum_univ_succ]
  have hraw : lsRSS y (applicationX z x) = 655/708 := by
    have hcert := lsRSS_of_square_certificate y (applicationX z x) (![-121/354,1/354,34/59] : Fin 3 → ℝ) (by
      intro c
      simp only [lsObjective,fitted,applicationX,hx,y,z,Fin.sum_univ_succ,Fin.sum_univ_zero]
      norm_num [bit]
      ring)
    rw [hcert]
    norm_num [lsObjective,applicationX,hx,y,z,bit,Fin.sum_univ_succ]
  have hdeg : lsRSS y (fun i => (![1,bit (z i),x i,degree S i] : Fin 4 → ℝ)) = 515/859 := by
    have hcert := lsRSS_of_square_certificate y (fun i => (![1,bit (z i),x i,degree S i] : Fin 4 → ℝ))
        (![-1437/1718,-919/859,-576/859,890/859] : Fin 4 → ℝ) (by
      intro c
      simp only [lsObjective,fitted,hx,hd,y,z,Fin.sum_univ_succ,Fin.sum_univ_zero]
      norm_num [bit]
      ring)
    rw [hcert]
    norm_num [lsObjective,hx,hd,y,z,bit,Fin.sum_univ_succ]
  refine ⟨hmatrix,hvals,hmean,hvar,he,?_,hn,hc,?_,hraw,hdeg⟩
  · rintro ⟨A,C,hfit⟩; exact hn ⟨A,0,C,by simpa using hfit⟩
  · rw [(t4_standardization (by decide : 2 ≤ 6) h y z (by rw [hsd]; positivity)).2.2]
    exact hc

/-- T4(d): the complete four-unit bank has positive exposure SD and even the
standardized coded exposure cannot be absorbed into an intercept, own-treatment
coefficient and raw similarity sum, P016-E006 corrected model, p. 400. -/
theorem t4_centering_not_rescaling :
    let S := similarity (fun k => some (scores4 k))
    let h := centeredExposure S matchedBank4 (complete4 1)
    0 < sampleSD h ∧
    (¬ ∃ A B C : ℝ, ∀ i, h i = A+B*bit (complete4 1 i)+C*exposureSum S (complete4 1) i) ∧
    (¬ ∃ A B C : ℝ, ∀ i, standardize h i = A+B*bit (complete4 1 i)+C*exposureSum S (complete4 1) i) := by
  let S := similarity (fun k => some (scores4 k))
  let h := centeredExposure S matchedBank4 (complete4 1)
  have hh : h = ![1/8,1/8,-1/8,-1/8] := by
    funext i
    exact (t3_four_unit_exposure.2.2.1 i).2.2
  have hx : ∀ i, exposureSum S (complete4 1) i = (![1/4,5/4,1/4,3/4] : Outcome 4) i :=
    fun i => (t3_four_unit_exposure.2.2.1 i).1
  have hs : 0 < sampleSD h := by
    rw [hh]
    apply Real.sqrt_pos.mpr
    norm_num [sampleVariance,pooledMean,Fin.sum_univ_succ]
  have hnot : ¬ ∃ A B C : ℝ, ∀ i, h i = A+B*bit (complete4 1 i)+C*exposureSum S (complete4 1) i := by
    rw [hh]
    simp only [hx]
    exact t3_four_unit_exposure.2.2.2.1
  change 0 < sampleSD h ∧ _ ∧ _
  refine ⟨hs,hnot,?_⟩
  rintro ⟨A,B,C,hfit⟩
  apply hnot
  refine ⟨pooledMean h+sampleSD h*A,sampleSD h*B,sampleSD h*C,?_⟩
  intro i
  have hi := hfit i
  change (h i-pooledMean h)/sampleSD h = _ at hi
  have heq := (div_eq_iff (ne_of_gt hs)).mp hi
  nlinarith [heq]

/-- T4(c): similarity sums equal m−z_i−half the distance sums; with the SAME
fixed-size bank conditional centering cancels the first two terms and the
standardized exposures differ in sign, P016-E006 corrected model, p. 400. -/
theorem t4_similarity_orientation {n N : ℕ} (hn : 2 ≤ n) (s : Outcome n)
    (bank : Fin N → Assignment n) (hbank : ∀ i a, ∃ b, bank b i = a)
    (z : Assignment n) (m : ℕ) (hz : groupSize z true = m)
    (hm : ∀ b, groupSize (bank b) true = m) :
    let S := similarity (fun i => some (s i))
    let D := distance s
    (∀ i, exposureSum S z i = (m : ℝ)-bit (z i)-(1/2)*exposureSum D z i) ∧
    (∀ i, centeredExposure S bank z i = -(1/2)*centeredExposure D bank z i) ∧
    (0 < sampleSD (centeredExposure D bank z) →
      codedExposure S bank z = fun i => -codedExposure D bank z i) := by
  classical
  let S := similarity (fun i => some (s i))
  let D := distance s
  have hraw : ∀ v : Assignment n, groupSize v true = m → ∀ i,
      exposureSum S v i = (m : ℝ)-bit (v i)-(1/2)*exposureSum D v i := by
    intro v hv i
    have hbits : (∑ j, bit (v j)) = (m : ℝ) := by
      rw [← hv]
      simp only [groupSize,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      apply Finset.sum_congr rfl
      intro j _
      cases v j <;> simp [bit]
    have heq : ∀ j, S i j * bit (v j) =
        bit (v j)-(if j = i then bit (v i) else 0)-(1/2)*(D i j*bit (v j)) := by
      intro j
      by_cases hji : j = i
      · subst j; simp [S,D,similarity,distance]
      · simp [S,D,similarity,distance,hji,Ne.symm hji]
        ring
    unfold exposureSum
    simp_rw [heq]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.mul_sum,hbits]
  have hcond : ∀ i a, conditionalMean S bank i a =
      (m : ℝ)-bit a-(1/2)*conditionalMean D bank i a := by
    intro i a
    let den : ℝ := ∑ b, if bank b i = a then (1 : ℝ) else 0
    have hden : 0 < den := by
      obtain ⟨b,hb⟩ := hbank i a
      apply Finset.sum_pos'
      · intro b _; split_ifs <;> norm_num
      · exact ⟨b,Finset.mem_univ _,by simp [hb]⟩
    have hnum : (∑ b, if bank b i = a then exposureSum S (bank b) i else 0) =
        ((m : ℝ)-bit a)*den-(1/2)*(∑ b, if bank b i = a then exposureSum D (bank b) i else 0) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : bank b i = a
      · rw [if_pos hb,if_pos hb,if_pos hb,hraw (bank b) (hm b) i,hb]
        ring
      · simp [hb]
    change _/den = (m : ℝ)-bit a-(1/2)*(_/den)
    rw [hnum]
    field_simp [ne_of_gt hden]
  have hcenter : ∀ i, centeredExposure S bank z i = -(1/2)*centeredExposure D bank z i := by
    intro i
    simp only [centeredExposure,hraw z hz i,hcond]
    cases z i <;> simp [bit] <;> ring
  refine ⟨hraw z hz,hcenter,?_⟩
  intro hs
  let h := centeredExposure D bank z
  have hmean : pooledMean (centeredExposure S bank z) = -(1/2)*pooledMean h := by
    simp only [pooledMean,hcenter,← Finset.mul_sum,h]
    ring
  have hvar : sampleVariance (centeredExposure S bank z) = (1/4)*sampleVariance h := by
    simp only [sampleVariance,hcenter,hmean]
    have heq : ∀ i, (-(1/2)*h i-(-(1/2)*pooledMean h))^2 = (1/4)*(h i-pooledMean h)^2 := by
      intro i; ring
    change (∑ i, (-(1/2)*h i-(-(1/2)*pooledMean h))^2)/_ = _
    simp_rw [heq]
    rw [← Finset.mul_sum]
    ring
  have hsd : sampleSD (centeredExposure S bank z) = (1/2)*sampleSD h := by
    unfold sampleSD
    rw [hvar,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
    have hquarter : Real.sqrt (1/4 : ℝ) = 1/2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
      norm_num
    rw [hquarter]
  funext i
  change (centeredExposure S bank z i-pooledMean (centeredExposure S bank z))/
      sampleSD (centeredExposure S bank z) = -((h i-pooledMean h)/sampleSD h)
  rw [hcenter,hmean,hsd]
  dsimp only [h]
  field_simp [ne_of_gt hs] <;> ring

/-- "effect increasing": for EVERY fixed binary assignment, raising treated
and lowering control outcomes cannot decrease the statistic, P016-E005 correction,
p. 397. The paper itself does not define this directional property. -/
def EffectIncreasing {n : ℕ} (T : Outcome n → Assignment n → ℝ) : Prop :=
  ∀ z y y', (∀ i, if z i then y i ≤ y' i else y' i ≤ y i) → T y z ≤ T y' z

/-- The same directional condition on the domain of assignments with both
groups nonempty; the domain needed by the difference in means in T12(i). -/
def EffectIncreasingOnGroups {n : ℕ} (T : Outcome n → Assignment n → ℝ) : Prop :=
  ∀ z, 0 < groupSize z false → 0 < groupSize z true → ∀ y y',
    (∀ i, if z i then y i ≤ y' i else y' i ≤ y i) → T y z ≤ T y' z

/-- T12(i): the directional difference of group means IS effect increasing,
P016-E005 corrected explanatory text, p. 397. -/
theorem t12_mean_effect_increasing {n : ℕ} : EffectIncreasingOnGroups (meanDifference (n := n)) := by
  intro z h0 h1 y y' h
  have ht : groupSum y z true ≤ groupSum y' z true := by
    unfold groupSum
    apply Finset.sum_le_sum
    intro i _
    cases hz : z i <;> simp [hz] <;> simpa [hz] using h i
  have hc : groupSum y' z false ≤ groupSum y z false := by
    unfold groupSum
    apply Finset.sum_le_sum
    intro i _
    cases hz : z i <;> simp [hz] <;> simpa [hz] using h i
  unfold meanDifference groupMean
  exact sub_le_sub (div_le_div_of_nonneg_right ht (by positivity))
    (div_le_div_of_nonneg_right hc (by positivity))

/-- T12(ii): the recommended divergence property does not imply directional
effect increasing: neither two-sided nor printed signed KS satisfies it;
P016-E005 corrected explanation, p. 397, using the T11(i) witness. -/
theorem t12_ks_not_effect_increasing :
    ¬ EffectIncreasing (ks (n := 4)) ∧ ¬ EffectIncreasing (signedKS (n := 4)) := by
  constructor <;> intro h
  all_goals
    have h0 : 0 < groupSize (complete4 0) false := by audit_num
    have h1 : 0 < groupSize (complete4 0) true := by audit_num
    have hi := h (complete4 0) u4 ![2,3,2,3] t11_ks_witness.1
    first
    | rw [t11_ks_witness.2.1,t11_ks_witness.2.2.1] at hi
      norm_num at hi
    | rw [t11_ks_witness.2.2.2.1,t11_ks_witness.2.2.2.2.1] at hi
      norm_num at hi

/-- T8(b): observed and reference statistics have the same law under a true
additive hypothesis, and the exact inclusive upper p value is valid; P016-E001
corrected step (4), p. 396, for every statistic and every finite design. -/
theorem t8_corrected_comparison {n : ℕ} {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (assign : Ω → Assignment n) (y0 : Outcome n) (t : ℝ)
    (T : Outcome n → Ω → ℝ) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (∀ E : ℝ → Prop,
      mass P (fun ω => E (T (additiveAdjust (additiveGenerate y0 (assign ω) t) (assign ω) t) ω)) =
      mass P (fun ω => E (T y0 ω))) ∧
    mass P (fun ω => upperP P (fun w => T
      (additiveAdjust (additiveGenerate y0 (assign ω) t) (assign ω) t) w) ω ≤ α) ≤ α := by
  have hm : ∀ ω, additiveAdjust (additiveGenerate y0 (assign ω) t) (assign ω) t = y0 :=
    fun ω => (t8_additive_mapping y0 (assign ω) t t).2
  constructor
  · intro E; simp only [hm]
  · simpa only [hm] using upper_tail_bound P (fun w => T y0 w) α hα

/-- Equality of outcomes within one group suffices for equality of its mean,
corrections P016-E001/P016-E011/P016-N002, pp. 396–398. -/
theorem group_mean_congr {n : ℕ} (u v : Outcome n) (z : Assignment n) (g : Bool)
    (h : ∀ i, z i = g → u i = v i) : groupMean u z g = groupMean v z g := by
  classical
  unfold groupMean
  congr 1
  unfold groupSum
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z i = g
  · simp [hi,h i hi]
  · simp [hi]

/-- Adding a constant shifts a nonempty group's mean by that constant,
finite lemma for corrected P016-E001/P016-N002/P016-N003, pp. 396–398. -/
theorem group_mean_shift {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool)
    (hg : 0 < groupSize z g) (c : ℝ) : groupMean (fun i => u i+c) z g = groupMean u z g+c := by
  classical
  have hcard : (groupSize z g : ℝ) = ∑ i, if z i = g then (1 : ℝ) else 0 := by
    simp [groupSize]
  have hsum : groupSum (fun i => u i+c) z g = groupSum u z g + (groupSize z g : ℝ)*c := by
    rw [hcard]
    unfold groupSum
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hn : (groupSize z g : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hg)
  unfold groupMean
  rw [hsum]
  field_simp

/-- Scaling all group outcomes scales its mean, P016-N003 mean reductions, p. 398. -/
theorem group_mean_scale {n : ℕ} (u : Outcome n) (z : Assignment n) (g : Bool) (c : ℝ) :
    groupMean (fun i => c*u i) z g = c*groupMean u z g := by
  classical
  unfold groupMean groupSum
  rw [← mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- Each group mean under the additive adjustment, P016-E001/P016-N002, pp. 396–397. -/
theorem additive_group_means {n : ℕ} (Y : Outcome n) (z : Assignment n)
    (h1 : 0 < groupSize z true) (t : ℝ) :
    groupMean (additiveAdjust Y z t) z false = groupMean Y z false ∧
    groupMean (additiveAdjust Y z t) z true = groupMean Y z true-t := by
  constructor
  · apply group_mean_congr
    intro i hi
    simp [additiveAdjust,hi,bit]
  · calc
      _ = groupMean (fun i => Y i+(-t)) z true := by
        apply group_mean_congr
        intro i hi
        simp [additiveAdjust,hi,bit,sub_eq_add_neg]
      _ = _ := by simpa [sub_eq_add_neg] using group_mean_shift Y z true h1 (-t)

/-- T8(c): the raw difference of means retains exactly the hypothesized
additive shift and coincides with the adjusted difference iff that shift is zero,
P016-E001 correction of step (4), p. 396. -/
theorem t8_raw_mean_shift {n : ℕ} (Y : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (t : ℝ) :
    meanDifference Y z = meanDifference (additiveAdjust Y z t) z + t ∧
    (meanDifference Y z = meanDifference (additiveAdjust Y z t) z ↔ t = 0) := by
  have h := additive_group_means Y z h1 t
  unfold meanDifference
  rw [h.1,h.2]
  constructor
  · ring
  · constructor <;> intro ht <;> linarith

/-- T17: both means in the intended comparison are of uniformity outcomes;
the imputed-treated reading of the undefined printed symbol instead yields
the raw contrast, independent of tau, p. 397 (P016-N002 correction). -/
theorem t17_adjusted_comparison {n : ℕ} (Y : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (t : ℝ) :
    let u := additiveAdjust Y z t
    (∀ i, z i = true → u i+t = Y i) ∧
    groupMean (fun i => u i+t) z true - groupMean u z false = meanDifference u z+t ∧
    groupMean (fun i => u i+t) z true - groupMean u z false = meanDifference Y z := by
  dsimp
  refine ⟨?_,?_,?_⟩
  · intro i hi
    simp [additiveAdjust,hi,bit]
  · rw [group_mean_shift _ z true h1 t]
    unfold meanDifference
    ring
  · rw [group_mean_shift _ z true h1 t]
    have h := (t8_raw_mean_shift Y z h0 h1 t).1
    unfold meanDifference at h ⊢
    linarith

/-- T17 exact instance: the corrected contrast is 2 and the printed-imputation
contrast is 12, P016-N002 correction witness, p. 397. -/
theorem t17_comparison_witness :
    meanDifference u4 (complete4 5) = 2 ∧
    groupMean (fun i => u4 i+10) (complete4 5) true - groupMean u4 (complete4 5) false = 12 := by audit_num

/-- All assignments with exactly m treated units, the complete randomization
design of §§2–2.2, pp. 397, 399. -/
abbrev Balanced (n m : ℕ) := {z : Assignment n // groupSize z true = m}

/-- Complete randomization is equivalently a subset of exactly m treated
units, pp. 397, 399; structural counting certificate for T7/T13/T21. -/
noncomputable def balancedSetEquiv (n m : ℕ) : Balanced n m ≃ {s : Finset (Fin n) // s.card = m} := by
  classical
  have hcount : ∀ z : Assignment n,
      (Finset.univ.filter (fun i => z i = true)).card = groupSize z true := by
    intro z
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rfl
  refine {
    toFun := fun z => ⟨Finset.univ.filter (fun i => z.val i = true), (hcount z.val).trans z.property⟩
    invFun := fun t => ⟨fun i => decide (i ∈ t.val), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [← hcount]
    have hf : (Finset.univ.filter (fun i : Fin n => decide (i ∈ t.val) = true)) = t.val := by
      ext i
      simp
    simpa [hf] using t.property
  · intro z
    apply Subtype.ext
    funext i
    simp
  · intro t
    apply Subtype.ext
    ext i
    simp

/-- The complete n-unit, m-treated assignment support has choose(n,m) points,
p. 397 and P016-E008. -/
theorem balanced_card (n m : ℕ) : Fintype.card (Balanced n m) = Nat.choose n m := by
  rw [Fintype.card_congr (balancedSetEquiv n m),Fintype.card_finset_len]
  simp

/-- Natural binary subset-sum code of a treatment assignment, a parity
certificate for the P016-E008 power-of-two population. -/
def binaryCode {n : ℕ} (z : Assignment n) : ℕ := ∑ i, if z i then 2^i.val else 0

/-- Splitting off the least significant treatment bit, finite certificate
for P016-E008 subset-sum uniqueness. -/
theorem binaryCode_succ {n : ℕ} (z : Assignment (n+1)) :
    binaryCode z = (if z 0 then 1 else 0) + 2*binaryCode (fun i => z i.succ) := by
  simp only [binaryCode, Fin.sum_univ_succ, Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hzi : z i.succ = true <;> simp [hzi,mul_comm]

/-- Binary subset sums uniquely identify the assignment, P016-E008; proved by parity and induction, without enumeration. -/
theorem binaryCode_injective (n : ℕ) : Function.Injective (binaryCode (n := n)) := by
  induction n with
  | zero => intro z w _; funext i; exact Fin.elim0 i
  | succ n ih =>
    intro z w h
    rw [binaryCode_succ,binaryCode_succ] at h
    have hhead : z 0 = w 0 := by
      cases hz : z 0 <;> cases hw : w 0 <;> simp_all <;> omega
    have htail : binaryCode (fun i => z i.succ) = binaryCode (fun i => w i.succ) := by
      rw [hhead] at h
      omega
    have heq := ih htail
    funext i
    refine Fin.cases hhead (fun j => congrFun heq j) i

/-- Real treated-outcome sum for y_i=2^i, the P016-E008 exact witness population. -/
noncomputable def binarySum {n : ℕ} (z : Assignment n) : ℝ := ∑ i, if z i then (2:ℝ)^i.val else 0

/-- The real power-of-two sum is the cast of its natural binary code,
P016-E008 finite witness certificate. -/
theorem binarySum_cast {n : ℕ} (z : Assignment n) : binarySum z = (binaryCode z : ℝ) := by
  simp only [binarySum,binaryCode,Nat.cast_sum,Nat.cast_ite,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero]

/-- The treated sum of the P016-E008 power-of-two population identifies each
assignment. -/
theorem binarySum_injective (n : ℕ) : Function.Injective (binarySum (n := n)) := by
  intro z w h
  rw [binarySum_cast,binarySum_cast] at h
  exact binaryCode_injective n (Nat.cast_injective h)

/-- A complementary assignment has treated sum 65535 minus the original
sum, P016-E008 16-unit witness. -/
theorem binarySum_complement (z : Assignment 16) :
    binarySum (fun i => !(z i)) = 65535-binarySum z := by
  have h : binarySum z + binarySum (fun i => !(z i)) = ∑ i : Fin 16, (2:ℝ)^i.val := by
    rw [binarySum,binarySum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases z i <;> simp
  have hs : (∑ i : Fin 16, (2:ℝ)^i.val) = 65535 := by norm_num [Fin.sum_univ_succ]
  rw [hs] at h
  linarith

/-- The polynomial Q-(s^2+(S-s)^2)/8 of the 16-unit P016-E008 witness. This is a
certificate expression; t13_rss_identity connects it to the actual SSR. -/
noncomputable def powerTwoRSSExpression (z : Assignment 16) : ℝ :=
  1431655765-((binarySum z)^2+(65535-binarySum z)^2)/8

/-- Equality of the P016-E008 SSR polynomial occurs exactly on an assignment
and its complement. -/
theorem powerTwoRSSExpression_equal (z w : Assignment 16) : powerTwoRSSExpression z = powerTwoRSSExpression w ↔
    z = w ∨ z = fun i => !(w i) := by
  constructor
  · intro h
    have hf : (binarySum z-binarySum w)*(binarySum z+binarySum w-65535) = 0 := by
      dsimp [powerTwoRSSExpression] at h
      nlinarith
    rcases mul_eq_zero.mp hf with hzw | hzw
    · exact Or.inl (binarySum_injective 16 (sub_eq_zero.mp hzw))
    · apply Or.inr
      apply binarySum_injective 16
      rw [binarySum_complement]
      linarith
  · rintro (rfl | rfl)
    · rfl
    · rw [powerTwoRSSExpression,powerTwoRSSExpression,binarySum_complement]
      ring

/-- An abstract finite statistic with exactly two points in every fiber
has half as many values as input points; P016-E008 finite counting certificate. -/
theorem two_fiber_image_card {Ω : Type} [Fintype Ω] (f : Ω → ℝ)
    (hfiber : ∀ x, (Finset.univ.filter (fun y => f y = f x)).card = 2) :
    Fintype.card Ω = 2*(Finset.univ.image f).card := by
  classical
  have hcount := Finset.card_eq_sum_card_image f Finset.univ
  have hs : (∑ r ∈ Finset.univ.image f, (Finset.univ.filter (fun x => f x = r)).card) =
      (Finset.univ.image f).card * 2 := by
    calc
      _ = ∑ r ∈ Finset.univ.image f, 2 := by
        apply Finset.sum_congr rfl
        intro r hr
        obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hr
        exact hfiber x
      _ = _ := by simp
  simpa only [hs,Finset.card_univ,Nat.mul_comm] using hcount

/-- The P016-E008 SSR polynomial has exactly 6435 distinct values on the
16-unit, eight-treated support, each on a complementary pair. -/
theorem powerTwoRSSExpression_card :
    (Finset.univ.image (fun z : Balanced 16 8 => powerTwoRSSExpression z.val)).card = 6435 := by
  classical
  have hcomp : ∀ z : Balanced 16 8, groupSize (fun i => !(z.val i)) true = 8 := by
    intro z
    have hs : groupSize z.val true + groupSize z.val false = 16 := by
      rw [groupSize,groupSize,← Finset.sum_add_distrib]
      have h : (fun i => (if z.val i = true then 1 else 0) + (if z.val i = false then 1 else 0)) =
          (fun _ : Fin 16 => 1) := by funext i; cases z.val i <;> simp
      rw [h]
      simp
    have hnot : groupSize (fun i => !(z.val i)) true = groupSize z.val false := by
      unfold groupSize
      apply Finset.sum_congr rfl
      intro i _
      cases hzi : z.val i <;> simp [hzi]
    rw [hnot]
    omega
  let comp (z : Balanced 16 8) : Balanced 16 8 := ⟨fun i => !(z.val i),hcomp z⟩
  have hne : ∀ z : Balanced 16 8, z ≠ comp z := by
    intro z heq
    have hi := congrFun (congrArg Subtype.val heq) (0 : Fin 16)
    change z.val 0 = !(z.val 0) at hi
    cases hb : z.val 0 <;> simp [hb] at hi
  have hfiber : ∀ z : Balanced 16 8,
      (Finset.univ.filter (fun w : Balanced 16 8 => powerTwoRSSExpression w.val = powerTwoRSSExpression z.val)).card = 2 := by
    intro z
    have hf : (Finset.univ.filter (fun w : Balanced 16 8 => powerTwoRSSExpression w.val = powerTwoRSSExpression z.val)) =
        {z, comp z} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, powerTwoRSSExpression_equal,
        Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
    rw [hf,Finset.card_pair (hne z)]
  have hcount := two_fiber_image_card (fun z : Balanced 16 8 => powerTwoRSSExpression z.val) hfiber
  rw [balanced_card] at hcount
  have hchoose : Nat.choose 16 8 = 12870 := by decide
  rw [hchoose] at hcount
  omega

/-- Uniform finite-design probability written as event cardinality divided by
support cardinality, pp. 397, 399. Uses below have explicitly nonempty support. -/
noncomputable def uniformMass (Ω : Type) [Fintype Ω] (E : Ω → Prop) : ℝ := by
  classical
  exact (∑ ω, if E ω then (1 : ℝ) else 0) / Fintype.card Ω

/-- Uniform design expectation for complete randomization, p. 397 and P016-N003. -/
noncomputable def uniformExpectation (Ω : Type) [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω


/-- T9(iii): including the conventional intercept changes the minimum from
2 to 0 in the exact six-unit one-edge witness, P016-E002, equation (2), p. 399. -/
theorem t9_intercept_witness :
    let S : Fin 6 → Fin 6 → ℝ := fun i j => if (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) then 1 else 0
    let z : Assignment 6 := ![true,false,true,false,true,false]
    let u : Outcome 6 := fun _ => 1
    let X := networkX S z
    let W := fun i : Fin 6 => (![bit (z i),treatedNeighbors S z i,degree S i] : Fin 3 → ℝ)
    (∀ i j, X i j = (!![1,1,0,1; 1,0,1,1; 1,1,0,0; 1,0,0,0; 1,1,0,0; 1,0,0,0] :
      Matrix (Fin 6) (Fin 4) ℝ) i j) ∧
    lsObjective u X ![1,0,0,0] = 0 ∧ lsRSS u X = 0 ∧
    lsObjective u W ![1,1,0] = 2 ∧ lsRSS u W = 2 := by
  let S : Fin 6 → Fin 6 → ℝ := fun i j => if (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) then 1 else 0
  let z : Assignment 6 := ![true,false,true,false,true,false]
  let u : Outcome 6 := fun _ => 1
  let X := networkX S z
  let W := fun i : Fin 6 => (![bit (z i),treatedNeighbors S z i,degree S i] : Fin 3 → ℝ)
  have hc0 : ∀ c : Fin 4 → ℝ, lsObjective u X c = lsObjective u X ![1,0,0,0] +
      ∑ i, (fitted X c i-fitted X ![1,0,0,0] i)^2 := by
    intro c
    simp [lsObjective,fitted,X,networkX,degree,treatedNeighbors,S,z,u,bit,Fin.sum_univ_succ]
    ring
  have hc1 : ∀ c : Fin 3 → ℝ, lsObjective u W c = lsObjective u W ![1,1,0] +
      ∑ i, (fitted W c i-fitted W ![1,1,0] i)^2 := by
    intro c
    simp [lsObjective,fitted,W,degree,treatedNeighbors,S,z,u,bit,Fin.sum_univ_succ]
    ring
  change (∀ i j, X i j = (!![1,1,0,1; 1,0,1,1; 1,1,0,0; 1,0,0,0; 1,1,0,0; 1,0,0,0] :
    Matrix (Fin 6) (Fin 4) ℝ) i j) ∧ lsObjective u X ![1,0,0,0] = 0 ∧ lsRSS u X = 0 ∧
    lsObjective u W ![1,1,0] = 2 ∧ lsRSS u W = 2
  rw [lsRSS_of_square_certificate u X _ hc0,lsRSS_of_square_certificate u W _ hc1]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [X,networkX,degree,treatedNeighbors,S,z,u,bit,Fin.sum_univ_succ]
  all_goals norm_num [lsObjective,X,W,networkX,degree,treatedNeighbors,S,z,u,bit,Fin.sum_univ_succ]

/-- Joint statistic vector (T0,...,TB) for the sampled-reference test, p. 400,
correction P016-E008. Its measure space has the usual Borel sigma algebra. -/
abbrev ReferenceVector (B : ℕ) := Fin (B+1) → ℝ

/-- "exchangeable (invariant under every permutation of B+1 indices)",
P016-E008 repair of sampled-reference validity, p. 400. -/
def Exchangeable {B : ℕ} (μ : Measure (ReferenceVector B)) : Prop :=
  ∀ π : Equiv.Perm (Fin (B+1)), Measure.map (fun t i => t (π i)) μ = μ

/-- Inclusive rank among ALL B+1 statistics, including the observed statistic;
lower when upper=false and upper when upper=true. P016-E008 correction, p. 400. -/
noncomputable def coordinateCount {B : ℕ} (upper : Bool) (t : ReferenceVector B)
    (i : Fin (B+1)) : ℝ :=
  ∑ j, if (if upper then t i ≤ t j else t j ≤ t i) then (1 : ℝ) else 0

open scoped Classical in
/-- Exact uniform mass is the indicator sum divided by the support size,
finite bridge for the exchangeable-rank correction P016-E008, p. 400. -/
theorem uniform_mass_sum {Ω : Type} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) :
    mass (uniformLaw Ω) E = (∑ ω, if E ω then (1 : ℝ) else 0)/Fintype.card Ω := by
  classical
  simp only [mass,uniformLaw,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

/-- Inclusive coordinate ranks are permuted when the statistic indices are
permuted; P016-E008 exchangeability argument, p. 400. -/
theorem coordinate_count_perm {B : ℕ} (upper : Bool) (t : ReferenceVector B)
    (π : Equiv.Perm (Fin (B+1))) (i : Fin (B+1)) :
    coordinateCount upper (fun j => t (π j)) i = coordinateCount upper t (π i) := by
  classical
  exact Equiv.sum_comp π (fun j => if (if upper then t (π i) ≤ t j else t j ≤ t (π i)) then (1 : ℝ) else 0)

/-- Coordinate ranks are measurable functions of real statistics, P016-E008
correction under their usual Borel joint distribution, p. 400. -/
theorem measurable_coordinate_count {B : ℕ} (upper : Bool) (i : Fin (B+1)) :
    Measurable (fun t : ReferenceVector B => coordinateCount upper t i) := by
  classical
  unfold coordinateCount
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite
  · cases upper <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)
    · exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  · exact measurable_const
  · exact measurable_const

/-- For any fixed statistic vector, at most c+1 indices have inclusive rank
at most c+1, including ties. P016-E008 finite counting lemma, p. 400. -/
theorem coordinate_rank_count {B : ℕ} (upper : Bool) (t : ReferenceVector B) (c : ℕ) :
    (∑ i, if coordinateCount upper t i ≤ (c+1 : ℝ) then (1 : ℝ) else 0) ≤ c+1 := by
  classical
  have hN : (0 : ℝ) < B+1 := by positivity
  have hN0 : (B+1 : ℝ) ≠ 0 := ne_of_gt hN
  have heq : ∀ i, (if upper then upperP (uniformLaw (Fin (B+1))) t i
      else lowerP (uniformLaw (Fin (B+1))) t i) = coordinateCount upper t i/(B+1) := by
    intro i
    cases upper <;> simp only [Bool.false_eq_true,ite_false,ite_true,upperP,lowerP,
      uniform_mass_sum,coordinateCount,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have hv : mass (uniformLaw (Fin (B+1)))
      (fun i => coordinateCount upper t i/(B+1) ≤ (c+1 : ℝ)/(B+1)) ≤ (c+1 : ℝ)/(B+1) := by
    cases upper
    · have heq' : ∀ i, lowerP (uniformLaw (Fin (B+1))) t i = coordinateCount false t i/(B+1) := by
        simpa only [Bool.false_eq_true,ite_false] using heq
      simpa only [heq'] using
        lower_tail_bound (uniformLaw (Fin (B+1))) t ((c+1 : ℝ)/(B+1)) (by positivity)
    · have heq' : ∀ i, upperP (uniformLaw (Fin (B+1))) t i = coordinateCount true t i/(B+1) := by
        simpa only [ite_true] using heq
      simpa only [heq'] using
        upper_tail_bound (uniformLaw (Fin (B+1))) t ((c+1 : ℝ)/(B+1)) (by positivity)
  simp only [uniform_mass_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_one,
    div_le_div_iff_of_pos_right hN] at hv
  exact hv

/-- Integrating the finite count with exchangeability bounds the probability
of an extreme inclusive coordinate rank; P016-E008 correction, p. 400. -/
theorem exchangeable_coordinate_bound {B : ℕ} (μ : Measure (ReferenceVector B))
    [IsProbabilityMeasure μ] (hex : Exchangeable μ) (upper : Bool) (c : ℕ) :
    μ.real {t | coordinateCount upper t 0 ≤ (c+1 : ℝ)} ≤ (c+1 : ℝ)/(B+1) := by
  classical
  let E : Fin (B+1) → Set (ReferenceVector B) := fun i => {t | coordinateCount upper t i ≤ (c+1 : ℝ)}
  have hmeas : ∀ i, MeasurableSet (E i) := fun i =>
    measurableSet_le (measurable_coordinate_count upper i) measurable_const
  have hprob : ∀ i, μ.real (E i) = μ.real (E 0) := by
    intro i
    let π : Equiv.Perm (Fin (B+1)) := Equiv.swap 0 i
    have hf : Measurable (fun t : ReferenceVector B => fun j => t (π j)) :=
      measurable_pi_iff.mpr (fun j => measurable_pi_apply (π j))
    have hp := map_measureReal_apply (μ := μ) hf (hmeas 0)
    rw [hex π] at hp
    have hevent : (fun t : ReferenceVector B => fun j => t (π j)) ⁻¹' E 0 = E i := by
      ext t
      simp only [E,Set.mem_preimage,Set.mem_setOf_eq,coordinate_count_perm]
      simp [π]
    rw [hevent] at hp
    exact hp.symm
  have hi : ∀ i, Integrable ((E i).indicator (fun _ => (1 : ℝ))) μ :=
    fun i => (integrable_const (1 : ℝ)).indicator (hmeas i)
  have hsum : Integrable (fun t => ∑ i, (E i).indicator (fun _ => (1 : ℝ)) t) μ :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hpoint : ∀ t, (∑ i, (E i).indicator (fun _ => (1 : ℝ)) t) ≤ (c+1 : ℝ) := by
    intro t
    simpa only [E,Set.indicator,Set.mem_setOf_eq] using coordinate_rank_count upper t c
  have hb := integral_mono hsum (integrable_const (c+1 : ℝ)) hpoint
  rw [integral_finsetSum _ (fun i _ => hi i)] at hb
  have hind : ∀ i, (∫ t, (E i).indicator (fun _ => (1 : ℝ)) t ∂μ) = μ.real (E i) :=
    fun i => by simpa using (integral_indicator_const (μ := μ) (1 : ℝ) (hmeas i))
  have hunit : μ.real Set.univ = 1 := by simp [measureReal_def]
  simp only [hind,hprob,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,integral_const,hunit,one_smul] at hb
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < B+1)).mpr
  simpa only [mul_comm,E] using hb

/-- The inclusive rank among B+1 coordinates counts the observed value once,
so it is 1 plus the reference count, P016-E008 correction, p. 400. -/
theorem coordinate_count_observed {B : ℕ} (t : ReferenceVector B) :
    coordinateCount false t 0 = 1+(lowerCount (fun b => t b.succ) (t 0) : ℝ) ∧
    coordinateCount true t 0 = 1+(upperCount (fun b => t b.succ) (t 0) : ℝ) := by
  classical
  simp only [coordinateCount,Bool.false_eq_true,ite_false,ite_true,Fin.sum_univ_succ,
    le_refl,lowerCount,upperCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  trivial

/-- With distinct statistic values, the lower reference count equals the strict
observed rank, and the upper reference count is its complement in B. -/
lemma observed_counts_injective {B : ℕ} (t : ReferenceVector B) (ht : Function.Injective t) :
    lowerCount (fun b => t b.succ) (t 0) = RankCompletion.strictRank t 0 ∧
    upperCount (fun b => t b.succ) (t 0) = B-RankCompletion.strictRank t 0 := by
  classical
  have hn (b : Fin B) : t b.succ ≠ t 0 := fun h => Fin.succ_ne_zero b (ht h)
  have hl : lowerCount (fun b => t b.succ) (t 0) = RankCompletion.strictRank t 0 := by
    unfold lowerCount
    simp only [RankCompletion.strictRank,Fin.sum_univ_succ,lt_self_iff_false,ite_false,zero_add]
    apply Finset.sum_congr rfl
    intro b _
    simp [le_iff_lt_or_eq,hn b]
  have hs : lowerCount (fun b => t b.succ) (t 0) +
      upperCount (fun b => t b.succ) (t 0) = B := by
    unfold lowerCount upperCount
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ b : Fin B, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro b _
        rcases lt_or_gt_of_ne (hn b) with h | h <;> simp [h.le,not_le.mpr h]
      _ = B := by simp
  exact ⟨hl,by omega⟩

lemma weak_integer_tail {B : ℕ} (hB : 0 < B) (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (L U : ℕ) :
    min 1 (2 * min ((L : ℝ)/B) ((U : ℝ)/B)) ≤ α ↔
      L ≤ Nat.floor (α*B/2) ∨ U ≤ Nat.floor (α*B/2) := by
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hnn : 0 ≤ α*B/2 := by positivity
  constructor
  · intro h
    have hm : min ((L : ℝ)/B) ((U : ℝ)/B) ≤ α/2 := by
      rcases min_le_iff.mp h with h | h
      · linarith
      · linarith
    rcases min_le_iff.mp hm with h | h
    · left
      apply (Nat.le_floor_iff hnn).mpr
      have h' := (div_le_iff₀ hBr).mp h
      nlinarith
    · right
      apply (Nat.le_floor_iff hnn).mpr
      have h' := (div_le_iff₀ hBr).mp h
      nlinarith
  · intro h
    apply min_le_of_right_le
    rcases h with h | h
    · have hr := (Nat.le_floor_iff hnn).mp h
      have hd : (L : ℝ)/B ≤ α/2 := (div_le_iff₀ hBr).mpr (by nlinarith)
      have hm := min_le_left ((L : ℝ)/B) ((U : ℝ)/B)
      linarith
    · have hr := (Nat.le_floor_iff hnn).mp h
      have hd : (U : ℝ)/B ≤ α/2 := (div_le_iff₀ hBr).mpr (by nlinarith)
      have hm := min_le_right ((L : ℝ)/B) ((U : ℝ)/B)
      linarith

lemma rank_tail_card {B c : ℕ} (hc : 2*c < B) :
    (Finset.univ.filter (fun k : Fin (B+1) => k.val ≤ c ∨ B-k.val ≤ c)).card = 2*(c+1) := by
  classical
  have hcb : c < B+1 := by omega
  let l : Fin (B+1) := ⟨c,hcb⟩
  let u : Fin (B+1) := ⟨B-c,by omega⟩
  have he : Finset.univ.filter (fun k : Fin (B+1) => k.val ≤ c ∨ B-k.val ≤ c) =
      Finset.Iic l ∪ Finset.Ici u := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
      Finset.mem_Iic,Finset.mem_Ici,Fin.le_iff_val_le_val,l,u]
    omega
  have hd : Disjoint (Finset.Iic l) (Finset.Ici u) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    simp only [Finset.mem_Iic,Finset.mem_Ici,Fin.le_iff_val_le_val,l,u] at hk hk'
    omega
  rw [he,Finset.card_union_of_disjoint hd,Fin.card_Iic,Fin.card_Ici]
  simp only [l,u]
  omega

/-- T13(i): under an exchangeable probability law with almost-sure distinctness,
the observed strict rank is uniform on 0,...,B. For B > 0, 0 ≤ α < 1,
c = floor(α*B/2), and 2*c < B, the weak raw-p-value cutoff has rejection
probability 2*(c+1)/(B+1) (P016-E008, p. 400). -/
theorem t13_no_ties {B : ℕ} (hB : 0 < B) (μ : Measure (ReferenceVector B))
    [IsProbabilityMeasure μ] (hex : Exchangeable μ) (hnt : ∀ᵐ t ∂μ, Function.Injective t)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (c : ℕ) (hc : c = Nat.floor (α*B/2)) (hdisj : 2*c < B) :
    (∀ k : Fin (B+1), μ.real {t | (∑ b : Fin B, if t b.succ < t 0 then (1 : ℕ) else 0) = k.val} =
      1/(B+1)) ∧
    (∀ᵐ t ∂μ, lowerCount (fun b => t b.succ) (t 0) =
      (∑ b : Fin B, if t b.succ < t 0 then (1 : ℕ) else 0) ∧
      upperCount (fun b => t b.succ) (t 0) = B-lowerCount (fun b => t b.succ) (t 0)) ∧
    μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ α} = 2*(c+1)/(B+1) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simpa only [RankCompletion.strictRank, Fin.sum_univ_succ, lt_self_iff_false,
      ite_false, zero_add] using RankCompletion.strict_rank_uniform μ hex hnt 0 k
  · filter_upwards [hnt] with t ht
    obtain ⟨hl,hu⟩ := observed_counts_injective t ht
    constructor
    · simpa only [RankCompletion.strictRank, Fin.sum_univ_succ, lt_self_iff_false,
        ite_false, zero_add] using hl
    · exact hu.trans (congrArg (fun q : ℕ => B-q) hl.symm)
  · let A : Finset (Fin (B+1)) := Finset.univ.filter
      (fun k => k.val ≤ c ∨ B-k.val ≤ c)
    have hevent : {t : ReferenceVector B | rawP (fun b => t b.succ) (t 0) ≤ α} =ᵐ[μ]
        {t | ∃ k ∈ A, RankCompletion.strictRank t 0 = k.val} := by
      filter_upwards [hnt] with t ht
      apply propext
      change rawP (fun b => t b.succ) (t 0) ≤ α ↔ _
      rw [show rawP (fun b => t b.succ) (t 0) ≤ α ↔
          lowerCount (fun b => t b.succ) (t 0) ≤ c ∨
          upperCount (fun b => t b.succ) (t 0) ≤ c by
        simpa only [rawP,doubledP,← hc] using weak_integer_tail hB α hα hα1
          (lowerCount (fun b => t b.succ) (t 0)) (upperCount (fun b => t b.succ) (t 0))]
      have hh := observed_counts_injective t ht
      rw [hh.1,hh.2]
      obtain ⟨e,he⟩ := RankCompletion.rank_permutation t ht
      have hr : RankCompletion.strictRank t 0 = (e 0).val := he 0
      rw [hr]
      constructor
      · intro h
        exact ⟨e 0,by simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using h,rfl⟩
      · rintro ⟨k,hk,heq⟩
        rw [heq]
        simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using hk
    rw [measureReal_congr hevent,RankCompletion.strict_rank_finite_event μ hex hnt 0 A,
      rank_tail_card hdisj]
    push_cast
    ring


/-- The exact finite-design binomial mixture S_B(c) in the P016-E008 witness, not a formula printed in the paper. -/
noncomputable def binomialMixture (M B c : ℕ) : ℝ :=
  2/(M : ℝ) * ∑ r : Fin M, ∑ k ∈ Finset.range (c+1),
    (Nat.choose B k : ℝ) * (((r.val+1 : ℕ) : ℝ)/M)^k *
      (((M : ℝ)-(r.val+1))/M)^(B-k)

/-- T13(ii) finite identity: on the exact power-of-two population, the balanced
SSR has the integer-moment formula used by the P016-E008 counterexample.
This lemma does not assert the separate multiplicity or sampled-size claims. -/
theorem t13_rss_identity (z : Assignment 16) (hz : groupSize z true = 8) :
    let y : Outcome 16 := fun i => (2 : ℝ)^i.val
    (∑ i, y i) = 65535 ∧ (∑ i, (y i)^2) = 1431655765 ∧
    rss y z = 1431655765-((groupSum y z true)^2+(65535-groupSum y z true)^2)/8 := by
  let y : Outcome 16 := fun i => (2 : ℝ)^i.val
  have hs : (∑ i, y i) = 65535 := by norm_num [y,Fin.sum_univ_succ]
  have hq : (∑ i, (y i)^2) = 1431655765 := by norm_num [y,Fin.sum_univ_succ]
  have hz0 : groupSize z false = 8 := by have h := group_sizes z; omega
  have h0 : 0 < groupSize z false := by omega
  have h1 : 0 < groupSize z true := by omega
  have hgs : groupSum y z false = 65535-groupSum y z true := by
    have h := group_sums y z
    rw [hs] at h
    linarith
  change (∑ i, y i) = 65535 ∧ (∑ i, (y i)^2) = 1431655765 ∧ _
  refine ⟨hs,hq,?_⟩
  rw [rss_second_moments y z h0 h1,hq,groupMean,groupMean,hz0,hz,hgs]
  ring

/-- T13(ii): the explicit 16-unit power-of-two population has 12870 balanced
assignments and exactly 6435 SSR values, each on a complementary pair; P016-E008. -/
theorem t13_finite_design :
    let y : Outcome 16 := fun i => (2 : ℝ)^i.val
    Fintype.card (Balanced 16 8) = 12870 ∧
    (∑ i, y i) = 65535 ∧ (∑ i, (y i)^2) = 1431655765 ∧
    (∀ z : Balanced 16 8, rss y z.val = 1431655765 -
      ((groupSum y z.val true)^2 + (65535-groupSum y z.val true)^2)/8) ∧
    (Finset.univ.image (fun z : Balanced 16 8 => rss y z.val)).card = 6435 ∧
    (∀ z w : Balanced 16 8, rss y z.val = rss y w.val ↔
      z.val = w.val ∨ z.val = fun i => !(w.val i)) := by
  let y : Outcome 16 := fun i => (2 : ℝ)^i.val
  have hr : ∀ z : Balanced 16 8, rss y z.val = powerTwoRSSExpression z.val := by
    intro z
    exact (t13_rss_identity z.val z.property).2.2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [balanced_card]
    decide
  · norm_num [y,Fin.sum_univ_succ]
  · norm_num [y,Fin.sum_univ_succ]
  · intro z
    exact (t13_rss_identity z.val z.property).2.2
  · have heq : (fun z : Balanced 16 8 => rss y z.val) =
        (fun z : Balanced 16 8 => powerTwoRSSExpression z.val) := funext hr
    rw [heq]
    exact powerTwoRSSExpression_card
  · intro z w
    rw [hr z,hr w]
    exact powerTwoRSSExpression_equal z.val w.val


/-- T13 arithmetic certificates: no-tie weak sizes and the finite-design lower
bound exceed .05. These calculations alone do not prove the probability laws. -/
theorem t13_numeric_certificates :
    (52/1001 : ℝ) = 4/77 ∧ (1/20 : ℝ) < 52/1001 ∧ (1/20 : ℝ) < 502/10001 ∧
    (4/77 : ℝ)-2/6435 = 2326/45045 ∧ (1/20 : ℝ) < 2326/45045 := by norm_num

/-- T14(a): exchangeability with ties gives each inclusive reference rank the
bound (c+1)/(B+1), P016-E008 correction of sampled-reference validity, p. 400. -/
theorem t14_rank_bound {B : ℕ} (hB : 0 < B) (μ : Measure (ReferenceVector B))
    [IsProbabilityMeasure μ] (hex : Exchangeable μ) (c : ℕ) (hc : c ≤ B) :
    μ.real {t | lowerCount (fun b => t b.succ) (t 0) ≤ c} ≤ (c+1 : ℝ)/(B+1) ∧
      μ.real {t | upperCount (fun b => t b.succ) (t 0) ≤ c} ≤ (c+1 : ℝ)/(B+1) := by
  have heL : {t : ReferenceVector B | coordinateCount false t 0 ≤ (c+1 : ℝ)} =
      {t | lowerCount (fun b => t b.succ) (t 0) ≤ c} := by
    ext t
    simp only [Set.mem_setOf_eq,(coordinate_count_observed t).1]
    constructor <;> intro h
    · exact_mod_cast (show (lowerCount (fun b => t b.succ) (t 0) : ℝ) ≤ c by linarith)
    · have hc : (lowerCount (fun b => t b.succ) (t 0) : ℝ) ≤ c := by exact_mod_cast h
      linarith
  have heU : {t : ReferenceVector B | coordinateCount true t 0 ≤ (c+1 : ℝ)} =
      {t | upperCount (fun b => t b.succ) (t 0) ≤ c} := by
    ext t
    simp only [Set.mem_setOf_eq,(coordinate_count_observed t).2]
    constructor <;> intro h
    · exact_mod_cast (show (upperCount (fun b => t b.succ) (t 0) : ℝ) ≤ c by linarith)
    · have hc : (upperCount (fun b => t b.succ) (t 0) : ℝ) ≤ c := by exact_mod_cast h
      linarith
  constructor
  · rw [← heL]; exact exchangeable_coordinate_bound μ hex false c
  · rw [← heU]; exact exchangeable_coordinate_bound μ hex true c

/-- T14(b): the raw strict test has size at most 2 ceil(alpha B/2)/(B+1),
P016-E008 corrected validity statement, pp. 400–401. Ties are allowed. -/
theorem t14_strict_bound {B : ℕ} (hB : 0 < B) (μ : Measure (ReferenceVector B))
    [IsProbabilityMeasure μ] (hex : Exchangeable μ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    μ.real {t | rawP (fun b => t b.succ) (t 0) < α} ≤
      2*(Nat.ceil (α*B/2) : ℝ)/(B+1) := by
  classical
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  let q := Nat.ceil (α*B/2)
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have h := (Nat.ceil_eq_zero.mp hzero)
    nlinarith
  have hqB : q ≤ B := by
    apply Nat.ceil_le.mpr
    nlinarith
  let c := q-1
  have hc : c ≤ B := by omega
  have hcq : (c+1 : ℝ) = q := by exact_mod_cast (show c+1 = q by omega)
  let EL : Set (ReferenceVector B) := {t | lowerCount (fun b => t b.succ) (t 0) ≤ c}
  let EU : Set (ReferenceVector B) := {t | upperCount (fun b => t b.succ) (t 0) ≤ c}
  have hsubset : {t : ReferenceVector B | rawP (fun b => t b.succ) (t 0) < α} ⊆ EL ∪ EU := by
    intro t ht
    change rawP (fun b => t b.succ) (t 0) < α at ht
    unfold rawP doubledP at ht
    have hm : 2*min ((lowerCount (fun b => t b.succ) (t 0) : ℝ)/B)
        ((upperCount (fun b => t b.succ) (t 0) : ℝ)/B) < α := by
      rcases min_lt_iff.mp ht with h | h
      · exact False.elim (by linarith)
      · exact h
    have hmin : min ((lowerCount (fun b => t b.succ) (t 0) : ℝ)/B)
        ((upperCount (fun b => t b.succ) (t 0) : ℝ)/B) < α/2 := by linarith
    rcases min_lt_iff.mp hmin with h | h
    · left
      have hr : (lowerCount (fun b => t b.succ) (t 0) : ℝ) < α*B/2 := by
        have h' := (div_lt_iff₀ hBr).mp h
        nlinarith
      have hn : lowerCount (fun b => t b.succ) (t 0) < q := Nat.lt_ceil.mpr hr
      change _ ≤ c
      omega
    · right
      have hr : (upperCount (fun b => t b.succ) (t 0) : ℝ) < α*B/2 := by
        have h' := (div_lt_iff₀ hBr).mp h
        nlinarith
      have hn : upperCount (fun b => t b.succ) (t 0) < q := Nat.lt_ceil.mpr hr
      change _ ≤ c
      omega
  have hbound := t14_rank_bound hB μ hex c hc
  rw [hcq] at hbound
  have hm := (measureReal_mono (μ := μ) hsubset).trans (measureReal_union_le (μ := μ) EL EU)
  change μ.real EL ≤ (q : ℝ)/(B+1) ∧ μ.real EU ≤ (q : ℝ)/(B+1) at hbound
  change _ ≤ 2*(q : ℝ)/(B+1)
  rw [mul_div_assoc]
  linarith [hbound.1,hbound.2]

/-- "(1+C)/(B+1)", rank-corrected inclusive empirical tails, P016-E008, p. 400. -/
noncomputable def correctedLower {B : ℕ} (t : ReferenceVector B) : ℝ :=
  (1+(lowerCount (fun b => t b.succ) (t 0) : ℝ))/(B+1)

/-- "(1+C)/(B+1)", rank-corrected upper empirical tail, P016-E008, p. 400. -/
noncomputable def correctedUpper {B : ℕ} (t : ReferenceVector B) : ℝ :=
  (1+(upperCount (fun b => t b.succ) (t 0) : ℝ))/(B+1)

/-- The all-coordinate count is a positive integer, P016-E008 corrected empirical
rank calculation, p. 400. -/
theorem coordinate_count_integer {B : ℕ} (upper : Bool) (t : ReferenceVector B) :
    coordinateCount upper t 0 =
      ((1+(if upper then upperCount (fun b => t b.succ) (t 0)
        else lowerCount (fun b => t b.succ) (t 0)) : ℕ) : ℝ) := by
  cases upper <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_add,Nat.cast_one]
  · exact (coordinate_count_observed t).1
  · exact (coordinate_count_observed t).2

/-- The one-sided corrected rank probability has the sharper integer floor
bound at every nonnegative threshold; P016-E008 correction, p. 400. -/
theorem corrected_coordinate_floor {B : ℕ} (μ : Measure (ReferenceVector B))
    [IsProbabilityMeasure μ] (hex : Exchangeable μ) (upper : Bool) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {t | coordinateCount upper t 0/(B+1) ≤ a} ≤
      (Nat.floor (a*(B+1)) : ℝ)/(B+1) := by
  classical
  have hN : (0 : ℝ) < B+1 := by positivity
  let q := Nat.floor (a*(B+1))
  have hnat : ∀ t : ReferenceVector B, coordinateCount upper t 0/(B+1) ≤ a →
      1+(if upper then upperCount (fun b => t b.succ) (t 0)
        else lowerCount (fun b => t b.succ) (t 0)) ≤ q := by
    intro t ht
    apply (Nat.le_floor_iff (mul_nonneg ha hN.le)).mpr
    rw [← coordinate_count_integer]
    exact (div_le_iff₀ hN).mp ht
  by_cases hq : q = 0
  · have he : {t : ReferenceVector B | coordinateCount upper t 0/(B+1) ≤ a} = ∅ := by
      ext t
      constructor
      · intro ht; have h := hnat t ht; omega
      · simp
    change _ ≤ (q : ℝ)/(B+1)
    rw [he,hq]
    simp
  · let c := q-1
    have hcq : (c+1 : ℝ) = q := by exact_mod_cast (show c+1 = q by omega)
    have he : {t : ReferenceVector B | coordinateCount upper t 0/(B+1) ≤ a} ⊆
        {t | coordinateCount upper t 0 ≤ (c+1 : ℝ)} := by
      intro t ht
      change coordinateCount upper t 0 ≤ (c+1 : ℝ)
      rw [coordinate_count_integer,hcq]
      exact_mod_cast hnat t ht
    have hb := (measureReal_mono (μ := μ) he).trans (exchangeable_coordinate_bound μ hex upper c)
    rw [hcq] at hb
    exact hb

/-- The floor rank bound is at most the nominal threshold, P016-E008, p. 400. -/
theorem corrected_floor_le {B : ℕ} (a : ℝ) (ha : 0 ≤ a) :
    (Nat.floor (a*(B+1)) : ℝ)/(B+1) ≤ a := by
  have hN : (0 : ℝ) < B+1 := by positivity
  exact (div_le_iff₀ hN).mpr (Nat.floor_le (mul_nonneg ha hN.le))

/-- T14(c): rank-corrected empirical p values are valid at every threshold,
including the sharper floor bound for each one-sided tail, P016-E008, p. 400. -/
theorem t14_corrected_valid {B : ℕ} (hB : 0 < B) (μ : Measure (ReferenceVector B))
    [IsProbabilityMeasure μ] (hex : Exchangeable μ) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    μ.real {t | correctedLower t ≤ α} ≤ (Nat.floor (α*(B+1)) : ℝ)/(B+1) ∧
    μ.real {t | correctedUpper t ≤ α} ≤ (Nat.floor (α*(B+1)) : ℝ)/(B+1) ∧
    (Nat.floor (α*(B+1)) : ℝ)/(B+1) ≤ α ∧
    μ.real {t | doubledP (correctedLower t) (correctedUpper t) ≤ α} ≤ α := by
  have hL : ∀ a, 0 ≤ a → μ.real {t : ReferenceVector B | correctedLower t ≤ a} ≤
      (Nat.floor (a*(B+1)) : ℝ)/(B+1) := by
    intro a ha
    simpa only [correctedLower,(coordinate_count_observed _).1] using
      corrected_coordinate_floor μ hex false a ha
  have hU : ∀ a, 0 ≤ a → μ.real {t : ReferenceVector B | correctedUpper t ≤ a} ≤
      (Nat.floor (a*(B+1)) : ℝ)/(B+1) := by
    intro a ha
    simpa only [correctedUpper,(coordinate_count_observed _).2] using
      corrected_coordinate_floor μ hex true a ha
  refine ⟨hL α hα,hU α hα,corrected_floor_le α hα,?_⟩
  by_cases ha1 : α = 1
  · rw [ha1]
    have h := measureReal_mono (μ := μ) (Set.subset_univ {t : ReferenceVector B | doubledP (correctedLower t) (correctedUpper t) ≤ 1})
    simpa [measureReal_def] using h
  · have hαlt : α < 1 := lt_of_le_of_ne hα1 ha1
    have hhalf : 0 ≤ α/2 := by linarith
    have hs : {t : ReferenceVector B | doubledP (correctedLower t) (correctedUpper t) ≤ α} ⊆
        {t | correctedLower t ≤ α/2} ∪ {t | correctedUpper t ≤ α/2} := by
      intro t ht
      change doubledP (correctedLower t) (correctedUpper t) ≤ α at ht
      unfold doubledP at ht
      have hm : 2*min (correctedLower t) (correctedUpper t) ≤ α := by
        rcases min_le_iff.mp ht with h | h
        · exact False.elim (by linarith)
        · exact h
      have hh : min (correctedLower t) (correctedUpper t) ≤ α/2 := by linarith
      exact min_le_iff.mp hh
    have hm := (measureReal_mono (μ := μ) hs).trans
      (measureReal_union_le (μ := μ) {t : ReferenceVector B | correctedLower t ≤ α/2}
        {t | correctedUpper t ≤ α/2})
    have hb := corrected_floor_le (B := B) (α/2) hhalf
    linarith [hL (α/2) hhalf,hU (α/2) hhalf]

/-- Independent draws from a finite design have product weight, p. 400,
fresh-reference interpretation of the permutation simulation (P016-E008). -/
noncomputable def iidWeight {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (m : ℕ)
    (draw : Fin m → Ω) : ℝ := ∏ i, P.weight (draw i)

/-- Independent product weights sum to one; fresh-reference design of
p. 400, P016-E008. No nonzero-measure premise is left implicit. -/
noncomputable def iidLaw {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (m : ℕ) :
    FiniteLaw (Fin m → Ω) where
  weight := iidWeight P m
  nonneg := fun draw => Finset.prod_nonneg (fun i _ => P.nonneg (draw i))
  total := by
    unfold iidWeight
    rw [← Fintype.sum_pow,P.total]
    simp

/-- Probability of an event in m independent design draws, p. 400 (P016-E008). -/
noncomputable def iidMass {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (m : ℕ)
    (E : (Fin m → Ω) → Prop) : ℝ := by
  classical
  exact ∑ draw, if E draw then iidWeight P m draw else 0

/-- Independent-draw event probabilities are exactly the product-law mass,
p. 400, P016-E008 fresh-reference correction. -/
theorem iid_mass_law {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (m : ℕ)
    (E : (Fin m → Ω) → Prop) : iidMass P m E = mass (iidLaw P m) E := rfl

/-- T14(d): applying ONE fixed statistic to iid draws from ONE assignment law
gives an exchangeable joint statistic law; P016-E008 premise for p. 400. A finite-
design event formulation avoids constructing a continuous law unnecessarily. -/
theorem t14_iid_exchangeable {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (B : ℕ)
    (s : Ω → ℝ) (π : Equiv.Perm (Fin (B+1))) (E : ReferenceVector B → Prop) :
    iidMass P (B+1) (fun draw => E (fun i => s (draw (π i)))) =
      iidMass P (B+1) (fun draw => E (fun i => s (draw i))) := by
  classical
  let e : (Fin (B+1) → Ω) ≃ (Fin (B+1) → Ω) := {
    toFun := fun f i => f (π i)
    invFun := fun f i => f (π.symm i)
    left_inv := fun f => by funext i; simp
    right_inv := fun f => by funext i; simp }
  have hw : ∀ draw : Fin (B+1) → Ω, iidWeight P (B+1) (e draw) = iidWeight P (B+1) draw := by
    intro draw
    exact Equiv.prod_comp π (fun i => P.weight (draw i))
  unfold iidMass
  calc
    _ = ∑ draw, if E (fun i => s (e draw i)) then iidWeight P (B+1) (e draw) else 0 := by
      apply Finset.sum_congr rfl
      intro draw _
      rw [hw]
      rfl
    _ = _ := e.sum_comp (fun draw => if E (fun i => s (draw i)) then iidWeight P (B+1) draw else 0)

/-- The general exchangeable-rank bound for iid finite-design statistics,
proved directly by weighted finite sums; P016-E008, p. 400. -/
theorem iid_coordinate_bound {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (B : ℕ)
    (s : Ω → ℝ) (upper : Bool) (c : ℕ) :
    iidMass P (B+1) (fun draw => coordinateCount upper (fun j => s (draw j)) 0 ≤ (c+1 : ℝ)) ≤
      (c+1 : ℝ)/(B+1) := by
  classical
  let Q := iidLaw P (B+1)
  let E : Fin (B+1) → (Fin (B+1) → Ω) → Prop :=
    fun i draw => coordinateCount upper (fun j => s (draw j)) i ≤ (c+1 : ℝ)
  have hprob : ∀ i, mass Q (E i) = mass Q (E 0) := by
    intro i
    let π : Equiv.Perm (Fin (B+1)) := Equiv.swap 0 i
    have hp := t14_iid_exchangeable P B s π
      (fun t => coordinateCount upper t 0 ≤ (c+1 : ℝ))
    have hπ : π 0 = i := by simp [π]
    have hcount : ∀ draw : Fin (B+1) → Ω,
        coordinateCount upper (fun j => s (draw (π j))) 0 =
          coordinateCount upper (fun j => s (draw j)) i := by
      intro draw
      exact (coordinate_count_perm upper (fun j => s (draw j)) π 0).trans (by rw [hπ])
    simp_rw [hcount] at hp
    exact hp
  have hswap : (∑ i, mass Q (E i)) =
      ∑ draw, Q.weight draw*(∑ i, if E i draw then (1 : ℝ) else 0) := by
    unfold mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro draw _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hpoint : ∀ draw, (∑ i, if E i draw then (1 : ℝ) else 0) ≤ c+1 := by
    intro draw
    exact coordinate_rank_count upper (fun j => s (draw j)) c
  have hb : (∑ draw, Q.weight draw*(∑ i, if E i draw then (1 : ℝ) else 0)) ≤ c+1 := by
    calc
      _ ≤ ∑ draw, Q.weight draw*(c+1) :=
        Finset.sum_le_sum (fun draw _ => mul_le_mul_of_nonneg_left (hpoint draw) (Q.nonneg draw))
      _ = c+1 := by rw [← Finset.sum_mul,Q.total,one_mul]
  rw [← hswap] at hb
  simp only [hprob,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one] at hb
  rw [iid_mass_law]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < B+1)).mpr
  simpa only [mul_comm,Q,E] using hb

/-- Inclusive reference-count events are exactly inclusive all-coordinate
rank events with one added to the count; P016-E008, p. 400. -/
theorem coordinate_count_le_iff {B : ℕ} (upper : Bool) (t : ReferenceVector B) (c : ℕ) :
    coordinateCount upper t 0 ≤ (c+1 : ℝ) ↔
      (if upper then upperCount (fun b => t b.succ) (t 0)
        else lowerCount (fun b => t b.succ) (t 0)) ≤ c := by
  rw [coordinate_count_integer]
  have heq : ((1+c : ℕ) : ℝ) = (c+1 : ℝ) := by simp only [Nat.cast_add,Nat.cast_one]; ring
  rw [← heq,Nat.cast_le]
  omega

/-- The raw strict rejection event is contained in the two corresponding
integer-rank tails, P016-E008 correction of the p. 400 cutoff. -/
theorem raw_strict_rank_event {B : ℕ} (hB : 0 < B) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (t : ReferenceVector B) (ht : rawP (fun b => t b.succ) (t 0) < α) :
    lowerCount (fun b => t b.succ) (t 0) ≤ Nat.ceil (α*B/2)-1 ∨
      upperCount (fun b => t b.succ) (t 0) ≤ Nat.ceil (α*B/2)-1 := by
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hq : 0 < Nat.ceil (α*B/2) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := Nat.ceil_eq_zero.mp hz
    nlinarith
  unfold rawP doubledP at ht
  have hm : 2*min ((lowerCount (fun b => t b.succ) (t 0) : ℝ)/B)
      ((upperCount (fun b => t b.succ) (t 0) : ℝ)/B) < α := by
    rcases min_lt_iff.mp ht with h | h
    · exact False.elim (by linarith)
    · exact h
  have hh : min ((lowerCount (fun b => t b.succ) (t 0) : ℝ)/B)
      ((upperCount (fun b => t b.succ) (t 0) : ℝ)/B) < α/2 := by linarith
  rcases min_lt_iff.mp hh with h | h
  · left
    have hr : (lowerCount (fun b => t b.succ) (t 0) : ℝ) < α*B/2 := by
      have h' := (div_lt_iff₀ hBr).mp h
      nlinarith
    have hn := Nat.lt_ceil.mpr hr
    omega
  · right
    have hr : (upperCount (fun b => t b.succ) (t 0) : ℝ) < α*B/2 := by
      have h' := (div_lt_iff₀ hBr).mp h
      nlinarith
    have hn := Nat.lt_ceil.mpr hr
    omega

/-- Strict sampled-reference validity for every fixed statistic and every
finite iid randomization law, P016-E008 premise for the headline on p. 400. -/
theorem iid_strict_bound {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (B : ℕ) (hB : 0 < B)
    (s : Ω → ℝ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    iidMass P (B+1) (fun draw => rawP (fun b => s (draw b.succ)) (s (draw 0)) < α) ≤
      2*(Nat.ceil (α*B/2) : ℝ)/(B+1) := by
  classical
  let q := Nat.ceil (α*B/2)
  let c := q-1
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := Nat.ceil_eq_zero.mp hz
    have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
    nlinarith
  have hcq : (c+1 : ℝ) = q := by exact_mod_cast (show c+1 = q by omega)
  let EL := fun draw : Fin (B+1) → Ω => lowerCount (fun b => s (draw b.succ)) (s (draw 0)) ≤ c
  let EU := fun draw : Fin (B+1) → Ω => upperCount (fun b => s (draw b.succ)) (s (draw 0)) ≤ c
  have hL : mass (iidLaw P (B+1)) EL ≤ (c+1 : ℝ)/(B+1) := by
    simpa only [iid_mass_law,coordinate_count_le_iff,Bool.false_eq_true,ite_false,EL] using
      iid_coordinate_bound P B s false c
  have hU : mass (iidLaw P (B+1)) EU ≤ (c+1 : ℝ)/(B+1) := by
    simpa only [iid_mass_law,coordinate_count_le_iff,ite_true,EU] using
      iid_coordinate_bound P B s true c
  have hs : ∀ draw : Fin (B+1) → Ω, rawP (fun b => s (draw b.succ)) (s (draw 0)) < α → EL draw ∨ EU draw := by
    intro draw ht
    exact raw_strict_rank_event hB α hα hα1 (fun j => s (draw j)) ht
  rw [iid_mass_law]
  have hm := (mass_mono (iidLaw P (B+1)) hs).trans (mass_or_le (iidLaw P (B+1)) EL EU)
  rw [hcq] at hL hU
  change _ ≤ 2*(q : ℝ)/(B+1)
  rw [mul_div_assoc]
  linarith

/-- T14(b) numeric corollary: the two printed strict-rule size bounds are
below .05. This is arithmetic; the exchangeable probability bound is T14(b). -/
theorem t14_printed_bounds :
    2*(Nat.ceil ((1/20 : ℝ)*1000/2) : ℝ)/(1000+1) = 50/1001 ∧
    2*(Nat.ceil ((1/20 : ℝ)*10000/2) : ℝ)/(10000+1) = 500/10001 ∧
    (50/1001 : ℝ) < 1/20 ∧ (500/10001 : ℝ) < 1/20 := by norm_num

/-- T15(a): hypotheses change treated ECDFs and leave controls unchanged;
P016-E011 witness against the printed "control group" sentence, p. 398. -/
theorem t15_adjustment_witness :
    let Y : Outcome 4 := ![9,11,10,12]
    let z := complete4 5
    additiveAdjust Y z (1/2) = ![9,11,19/2,23/2] ∧
    multiplicativeAdjust Y z 2 = ![9,11,5,6] ∧
    ecdf (additiveAdjust Y z (1/2)) z true 6 = 0 ∧
    ecdf (multiplicativeAdjust Y z 2) z true 6 = 1 := by
  dsimp
  refine ⟨?_,?_,?_,?_⟩
  · funext i; fin_cases i <;> audit_num
  · funext i; fin_cases i <;> audit_num
  · audit_num
  · audit_num

/-- T15(b): ECDF is evaluated at its argument, not at the indexed sample point,
footnote 3, p. 396 (P016-E011 exact witness). -/
theorem t15_ecdf_witness : sampleECDF (![1,3] : Outcome 2) 2 = 1/2 ∧
    sampleECDF (![1,3] : Outcome 2) 3 = 1 := by audit_num

/-- T15(c): the printed family is exactly the diagonal and misses the stated
true parameter pair, p. 400 (P016-E011 exact witness). -/
theorem t15_diagonal_witness :
    (∀ t b : ℝ, (∃ t0 : ℝ, t=t0 ∧ b=t0) ↔ b=t) ∧
    ¬ (∃ t0 : ℝ, (1/2 : ℝ)=t0 ∧ (2 : ℝ)=t0) := by
  constructor
  · intro t b
    constructor
    · rintro ⟨t0,rfl,rfl⟩; rfl
    · intro h; exact ⟨t,rfl,h⟩
  · rintro ⟨t0,h1,h2⟩; linarith

/-- T16(a): controls stay unchanged under every additive or nonzero
multiplicative hypothesis, while treated adjustments depend on the parameter;
P016-E011 corrected explanation, p. 398. -/
theorem t16_group_adjustments {n : ℕ} (Y : Outcome n) (z : Assignment n) (i : Fin n)
    (t t' a a' : ℝ) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    (z i = false → additiveAdjust Y z t i = Y i ∧ multiplicativeAdjust Y z a i = Y i) ∧
    (z i = true → additiveAdjust Y z t i = Y i-t ∧ multiplicativeAdjust Y z a i = Y i/a ∧
      (t ≠ t' → additiveAdjust Y z t i ≠ additiveAdjust Y z t' i) ∧
      (a ≠ a' → Y i ≠ 0 → multiplicativeAdjust Y z a i ≠ multiplicativeAdjust Y z a' i)) := by
  constructor
  · intro hi; simp [additiveAdjust,multiplicativeAdjust,bit,hi]
  · intro hi
    simp only [additiveAdjust,multiplicativeAdjust,bit,hi,↓reduceIte,mul_one,one_mul,
      add_sub_cancel]
    refine ⟨trivial,trivial,?_,?_⟩
    · intro hte he; apply hte; linarith
    · intro hae hy he
      apply hae
      have hc : Y i/a = Y i/a' → a = a' := by
        intro hd
        field_simp [ha,ha'] at hd
        exact hd.symm
      exact hc he

/-- T16(a), ECDF consequence: controls' empirical distributions are identical
under hypotheses of either model, P016-E011 corrected sentence, p. 398. -/
theorem t16_control_ecdf {n : ℕ} (Y : Outcome n) (z : Assignment n) (t a x : ℝ) (ha : a ≠ 0) :
    ecdf (additiveAdjust Y z t) z false x = ecdf Y z false x ∧
    ecdf (multiplicativeAdjust Y z a) z false x = ecdf Y z false x := by
  constructor <;> unfold ecdf
  all_goals
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases hi : z i <;> simp [hi,additiveAdjust,multiplicativeAdjust,bit]

/-- T16(b): the indicator-sum ECDF is exactly the proportion at or below its
argument, corrected footnote 3, p. 396 (P016-E011). -/
theorem t16_ecdf_argument {n : ℕ} (u : Outcome n) (x : ℝ) :
    sampleECDF u x = ((Finset.univ.filter (fun i => u i ≤ x)).card : ℝ)/n := by
  classical
  simp [sampleECDF]

/-- T16(c): the corrected two-parameter family contains the stated truth,
whereas the printed diagonal family does not, p. 400 (P016-E011). -/
theorem t16_joint_hypothesis :
    (∃ t0 b0 : ℝ, (1/2 : ℝ)=t0 ∧ (2 : ℝ)=b0) ∧
    ¬ (∃ t0 : ℝ, (1/2 : ℝ)=t0 ∧ (2 : ℝ)=t0) := by
  exact ⟨⟨1/2,2,rfl,rfl⟩,t15_diagonal_witness.2⟩

/-- "median ... average of the m-th and (m+1)-th smallest" for 2m units,
the released calibration criterion (P016-N003), Fig. 2, p. 398. Indices in Lean are
zero-based. The middle-order-statistic interpretation requires m ≥ 1;
at m = 0 the definition uses zero defaults. -/
noncomputable def evenMedian {m : ℕ} (v : Outcome (2*m)) : ℝ :=
  let ordered := (List.ofFn v).mergeSort (fun a b => decide (a ≤ b))
  (ordered.getD (m-1) 0 + ordered.getD m 0)/2

/-- "absolute difference ... generated by multiplicative and additive model",
the full-population calibration objective, P016-N003, Fig. 2, p. 398. -/
noncomputable def discrepancy {n : ℕ} (y : Outcome n) (z : Assignment n) (t a : ℝ) : Outcome n :=
  fun i => |multiplicativeGenerate y z a i - additiveGenerate y z t i|

/-- The 256-unit half-treated exact calibration witness of P016-N003, not paper data. -/
def calibrationZ : Assignment 256 := fun i => decide (128 ≤ i.val)

/-- P016-N003 witness outcomes: controls 64 nines/64 elevens; treated one eight,
63 nines, 63 elevens, one twelve. Printed scale/design p. 397; constructed data. -/
def calibrationY : Outcome 256 := fun i =>
  if i.val < 64 then 9 else if i.val < 128 then 11 else if i.val = 128 then 8
  else if i.val < 192 then 9 else if i.val < 255 then 11 else 12

/-- Six constant-block aggregate certificate for the actual 256 outcomes and
128/128 assignment in P016-N003, Fig. 2, p. 398.
No index-wise expansion of a real 256-coordinate sum is required. -/
theorem calibration_sum (f : ℝ → Bool → ℝ) :
    (∑ i : Fin 256, f (calibrationY i) (calibrationZ i)) =
      64*f 9 false + 64*f 11 false + f 8 true + 63*f 9 true + 63*f 11 true + f 12 true := by
  have hb : ∀ i : Fin 256, f (calibrationY i) (calibrationZ i) =
      Fin.append (fun _ : Fin 64 => f 9 false)
       (Fin.append (fun _ : Fin 64 => f 11 false)
        (Fin.append (fun _ : Fin 1 => f 8 true)
         (Fin.append (fun _ : Fin 63 => f 9 true)
          (Fin.append (fun _ : Fin 63 => f 11 true) (fun _ : Fin 1 => f 12 true))))) i := by
    intro i
    refine Fin.addCases (m := 64) (n := 192) (fun j => ?_) (fun j => ?_) i
    · have h : ¬128 ≤ j.val := by omega
      simp [Fin.append_left,calibrationY,calibrationZ,h,j.isLt]
    · refine Fin.addCases (m := 64) (n := 128) (fun k => ?_) (fun k => ?_) j
      · have h0 : ¬64+k.val < 64 := by omega
        have h1 : 64+k.val < 128 := by omega
        have hz : ¬128 ≤ 64+k.val := by omega
        simp [Fin.append_left,Fin.append_right,calibrationY,calibrationZ,h0,h1,hz]
      · refine Fin.addCases (m := 1) (n := 127) (fun k => ?_) (fun k => ?_) k
        · have hk : k.val = 0 := by omega
          simp [Fin.append_left,Fin.append_right,calibrationY,calibrationZ,hk]
        · refine Fin.addCases (m := 63) (n := 64) (fun k => ?_) (fun k => ?_) k
          · have h0 : ¬64+(64+(1+k.val)) < 64 := by omega
            have h1 : ¬64+(64+(1+k.val)) < 128 := by omega
            have h2 : 64+(64+(1+k.val)) ≠ 128 := by omega
            have h3 : 64+(64+(1+k.val)) < 192 := by omega
            have hz : 128 ≤ 64+(64+(1+k.val)) := by omega
            simp [Fin.append_left,Fin.append_right,calibrationY,calibrationZ,h0,h1,h2,h3,hz]
          · refine Fin.addCases (m := 63) (n := 1) (fun k => ?_) (fun k => ?_) k
            · have h0 : ¬64+(64+(1+(63+k.val))) < 64 := by omega
              have h1 : ¬64+(64+(1+(63+k.val))) < 128 := by omega
              have h2 : 64+(64+(1+(63+k.val))) ≠ 128 := by omega
              have h3 : ¬64+(64+(1+(63+k.val))) < 192 := by omega
              have h4 : 64+(64+(1+(63+k.val))) < 255 := by omega
              have hz : 128 ≤ 64+(64+(1+(63+k.val))) := by omega
              simp [Fin.append_left,Fin.append_right,calibrationY,calibrationZ,h0,h1,h2,h3,h4,hz]
            · have hk : k.val = 0 := by omega
              simp [Fin.append_right,calibrationY,calibrationZ,hk]
  simp_rw [hb]
  have hsum {a b : ℕ} (g : Fin a → ℝ) (h : Fin b → ℝ) :
      (∑ i : Fin (a+b), Fin.append g h i) = (∑ i, g i)+(∑ j, h j) := by
    simpa only [Fin.append_left,Fin.append_right] using Fin.sum_univ_add (Fin.append g h)
  rw [hsum (fun _ : Fin 64 => f 9 false)
       (Fin.append (fun _ : Fin 64 => f 11 false)
        (Fin.append (fun _ : Fin 1 => f 8 true)
         (Fin.append (fun _ : Fin 63 => f 9 true)
          (Fin.append (fun _ : Fin 63 => f 11 true) (fun _ : Fin 1 => f 12 true)))))]
  rw [hsum (fun _ : Fin 64 => f 11 false)
        (Fin.append (fun _ : Fin 1 => f 8 true)
         (Fin.append (fun _ : Fin 63 => f 9 true)
          (Fin.append (fun _ : Fin 63 => f 11 true) (fun _ : Fin 1 => f 12 true))))]
  rw [hsum (fun _ : Fin 1 => f 8 true)
         (Fin.append (fun _ : Fin 63 => f 9 true)
          (Fin.append (fun _ : Fin 63 => f 11 true) (fun _ : Fin 1 => f 12 true)))]
  rw [hsum (fun _ : Fin 63 => f 9 true)
          (Fin.append (fun _ : Fin 63 => f 11 true) (fun _ : Fin 1 => f 12 true))]
  rw [hsum (fun _ : Fin 63 => f 11 true) (fun _ : Fin 1 => f 12 true)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- T19(a): controls' forward discrepancies vanish and treated discrepancies
are |(a−1)y_i−t|, P016-N003 correction of the Fig. 2 calibration, p. 398. -/
theorem discrepancy_formula {n : ℕ} (y : Outcome n) (z : Assignment n) (t a : ℝ) (i : Fin n) :
    discrepancy y z t a i = if z i then |(a-1)*y i-t| else 0 := by
  cases hi : z i <;> simp [discrepancy,multiplicativeGenerate,additiveGenerate,bit,hi]
  congr 1
  ring

/-- Finite algebraic part of T19(c): matching one treated nonzero outcome
annuls its discrepancy and leaves a differently valued treated outcome
unmatched when t≠0; P016-N003 calibration correction, Fig. 2, p. 398. -/
theorem root_discrepancies {n : ℕ} (y : Outcome n) (z : Assignment n) (t : ℝ)
    (j : Fin n) (hj : z j = true) (hyj : y j ≠ 0) :
    discrepancy y z t (1+t/y j) j = 0 ∧
    (∀ i, z i = true → discrepancy y z t (1+t/y j) i = |t| * |y i/y j-1| ∧
      (t ≠ 0 → y i ≠ y j → discrepancy y z t (1+t/y j) i ≠ 0)) := by
  have hf : ∀ i, z i = true → discrepancy y z t (1+t/y j) i = |t| * |y i/y j-1| := by
    intro i hi
    rw [discrepancy_formula,if_pos hi,← abs_mul]
    congr 1
    field_simp [hyj]
    ring
  refine ⟨?_,?_⟩
  · rw [hf j hj]
    simp [hyj]
  · intro i hi
    refine ⟨hf i hi,?_⟩
    intro ht hne
    rw [hf i hi]
    apply mul_ne_zero (abs_ne_zero.mpr ht)
    apply abs_ne_zero.mpr
    intro hratio
    have hr : y i/y j = 1 := by linarith
    exact hne (by simpa using (div_eq_iff hyj).mp hr)

/-- A nonnegative finite list has nonnegative default-zero order statistics,
finite order-statistic lemma for P016-N003's full-population median, p. 398. -/
theorem list_getD_nonneg (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x) (k : ℕ) :
    0 ≤ l.getD k 0 := by
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem l 0 hk]
    exact hl _ (List.getElem_mem hk)
  · rw [List.getD_eq_default l 0 (by omega)]

/-- Finite part of T19(c): the calibration criterion is nonnegative for every
parameter because all discrepancies are absolute values, Fig. 2, p. 398. -/
theorem median_discrepancy_nonneg {m : ℕ} (y : Outcome (2*m)) (z : Assignment (2*m)) (t a : ℝ) :
    0 ≤ evenMedian (discrepancy y z t a) := by
  let l := (List.ofFn (discrepancy y z t a)).mergeSort (fun x y => decide (x ≤ y))
  have hl : ∀ x ∈ l, 0 ≤ x := by
    intro x hx
    have hmem := (List.mergeSort_perm (List.ofFn (discrepancy y z t a)) (fun x y => decide (x ≤ y))).mem_iff.mp hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    exact abs_nonneg _
  exact div_nonneg (add_nonneg (list_getD_nonneg l hl (m-1)) (list_getD_nonneg l hl m)) (by norm_num)

/-- T19(a): the forward discrepancy formula for a positive balanced
2m-unit design, P016-N003 corrected calibration explanation, Fig. 2, p. 398. -/
theorem t19_discrepancy_formula {m : ℕ} (hm : 0 < m) (y : Outcome (2*m))
    (z : Assignment (2*m)) (hz : groupSize z true = m) (t a : ℝ) (i : Fin (2*m)) :
    discrepancy y z t a i = if z i then |(a-1)*y i-t| else 0 :=
  discrepancy_formula y z t a i

/-- T19(c), component identities on the balanced calibration domain:
a root matches its chosen unit and leaves different treated outcomes unmatched,
P016-N003 correction, Fig. 2, p. 398. -/
theorem t19_root_discrepancies {m : ℕ} (hm : 0 < m) (y : Outcome (2*m))
    (z : Assignment (2*m)) (hz : groupSize z true = m) (t : ℝ)
    (j : Fin (2*m)) (hj : z j = true) (hyj : y j ≠ 0) :
    discrepancy y z t (1+t/y j) j = 0 ∧
    (∀ i, z i = true → discrepancy y z t (1+t/y j) i = |t| * |y i/y j-1| ∧
      (t ≠ 0 → y i ≠ y j → discrepancy y z t (1+t/y j) i ≠ 0)) :=
  root_discrepancies y z t j hj hyj

/-- T19(c), the median criterion is nonnegative on the positive balanced
2m-unit design, P016-N003 corrected Fig. 2 calibration, p. 398. -/
theorem t19_median_nonneg {m : ℕ} (hm : 0 < m) (y : Outcome (2*m))
    (z : Assignment (2*m)) (hz : groupSize z true = m) (t a : ℝ) :
    0 ≤ evenMedian (discrepancy y z t a) :=
  median_discrepancy_nonneg y z t a

/-- Finite counting lemma: the length of a filtered index list equals the
number of included units, supporting P016-N003 calibration, Fig. 2, p. 398. -/
theorem filter_indices_length {n : ℕ} (p : Fin n → Bool) :
    ((List.ofFn id).filter p).length = ∑ i, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    have hi := ih (fun i => p i.succ)
    have htail : (List.ofFn fun i : Fin n => i.succ) =
        (List.ofFn (id : Fin n → Fin n)).map Fin.succ := by simp
    simp only [id_eq] at *
    rw [htail]
    cases hp : p 0 <;> simp only [List.filter_cons, hp, Bool.false_eq_true,
      ↓reduceIte, List.length_cons, List.filter_map, List.length_map, Function.comp_def]
    all_goals omega

/-- P016-N003 order-statistic lemma: with m control zeros and m nonnegative treated
values, the full even median is half the smallest treated value. This uses
the actual sorted list, including multiplicities, Fig. 2, p. 398. -/
theorem even_median_partition {m : ℕ} (hm : 0 < m)
    (v : Outcome (2*m)) (z : Assignment (2*m))
    (hz : groupSize z true = m) (hv : ∀ i, 0 ≤ v i)
    (hc : ∀ i, z i = false → v i = 0) :
    evenMedian v = (1/2) * sInf {x : ℝ | ∃ i, z i = true ∧ x = v i} := by
  let indices : List (Fin (2*m)) := List.ofFn id
  let controls := indices.filter (fun i => !(z i))
  let treated := (indices.filter z).map v
  let ordered := treated.mergeSort (fun a b => decide (a ≤ b))
  have htlen : treated.length = m := by
    simp only [treated, List.length_map]
    simpa [indices, groupSize] using (filter_indices_length z).trans hz
  have hclen : controls.length = m := by
    have hp := List.length_eq_length_filter_add (l := indices) z
    have hi : indices.length = 2*m := by simp [indices]
    have ht : (indices.filter z).length = m := by simpa [treated] using htlen
    dsimp only [controls]
    omega
  have hcmap : controls.map v = List.replicate m 0 := by
    calc
      controls.map v = List.replicate controls.length 0 := by
        apply List.map_eq_replicate_iff.mpr
        intro i hi
        have hzi : z i = false := by simpa using (List.mem_filter.mp hi).2
        exact hc i hzi
      _ = List.replicate m 0 := by rw [hclen]
  have hperm : (List.replicate m 0 ++ ordered).Perm (List.ofFn v) := by
    have hp := (List.filter_append_perm (fun i => !(z i)) indices).map v
    simp only [List.map_append, Bool.not_not] at hp
    have hmapped : indices.map v = List.ofFn v := by simp [indices]
    rw [hcmap, hmapped] at hp
    exact (List.Perm.refl _ |>.append (List.mergeSort_perm treated _)).trans hp
  have hmem : ∀ x, x ∈ ordered ↔ ∃ i, z i = true ∧ x = v i := by
    intro x
    rw [(List.mergeSort_perm treated _).mem_iff]
    simp only [treated, List.mem_map, List.mem_filter, indices, List.mem_ofFn]
    constructor
    · rintro ⟨i,⟨_,hi⟩,rfl⟩
      exact ⟨i,hi,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨i,⟨⟨i,rfl⟩,hi⟩,rfl⟩
  have hnonneg : ∀ x ∈ ordered, 0 ≤ x := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := (hmem x).mp hx
    exact hv i
  have hsort : ordered.SortedLE := List.sortedLE_mergeSort
  have hall : (List.replicate m 0 ++ ordered).SortedLE := by
    apply List.sortedLE_append.mpr
    refine ⟨List.sortedLE_replicate m, hsort, ?_⟩
    intro a ha b hb
    have : a = 0 := List.mem_replicate.mp ha |>.2
    simpa [this] using hnonneg b hb
  have hsorted : (List.ofFn v).mergeSort (fun a b => decide (a ≤ b)) =
      List.replicate m 0 ++ ordered := by
    exact ((List.mergeSort_perm (List.ofFn v) _).trans hperm.symm).eq_of_sortedLE
      List.sortedLE_mergeSort hall
  have holen : ordered.length = m := by simp [ordered, htlen]
  have hfirst : ordered.getD 0 0 = sInf {x : ℝ | ∃ i, z i = true ∧ x = v i} := by
    have hzero : 0 < ordered.length := by omega
    rw [List.getD_eq_getElem ordered 0 hzero]
    apply le_antisymm
    · apply le_csInf
      · refine ⟨ordered[0],?_⟩
        exact (hmem _).mp (List.getElem_mem hzero)
      · intro x hx
        have hxmem : x ∈ ordered := (hmem x).mpr hx
        obtain ⟨k,hk,hkx⟩ := List.mem_iff_getElem.mp hxmem
        rw [← hkx]
        exact hsort.getElem_le_getElem_of_le (Nat.zero_le k)
    · apply csInf_le
      · exact ⟨0,fun x hx => hnonneg x ((hmem x).mpr hx)⟩
      · exact (hmem _).mp (List.getElem_mem hzero)
  unfold evenMedian
  rw [hsorted]
  dsimp only
  have hleft : (List.replicate m (0 : ℝ) ++ ordered).getD (m-1) 0 = 0 := by
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    exact List.getD_replicate (x := (0 : ℝ)) (y := 0) (by omega)
  have hright : (List.replicate m (0 : ℝ) ++ ordered).getD m 0 = ordered.getD 0 0 := by
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.sub_self]
  rw [hleft, hright, hfirst]
  ring

/-- T19(b): the median criterion sees only the smallest discrepancy of a
treated unit, P016-N003 corrected calibration explanation, Fig. 2, p. 398. -/
theorem t19_median_identity {m : ℕ} (hm : 0 < m) (y : Outcome (2*m))
    (z : Assignment (2*m)) (hz : groupSize z true = m) (t a : ℝ) :
    evenMedian (discrepancy y z t a) = (1/2) *
      sInf {v : ℝ | ∃ i, z i = true ∧ v = |(a-1)*y i-t|} := by
  have hc : ∀ i, z i = false → discrepancy y z t a i = 0 := by
    intro i hi
    simp [discrepancy_formula, hi]
  have hp := even_median_partition hm (discrepancy y z t a) z hz
    (fun i => abs_nonneg _) hc
  have hset : {x : ℝ | ∃ i, z i = true ∧ x = discrepancy y z t a i} =
      {x : ℝ | ∃ i, z i = true ∧ x = |(a-1)*y i-t|} := by
    ext x
    constructor <;> rintro ⟨i,hi,hx⟩ <;> refine ⟨i,hi,?_⟩ <;>
      simpa [discrepancy_formula,hi] using hx
  simpa only [hset] using hp

/-- T19(c): matching any nonzero treated unit gives a global zero of the median
criterion and leaves every differently valued treated unit unmatched if t≠0,
P016-N003 correction, Fig. 2, p. 398. -/
theorem t19_calibration_roots {m : ℕ} (hm : 0 < m) (y : Outcome (2*m))
    (z : Assignment (2*m)) (hz : groupSize z true = m) (t : ℝ) (j : Fin (2*m))
    (hj : z j = true) (hyj : y j ≠ 0) :
    evenMedian (discrepancy y z t (1+t/y j)) = 0 ∧
    (∀ a, 0 ≤ evenMedian (discrepancy y z t a)) ∧
    (∀ i, z i = true → discrepancy y z t (1+t/y j) i = |t| * |y i/y j-1| ∧
      (t ≠ 0 → y i ≠ y j → discrepancy y z t (1+t/y j) i ≠ 0)) := by
  refine ⟨?_,?_,?_⟩
  · rw [t19_median_identity hm y z hz]
    have hroot : |((1+t/y j)-1)*y j-t| = 0 := by
      have h := (root_discrepancies y z t j hj hyj).1
      simpa [discrepancy_formula,hj] using h
    have hzero : (0 : ℝ) ∈ {x : ℝ | ∃ i, z i = true ∧ x = |((1+t/y j)-1)*y i-t|} :=
      ⟨j,hj,hroot.symm⟩
    have hinf : sInf {x : ℝ | ∃ i, z i = true ∧ x = |((1+t/y j)-1)*y i-t|} = 0 := by
      apply le_antisymm
      · exact csInf_le ⟨0,fun x ⟨i,hi,hx⟩ => hx ▸ abs_nonneg _⟩ hzero
      · apply le_csInf ⟨0,hzero⟩
        rintro x ⟨i,hi,rfl⟩
        exact abs_nonneg _
    rw [hinf,mul_zero]
  · intro a
    exact median_discrepancy_nonneg y z t a
  · exact (root_discrepancies y z t j hj hyj).2

/-- T19(d): additive and multiplicative adjustments reduce the treated mean
by t and (1−1/a) times its observed mean, P016-N003 corrected Fig. 2 comparison. -/
theorem t19_mean_reductions {n : ℕ} (Y : Outcome n) (z : Assignment n)
    (h1 : 0 < groupSize z true) (t a : ℝ) (ha : a ≠ 0) :
    groupMean Y z true - groupMean (additiveAdjust Y z t) z true = t ∧
    groupMean Y z true - groupMean (multiplicativeAdjust Y z a) z true =
      (1-1/a)*groupMean Y z true := by
  constructor
  · rw [(additive_group_means Y z h1 t).2]
    ring
  · have hm : groupMean (multiplicativeAdjust Y z a) z true = (1/a)*groupMean Y z true := by
      calc
        _ = groupMean (fun i => (1/a)*Y i) z true := by
          apply group_mean_congr
          intro i hi
          simp [multiplicativeAdjust,hi,bit,div_eq_mul_inv,mul_comm]
        _ = _ := group_mean_scale Y z true (1/a)
    rw [hm]
    ring

/-- Index-count certificate for the 127 nonzero treated discrepancies in the
256-unit P016-N003 witness, Fig. 2, p. 398. This is
a small natural-number comparison certificate, with no real-valued enumeration. -/
theorem calibration_index_count :
    (Finset.univ.filter (fun i : Fin 256 => 129 ≤ i.val)).card = 127 := by decide

/-- T18: a full-sample median of zero coexists with 127 unmatched treated units
and different treated mean shifts, P016-N003 exact 256-unit witness, Fig. 2, p. 398.
The variance divisor is 256, not the sample-variance divisor 255. -/
theorem t18_calibration_witness :
    let y := calibrationY
    let z := calibrationZ
    let t : ℝ := 34/99
    let a : ℝ := 413/396
    let d := discrepancy y z t a
    groupSize z false = 128 ∧ groupSize z true = 128 ∧
    groupMean y z false = 10 ∧ groupMean y z true = 10 ∧ tss y/256 = 131/128 ∧
    a = 1+t/8 ∧
    (∀ i, d i = if i.val < 129 then 0 else if i.val < 192 then t/8
      else if i.val < 255 then 3*t/8 else t/2) ∧
    (Finset.univ.filter (fun i => z i = true ∧ d i ≠ 0)).card = 127 ∧
    evenMedian (m := 128) d = 0 ∧
    groupMean (multiplicativeGenerate y z a) z true - 10 = 85/198 ∧
    groupMean (additiveGenerate y z t) z true - 10 = t ∧
    (85/198 : ℝ) = (5/4)*t ∧
    10-groupMean (multiplicativeAdjust y z a) z true = 170/413 ∧
    10-groupMean (additiveAdjust y z t) z true = t ∧
    (170/413 : ℝ)/t = 495/413 ∧ (1 : ℝ) < 495/413 := by
  classical
  dsimp only
  let y := calibrationY
  let z := calibrationZ
  let t : ℝ := 34/99
  let a : ℝ := 413/396
  let d := discrepancy y z t a
  have hN : ∀ g, groupSize z g = 128 := by
    intro g
    have hs := calibration_sum (fun _ b => if b = g then (1 : ℝ) else 0)
    have hsval : (∑ i, if z i = g then (1 : ℝ) else 0) = 128 := by
      cases g <;> norm_num [z] at hs ⊢ <;> exact hs
    have hcast : (groupSize z g : ℝ) = 128 := by
      simpa only [groupSize,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using hsval
    exact_mod_cast hcast
  have hgs : ∀ g, groupSum y z g = 1280 := by
    intro g
    have hs := calibration_sum (fun u b => if b = g then u else 0)
    cases g <;> norm_num at hs <;> exact hs
  have hm : ∀ g, groupMean y z g = 10 := by
    intro g
    rw [groupMean,hgs,hN]
    norm_num
  have htotal : (∑ i, y i) = 2560 := by
    have hs := group_sums y z
    rw [hgs,hgs] at hs
    linarith
  have hpm : pooledMean y = 10 := by
    rw [pooledMean,htotal]
    norm_num
  have hvar : tss y/256 = 131/128 := by
    have hs := calibration_sum (fun u _ => (u-10)^2)
    norm_num at hs
    unfold tss
    rw [hpm]
    change (∑ i, (calibrationY i-10)^2)/256 = 131/128
    rw [hs]
    norm_num
  have hd : ∀ i, d i = if i.val < 129 then 0 else if i.val < 192 then t/8
      else if i.val < 255 then 3*t/8 else t/2 := by
    intro i
    change discrepancy y z t a i = _
    rw [discrepancy_formula]
    dsimp only [y,z,t,a]
    simp only [calibrationY,calibrationZ,decide_eq_true_eq]
    split_ifs <;> norm_num <;> omega
  have hcount : (Finset.univ.filter (fun i => z i = true ∧ d i ≠ 0)).card = 127 := by
    have hevent : (Finset.univ.filter (fun i => z i = true ∧ d i ≠ 0)) =
        Finset.univ.filter (fun i : Fin 256 => 129 ≤ i.val) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hd]
      dsimp only [z,t]
      simp only [calibrationZ,decide_eq_true_eq]
      split_ifs <;> norm_num <;> omega
    rw [hevent]
    exact calibration_index_count
  have hmed : evenMedian (m := 128) d = 0 := by
    have hy128 : y (⟨128,by decide⟩ : Fin 256) = 8 := by norm_num [y,calibrationY]
    have hz128 : z (⟨128,by decide⟩ : Fin 256) = true := by norm_num [z,calibrationZ]
    have ha : a = 1+t/y (⟨128,by decide⟩ : Fin 256) := by norm_num [a,t,y,calibrationY]
    have hr := (t19_calibration_roots (m := 128) (by norm_num) y z (hN true) t
      ⟨128,by decide⟩ hz128 (by rw [hy128]; norm_num)).1
    simpa only [← ha] using hr
  have hmeanmg : groupMean (multiplicativeGenerate y z a) z true = a*10 := by
    calc
      _ = groupMean (fun i => a*y i) z true := by
        apply group_mean_congr
        intro i hi
        simp only [multiplicativeGenerate,bit,hi,↓reduceIte]
        ring
      _ = a*groupMean y z true := group_mean_scale y z true a
      _ = a*10 := by rw [hm]
  have hmeanag : groupMean (additiveGenerate y z t) z true = 10+t := by
    calc
      _ = groupMean (fun i => y i+t) z true := by
        apply group_mean_congr
        intro i hi
        simp [additiveGenerate,bit,hi]
      _ = groupMean y z true+t := group_mean_shift y z true (by rw [hN]; norm_num) t
      _ = 10+t := by rw [hm]
  have hreductions := t19_mean_reductions y z (by rw [hN]; norm_num) t a (by norm_num [a])
  have hmult : 10-groupMean (multiplicativeAdjust y z a) z true = 170/413 := by
    calc
      _ = (1-1/a)*10 := by simpa only [hm] using hreductions.2
      _ = _ := by norm_num [a]
  have hadd : 10-groupMean (additiveAdjust y z t) z true = t := by
    simpa only [hm] using hreductions.1
  refine ⟨hN false,hN true,hm false,hm true,hvar,?_,hd,hcount,hmed,?_,?_,?_,hmult,hadd,?_,?_⟩
  · norm_num [a,t]
  · rw [hmeanmg]
    norm_num [a]
  · rw [hmeanag]
    ring
  · norm_num [t]
  · norm_num [t]
  · norm_num


/-- Exchanging treated and control labels preserves the complete balanced
design, p. 397 and the P016-N003 corrected expected-mean calculation. -/
noncomputable def balancedComplement (m : ℕ) : Equiv.Perm (Balanced (2*m) m) := by
  classical
  let f : Balanced (2*m) m → Balanced (2*m) m := fun z =>
    ⟨fun i => !(z.val i),by
      have hg : groupSize (fun i => !(z.val i)) true = groupSize z.val false := by
        unfold groupSize
        apply Finset.sum_congr rfl
        intro i _; cases hi : z.val i <;> simp [hi]
      rw [hg]
      have hs := group_sizes z.val
      have hz := z.property
      omega⟩
  exact ⟨f,f,fun z => by apply Subtype.ext; funext i; simp [f],
    fun z => by apply Subtype.ext; funext i; simp [f]⟩

/-- Each balanced design has positive cardinality: treat the first m of 2m
units, complete randomization p. 397, P016-N003 mean-shift correction. -/
theorem balanced_card_pos (m : ℕ) : 0 < Fintype.card (Balanced (2*m) m) := by
  have hn : Nonempty (Balanced (2*m) m) := by
    rw [two_mul]
    refine ⟨⟨Fin.append (fun _ : Fin m => true) (fun _ : Fin m => false),?_⟩⟩
    unfold groupSize
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right]
    norm_num
  exact Fintype.card_pos_iff.mpr hn

/-- The complete balanced design makes the treated mean unbiased for the
finite population mean, p. 397, finite identity for the P016-N003 correction. -/
theorem balanced_expected_mean {m : ℕ} (hm : 0 < m) (y : Outcome (2*m)) :
    uniformExpectation (Balanced (2*m) m) (fun z => groupMean y z.val true) = pooledMean y := by
  classical
  have hcomp : ∀ z : Balanced (2*m) m,
      groupMean y ((balancedComplement m) z).val true = groupMean y z.val false := by
    intro z
    have hz : ∀ i, ((balancedComplement m) z).val i = Bool.not (z.val i) := by intro i; rfl
    have hiff : ∀ i, ((balancedComplement m) z).val i = true ↔ z.val i = false := by
      intro i; rw [hz]; cases hi : z.val i <;> simp
    simp only [groupMean,groupSum,groupSize,hiff]
  have hsum : (∑ z : Balanced (2*m) m, groupMean y z.val true) =
      ∑ z : Balanced (2*m) m, groupMean y z.val false := by
    simpa only [hcomp] using (Equiv.sum_comp (balancedComplement m) (fun z : Balanced (2*m) m => groupMean y z.val true)).symm
  have hpoint : ∀ z : Balanced (2*m) m,
      groupMean y z.val true+groupMean y z.val false = 2*pooledMean y := by
    intro z
    have hz1 := z.property
    have hz0 : groupSize z.val false = m := by have hs := group_sizes z.val; omega
    have hc := design_mean_constraint (by omega : 0 < 2*m) y (fun z : Balanced (2*m) m => z.val)
      m m hm hm (fun z => ⟨by have hs := group_sizes z.val; have hz := z.property; omega,z.property⟩) z
    have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
    have hcast : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_cast
    rw [hcast] at hc
    apply (mul_left_cancel₀ hm0)
    calc
      (m : ℝ)*(groupMean y z.val true+groupMean y z.val false) =
        (m : ℝ)*groupMean y z.val true+(m : ℝ)*groupMean y z.val false := by ring
      _ = (2*(m : ℝ))*pooledMean y := hc
      _ = (m : ℝ)*(2*pooledMean y) := by ring
  have hall := congrArg (fun f : Balanced (2*m) m → ℝ => ∑ z, f z) (funext hpoint)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hall
  rw [← hsum] at hall
  unfold uniformExpectation
  have hcard : (Fintype.card (Balanced (2*m) m) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (balanced_card_pos m))
  apply (div_eq_iff hcard).mpr
  linarith

/-- T19(d): under complete balanced randomization and no effect, the expected
treated mean is the population mean, so expected reductions are t and
(1−1/a)bar y; P016-N003 correction, design p. 397 and Fig. 2, p. 398. -/
theorem t19_expected_reductions {m : ℕ} (hm : 0 < m) (y : Outcome (2*m)) (t a : ℝ) (ha : a ≠ 0) :
    uniformExpectation (Balanced (2*m) m) (fun z => groupMean y z.val true) = pooledMean y ∧
    uniformExpectation (Balanced (2*m) m) (fun z =>
      groupMean y z.val true - groupMean (additiveAdjust y z.val t) z.val true) = t ∧
    uniformExpectation (Balanced (2*m) m) (fun z =>
      groupMean y z.val true - groupMean (multiplicativeAdjust y z.val a) z.val true) =
      (1-1/a)*pooledMean y := by
  have hcard : (Fintype.card (Balanced (2*m) m) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (balanced_card_pos m))
  refine ⟨balanced_expected_mean hm y,?_,?_⟩
  · have hf : (fun z : Balanced (2*m) m =>
        groupMean y z.val true-groupMean (additiveAdjust y z.val t) z.val true) = fun _ => t := by
      funext z
      exact (t19_mean_reductions y z.val (by simpa [z.property] using hm) t a ha).1
    rw [hf]
    simp [uniformExpectation,Finset.sum_const,hcard]
  · have hf : (fun z : Balanced (2*m) m =>
        groupMean y z.val true-groupMean (multiplicativeAdjust y z.val a) z.val true) =
        fun z => (1-1/a)*groupMean y z.val true := by
      funext z
      exact (t19_mean_reductions y z.val (by simpa [z.property] using hm) t a ha).2
    rw [hf]
    unfold uniformExpectation
    rw [← Finset.mul_sum]
    rw [mul_div_assoc]
    exact congrArg ((1-1/a) * ·) (balanced_expected_mean hm y)

/-- T19(e): the unique parameter matching expected ADJUSTED mean drops is
bar y/(bar y−t), P016-N003 corrected matching target, Fig. 2, p. 398. -/
theorem t19_matched_parameter (μ t a : ℝ) (hμ : μ ≠ 0) (hμt : μ ≠ t) :
    (1-1/a)*μ = t ↔ a = μ/(μ-t) := by
  have hd : μ-t ≠ 0 := sub_ne_zero.mpr hμt
  by_cases ha : a = 0
  · subst a
    simp only [div_zero,sub_zero,one_mul]
    constructor
    · intro h; exact False.elim (hμt h)
    · intro h; exact False.elim ((div_ne_zero hμ hd) h.symm)
  · constructor
    · intro h
      apply (eq_div_iff hd).mpr
      field_simp at h
      nlinarith
    · intro h
      rw [h]
      field_simp
      ring

/-- T19(f): the zero-criterion parameter differs from the matched parameter
and the two mean reductions differ in the P016-N003 witness. This arithmetic lemma
does not by itself establish the witness's median or group sums. -/
theorem t19_mismatch_numbers :
    (10 : ℝ)/(10-34/99) = 495/478 ∧ (413/396 : ℝ) ≠ 495/478 ∧
    (10 : ℝ)*(1-1/(413/396)) = 170/413 ∧ (170/413 : ℝ) ≠ 34/99 := by norm_num

/-- "c_i(v)=beta+(1−v_i)(1−beta)exp(−tau²(v^T S)_i)",
componentwise multiplier in equation (3), p. 399. -/
noncomputable def modelMultiplier {n : ℕ} (S : Fin n → Fin n → ℝ) (β τ : ℝ)
    (v : Assignment n) (i : Fin n) : ℝ :=
  β+(1-bit (v i))*(1-β)*Real.exp (-(τ^2)*treatedNeighbors S v i)

/-- "H(y_z,w,beta,tau)_i=(c_i(w)/c_i(z))y_{z,i}", equation (3), p. 399. -/
noncomputable def modelMap {n : ℕ} (S : Fin n → Fin n → ℝ) (β τ : ℝ)
    (y : Outcome n) (z w : Assignment n) : Outcome n :=
  fun i => modelMultiplier S β τ w i / modelMultiplier S β τ z i * y i

/-- T20(a): substituting the constant additive potential-outcome relationship
in the printed observed-data identity gives the uniformity outcome,
p. 396, steps (1)–(2), headline H2. -/
theorem t20_additive_identity (y0 y1 Y τ : ℝ) (z : Bool)
    (hY : Y = bit z*y1+(1-bit z)*y0) (hy : y1 = y0+τ) : y0 = Y-bit z*τ := by
  rw [hY,hy]
  ring

/-- T20(b1): positive beta and nonnegative adjacency weights make every
multiplier in (3) positive, p. 399; the ratio in (3) is therefore defined. -/
theorem t20_model_positive {n : ℕ} (S : Fin n → Fin n → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (β τ : ℝ) (hβ : 0 < β) (v : Assignment n) (i : Fin n) :
    0 < modelMultiplier S β τ v i := by
  have hn : 0 ≤ treatedNeighbors S v i := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg
    · cases v j <;> norm_num [bit]
    · exact hS j i
  have he0 : 0 ≤ Real.exp (-(τ^2)*treatedNeighbors S v i) := (Real.exp_pos _).le
  have he1 : Real.exp (-(τ^2)*treatedNeighbors S v i) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg τ]) hn)
  cases hv : v i
  · simp only [modelMultiplier,bit,hv,Bool.false_eq_true,↓reduceIte,sub_zero,one_mul]
    by_cases hb1 : β ≤ 1
    · have hprod := mul_nonneg (sub_nonneg.mpr hb1) he0
      linarith
    · have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hb1)) (sub_nonneg.mpr he1)
      nlinarith
  · simpa [modelMultiplier,bit,hv] using hβ

/-- T20(b2): the no-treated assignment has multiplier one and (3) then
adjusts y_z to y_z/c(z), p. 399, mapping to the uniformity trial. -/
theorem t20_zero_assignment {n : ℕ} (S : Fin n → Fin n → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (β τ : ℝ) (hβ : 0 < β)
    (y : Outcome n) (z : Assignment n) :
    (∀ i, modelMultiplier S β τ (fun _ => false) i = 1) ∧
    modelMap S β τ y z (fun _ => false) = fun i => y i/modelMultiplier S β τ z i := by
  have hc : ∀ i, modelMultiplier S β τ (fun _ => false) i = 1 := by
    intro i
    simp [modelMultiplier,treatedNeighbors,bit]
  refine ⟨hc,?_⟩
  funext i
  simp [modelMap,hc,div_eq_mul_inv,mul_comm]

/-- T20(b3): equation (3) is identity at the same assignment and composes
consistently through an intermediate assignment, p. 399. -/
theorem t20_model_composition {n : ℕ} (S : Fin n → Fin n → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (β τ : ℝ) (hβ : 0 < β) (y : Outcome n) (z w w' : Assignment n) :
    modelMap S β τ y z z = y ∧
    modelMap S β τ (modelMap S β τ y z w) w w' = modelMap S β τ y z w' := by
  have hc : ∀ v i, modelMultiplier S β τ v i ≠ 0 :=
    fun v i => ne_of_gt (t20_model_positive S hS β τ hβ v i)
  constructor <;> funext i
  · simp [modelMap,hc]
  · unfold modelMap
    field_simp [hc]

/-- T20(b4): under the true model (3), adjustment recovers the SAME no-treated
outcome for every assignment, p. 399, headline H2. -/
theorem t20_model_uniformity {n : ℕ} (S : Fin n → Fin n → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (β τ : ℝ) (hβ : 0 < β) (y0 : Outcome n) (y : Assignment n → Outcome n)
    (hmodel : ∀ z i, y z i = modelMultiplier S β τ z i*y0 i) :
    ∀ z, (fun i => y z i/modelMultiplier S β τ z i) = y0 := by
  intro z
  funext i
  rw [hmodel z i]
  exact mul_div_cancel_left₀ _ (ne_of_gt (t20_model_positive S hS β τ hβ z i))

/-- T21(i),(ii): in the paper's 256-unit, 128-treated uniform design, true
(beta,tau)=(2,1/2) gives fixed adjusted outcomes, and EVERY statistic has valid
inclusive exact upper/lower/doubled-minimum p values at .05 (also strict cutoff),
headline H4, p. 400. No effect-increasing premise is needed. -/
theorem t21_exact_level (P : FiniteLaw (Balanced 256 128))
    (hP : ∀ z, P.weight z = 1/(Nat.choose 256 128 : ℝ))
    (S : Fin 256 → Fin 256 → ℝ) (hsym : ∀ i j, S i j = S j i)
    (hbin : ∀ i j, S i j = 0 ∨ S i j = 1) (y0 : Outcome 256)
    (T : Outcome 256 → Assignment 256 → ℝ) :
    let Y := fun z : Balanced 256 128 => fun i => modelMultiplier S 2 (1/2) z.val i*y0 i
    let u := fun z : Balanced 256 128 => fun i => Y z i/modelMultiplier S 2 (1/2) z.val i
    let s := fun z : Balanced 256 128 => T (u z) z.val
    (∀ z, u z = y0) ∧
    (∀ p ∈ ({upperP P s,lowerP P s,fun z => doubledP (lowerP P s z) (upperP P s z)} :
      Finset (Balanced 256 128 → ℝ)),
      mass P (fun z => p z ≤ 1/20) ≤ 1/20 ∧ mass P (fun z => p z < 1/20) ≤ 1/20) := by
  classical
  dsimp
  have hS : ∀ i j, 0 ≤ S i j := by
    intro i j; rcases hbin i j with h | h <;> rw [h] <;> norm_num
  have hm : ∀ z : Balanced 256 128,
      (fun i => modelMultiplier S 2 (1/2) z.val i*y0 i/modelMultiplier S 2 (1/2) z.val i) = y0 := by
    intro z; funext i
    exact mul_div_cancel_left₀ _ (ne_of_gt (t20_model_positive S hS 2 (1/2) (by norm_num) z.val i))
  refine ⟨hm,?_⟩
  intro p hp
  have hbound : mass P (fun z => p z ≤ 1/20) ≤ 1/20 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact upper_tail_bound P _ _ (by norm_num)
    · exact lower_tail_bound P _ _ (by norm_num)
    · exact two_tail_bound P _ _ (by norm_num) (by norm_num)
  exact ⟨hbound,(mass_mono P (fun _ h => h.le)).trans hbound⟩

/-- T21(iii): with fresh iid references and one fixed statistic under the true
network model, the printed strict .05 rule has size bounded by 50/1001 at
B=1000 and 500/10001 at B=10000, headline H4, p. 400. These are finite-sample
guarantees, not the paper's reported empirical rates of 4% and 2%. -/
theorem t21_sampled_level (P : FiniteLaw (Balanced 256 128))
    (hP : ∀ z, P.weight z = 1/(Nat.choose 256 128 : ℝ))
    (S : Fin 256 → Fin 256 → ℝ) (hsym : ∀ i j, S i j = S j i)
    (hbin : ∀ i j, S i j = 0 ∨ S i j = 1) (y0 : Outcome 256)
    (T : Outcome 256 → Assignment 256 → ℝ) :
    let Y := fun z : Balanced 256 128 => fun i => modelMultiplier S 2 (1/2) z.val i*y0 i
    let u := fun z : Balanced 256 128 => fun i => Y z i/modelMultiplier S 2 (1/2) z.val i
    let s := fun z : Balanced 256 128 => T (u z) z.val
    iidMass P 1001 (fun draw => rawP (fun b : Fin 1000 => s (draw b.succ)) (s (draw 0)) < 1/20) ≤
      50/1001 ∧ (50/1001 : ℝ) < 1/20 ∧
    iidMass P 10001 (fun draw => rawP (fun b : Fin 10000 => s (draw b.succ)) (s (draw 0)) < 1/20) ≤
      500/10001 ∧ (500/10001 : ℝ) < 1/20 := by
  let Y := fun z : Balanced 256 128 => fun i => modelMultiplier S 2 (1/2) z.val i*y0 i
  let u := fun z : Balanced 256 128 => fun i => Y z i/modelMultiplier S 2 (1/2) z.val i
  let s := fun z : Balanced 256 128 => T (u z) z.val
  have hS : ∀ i j, 0 ≤ S i j := by
    intro i j
    rcases hbin i j with h | h <;> rw [h] <;> norm_num
  have hu : ∀ z, u z = y0 := by
    intro z; funext i
    have hp := t20_model_positive S hS 2 (1/2) (by norm_num) z.val i
    dsimp [u,Y]
    field_simp [ne_of_gt hp]
  have hs : s = fun z : Balanced 256 128 => T y0 z.val := by
    funext z
    exact congrArg (fun v => T v z.val) (hu z)
  change iidMass P 1001 (fun draw => rawP (fun b : Fin 1000 => s (draw b.succ)) (s (draw 0)) < 1/20) ≤
      50/1001 ∧ (50/1001 : ℝ) < 1/20 ∧
    iidMass P 10001 (fun draw => rawP (fun b : Fin 10000 => s (draw b.succ)) (s (draw 0)) < 1/20) ≤
      500/10001 ∧ (500/10001 : ℝ) < 1/20
  rw [hs]
  have h1000 := iid_strict_bound P 1000 (by decide) (fun z => T y0 z.val) (1/20) (by norm_num) (by norm_num)
  have h10000 := iid_strict_bound P 10000 (by decide) (fun z => T y0 z.val) (1/20) (by norm_num) (by norm_num)
  norm_num at h1000 h10000
  exact ⟨h1000,by norm_num,h10000,by norm_num⟩

end AronowAudit.P016
