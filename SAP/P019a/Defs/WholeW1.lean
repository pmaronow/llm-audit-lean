import Mathlib
import SAP.P019a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical
universe u

/-- Full joint law of k independent fair Boolean coordinates. -/
def wholeFairBits {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (k : ℕ)
    (bits : Fin k → Ω → Bool) : Prop :=
  ∀ a : Fin k → Bool, P.prob (fun ω => ∀ i, bits i ω = a i) = (1/2 : ℝ)^k

/-- Independence expressed by all point-mass factorizations; the variables have finite range. -/
def wholeIndependent {Ω A B : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f : Ω → A) (g : Ω → B) : Prop :=
  ∀ a b, P.prob (fun ω => f ω = a ∧ g ω = b) =
    P.prob (fun ω => f ω = a) * P.prob (fun ω => g ω = b)

/-- Numerical population table, including the existence of every conditional law. -/
def wholeCellTable {Ω : Type*} [Fintype Ω] (S : Study Ω)
    (p m v : Bool → Bool → ℝ) : Prop :=
  ∀ z y, 0 < S.law.prob (S.cell z y) ∧
    S.law.prob (S.cell z y) = p z y ∧ S.listMean z y = m z y ∧
    S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y) = v z y

/-- Observable mass function of the sixteen-atom finite-sample witness. -/
def wholeT3Mass (y z : Bool) (v : ℕ) : ℝ :=
  match y, z, v with
  | false, false, 0 => 3/16
  | false, false, 1 => 3/16
  | false, true, 0 => 1/8
  | false, true, 1 => 3/16
  | false, true, 2 => 1/16
  | true, false, 0 => 1/16
  | true, false, 1 => 1/16
  | true, true, 1 => 1/16
  | true, true, 2 => 1/16
  | _, _, _ => 0

/-- Additional eight-atom counterexample: X=1, W=B+C, Y=1{C=Z}, V=W+Z. -/
def wholeDiagnosisEight : Study (Fin 8) where
  law := uniformFin 8 (by norm_num)
  W := fun ω => (if fairBit ω 0 then 1 else 0) + (if fairBit ω 1 then 1 else 0)
  X := fun _ => true
  Y := fun ω => decide (fairBit ω 1 = fairBit ω 2)
  Z := fun ω => fairBit ω 2
  V := fun ω => (if fairBit ω 0 then 1 else 0) + (if fairBit ω 1 then 1 else 0) +
    (if fairBit ω 2 then 1 else 0)

/-- The two potential direct responses in the sixteen-atom diagnostic population. -/
def wholeDiagnosisPotential (z : Bool) (ω : Fin 16) : Bool :=
  fairBit ω 2 && decide (fairBit ω 1 = z)

/-- Complete finite population data for the Lemma 2 counterexample. -/
def wholeT3Population : Prop :=
  let S := finiteSampleWitness
  wholeFairBits S.law 4 (fun i ω => fairBit ω i.val) ∧
  wholeCellTable S (fun _ y => if y then 1/8 else 3/8)
    (fun z y => if z then (if y then 3/2 else 5/6) else 1/2)
    (fun z y => if z && !y then 17/36 else 1/4) ∧
  S.law.variance (fun ω => bitVal (S.Y ω)) = 3/16 ∧
  S.law.variance (fun ω => bitVal (S.Z ω)) = 1/4 ∧
  S.mu = 1/2 ∧ S.truthRate = 1/2 ∧ S.gamma = 1/2 ∧
  S.law.prob (fun ω => S.Y ω = true) = S.mu*S.truthRate ∧
  S.law.prob (fun ω => S.Y ω = true) = 1/4 ∧
  (∀ y z v, S.law.prob (fun ω => S.Y ω = y ∧ S.Z ω = z ∧ S.V ω = v) =
    wholeT3Mass y z v)

/-- The zero-completed n=1 means and their product expectations. -/
def wholeT3Singleton : Prop :=
  let S := finiteSampleWitness
  let P := S.law.iid 1
  let A := @Study.sampleA (Fin 16) _ S 1
  let M := fun z (s : Fin 1 → Fin 16) => S.cellMean s z false 0
  P.mean A = 3/4 ∧
  P.mean (M true) = 5/16 ∧ P.mean (fun s => A s*M true s) = 5/16 ∧
  P.mean (M false) = 3/16 ∧ P.mean (fun s => A s*M false s) = 3/16

/-- General conditional count law for the finite-sample counterexample, including n=0,1. -/
def wholeT3Counts : Prop :=
  let S := finiteSampleWitness
  ∀ n k : ℕ, k ≤ n →
    let P := S.law.iid n
    let K := fun s => S.negativeCount s = k
    0 < P.prob K ∧
    (∀ z : Bool, ∀ i : ℕ, i ≤ k →
      P.ce (fun s => if S.cellCount s z false = i then 1 else 0) K =
        (Nat.choose k i : ℝ)*(1/2 : ℝ)^k) ∧
    (∀ z : Bool,
      (∑ i ∈ Finset.Icc 1 k,
        P.ce (fun s => if S.cellCount s z false = i then 1 else 0) K) =
          1-(1/2 : ℝ)^k) ∧
    1-(1/2 : ℝ)^k < 1

/-- The six exact occupied-cell moments at n=4 in the finite product witness. -/
def wholeT3Moments : Prop :=
  let S := finiteSampleWitness
  let P := S.law.iid 4
  let A := @Study.sampleA (Fin 16) _ S 4
  let B := fun s : Fin 4 → Fin 16 => S.sampleB s 0 0
  P.ce A S.occupied = 43/53 ∧
  P.ce (fun s => A s^2) S.occupied = 73/106 ∧
  P.ce B S.occupied = -2/3 ∧
  P.ce (fun s => B s^2) S.occupied = 1849/1908 ∧
  P.ce (fun s => A s*B s) S.occupied = -86/159 ∧
  P.ce (fun s => A s^2*B s^2) S.occupied = 4897/7632

/-- P019-T3; Lemma 2, p. 48; Appendix B, pp. 62–63, displays (6), (9), and the following sentence.
The four independent fair-bit population has the complete stated cell and observable laws. Its printed
ratios have positive empty-cell probabilities for every sample size; zero completion gives the stated
nonzero covariances. Conditional binomial counts expose the missing mass for every k. At n=4 the six
occupied-cell moments refute the exact product-variance formula, and the realized treatment count need
not equal its expectation. The comparison uses the specified completion and conditioning. -/
def T3WholeStatement : Prop :=
  T3Statement ∧ wholeT3Population ∧ wholeT3Singleton ∧ wholeT3Counts ∧ wholeT3Moments ∧
  (let S := finiteSampleWitness
   let P := S.law.iid 4
   P.cv (fun s => S.muHat s 0 0) S.occupied =
     P.cv (fun s => S.sampleA s * S.sampleB s 0 0) S.occupied)

/-- Complete data and conditional laws for the sign-error counterexample. -/
def wholeT5Data : Prop :=
  let S := distributionWitness
  wholeFairBits S.law 3 (fun i ω => fairBit ω i.val) ∧
  (∀ ω, S.Y ω = S.X ω) ∧
  wholeCellTable S (fun _ _ => 1/4)
    (fun z y => if z && y then 3/2 else 1/2) (fun _ _ => 1/4) ∧
  S.law.variance (fun ω => bitVal (S.Y ω)) = 1/4 ∧
  S.law.variance (fun ω => bitVal (S.Z ω)) = 1/4 ∧
  S.mu = 1/2 ∧ S.truthRate = 1 ∧ S.beta = 1 ∧
  (∀ t : ℝ,
    S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
      (if t = 0 then 1/2 else 0) + (if t = 1 then 1/2 else 0) ∧
    S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell true true) =
      (if t = 1 then 1/2 else 0) + (if t = 2 then 1/2 else 0) ∧
    S.law.ce (fun ω => if (S.V ω : ℝ)+1 = t then 1 else 0) (S.cell true true) =
      (if t = 2 then 1/2 else 0) + (if t = 3 then 1/2 else 0) ∧
    S.law.ce (fun ω => if (S.V ω : ℝ)-1 = t then 1 else 0) (S.cell true true) =
      (if t = 0 then 1/2 else 0) + (if t = 1 then 1/2 else 0))

/-- P019-T5; Section 4.1, p. 50, final distribution-comparison sentence.
The independent fair X,W,Z population with Y=X satisfies all four assumptions. Every cell and marginal
variance is positive as specified. The full conditional laws of control V and treated V+1 have disjoint
supports {0,1} and {2,3}. The preceding displayed identity is true for every real t: control V has the
same conditional law as treated V-1, including equality of all distribution functions. -/
def T5WholeStatement : Prop :=
  T5Statement ∧ wholeT5Data ∧
  Disjoint ({0,1} : Set ℝ) {2,3} ∧
  (let S := distributionWitness
   (∃ t : ℝ,
     S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) ≠
     S.law.ce (fun ω => if (S.V ω : ℝ)+1 = t then 1 else 0) (S.cell true true)) ∧
   ∀ t : ℝ,
     S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
       S.law.ce (fun ω => if (S.V ω : ℝ)-1 = t then 1 else 0) (S.cell true true) ∧
     S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
       S.law.ce (fun ω => if (S.V ω : ℝ) = t+1 then 1 else 0) (S.cell true true) ∧
     S.law.ce (fun ω => if (S.V ω : ℝ) ≤ t then 1 else 0) (S.cell false true) =
       S.law.ce (fun ω => if (S.V ω : ℝ)-1 ≤ t then 1 else 0) (S.cell true true))

/-- The additional population summaries and independence facts for the sixteen-atom diagnostic witness. -/
def wholeT7Sixteen : Prop :=
  let S := diagnosisWitness
  wholeFairBits S.law 4 (fun i ω => fairBit ω i.val) ∧
  (∀ ω, S.W ω ≤ 2 ∧ S.Y ω = wholeDiagnosisPotential (S.Z ω) ω) ∧
  S.law.prob (fun ω => S.X ω = false ∧ S.Y ω = false) = 1/2 ∧
  S.law.prob (fun ω => S.X ω = true ∧ S.Y ω = false) = 1/4 ∧
  S.law.prob (fun ω => S.X ω = true ∧ S.Y ω = true) = 1/4 ∧
  wholeCellTable S (fun _ y => if y then 1/8 else 3/8)
    (fun z y => if y then (if z then 5/2 else 1/2) else 7/6)
    (fun _ y => if y then 1/4 else 17/36) ∧
  S.law.variance (fun ω => bitVal (S.Y ω)) = 3/16 ∧
  S.law.variance (fun ω => bitVal (S.Z ω)) = 1/4 ∧
  wholeIndependent S.law (fun ω => (fairBit ω 0, fairBit ω 1, fairBit ω 2)) S.Z ∧
  wholeIndependent S.law (fun ω => (S.W ω, S.X ω)) S.Z ∧
  wholeIndependent S.law (fun ω => (wholeDiagnosisPotential false ω,
    wholeDiagnosisPotential true ω)) S.Z ∧
  wholeIndependent S.law S.Y S.Z ∧
  S.law.prob (fun ω => S.W ω = 0 ∧ S.X ω = true ∧ S.Y ω = false ∧ S.Z ω = false) = 0 ∧
  S.law.prob (fun ω => S.W ω = 0 ∧ S.X ω = true ∧ S.Y ω = false) = 1/16 ∧
  S.law.prob (fun ω => S.Z ω = false) = 1/2 ∧
  S.law.prob (fun ω => S.W ω = 0 ∧ S.X ω = true ∧ S.Y ω = false) *
    S.law.prob (fun ω => S.Z ω = false) = 1/32

/-- The full eight-atom diagnostic witness. Constant X=1 is allowed by Assumption 4. -/
def wholeT7Eight : Prop :=
  let S := wholeDiagnosisEight
  wholeFairBits S.law 3 (fun i ω => fairBit ω i.val) ∧
  S.monotone ∧ S.noLiarsDesign ∧ S.nondegenerate ∧
  (∀ ω, S.X ω = true ∧ S.W ω ≤ 2) ∧
  wholeCellTable S (fun _ _ => 1/4)
    (fun z y => if z then (if y then 5/2 else 3/2) else (if y then 1/2 else 3/2))
    (fun _ _ => 1/4) ∧
  S.law.variance (fun ω => bitVal (S.Y ω)) = 1/4 ∧
  S.law.variance (fun ω => bitVal (S.Z ω)) = 1/4 ∧
  S.delta = 0 ∧ S.beta = 2 ∧ ¬ S.treatmentIndependent

/-- P019-T7; supplement Appendix C, p. 2, first paragraph; Section 4.1, p. 50.
Both the sixteen-atom and eight-atom fair-bit constructions satisfy Monotonicity, No Liars and No Design
Effects, and Non-Degeneracy, with delta zero and beta two. The first has the stated latent classes,
cell moments, potential-response independence, marginal Y independence, and explicit zero-versus-1/32
failure of whole-triple independence. Thus Treatment Independence supplies a missing cause of beta
being different from one, while false confession and list design effects are absent in both examples. -/
def T7WholeStatement : Prop :=
  T7Statement ∧ wholeT7Sixteen ∧ wholeT7Eight ∧ wholeDiagnosisEight.beta ≠ 1

/-- Fisher's continuous transform and its one-dimensional Gaussian conditional average. -/
def wholeFisherG (x : ℝ) : ℝ := -2*Real.log (2*normalCDF (-|x|))
def wholeFisherH (t : ℝ) : ℝ :=
  ∫ a : ℝ, wholeFisherG ((a+t)/Real.sqrt 2) ∂gaussianReal 0 1

def wholeGaussianFive : Measure (Fin 5 → ℝ) := Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)
def wholeCovariance {E : Type*} [MeasurableSpace E] (P : Measure E) (f g : E → ℝ) : ℝ :=
  (∫ x, f x*g x ∂P) - (∫ x, f x ∂P)*(∫ x, g x ∂P)
def wholeVariance {E : Type*} [MeasurableSpace E] (P : Measure E) (f : E → ℝ) : ℝ :=
  (∫ x, (f x)^2 ∂P) - (∫ x, f x ∂P)^2

/-- Complete finite summaries for the sequential five-list witness. -/
def wholeT9Finite : Prop :=
  wholeFairBits (uniformFin 128 (by norm_num)) 7 (fun i ω => fairBit ω i.val) ∧
  ∀ j : Fin 5,
    let S := sequentialStudy j
    (∀ ω, (S.W ω : ℝ) = 3/2+(1/2)*bitSign (fairBit ω 1)*prefixSign ω j.val ∧
      (S.W ω = 1 ∨ S.W ω = 2)) ∧
    (∀ ω t, fairBit t 0 = fairBit ω 0 → fairBit t 1 = fairBit ω 1 →
      (∀ k : Fin 5, k ≠ j → fairBit t (k.val+2) = fairBit ω (k.val+2)) →
      S.W t = S.W ω ∧ S.X t = S.X ω ∧ S.Y t = S.Y ω) ∧
    wholeCellTable S
      (fun _ y => if j.val < 4 then (if y then 1/8 else 3/8) else 1/4)
      (fun z y => if z then (if y then 5/2 else (if j.val < 4 then 11/6 else 3/2)) else 3/2)
      (fun z y => if j.val < 4 ∧ z = true ∧ y = false then 17/36 else 1/4) ∧
    S.law.prob (fun ω => S.Y ω = true) = (if j.val < 4 then 1/4 else 1/2) ∧
    S.gamma = 1/2 ∧ S.law.variance (fun ω => bitVal (S.Z ω)) = 1/4 ∧
    S.law.variance (fun ω => bitVal (S.Y ω)) = (if j.val < 4 then 3/16 else 1/4) ∧
    S.law.ce (fun ω => (S.W ω : ℝ)) (fun ω => S.Y ω = true) = 3/2

/-- Finite-sample remainder probability, an intrinsic o_p(1) statement on the iid sample laws. -/
def wholeT9Linearization : Prop :=
  ∀ j : Fin 5, ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => ((uniformFin 128 (by norm_num)).iid n).prob (fun s =>
      ε ≤ |Real.sqrt (n : ℝ)*((sequentialStudy j).betaHat s 0 0-1) -
        (Real.sqrt (n : ℝ))⁻¹ * ∑ i, sequentialPsi j (s i)|)) atTop (nhds 0)

/-- Event where all five printed placebo means, sample variances, and studentizations exist. -/
def wholeT9Defined {n : ℕ} (s : Fin n → Fin 128) : Prop :=
  ∀ j : Fin 5, 2 ≤ (sequentialStudy j).cellCount s true true ∧
    2 ≤ (sequentialStudy j).cellCount s false true ∧
    0 < (sequentialStudy j).betaVarianceHat s 0

/-- All marginal Gaussian laws, covariances (equal to correlations), and uniform p-value limits. -/
def wholeT9Margins : Prop :=
  (∀ j : Fin 5,
    HasLaw (fun e => correlatedNormals e j) (gaussianReal 0 1) wholeGaussianFive ∧
    Integrable (fun e => correlatedNormals e j) wholeGaussianFive ∧
    Integrable (fun e => (correlatedNormals e j)^2) wholeGaussianFive ∧
    (∫ e, correlatedNormals e j ∂wholeGaussianFive) = 0 ∧
    wholeVariance wholeGaussianFive (fun e => correlatedNormals e j) = 1 ∧
    WeakLimit (uniformFin 128 (by norm_num))
      (fun _ s => normalPValue ((sequentialStudy j).betaHat s 0 0) 1
        ((sequentialStudy j).betaVarianceHat s 0)) (volume.restrict (Set.Icc (0 : ℝ) 1))) ∧
  (∀ j k : Fin 5, j ≠ k →
    wholeCovariance wholeGaussianFive (fun e => correlatedNormals e j)
      (fun e => correlatedNormals e k) =
        (if j.val < 4 ∧ k.val < 4 then 1/2 else 1/Real.sqrt 2))

/-- The exact Gaussian Fisher variance, with the moment conditions needed by every integral. -/
def wholeT9Variance : Prop :=
  MemLp wholeFisherG 2 (gaussianReal 0 1) ∧
  MemLp wholeFisherH 2 (gaussianReal 0 1) ∧
  Integrable (fun t => wholeFisherH t*wholeFisherG t) (gaussianReal 0 1) ∧
  (∀ᵐ t ∂gaussianReal 0 1, Integrable (fun a => wholeFisherG ((a+t)/Real.sqrt 2)) (gaussianReal 0 1)) ∧
  sequentialFisherLimit = wholeGaussianFive.map (fun e => ∑ j, wholeFisherG (correlatedNormals e j)) ∧
  continuousVariance sequentialFisherLimit = 20 +
    12*wholeVariance (gaussianReal 0 1) wholeFisherH +
    8*wholeCovariance (gaussianReal 0 1) wholeFisherH wholeFisherG ∧
  Integrable (fun x : ℝ => x) chiSquareTen ∧
  Integrable (fun x : ℝ => x^2) chiSquareTen ∧ continuousVariance chiSquareTen = 20

/-- Completion invariance of the joint normal and Fisher limits on the exceptional samples. -/
def wholeT9Completions : Prop :=
  Tendsto (fun n : ℕ => ((uniformFin 128 (by norm_num)).iid n).prob
    (fun s => wholeT9Defined s)) atTop (nhds 1) ∧
  ∀ C : (n : ℕ) → (Fin n → Fin 128) → (Fin 5 → ℝ),
    (∀ n s, wholeT9Defined s → ∀ j,
      C n s j = studentized ((sequentialStudy j).betaHat s 0 0) 1
        ((sequentialStudy j).betaVarianceHat s 0)) →
    WeakLimit (uniformFin 128 (by norm_num)) C (wholeGaussianFive.map correlatedNormals) ∧
    WeakLimit (uniformFin 128 (by norm_num))
      (fun n s => fisherStatistic (fun j => 2*normalCDF (-|C n s j|))) sequentialFisherLimit

/-- P019-T9; Section 5.3, p. 56, the Fisher joint-test reference distribution.
The seven independent fair coordinates give the stated ordered five-list construction, each list's
Assumptions 1–4 and beta one, exact cell summaries, influence functions, and root-n linearization.
The joint Gaussian limit has standard normal margins and correlations 1/2 and 1/sqrt(2); every marginal
p-value tends to the uniform law. Fisher's limit is the stated Gaussian transform, with variance
20+12 Var(h(E5))+8 Cov(h(E5),g(E5)) greater than 20, whereas chi-square ten has variance 20.
Every expectation defining h(t) is integrable, for every real t.
The statistics are defined with probability tending to one and their limits hold for every completion.
Thus these per-list assumptions and independent assignments do not ensure Fisher calibration. -/
def T9WholeStatement : Prop :=
  T9Statement ∧ wholeT9Finite ∧
  (∀ j ω,
    let S := sequentialStudy j
    let q := S.law.prob (fun t => S.Y t = true)
    let m := S.law.ce (fun t => (S.W t : ℝ)) (fun t => S.Y t = true)
    bitVal (S.Y ω)*bitVal (S.Z ω)/(q*S.gamma)*((S.V ω : ℝ)-m-1) -
      bitVal (S.Y ω)*(1-bitVal (S.Z ω))/(q*(1-S.gamma))*((S.V ω : ℝ)-m) =
        S.betaPsi ω) ∧
  wholeT9Linearization ∧ wholeT9Margins ∧ wholeT9Variance ∧
  (∀ t : ℝ, Integrable (fun a => wholeFisherG ((a+t)/Real.sqrt 2)) (gaussianReal 0 1)) ∧
  wholeT9Completions

/-- A measure-backed law; all uses below have probability and bounded-observation guards. -/
structure WholeMeasureLaw (Ω : Type u) [MeasurableSpace Ω] where
  measure : Measure Ω

def WholeMeasureLaw.mean {Ω : Type u} [MeasurableSpace Ω]
    (P : WholeMeasureLaw Ω) (f : Ω → ℝ) : ℝ := ∫ ω, f ω ∂P.measure

variable {Ω : Type u} [MeasurableSpace Ω]

def WholeMeasureLaw.prob (P : WholeMeasureLaw Ω) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.mean fun ω => if D ω then 1 else 0

/-- Event conditional mean; statements using it require a nonzero event probability. -/
def WholeMeasureLaw.ce (P : WholeMeasureLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  (P.mean fun ω => if D ω then f ω else 0) / P.prob D

def WholeMeasureLaw.variance (P : WholeMeasureLaw Ω) (f : Ω → ℝ) : ℝ :=
  P.mean (fun ω => f ω ^ 2) - (P.mean f) ^ 2

def WholeMeasureLaw.cv (P : WholeMeasureLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.ce (fun ω => f ω ^ 2) D - (P.ce f D) ^ 2

def WholeMeasureLaw.cov (P : WholeMeasureLaw Ω) (f g : Ω → ℝ) : ℝ :=
  P.mean (fun ω => f ω * g ω) - P.mean f * P.mean g

def WholeMeasureLaw.ccov (P : WholeMeasureLaw Ω) (f g : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.ce (fun ω => f ω * g ω) D - P.ce f D * P.ce g D

/-- The original population on an arbitrary probability space. The fields are count-valued
or Boolean; measurability and the four standing assumptions are stated separately. -/
structure WholeMeasureStudy (Ω : Type u) [MeasurableSpace Ω] where
  law : WholeMeasureLaw Ω
  W : Ω → ℕ
  X : Ω → Bool
  Y : Ω → Bool
  Z : Ω → Bool
  V : Ω → ℕ

/-- The full five-coordinate observable vector. -/
abbrev WholeObservation := ℕ × Bool × Bool × Bool × ℕ

def WholeMeasureStudy.observable (S : WholeMeasureStudy Ω) (ω : Ω) : WholeObservation :=
  (S.W ω, S.X ω, S.Y ω, S.Z ω, S.V ω)

def Study.wholeObservable {E : Type*} [Fintype E] (S : Study E) (ω : E) : WholeObservation :=
  (S.W ω, S.X ω, S.Y ω, S.Z ω, S.V ω)

def WholeMeasureStudy.measurableData (S : WholeMeasureStudy Ω) : Prop :=
  Measurable S.W ∧ Measurable S.X ∧ Measurable S.Y ∧ Measurable S.Z ∧ Measurable S.V

def WholeMeasureStudy.boundedData (S : WholeMeasureStudy Ω) : Prop :=
  ∃ M : ℕ, ∀ᵐ ω ∂S.law.measure, S.V ω ≤ M

def WholeMeasureStudy.monotone (S : WholeMeasureStudy Ω) : Prop :=
  ∀ᵐ ω ∂S.law.measure, S.Y ω = true → S.X ω = true

def WholeMeasureStudy.noLiarsDesign (S : WholeMeasureStudy Ω) : Prop :=
  ∀ᵐ ω ∂S.law.measure,
    (S.V ω : ℝ) = (S.W ω : ℝ) + bitVal (S.X ω)*bitVal (S.Z ω)

/-- Factorization against every function of the whole (W,X,Y) triple. -/
def WholeMeasureStudy.treatmentIndependent (S : WholeMeasureStudy Ω) : Prop :=
  ∀ (f : ℕ → Bool → Bool → ℝ) (z : Bool),
    S.law.mean (fun ω => if S.Z ω = z then f (S.W ω) (S.X ω) (S.Y ω) else 0) =
    S.law.prob (fun ω => S.Z ω = z) *
      S.law.mean (fun ω => f (S.W ω) (S.X ω) (S.Y ω))

def WholeMeasureStudy.cell (S : WholeMeasureStudy Ω) (z y : Bool) (ω : Ω) : Prop := S.Z ω = z ∧ S.Y ω = y

/-- Assumption 4 includes existence of all four conditional distributions. -/
def WholeMeasureStudy.nondegenerate (S : WholeMeasureStudy Ω) : Prop :=
  (∀ z y, 0 < S.law.prob (S.cell z y) ∧
    0 < S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y)) ∧
  0 < S.law.variance (fun ω => bitVal (S.Z ω)) ∧
  0 < S.law.variance (fun ω => bitVal (S.Y ω))

def WholeMeasureStudy.standing (S : WholeMeasureStudy Ω) : Prop :=
  S.monotone ∧ S.noLiarsDesign ∧ S.treatmentIndependent ∧ S.nondegenerate

def WholeMeasureStudy.mu (S : WholeMeasureStudy Ω) : ℝ := S.law.prob fun ω => S.X ω = true

def WholeMeasureStudy.truthRate (S : WholeMeasureStudy Ω) : ℝ :=
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.X ω = true)

def WholeMeasureStudy.gamma (S : WholeMeasureStudy Ω) : ℝ := S.law.prob fun ω => S.Z ω = true

def WholeMeasureStudy.listMean (S : WholeMeasureStudy Ω) (z y : Bool) : ℝ :=
  S.law.ce (fun ω => (S.V ω : ℝ)) (S.cell z y)

def WholeMeasureStudy.beta (S : WholeMeasureStudy Ω) : ℝ := S.listMean true true - S.listMean false true

def WholeMeasureStudy.delta (S : WholeMeasureStudy Ω) : ℝ :=
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true) -
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false)

/-- The full-vector iid law on ordered samples. -/
def WholeMeasureLaw.iid (P : WholeMeasureLaw Ω) (n : ℕ) : WholeMeasureLaw (Fin n → Ω) :=
  ⟨Measure.pi (fun _ : Fin n => P.measure)⟩

/-- The empty sample has mean zero by convention. -/
def WholeMeasureStudy.ybar (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (∑ i, bitVal (S.Y (s i))) / (n : ℝ)

def WholeMeasureStudy.cellCount (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℕ :=
  ∑ i, if S.cell z y (s i) then 1 else 0

/-- Printed subgroup ratio on occupied cells, with fixed value c on an empty cell. -/
def WholeMeasureStudy.cellMean (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) (c : ℝ) : ℝ :=
  if S.cellCount s z y = 0 then c else
    (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ) else 0) / (S.cellCount s z y : ℝ)

def WholeMeasureStudy.occupied (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) : Prop :=
  0 < S.cellCount s true false ∧ 0 < S.cellCount s false false

def WholeMeasureStudy.muHat (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.ybar s + (1 - S.ybar s) * (S.cellMean s true false c1 - S.cellMean s false false c0)

def WholeMeasureStudy.armCount (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) : ℕ :=
  ∑ i, if S.Z (s i) = z then 1 else 0

/-- Treatment fraction, with value zero on the empty sample. -/
def WholeMeasureStudy.gammaHat (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (S.armCount s true : ℝ) / (n : ℝ)

/-- Sample variance with divisor N-1, explicitly set to zero when N<2. -/
def WholeMeasureStudy.cellVariance (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℝ :=
  if S.cellCount s z y < 2 then 0 else
    (∑ i, if S.cell z y (s i) then
      ((S.V (s i) : ℝ) - S.cellMean s z y 0)^2 else 0) / ((S.cellCount s z y : ℝ) - 1)

/-- Whole variance estimate is cV whenever the printed formula is undefined. -/
def WholeMeasureStudy.muVarianceHat (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true false ∧ 2 ≤ S.cellCount s false false ∧
      S.ybar s < 1 ∧ 0 < S.gammaHat s ∧ S.gammaHat s < 1 then
    (((1 - S.muHat s c1 c0)^2 / (1 - S.ybar s)) * S.ybar s +
      (1 - S.ybar s) * (S.cellVariance s true false / S.gammaHat s +
        S.cellVariance s false false / (1 - S.gammaHat s))) / (n : ℝ)
  else cV

def WholeMeasureStudy.patternFibre (S : WholeMeasureStudy Ω) {n : ℕ} (s t : Fin n → Ω) : Prop :=
  ∀ i, S.Y (t i) = S.Y (s i) ∧ S.Z (t i) = S.Z (s i)

def WholeMeasureStudy.sampleA (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) : ℝ := 1 - S.ybar s

def WholeMeasureStudy.sampleB (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true false c1 - S.cellMean s false false c0 - 1

/-- Used only inside expectations conditional on occupied cells. -/
def WholeMeasureStudy.sampleH (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / (S.cellCount s true false : ℝ) +
    S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (S.cellCount s false false : ℝ)

def WholeMeasureStudy.negativeCount (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) : ℕ :=
  S.cellCount s true false + S.cellCount s false false

def WholeMeasureStudy.betaHat (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true true c1 - S.cellMean s false true c0

/-- Whole placebo variance estimate is cV when either cell has fewer than two observations. -/
def WholeMeasureStudy.betaVarianceHat (S : WholeMeasureStudy Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true true ∧ 2 ≤ S.cellCount s false true then
    S.cellVariance s true true / (S.cellCount s true true : ℝ) +
      S.cellVariance s false true / (S.cellCount s false true : ℝ)
  else cV

/-- Equality of every population and iid-sample observable moment. All functions here are measurable
because the observation space is countable; bounded effective support makes them integrable. -/
def wholeRepresentation (G : WholeMeasureStudy Ω) {E : Type*} [Fintype E] (S : Study E) : Prop :=
  (∀ f : WholeObservation → ℝ,
    G.law.mean (fun ω => f (G.observable ω)) = S.law.mean (fun ω => f (S.wholeObservable ω))) ∧
  (∀ n : ℕ, ∀ f : (Fin n → WholeObservation) → ℝ,
    (G.law.iid n).mean (fun s => f (fun i => G.observable (s i))) =
      (S.law.iid n).mean (fun s => f (fun i => S.wholeObservable (s i))))

/-- All the already established corrected finite-sample and asymptotic formulas. -/
def wholeT4Core {E : Type*} [Fintype E] (S : Study E) : Prop :=
  (∀ (n : ℕ) (z : Bool), (S.law.iid n).prob (fun s => S.cellCount s z false = 0) =
    (1 - S.law.prob (S.cell z false))^n ∧
    0 < (S.law.iid n).prob (fun s => S.cellCount s z false = 0)) ∧
  (∀ (n : ℕ), 2 ≤ n → ∀ c1 c0 : ℝ,
    let P := S.law.iid n
    let A := @Study.sampleA E _ S n
    let B := fun s : Fin n → E => S.sampleB s c1 c0
    let h := @Study.sampleH E _ S n
    let b := S.listMean true false - S.listMean false false - 1
    0 < P.prob S.occupied ∧
    (∀ k : ℕ, k ≤ n → P.prob (fun s => S.negativeCount s = k) ≠ 0 →
      (∀ i : ℕ, i ≤ k →
        P.ce (fun s => if S.cellCount s true false = i then 1 else 0)
          (fun s => S.negativeCount s = k) =
            (Nat.choose k i : ℝ) * S.gamma^i * (1-S.gamma)^(k-i)) ∧
      P.ce (fun s => if 0 < S.cellCount s true false then 1 else 0)
        (fun s => S.negativeCount s = k) = 1-(1-S.gamma)^k ∧
      P.ce (fun s => if 0 < S.cellCount s false false then 1 else 0)
        (fun s => S.negativeCount s = k) = 1-S.gamma^k) ∧
    (∀ s : Fin n → E, S.occupied s → P.prob (S.patternFibre s) ≠ 0 →
      (∀ z : Bool,
        P.ce (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.listMean z false ∧
        P.cv (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z false) / (S.cellCount s z false : ℝ)) ∧
      P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
        (S.patternFibre s) = 0 ∧
      P.ce B (S.patternFibre s) = b ∧ P.cv B (S.patternFibre s) = h s) ∧
    (∀ a : ℝ, P.prob (fun s => S.occupied s ∧ A s = a) ≠ 0 → ∀ z : Bool,
      P.ce (fun s => S.cellMean s z false (if z then c1 else c0))
        (fun s => S.occupied s ∧ A s = a) = S.listMean z false) ∧
    (∀ z : Bool,
      P.ccov (fun t => S.cellMean t z false (if z then c1 else c0)) A S.occupied = 0) ∧
    P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
      S.occupied = 0 ∧
    P.cv (fun s => S.muHat s c1 c0) S.occupied =
      b^2 * P.cv A S.occupied + P.ce (fun s => A s ^ 2 * h s) S.occupied ∧
    P.cv (fun s => A s * B s) S.occupied =
      b^2 * P.cv A S.occupied + P.ce (fun s => A s ^ 2 * h s) S.occupied ∧
    (P.ce A S.occupied)^2 * P.cv B S.occupied +
      P.cv A S.occupied * (P.ce B S.occupied)^2 +
      P.cv A S.occupied * P.cv B S.occupied =
        b^2 * P.cv A S.occupied +
          P.ce (fun s => A s ^ 2) S.occupied * P.ce h S.occupied ∧
    P.cv (fun s => A s * B s) S.occupied -
      ((P.ce A S.occupied)^2 * P.cv B S.occupied +
        P.cv A S.occupied * (P.ce B S.occupied)^2 +
        P.cv A S.occupied * P.cv B S.occupied) =
      P.ccov (fun s => A s^2) h S.occupied) ∧
  (let R := fun n : ℕ => (S.law.iid (n+2)).ccov
      (fun s => (S.sampleA s)^2) (fun s => S.sampleH s) (fun s => S.occupied s);
    Asymptotics.IsBigO atTop R (fun n : ℕ => (1/((n+2 : ℕ) : ℝ))^2) ∧
    Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)^2 * R n) atTop
      (nhds (-2 * (S.mu * S.truthRate) *
        (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / S.gamma +
         S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (1-S.gamma))))) ∧
  (∀ n : ℕ, 0 < n →
    (S.law.iid n).mean (fun s => (S.armCount s true : ℝ)) = (n : ℝ)*S.gamma ∧
    ∀ s : Fin n → E, (S.armCount s true : ℝ) = (n : ℝ)*S.gammaHat s)

/-- Count law and the actual positive-count sums for every n, including the empty sample. -/
def wholeT4Counts {E : Type*} [Fintype E] (S : Study E) : Prop :=
  ∀ n k : ℕ, k ≤ n →
    let P := S.law.iid n
    let K := fun s => S.negativeCount s = k
    0 < P.prob K ∧
    (∀ i : ℕ, i ≤ k →
      P.ce (fun s => if S.cellCount s true false = i then 1 else 0) K =
        (Nat.choose k i : ℝ)*S.gamma^i*(1-S.gamma)^(k-i)) ∧
    (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if S.cellCount s true false = i then 1 else 0) K) = 1-(1-S.gamma)^k ∧
    (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if S.cellCount s false false = i then 1 else 0) K) = 1-S.gamma^k

/-- Identities from the definitions, unconditional moments, and the unshifted asymptotic remainder.
At sample sizes zero and one the remainder is explicitly completed by zero. -/
def wholeT4Extras {E : Type*} [Fintype E] (S : Study E) : Prop :=
  (∀ (n : ℕ) (s : Fin n → E), (S.negativeCount s : ℝ) = (n : ℝ)*S.sampleA s ∧
    (∀ c1 c0 : ℝ, S.muHat s c1 c0 = 1+S.sampleA s*S.sampleB s c1 c0)) ∧
  S.law.prob (fun ω => S.Y ω = true) = S.mu*S.truthRate ∧
  0 < S.mu ∧ 0 < S.gamma ∧ S.gamma < 1 ∧ 0 < 1-S.mu*S.truthRate ∧
  (∀ n : ℕ, 0 < n →
    (S.law.iid n).mean S.sampleA = 1-S.mu*S.truthRate ∧
    (S.law.iid n).variance S.sampleA =
      (S.mu*S.truthRate)*(1-S.mu*S.truthRate)/(n : ℝ)) ∧
  S.listMean true false-S.listMean false false =
    ((1-S.truthRate)*S.mu)/(1-S.mu*S.truthRate) ∧
  S.listMean true false-S.listMean false false-1 = -(1-S.mu)/(1-S.mu*S.truthRate) ∧
  (let R := fun n : ℕ => (S.law.iid n).ccov
      (fun s => (S.sampleA s)^2) (fun s => S.sampleH s) (fun s => S.occupied s)
   Asymptotics.IsBigO atTop R (fun n : ℕ => (1/(n : ℝ))^2) ∧
   Tendsto (fun n : ℕ => (n : ℝ)^2*R n) atTop
     (nhds (-2*(S.mu*S.truthRate)*
       (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false)/S.gamma +
        S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)/(1-S.gamma)))))

/-- The finite representation's complete corrected formulas. -/
def wholeT4Finite {E : Type*} [Fintype E] (S : Study E) : Prop :=
  wholeT4Core S ∧ wholeT4Counts S ∧ wholeT4Extras S

/-- Corrected formulas on the original arbitrary probability space. Conditional moments have
positive-event guards. All functions are bounded almost surely, so the integrals are genuine moments. -/
def wholeT4MeasureCore (S : WholeMeasureStudy Ω) : Prop :=
  (∀ (n : ℕ) (z : Bool), (S.law.iid n).prob (fun s => S.cellCount s z false = 0) =
    (1 - S.law.prob (S.cell z false))^n ∧
    0 < (S.law.iid n).prob (fun s => S.cellCount s z false = 0)) ∧
  (∀ (n : ℕ), 2 ≤ n → ∀ c1 c0 : ℝ,
    let P := S.law.iid n
    let A := @WholeMeasureStudy.sampleA Ω _ S n
    let B := fun s : Fin n → Ω => S.sampleB s c1 c0
    let h := @WholeMeasureStudy.sampleH Ω _ S n
    let b := S.listMean true false - S.listMean false false - 1
    0 < P.prob S.occupied ∧
    (∀ k : ℕ, k ≤ n → P.prob (fun s => S.negativeCount s = k) ≠ 0 →
      (∀ i : ℕ, i ≤ k →
        P.ce (fun s => if S.cellCount s true false = i then 1 else 0)
          (fun s => S.negativeCount s = k) =
            (Nat.choose k i : ℝ) * S.gamma^i * (1-S.gamma)^(k-i)) ∧
      P.ce (fun s => if 0 < S.cellCount s true false then 1 else 0)
        (fun s => S.negativeCount s = k) = 1-(1-S.gamma)^k ∧
      P.ce (fun s => if 0 < S.cellCount s false false then 1 else 0)
        (fun s => S.negativeCount s = k) = 1-S.gamma^k) ∧
    (∀ s : Fin n → Ω, S.occupied s → P.prob (S.patternFibre s) ≠ 0 →
      (∀ z : Bool,
        P.ce (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.listMean z false ∧
        P.cv (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z false) / (S.cellCount s z false : ℝ)) ∧
      P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
        (S.patternFibre s) = 0 ∧
      P.ce B (S.patternFibre s) = b ∧ P.cv B (S.patternFibre s) = h s) ∧
    (∀ a : ℝ, P.prob (fun s => S.occupied s ∧ A s = a) ≠ 0 → ∀ z : Bool,
      P.ce (fun s => S.cellMean s z false (if z then c1 else c0))
        (fun s => S.occupied s ∧ A s = a) = S.listMean z false) ∧
    (∀ z : Bool,
      P.ccov (fun t => S.cellMean t z false (if z then c1 else c0)) A S.occupied = 0) ∧
    P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
      S.occupied = 0 ∧
    P.cv (fun s => S.muHat s c1 c0) S.occupied =
      b^2 * P.cv A S.occupied + P.ce (fun s => A s ^ 2 * h s) S.occupied ∧
    P.cv (fun s => A s * B s) S.occupied =
      b^2 * P.cv A S.occupied + P.ce (fun s => A s ^ 2 * h s) S.occupied ∧
    (P.ce A S.occupied)^2 * P.cv B S.occupied +
      P.cv A S.occupied * (P.ce B S.occupied)^2 +
      P.cv A S.occupied * P.cv B S.occupied =
        b^2 * P.cv A S.occupied +
          P.ce (fun s => A s ^ 2) S.occupied * P.ce h S.occupied ∧
    P.cv (fun s => A s * B s) S.occupied -
      ((P.ce A S.occupied)^2 * P.cv B S.occupied +
        P.cv A S.occupied * (P.ce B S.occupied)^2 +
        P.cv A S.occupied * P.cv B S.occupied) =
      P.ccov (fun s => A s^2) h S.occupied) ∧
  (let R := fun n : ℕ => (S.law.iid (n+2)).ccov
      (fun s => (S.sampleA s)^2) (fun s => S.sampleH s) (fun s => S.occupied s);
    Asymptotics.IsBigO atTop R (fun n : ℕ => (1/((n+2 : ℕ) : ℝ))^2) ∧
    Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)^2 * R n) atTop
      (nhds (-2 * (S.mu * S.truthRate) *
        (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / S.gamma +
         S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (1-S.gamma))))) ∧
  (∀ n : ℕ, 0 < n →
    (S.law.iid n).mean (fun s => (S.armCount s true : ℝ)) = (n : ℝ)*S.gamma ∧
    ∀ s : Fin n → Ω, (S.armCount s true : ℝ) = (n : ℝ)*S.gammaHat s)

/-- The all-size conditional count law on the original probability space. -/
def wholeT4MeasureCounts (S : WholeMeasureStudy Ω) : Prop :=
  ∀ n k : ℕ, k ≤ n →
    let P := S.law.iid n
    let K := fun s => S.negativeCount s = k
    0 < P.prob K ∧
    (∀ i : ℕ, i ≤ k →
      P.ce (fun s => if S.cellCount s true false = i then 1 else 0) K =
        (Nat.choose k i : ℝ)*S.gamma^i*(1-S.gamma)^(k-i)) ∧
    (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if S.cellCount s true false = i then 1 else 0) K) = 1-(1-S.gamma)^k ∧
    (∑ i ∈ Finset.Icc 1 k,
      P.ce (fun s => if S.cellCount s false false = i then 1 else 0) K) = 1-S.gamma^k

/-- The auxiliary identities and unshifted asymptotic remainder on the original probability space. -/
def wholeT4MeasureExtras (S : WholeMeasureStudy Ω) : Prop :=
  (∀ (n : ℕ) (s : Fin n → Ω), (S.negativeCount s : ℝ) = (n : ℝ)*S.sampleA s ∧
    (∀ c1 c0 : ℝ, S.muHat s c1 c0 = 1+S.sampleA s*S.sampleB s c1 c0)) ∧
  S.law.prob (fun ω => S.Y ω = true) = S.mu*S.truthRate ∧
  0 < S.mu ∧ 0 < S.gamma ∧ S.gamma < 1 ∧ 0 < 1-S.mu*S.truthRate ∧
  (∀ n : ℕ, 0 < n →
    (S.law.iid n).mean S.sampleA = 1-S.mu*S.truthRate ∧
    (S.law.iid n).variance S.sampleA =
      (S.mu*S.truthRate)*(1-S.mu*S.truthRate)/(n : ℝ)) ∧
  S.listMean true false-S.listMean false false =
    ((1-S.truthRate)*S.mu)/(1-S.mu*S.truthRate) ∧
  S.listMean true false-S.listMean false false-1 = -(1-S.mu)/(1-S.mu*S.truthRate) ∧
  (let R := fun n : ℕ => (S.law.iid n).ccov
      (fun s => (S.sampleA s)^2) (fun s => S.sampleH s) (fun s => S.occupied s)
   Asymptotics.IsBigO atTop R (fun n : ℕ => (1/(n : ℝ))^2) ∧
   Tendsto (fun n : ℕ => (n : ℝ)^2*R n) atTop
     (nhds (-2*(S.mu*S.truthRate)*
       (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false)/S.gamma +
        S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)/(1-S.gamma)))))

/-- P019-T4; corrected Lemma 2, p. 48, and Appendix B, pp. 62–63, displays (6)–(9).
For iid observations from any bounded count-valued population satisfying Assumptions 1–4, the empty-cell
probabilities, conditional binomial law and missing-mass sums hold for every n, including zero and one.
K=n(1-Ybar). On occupied cells, the stated pattern-conditional means, variances and covariances give the
corrected Lemma 2 and exact product-variance identity. Its discrepancy from the printed product expression
is Cov(A²,h | D), of order n⁻² with the stated limit coefficient. The unconditional direct-response moments
and population contrast identities hold, and n gamma is the expected treatment count; the realized count
is n gammaHat. Conditional moments are asserted only on positive-probability events. -/
def T4WholeStatement : Prop :=
  ∀ (E : Type u) [MeasurableSpace E] (S : WholeMeasureStudy E),
    IsProbabilityMeasure S.law.measure → S.measurableData → S.boundedData → S.standing →
    wholeT4MeasureCore S ∧ wholeT4MeasureCounts S ∧ wholeT4MeasureExtras S

end
end SAP.P019a
