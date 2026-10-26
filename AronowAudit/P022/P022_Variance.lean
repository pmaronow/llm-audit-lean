import Mathlib

namespace AronowAudit.P022

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false

noncomputable section

/-- "Consider a population U_N consisting of N ≥ 4 units ... m ≥ 2 ...
n-m ≥ 2" (Section 2, p. 851). Here k denotes n-m and n=m+k. -/
structure Design where
  N : ℕ
  m : ℕ
  k : ℕ
  population_min : 4 ≤ N
  treatment_min : 2 ≤ m
  control_min : 2 ≤ k
  sample_le : m + k ≤ N

/-- The paper's equally likely randomization (p. 851) is represented by a
uniform permutation of the N unit labels. The first m positions are treated,
the next k controlled; each unordered assignment has the same multiplicity
m! k! (N-m-k)!, so this is the same randomization distribution. -/
abbrev Assignment (d : Design) := Equiv.Perm (Fin d.N)

/-- "μ_N(v) = (1/N) ∑ v_i" (p. 851). Fin N uses zero-based unit labels. -/
def finiteMean {N : ℕ} (v : Fin N → ℝ) : ℝ := 𝔼 i, v i

/-- "σ_N²(v) = (1/N) ∑ {v_i-μ_N(v)}²" (p. 851). -/
def finiteVariance {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  finiteMean (fun i => (v i - finiteMean v) ^ 2)

/-- "σ_N(v,w) = (1/N) ∑ {v_i-μ_N(v)}{w_i-μ_N(w)}" (p. 851). -/
def finiteCovariance {N : ℕ} (v w : Fin N → ℝ) : ℝ :=
  finiteMean (fun i => (v i - finiteMean v) * (w i - finiteMean w))

/-- "E_X averages over all ... possible treatment assignments" (p. 851).
This finite average includes equal permutation multiplicities. -/
def designExpectation (d : Design) (f : Assignment d → ℝ) : ℝ := 𝔼 π, f π

/-- Probability under the uniform randomization of p. 851, as a finite
average of event indicators. No superpopulation randomness is introduced. -/
def designProbability (d : Design) (event : Assignment d → Prop) : ℝ :=
  by
    classical
    exact designExpectation d (fun π => if event π then 1 else 0)

/-- Randomization variance Var_X, Section 2, p. 851, defined by its finite
centered square, independently of the claimed formula (2). -/
def designVariance (d : Design) (f : Assignment d → ℝ) : ℝ :=
  designExpectation d (fun π => (f π - designExpectation d f) ^ 2)

/-- Observed treatment outcomes y_{1i}, positions 1,...,m in (1), p. 851. -/
def observedTreatment (d : Design) (y : Fin d.N → ℝ) (π : Assignment d) :
    Fin d.m → ℝ := fun i => y (π ⟨i.val, by have := d.sample_le; omega⟩)

/-- Observed control outcomes, positions m+1,...,n in (1), p. 851. -/
def observedControl (d : Design) (y : Fin d.N → ℝ) (π : Assignment d) :
    Fin d.k → ℝ := fun i => y (π ⟨d.m + i.val, by have := d.sample_le; omega⟩)

/-- "τ_N = μ_N(y_1)-μ_N(y_0)" (p. 851). -/
def averageEffect (d : Design) (y1 y0 : Fin d.N → ℝ) : ℝ :=
  finiteMean y1 - finiteMean y0

/-- "τ̂_N = μ̂_N(y_1)-μ̂_N(y_0)" (equation (1), p. 851). -/
def estimatedEffect (d : Design) (y1 y0 : Fin d.N → ℝ) (π : Assignment d) : ℝ :=
  finiteMean (observedTreatment d y1 π) - finiteMean (observedControl d y0 π)

/-- "Our inferential target is the variance of τ̂_N" (p. 851).
V_N is the actual finite randomization variance, not defined by (2). -/
def trueVariance (d : Design) (y1 y0 : Fin d.N → ℝ) : ℝ :=
  designVariance d (estimatedEffect d y1 y0)

/-- The right-hand side of equation (2), p. 851, with k=n-m. -/
def varianceExpression (N m k : ℕ) (v1 v0 cov : ℝ) : ℝ :=
  (((N : ℝ) - m) / m * v1 + ((N : ℝ) - k) / k * v0 + 2 * cov) /
    ((N : ℝ) - 1)

/-- "G_N(y) = N⁻¹ ∑ I(y_{1i}≤y)" and F_N analogously (p. 853). -/
def empiricalCDF {N : ℕ} (y : Fin N → ℝ) (x : ℝ) : ℝ :=
  finiteMean (fun i => if y i ≤ x then 1 else 0)

/-- G_N(x-) is the mean of I(y_{1i}<x); left limits in the proof of
Lemma 2, pp. 860–861. The same definition is used for control outcomes. -/
def empiricalLeftCDF {N : ℕ} (y : Fin N → ℝ) (x : ℝ) : ℝ :=
  finiteMean (fun i => if y i < x then 1 else 0)

/-- "y_{1(1)} ≤ ... ≤ y_{1(m)}" (p. 854): sorting retains duplicates. -/
def sortedOutcomes {N : ℕ} (y : Fin N → ℝ) : List ℝ :=
  (List.ofFn y).mergeSort (fun a b => decide (a ≤ b))

/-- Rank r is one-based, as on p. 854. For a nonempty sample, rank 0
returns the first sorted value; ranks above the sample size return 0.
An empty sample always returns 0. Only valid ranks enter cell interiors;
endpoint choices do not affect the integrals. -/
def orderStatistic {N : ℕ} (y : Fin N → ℝ) (r : ℕ) : ℝ :=
  (sortedOutcomes y).getD (r - 1) 0

/-- "Ĝ_N⁻¹(u)=y_{1(⌈mu⌉)}" (p. 854), equally for population quantiles.
On 0<u≤1 this is the generalized inverse. The u=0 value is the minimum;
the integral is unchanged by this measure-zero endpoint convention. -/
def empiricalQuantile {N : ℕ} (y : Fin N → ℝ) (u : ℝ) : ℝ :=
  orderStatistic y (Nat.ceil ((N : ℝ) * u))

/-- Upper and lower sharp covariance bounds, superscripts H and L,
equation (7), p. 853; estimates use the same definition on sampled outcomes. -/
inductive BoundSide | H | L
  deriving DecidableEq

/-- Equation (7), p. 853: the aligned or reversed quantile-product
integral, minus the product of marginal means. -/
def sharpCovariance {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  (∫ u in (0 : ℝ)..1, empiricalQuantile a u *
    empiricalQuantile b (if B = .H then u else 1 - u)) -
      finiteMean a * finiteMean b

/-- V_N^H and V_N^L following Lemma 1, p. 853. -/
def populationBound (d : Design) (y1 y0 : Fin d.N → ℝ) (B : BoundSide) : ℝ :=
  varianceExpression d.N d.m d.k (finiteVariance y1) (finiteVariance y0)
    (sharpCovariance y1 y0 B)

/-- Usual sample variance s²=(s-1)⁻¹∑(y_i-ȳ)²; the fixed-sample
infinite-population limit discussed on p. 852 and Appendix B, p. 869. -/
def sampleVariance {s : ℕ} (y : Fin s → ℝ) : ℝ :=
  (∑ i, (y i - finiteMean y) ^ 2) / ((s : ℝ) - 1)

/-- "σ̂_N² = (N-1)/{N(s-1)} ∑(y_i-μ̂)²" (p. 852). -/
def marginalVarianceEstimate {s : ℕ} (N : ℕ) (y : Fin s → ℝ) : ℝ :=
  ((N : ℝ) - 1) / N * sampleVariance y

/-- Equation (9), p. 854, evaluated at fixed observed outcomes. -/
def estimateBound {m k : ℕ} (N : ℕ) (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  varianceExpression N m k (marginalVarianceEstimate N a)
    (marginalVarianceEstimate N b) (sharpCovariance a b B)

/-- The random bound estimates V̂_N^H,V̂_N^L of (9), p. 854. -/
def estimatedVariance (d : Design) (y1 y0 : Fin d.N → ℝ) (B : BoundSide)
    (π : Assignment d) : ℝ :=
  estimateBound d.N (observedTreatment d y1 π) (observedControl d y0 π) B

/-- The conventional estimator V̂_n^a, equation (4), p. 852. -/
def conventionalEstimate (d : Design) (y1 y0 : Fin d.N → ℝ)
    (π : Assignment d) : ℝ :=
  (d.N : ℝ) / ((d.N : ℝ) - 1) *
    (marginalVarianceEstimate d.N (observedTreatment d y1 π) / d.m +
     marginalVarianceEstimate d.N (observedControl d y0 π) / d.k)

/-- Neyman's V̂_n^{b±}, equation (6), p. 853; used only when n=N. -/
def neymanEstimate (d : Design) (y1 y0 : Fin d.N → ℝ) (B : BoundSide)
    (π : Assignment d) : ℝ :=
  let A := marginalVarianceEstimate d.N (observedTreatment d y1 π)
  let C := marginalVarianceEstimate d.N (observedControl d y0 π)
  varianceExpression d.N d.m d.k A C
    (if B = .H then Real.sqrt (A * C) else -Real.sqrt (A * C))

/-- "Let {U_N}_N be a nested sequence ... outcomes ... fixed" (p. 855).
Row q has N=q+4, the first N values of two fixed outcome sequences. -/
structure ExperimentSequence where
  design : ℕ → Design
  size : ∀ q, (design q).N = q + 4
  y1 : ℕ → ℝ
  y0 : ℕ → ℝ

/-- The potential outcomes in row q of the nested sequence, p. 855. -/
def rowOutcomes (S : ExperimentSequence) (treatment : Bool) (q : ℕ) :
    Fin (S.design q).N → ℝ :=
  fun i => (if treatment then S.y1 else S.y0) i.val

/-- "H ... with marginals G ... and F" (Proposition 1, p. 855).
H is an actual Borel probability measure on ℝ²; G,F are its coordinate CDFs. -/
abbrev JointLaw := ProbabilityMeasure (ℝ × ℝ)

/-- Coordinate CDF G(x) or F(x) of H, Proposition 1, p. 855. -/
def lawCDF (H : JointLaw) (treatment : Bool) (x : ℝ) : ℝ :=
  ((H : Measure (ℝ × ℝ)) {p | (if treatment then p.1 else p.2) ≤ x}).toReal

/-- Coordinate left limits G(x-),F(x-) at the atoms in Lemma 2,
pp. 860–861, represented by strict threshold sets. -/
def lawLeftCDF (H : JointLaw) (treatment : Bool) (x : ℝ) : ℝ :=
  ((H : Measure (ℝ × ℝ)) {p | (if treatment then p.1 else p.2) < x}).toReal

/-- Weak convergence H_N⇒H (condition 2, p. 855), by integrals of every
bounded continuous real function; H_N is the finite empirical joint law. -/
def weakPopulationConvergence (S : ExperimentSequence) (H : JointLaw) : Prop :=
  ∀ f : BoundedContinuousFunction (ℝ × ℝ) ℝ,
    Tendsto (fun q => finiteMean (fun i : Fin (S.design q).N =>
      f (S.y1 i.val, S.y0 i.val))) atTop
        (𝓝 (∫ p, f p ∂(H : Measure (ℝ × ℝ))))

/-- Conditions 1–3 of Proposition 1, p. 855, exactly as printed.
No convergence of left limits at atoms is included here. -/
def Conditions123 (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ) : Prop :=
  0 < θ ∧ θ ≤ 1 ∧ 0 < ρ ∧ ρ < 1 ∧
  Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N) atTop (𝓝 (θ * ρ)) ∧
  Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) / (S.design q).N)
    atTop (𝓝 θ) ∧
  weakPopulationConvergence S H ∧
  (∀ t x, ¬ContinuousAt (lawCDF H t) x →
    Tendsto (fun q => empiricalCDF (rowOutcomes S t q) x) atTop (𝓝 (lawCDF H t x)))

/-- Condition 4, p. 855: as β→∞ the supremum over N of the empirical
square tail at y_i²≥β tends to zero, for each coordinate. -/
def UniformSquareIntegrability (S : ExperimentSequence) : Prop :=
  ∀ t : Bool, Tendsto (fun β : ℝ => sSup (Set.range (fun q =>
    finiteMean (fun i : Fin (S.design q).N =>
      let y := (if t then S.y1 else S.y0) i.val
      if β ≤ y ^ 2 then y ^ 2 else 0)))) atTop (𝓝 0) ∧
    (∀ β : ℝ, BddAbove (Set.range (fun q =>
      finiteMean (fun i : Fin (S.design q).N =>
        let y := (if t then S.y1 else S.y0) i.val
        if β ≤ y ^ 2 then y ^ 2 else 0))))

/-- Added hypothesis of the corrected Lemma 2 (P022-E001): convergence
of the left CDF values at every discontinuity of the limiting marginal. -/
def AtomLeftConvergence (S : ExperimentSequence) (H : JointLaw) : Prop :=
  ∀ t x, ¬ContinuousAt (lawCDF H t) x →
    Tendsto (fun q => empiricalLeftCDF (rowOutcomes S t q) x)
      atTop (𝓝 (lawLeftCDF H t x))

/-- The uniform CDF metric sup_y|G(y)-G_N(y)| of Lemma 2, p. 860. -/
def cdfDistance (A B : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |A x - B x|))

/-- Sample CDF Ĝ_N or F̂_N, p. 854, at each assignment in a row. -/
def sampledCDF (S : ExperimentSequence) (t : Bool) (q : ℕ)
    (π : Assignment (S.design q)) : ℝ → ℝ :=
  if t then empiricalCDF (observedTreatment (S.design q) (rowOutcomes S true q) π)
  else empiricalCDF (observedControl (S.design q) (rowOutcomes S false q) π)

/-- limsup_N N P(event_N), Lemma 2 and Proposition 2, as a nonnegative
extended real. Using ℝ≥0∞ preserves +∞ for the counterexample sequences. -/
def scaledProbabilityLimsup (S : ExperimentSequence)
    (events : (q : ℕ) → Assignment (S.design q) → Prop) : ℝ≥0∞ :=
  Filter.limsup (fun q => ENNReal.ofReal
    ((S.design q).N * designProbability (S.design q) (events q))) atTop

/-- All conclusions of Lemma 2, p. 860, including the nonincreasing
positive integer functions K_1,K_0. Quantification is over η>0. -/
def Lemma2Conclusions (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ) : Prop :=
  (∀ t, Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) ∧
  ∃ K1 K0 : ℝ → ℕ,
    (∀ η, 0 < η → 0 < K1 η ∧ 0 < K0 η) ∧
    (∀ a b, 0 < a → a ≤ b → K1 b ≤ K1 a ∧ K0 b ≤ K0 a) ∧
    (∀ η, 0 < η →
      scaledProbabilityLimsup S (fun q π =>
        η ≤ cdfDistance (lawCDF H true) (sampledCDF S true q π)) ≤
        ENNReal.ofReal ((1 - θ * ρ) * K1 η / (θ * ρ * η ^ 2))) ∧
    (∀ η, 0 < η →
      scaledProbabilityLimsup S (fun q π =>
        η ≤ cdfDistance (lawCDF H false) (sampledCDF S false q π)) ≤
        ENNReal.ofReal ((1 - θ * (1 - ρ)) * K0 η / (θ * (1 - ρ) * η ^ 2)))


/-- The explicit nested witness A, P022-E001:
y_{1i}=y_{0i}=-1/i, i≥1, n=N, m=floor(N/2). -/
def reciprocalWitness : ExperimentSequence where
  design q := {
    N := q + 4
    m := (q + 4) / 2
    k := q + 4 - (q + 4) / 2
    population_min := by omega
    treatment_min := by omega
    control_min := by omega
    sample_le := by omega }
  size q := rfl
  y1 i := -(1 / ((i : ℝ) + 1))
  y0 i := -(1 / ((i : ℝ) + 1))

/-- Point mass at (0,0), the weak limit of witness A. -/
def originLaw : JointLaw := ⟨Measure.dirac (0, 0), by infer_instance⟩

/-- D_1,D_0 of P022-T3: integrated absolute sampled-to-population CDF
error over [-C,C], P022-E001, replacing the proof on p. 867. -/
def integratedCDFError {N s : ℕ} (C : ℝ) (y : Fin N → ℝ) (a : Fin s → ℝ) : ℝ :=
  ∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF y x|


/-- The four-unit, two-treated/two-control design in P022-T5 and T9. -/
def fourUnitDesign : Design := ⟨4, 2, 2, by omega, by omega, by omega, by omega⟩

/-- Finite lemma: averaging a constant over a nonempty finite population.
Used for the explicit witnesses to (11) and Appendix B. -/
theorem finiteMean_const {N : ℕ} (hN : 0 < N) (c : ℝ) :
    finiteMean (fun _ : Fin N => c) = c := by
  letI : NeZero N := ⟨by omega⟩
  exact Finset.expect_const (Finset.univ_nonempty) c

/-- Finite lemma: every assignment has the same expectation of a constant
and zero variance. Uniform randomization, p. 851. -/
theorem design_constant (d : Design) (c : ℝ) :
    designExpectation d (fun _ => c) = c ∧ designVariance d (fun _ => c) = 0 := by
  have he : designExpectation d (fun _ => c) = c :=
    Finset.expect_const Finset.univ_nonempty c
  constructor
  · exact he
  · simp [designVariance, he, designExpectation]

/-- P022-T5: with N=n=4,m=2, all outcomes 1 and threshold 0, the population
CDF and its indicator variance are zero, every sample CDF is zero, and its
randomization variance 0 differs from the printed 1/12. Equation (11), p. 861. -/
theorem equation11_counterexample :
    empiricalCDF (fun _ : Fin 4 => (1 : ℝ)) 0 = 0 ∧
    finiteVariance (fun _ : Fin 4 => (if (1 : ℝ) ≤ 0 then 1 else 0)) = 0 ∧
    (∀ π : Assignment fourUnitDesign,
      empiricalCDF (observedTreatment fourUnitDesign (fun _ => 1) π) 0 = 0) ∧
    designVariance fourUnitDesign (fun π =>
      empiricalCDF (observedTreatment fourUnitDesign (fun _ => 1) π) 0) = 0 ∧
    ((4 - 2 : ℝ) / (4 * (4 - 1) * 2) = 1 / 12) ∧ (0 : ℝ) ≠ 1 / 12 := by
  norm_num [empiricalCDF, finiteVariance, finiteMean, observedTreatment,
    designVariance, designExpectation]

/-- The ordered distinct partition of {i/m}∪{j/k} in equation (8), p. 854. -/
def partitionKnots (m k : ℕ) : List ℝ :=
  (((Finset.range (m + 1)).image (fun i : ℕ => (i : ℝ) / m)) ∪
   ((Finset.range (k + 1)).image (fun j : ℕ => (j : ℝ) / k))).sort (· ≤ ·)

/-- p_r and cell widths of equation (8), p. 854. Defaults only totalize
out-of-range list access; valid cells use 0≤r<P. -/
def partitionPoint (m k r : ℕ) : ℝ := (partitionKnots m k).getD r 0
/-- P is the number of intervals in "{p_0,...,p_P}" (equation (8), p. 854). -/
def partitionCells (m k : ℕ) : ℕ := (partitionKnots m k).length - 1
/-- "p_i-p_{i-1}" is the integration weight in equation (8), p. 854. -/
def cellWidth (m k r : ℕ) : ℝ := partitionPoint m k (r + 1) - partitionPoint m k r

/-- Midpoints u_r=(p_{r-1}+p_r)/2 in the Appendix B correction,
P022-E002. Original partition widths are retained. -/
def cellMidpoint (m k r : ℕ) : ℝ :=
  (partitionPoint m k r + partitionPoint m k (r + 1)) / 2

/-- Centered midpoint covariance in the corrected sharp.var routine,
P022-E002; Appendix B, p. 869, implementing (8). -/
def midpointCovariance {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  ∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
    (empiricalQuantile a (cellMidpoint m k r) - finiteMean a) *
    (empiricalQuantile b (if B = .H then cellMidpoint m k r else
      1 - cellMidpoint m k r) - finiteMean b)

/-- Normalized overlap weights w_ij in P022-T8(d), computed from integer-grid overlaps.
Indices here are zero-based, so the rank endpoints are i+1 and j+1. -/
def overlapWeight (m k : ℕ) (i : Fin m) (j : Fin k) : ℝ :=
  max 0 (min (((i.val : ℝ) + 1) * k) (((j.val : ℝ) + 1) * m) -
    max ((i.val : ℝ) * k) ((j.val : ℝ) * m)) / ((m : ℝ) * k)


/-- e=2⁻²⁶, the exact value of sqrt(binary64 machine epsilon),
Appendix B, p. 869; P022-E002. -/
def codeEpsilon : ℝ := 1 / 67108864

/-- q_0=e and q_j=p_j-e (j>0), the shifted knots in printed sharp.var,
Appendix B, p. 869. -/
def codePoint (m k r : ℕ) : ℝ :=
  if r = 0 then codeEpsilon else partitionPoint m k r - codeEpsilon

/-- Real-arithmetic reading of printed sharp.var, joining only the
typeset FPvar line break. Appendix B, p. 869; P022-T9. -/
def printedCodeBound {m k : ℕ} (N : ℕ) (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  varianceExpression N m k (marginalVarianceEstimate N a)
    (marginalVarianceEstimate N b)
    ((∑ r ∈ Finset.range (partitionCells m k),
      (codePoint m k (r + 1) - codePoint m k r) *
      empiricalQuantile a (codePoint m k (r + 1)) *
      (if B = .H then orderStatistic b (Nat.ceil ((k : ℝ) * codePoint m k (r + 1)))
       else orderStatistic b (k + 1 - Nat.ceil ((k : ℝ) * codePoint m k (r + 1))))) -
      finiteMean a * finiteMean b)

/-- Finite lemma for P022-T9: the exact partition for m=k=2 is
(0,1/2,1), equation (8), p. 854. -/
theorem partition_two : partitionKnots 2 2 = [0, 1 / 2, 1] := by
  classical
  have hset : (((Finset.range (2 + 1)).image (fun i : ℕ => (i : ℝ) / 2)) ∪
      ((Finset.range (2 + 1)).image (fun j : ℕ => (j : ℝ) / 2))) =
      ([0, 1 / 2, 1] : List ℝ).toFinset := by
    ext x
    norm_num [Finset.range_add_one]
    tauto
  unfold partitionKnots
  norm_num only [Nat.cast_ofNat]
  rw [hset]
  exact (List.toFinset_sort (fun a b : ℝ => a ≤ b)
    (by norm_num : ([0, 1 / 2, 1] : List ℝ).Nodup)).2
    (by norm_num [List.Pairwise])

/-- Finite lemma for P022-T9: a constant two-observation sample has
quantile 1 throughout [0,1]. Equation (8), p. 854. -/
theorem quantile_two_ones (u : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) :
    empiricalQuantile (fun _ : Fin 2 => (1 : ℝ)) u = 1 := by
  have hs : sortedOutcomes (fun _ : Fin 2 => (1 : ℝ)) = [1, 1] := by
    norm_num [sortedOutcomes, List.ofFn_succ, List.mergeSort]
  have hc : Nat.ceil ((2 : ℝ) * u) ≤ 2 := Nat.ceil_le.mpr (by norm_num; linarith [hu.2])
  have hcases : Nat.ceil ((2 : ℝ) * u) = 0 ∨
      Nat.ceil ((2 : ℝ) * u) = 1 ∨ Nat.ceil ((2 : ℝ) * u) = 2 := by omega
  rcases hcases with h | h | h <;>
    simp [empiricalQuantile, orderStatistic, hs, h]

/-- Finite lemma for P022-T9: both empirical sharp covariances of
two all-one samples vanish, equations (8)–(9), p. 854. -/
theorem sharp_covariance_two_ones (B : BoundSide) :
    sharpCovariance (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) B = 0 := by
  have hint : (∫ u in (0 : ℝ)..1,
      empiricalQuantile (fun _ : Fin 2 => (1 : ℝ)) u *
      empiricalQuantile (fun _ : Fin 2 => (1 : ℝ)) (if B = .H then u else 1 - u)) =
      ∫ _u in (0 : ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    rw [quantile_two_ones u hu]
    cases B
    · simp [quantile_two_ones u hu]
    · have hr : 0 ≤ 1 - u ∧ 1 - u ≤ 1 := by constructor <;> linarith [hu.1, hu.2]
      simp [quantile_two_ones (1 - u) hr]
  unfold sharpCovariance
  rw [hint]
  simp_rw [finiteMean_const (by omega : 0 < 2) 1]
  norm_num

/-- P022-T9: the explicit N=n=4,m=k=2, all-ones input gives both correct
estimates and true variance zero, whereas the printed routine gives
-1/50331648 in both modes. Appendix B, p. 869. -/
theorem appendixB_counterexample :
    trueVariance fourUnitDesign (fun _ => 1) (fun _ => 1) = 0 ∧
    (∀ B, estimateBound 4 (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) B = 0 ∧
      printedCodeBound 4 (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) B =
        -(1 / 50331648 : ℝ)) := by
  have hmeans : ∀ π : Assignment fourUnitDesign,
      estimatedEffect fourUnitDesign (fun _ => 1) (fun _ => 1) π = 0 := by
    intro π
    norm_num [estimatedEffect, observedTreatment, observedControl, finiteMean,
      fourUnitDesign, Fintype.expect_eq_sum_div_card]
  constructor
  · simp [trueVariance, hmeans, designVariance, designExpectation]
  · intro B
    constructor
    · rw [estimateBound, sharp_covariance_two_ones]
      norm_num [varianceExpression, marginalVarianceEstimate, sampleVariance, finiteMean]
    · have hq1 : Nat.ceil ((2 : ℝ) * (1 / 2 - codeEpsilon)) = 1 := by
        apply (Nat.ceil_eq_iff (by omega : 1 ≠ 0)).2
        norm_num [codeEpsilon]
      have hq2 : Nat.ceil ((2 : ℝ) * (1 - codeEpsilon)) = 2 := by
        apply (Nat.ceil_eq_iff (by omega : 2 ≠ 0)).2
        norm_num [codeEpsilon]
      cases B <;>
        norm_num [printedCodeBound, partitionCells, partitionPoint, partition_two,
          codePoint, codeEpsilon, varianceExpression, marginalVarianceEstimate,
          sampleVariance, finiteMean, Finset.sum_range_succ, empiricalQuantile,
          orderStatistic, sortedOutcomes, List.ofFn_succ, List.mergeSort, hq1, hq2]

/-- P022-T10(a), finite identity: (9) at fixed observed samples equals
(1/m-1/N)s_1²+(1/k-1/N)s_0²+2σ̂^B/(N-1). Section 2, p. 852. -/
theorem fixed_sample_identity {m k N : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hN : m + k ≤ N) (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    estimateBound N a b B =
      (1 / (m : ℝ) - 1 / (N : ℝ)) * sampleVariance a +
      (1 / (k : ℝ) - 1 / (N : ℝ)) * sampleVariance b +
      2 * sharpCovariance a b B / ((N : ℝ) - 1) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have h : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
    linarith
  unfold estimateBound varianceExpression marginalVarianceEstimate
  field_simp
  <;> ring

/-- P022-T10(a), infinite-population correction: with observed outcomes
fixed, either mathematical endpoint in (9) tends to the standard independent
means variance estimate s_1²/m+s_0²/k. Section 2, p. 852; Appendix B, p. 869. -/
theorem fixed_sample_infinite_limit {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    Tendsto (fun N => estimateBound N a b B) atTop
      (𝓝 (sampleVariance a / m + sampleVariance b / k)) := by
  have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hNm1 : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro x
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (x + 1))] with N h
    linarith
  have hcov : Tendsto (fun N : ℕ => 2 * sharpCovariance a b B / ((N : ℝ) - 1))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNm1
  have hr := (((tendsto_const_nhds (x := 1 / (m : ℝ))).sub hi).mul_const
    (sampleVariance a)).add
    (((tendsto_const_nhds (x := 1 / (k : ℝ))).sub hi).mul_const (sampleVariance b))
  have hall := hr.add hcov
  have hh : Tendsto (fun N : ℕ =>
      (1 / (m : ℝ) - 1 / (N : ℝ)) * sampleVariance a +
      (1 / (k : ℝ) - 1 / (N : ℝ)) * sampleVariance b +
      2 * sharpCovariance a b B / ((N : ℝ) - 1)) atTop
      (𝓝 (sampleVariance a / m + sampleVariance b / k)) := by
    simpa [div_eq_mul_inv, mul_comm] using hall
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (m + k)] with N hN
  exact (fixed_sample_identity hm hk hN a b B).symm

/-- P022-T10(b): the exact finite-N variance remainder from (2), Section 2,
p. 852. This algebraic identity uses the RHS of (2), not an assumed proof
of the randomization variance identity. -/
theorem independent_means_remainder (N m k : ℕ) (v1 v0 cov : ℝ)
    (hm : m ≠ 0) (hk : k ≠ 0) (hN : 2 ≤ N) :
    varianceExpression N m k v1 v0 cov - (v1 / m + v0 / k) =
      (2 * cov - (1 - 1 / (m : ℝ)) * v1 - (1 - 1 / (k : ℝ)) * v0) /
        ((N : ℝ) - 1) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold varianceExpression
  field_simp
  <;> ring


/-- Sorted outcomes indexed by Fin N, the comonotonic pairing in
Lemma 1, p. 853. -/
def sortedValues {N : ℕ} (y : Fin N → ℝ) : Fin N → ℝ :=
  fun i => (sortedOutcomes y).getD i.val 0


/-- Limiting coordinate means, variances and covariance, Proposition 1,
p. 855. These are integrals under the actual Borel probability law. -/
def lawMean (H : JointLaw) (t : Bool) : ℝ :=
  ∫ p, (if t then p.1 else p.2) ∂(H : Measure (ℝ × ℝ))
/-- "Var_H(y_1)" and "Var_H(y_0)" in Proposition 1, p. 855. -/
def lawVariance (H : JointLaw) (t : Bool) : ℝ :=
  ∫ p, ((if t then p.1 else p.2) - lawMean H t) ^ 2 ∂(H : Measure (ℝ × ℝ))
/-- "Cov_h(y_1,y_0)" in Proposition 1, p. 855. -/
def lawCovariance (H : JointLaw) : ℝ :=
  ∫ p, (p.1 - lawMean H true) * (p.2 - lawMean H false) ∂(H : Measure (ℝ × ℝ))

/-- "The collection ℋ of all bivariate distributions with marginals G,F"
(Proposition 1, p. 855). Equality of CDFs specifies the marginal measures. -/
def compatibleLaws (H : JointLaw) : Set JointLaw :=
  {h | ∀ t x, lawCDF h t x = lawCDF H t x}

/-- The two deterministic limits printed in Proposition 1, p. 855. -/
def limitingBound (H : JointLaw) (θ ρ : ℝ) (B : BoundSide) : ℝ :=
  (1 - θ * ρ) / (θ * ρ) * lawVariance H true +
  (1 - θ * (1 - ρ)) / (θ * (1 - ρ)) * lawVariance H false +
  2 * (if B = .H then sSup (lawCovariance '' compatibleLaws H)
       else sInf (lawCovariance '' compatibleLaws H))

/-- (V̂^H-V^H,V̂^L-V^L)=o_P(1/N), Proposition 1, p. 855,
using the maximum norm and the separate randomization law in each row. -/
def boundConsistency (S : ExperimentSequence) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun q => designProbability (S.design q) (fun π =>
    ε ≤ max
      (((S.design q).N : ℝ) * |estimatedVariance (S.design q)
        (rowOutcomes S true q) (rowOutcomes S false q) .H π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|)
      (((S.design q).N : ℝ) * |estimatedVariance (S.design q)
        (rowOutcomes S true q) (rowOutcomes S false q) .L π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .L|)))
    atTop (𝓝 0)


/-- "Uniformly bounded third moments" (Corollary 1, p. 856), expressed by
a single finite uniform upper bound on both finite means of |y|³. -/
def BoundedThirdMoments (S : ExperimentSequence) : Prop :=
  ∃ M : ℝ, ∀ q (t : Bool), finiteMean (fun i : Fin (S.design q).N =>
    |(if t then S.y1 else S.y0) i.val| ^ 3) ≤ M

/-- "Support of H is nonsingular" (Corollary 1, p. 856): it is not
concentrated on any affine line in ℝ². -/
def NonsingularLaw (H : JointLaw) : Prop :=
  ∀ a b c : ℝ, a ≠ 0 ∨ b ≠ 0 →
    ¬(∀ᵐ p ∂(H : Measure (ℝ × ℝ)), a * p.1 + b * p.2 = c)

/-- The limit of NV_N obtained from (2), used in γ in Corollary 1, p. 856. -/
def limitingTrueVariance (H : JointLaw) (θ ρ : ℝ) : ℝ :=
  (1 - θ * ρ) / (θ * ρ) * lawVariance H true +
  (1 - θ * (1 - ρ)) / (θ * (1 - ρ)) * lawVariance H false + 2 * lawCovariance H

/-- The ratio γ=lim NV_N / lim NV_N^H, Corollary 1, p. 856. -/
def gamma (H : JointLaw) (θ ρ : ℝ) : ℝ :=
  limitingTrueVariance H θ ρ / limitingBound H θ ρ .H

/-- Φ, the CDF of the standard normal, Corollary 1 and Remark 4, pp. 856–857. -/
def normalCDF (x : ℝ) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

/-- z_{1-α/2}, the generalized inverse of Φ in Remark 4, p. 857. -/
def normalCritical (α : ℝ) : ℝ := sInf {x | 1 - α / 2 ≤ normalCDF x}

/-- Weak convergence of a triangular array statistic under its finite
randomization law to the standard normal, Corollary 1, p. 856. -/
def weakStandardNormal (S : ExperimentSequence)
    (Z : (q : ℕ) → Assignment (S.design q) → ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun q => designExpectation (S.design q) (fun π => f (Z q π))) atTop
      (𝓝 (∫ x, f x ∂ProbabilityTheory.gaussianReal 0 1))


/-- Finite lemma for Lemma 2: empirical CDFs lie in [0,1], using the
finite population definition on p. 853. -/
theorem empirical_cdf_bounds {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (x : ℝ) :
    0 ≤ empiricalCDF y x ∧ empiricalCDF y x ≤ 1 := by
  letI : NeZero N := ⟨by omega⟩
  unfold empiricalCDF finiteMean
  constructor
  · exact Finset.expect_nonneg (fun i _ => by split_ifs <;> norm_num)
  · exact Finset.expect_le Finset.univ_nonempty (fun i _ => by split_ifs <;> norm_num)

/-- Finite lemma for P022-T1: the point-mass limiting CDF is I(x≥0),
P022-E001. -/
theorem origin_cdf (t : Bool) (x : ℝ) :
    lawCDF originLaw t x = if 0 ≤ x then 1 else 0 := by
  cases t <;> by_cases hx : 0 ≤ x <;>
    simp [lawCDF, originLaw, Set.indicator, hx]

/-- Finite lemma for P022-T1: any nonempty sample wholly below a negative
threshold has uniform distance exactly 1 from the point mass at zero.
P022-E001; refutes the uniform metric in Lemma 2. -/
theorem zero_atom_distance {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ)
    (treatment : Bool) (x : ℝ) (hx : x < 0) (hy : ∀ i, y i ≤ x) :
    cdfDistance (lawCDF originLaw treatment) (empiricalCDF y) = 1 := by
  have hpop : empiricalCDF y x = 1 := by
    simp_rw [empiricalCDF, if_pos (hy _)]
    exact finiteMean_const hN 1
  have hupper : ∀ z, |lawCDF originLaw treatment z - empiricalCDF y z| ≤ 1 := by
    intro z
    have hb := empirical_cdf_bounds hN y z
    rw [origin_cdf]
    split_ifs <;> rw [abs_sub_le_iff] <;> constructor <;> linarith [hb.1, hb.2]
  have hbdd : BddAbove (Set.range (fun z => |lawCDF originLaw treatment z - empiricalCDF y z|)) :=
    ⟨1, by rintro z ⟨x, rfl⟩; exact hupper x⟩
  unfold cdfDistance
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro z ⟨x, rfl⟩; exact hupper x)
  · have hp : |lawCDF originLaw treatment x - empiricalCDF y x| = 1 := by
      rw [origin_cdf, if_neg (by linarith), hpop]
      norm_num
    rw [← hp]
    exact le_csSup hbdd (Set.mem_range_self x)

/-- t_N=-1/(2N), the moving threshold in counterexample A,
P022-E001. Row q has N=q+4. -/
def reciprocalThreshold (q : ℕ) : ℝ := -(1 / (2 * ((q : ℝ) + 4)))

/-- Finite lemma for P022-T1: every one of the first N reciprocal outcomes
is below t_N<0, for every N≥4. P022-E001. -/
theorem reciprocal_below_threshold (q : ℕ) (i : Fin (q + 4)) :
    -(1 / ((i.val : ℝ) + 1)) < reciprocalThreshold q ∧ reciprocalThreshold q < 0 := by
  have hi : 0 < (i.val : ℝ) + 1 := by positivity
  have hN : 0 < (q : ℝ) + 4 := by positivity
  have hle : (i.val : ℝ) + 1 ≤ (q : ℝ) + 4 := by
    exact_mod_cast (show i.val + 1 ≤ q + 4 by omega)
  have hlt : (i.val : ℝ) + 1 < 2 * ((q : ℝ) + 4) := by linarith
  have hd := one_div_lt_one_div_of_lt hi hlt
  unfold reciprocalThreshold
  constructor
  · linarith
  · exact neg_neg_of_pos (one_div_pos.mpr (by positivity))

/-- P022-T1, exact finite part of counterexample A: both population CDF
distances and both sampled CDF distances are 1 for every N and assignment.
This lemma alone is not a certificate of the asymptotic hypotheses.
P022-E001; Lemma 2, p. 860. -/
theorem reciprocal_finite_errors :
    (∀ q t, cdfDistance (lawCDF originLaw t)
      (empiricalCDF (rowOutcomes reciprocalWitness t q)) = 1) ∧
    (∀ q t π, cdfDistance (lawCDF originLaw t)
      (sampledCDF reciprocalWitness t q π) = 1) := by
  have hvalues : ∀ q (t : Bool) (i : Fin (reciprocalWitness.design q).N),
      rowOutcomes reciprocalWitness t q i ≤ reciprocalThreshold q := by
    intro q t i
    have h := (reciprocal_below_threshold q i).1.le
    cases t <;> exact h
  constructor
  · intro q t
    apply zero_atom_distance (by dsimp [reciprocalWitness]; omega) _ _
      (reciprocalThreshold q) (reciprocal_below_threshold q ⟨0, by omega⟩).2
    exact hvalues q t
  · intro q t π
    cases t
    · apply zero_atom_distance (by dsimp [reciprocalWitness]; omega) _ _
        (reciprocalThreshold q) (reciprocal_below_threshold q ⟨0, by omega⟩).2
      intro i
      exact hvalues q false _
    · apply zero_atom_distance (by dsimp [reciprocalWitness]; omega) _ _
        (reciprocalThreshold q) (reciprocal_below_threshold q ⟨0, by omega⟩).2
      intro i
      exact hvalues q true _


/-- Finite lemma for P022-T4: the Bernoulli variance bound is an inequality,
with equality exactly at p=1/2. Equation (11), p. 861, corrected. -/
theorem bernoulli_variance_bound (p : ℝ) :
    p * (1 - p) ≤ 1 / 4 ∧ (p * (1 - p) = 1 / 4 ↔ p = 1 / 2) := by
  constructor
  · nlinarith [sq_nonneg (p - 1 / 2)]
  · constructor
    · intro h
      have : (p - 1 / 2) ^ 2 = 0 := by nlinarith
      have := (sq_eq_zero_iff).mp this
      linarith
    · intro h; rw [h]; norm_num

/-- Finite lemma for P022-T1: at the limiting atom zero both empirical
CDFs and both empirical left CDFs equal 1, whereas the limiting left value
is 0. P022-E001; failed step on p. 861. -/
theorem reciprocal_atom_values (q : ℕ) (t : Bool) :
    empiricalCDF (rowOutcomes reciprocalWitness t q) 0 = 1 ∧
    empiricalLeftCDF (rowOutcomes reciprocalWitness t q) 0 = 1 ∧
    lawCDF originLaw t 0 = 1 ∧ lawLeftCDF originLaw t 0 = 0 := by
  have hneg : ∀ i, rowOutcomes reciprocalWitness t q i < 0 := by
    intro i
    have h := reciprocal_below_threshold q i
    cases t <;> exact lt_trans h.1 h.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [empiricalCDF, if_pos (hneg _).le]
    exact finiteMean_const (by dsimp [reciprocalWitness]; omega) 1
  · simp_rw [empiricalLeftCDF, if_pos (hneg _)]
    exact finiteMean_const (by dsimp [reciprocalWitness]; omega) 1
  · simp [origin_cdf]
  · cases t <;> simp [lawLeftCDF, originLaw, Set.indicator]

/-- Asymptotic hypothesis for P022-T1: the reciprocal outcomes tend to zero.
P022-E001, the fixed-outcome nested witness A. -/
theorem reciprocal_outcome_limit :
    Tendsto (fun i : ℕ => -(1 / ((i : ℝ) + 1))) atTop (𝓝 0) := by
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg

/-- Asymptotic hypothesis for P022-T1: the empirical joint distributions
of the first N reciprocal pairs converge weakly to δ_(0,0), by Cesaro
averages of every bounded continuous test function. -/
theorem reciprocal_weak_limit : weakPopulationConvergence reciprocalWitness originLaw := by
  intro f
  have hp : Tendsto (fun i : ℕ =>
      (-(1 / ((i : ℝ) + 1)), -(1 / ((i : ℝ) + 1)))) atTop
        (𝓝 ((0, 0) : ℝ × ℝ)) := reciprocal_outcome_limit.prodMk_nhds reciprocal_outcome_limit
  have hf := f.continuous.continuousAt.tendsto.comp hp
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  have hc := hf.cesaro.comp hshift
  have hmean : ∀ N : ℕ,
      finiteMean (fun i : Fin N => f (-(1 / ((i.val : ℝ) + 1)), -(1 / ((i.val : ℝ) + 1)))) =
        (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (-(1 / ((i : ℝ) + 1)), -(1 / ((i : ℝ) + 1))) := by
    intro N
    unfold finiteMean
    rw [Finset.expect_eq_sum_div_card]
    simp only [Finset.card_univ, Fintype.card_fin, div_eq_inv_mul]
    congr 1
    simpa [div_eq_inv_mul] using Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      f (-(1 / ((i : ℝ) + 1)), -(1 / ((i : ℝ) + 1)))) N
  simp only [originLaw, ProbabilityMeasure.coe_mk, integral_dirac]
  change Tendsto (fun q => finiteMean (fun i : Fin (q + 4) =>
    f (-(1 / ((i.val : ℝ) + 1)), -(1 / ((i.val : ℝ) + 1))))) atTop (𝓝 (f (0, 0)))
  simp_rw [hmean]
  simpa [Function.comp_def, div_eq_inv_mul] using hc

/-- Asymptotic hypothesis for P022-T1: floor(N/2)/N→1/2 and n/N=1.
The division remainder supplies an exact expression for the first ratio.
P022-E001. -/
theorem reciprocal_allocation_limit :
    Tendsto (fun q => ((reciprocalWitness.design q).m : ℝ) /
      (reciprocalWitness.design q).N) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun q => (((reciprocalWitness.design q).m : ℝ) +
      (reciprocalWitness.design q).k) / (reciprocalWitness.design q).N) atTop (𝓝 1) := by
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  have hmod : Tendsto (fun q : ℕ => (((q + 4) % 2 : ℕ) : ℝ) / (q + 4)) atTop (𝓝 0) :=
    by simpa [Function.comp_def] using
      (tendsto_mod_div_atTop_nhds_zero_nat (m := 2) (by omega)).comp hshift
  constructor
  · have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hmod).div_const 2
    convert hh using 1
    · funext q
      dsimp [reciprocalWitness]
      have hn : ((q + 4 : ℕ) : ℝ) ≠ 0 := by positivity
      have heq : (((q + 4) % 2 : ℕ) : ℝ) + 2 * (((q + 4) / 2 : ℕ) : ℝ) =
          ((q + 4 : ℕ) : ℝ) := by exact_mod_cast (Nat.mod_add_div (q + 4) 2)
      simp only [Nat.cast_add, Nat.cast_ofNat] at hn heq ⊢
      have heqmul := congrArg (fun x : ℝ => x * ((q : ℝ) + 4)) heq
      field_simp
      nlinarith [heqmul]
    · norm_num
  · convert (tendsto_const_nhds (x := (1 : ℝ))) using 1
    funext q
    dsimp [reciprocalWitness]
    have hn : (q + 4) / 2 + (q + 4 - (q + 4) / 2) = q + 4 := by omega
    rw [← Nat.cast_add, hn]
    exact div_self (by positivity)

/-- The limiting point-mass CDF is continuous away from zero.
This checks all discontinuity points in condition 3 for P022-T1. -/
theorem origin_cdf_continuous_off_atom (t : Bool) (x : ℝ) (hx : x ≠ 0) :
    ContinuousAt (lawCDF originLaw t) x := by
  change Tendsto (lawCDF originLaw t) (𝓝 x) (𝓝 (lawCDF originLaw t x))
  rcases lt_or_gt_of_ne hx with h | h
  · have heq : lawCDF originLaw t =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds h] with y hy
      simp [origin_cdf, not_le.mpr hy]
    rw [origin_cdf, if_neg (not_le.mpr h)]
    exact tendsto_const_nhds.congr' heq.symm
  · have heq : lawCDF originLaw t =ᶠ[𝓝 x] (fun _ => 1) := by
      filter_upwards [eventually_gt_nhds h] with y hy
      simp [origin_cdf, hy.le]
    rw [origin_cdf, if_pos h.le]
    exact tendsto_const_nhds.congr' heq.symm

/-- P022-T1: every hypothesis of printed Lemma 2 is satisfied by the
explicit nested reciprocal witness. Conditions 1–3, p. 855. -/
theorem reciprocal_conditions123 : Conditions123 reciprocalWitness originLaw 1 (1 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_,
    reciprocal_weak_limit, ?_⟩
  · simpa using reciprocal_allocation_limit.1
  · exact reciprocal_allocation_limit.2
  · intro t x hx
    have heq : x = 0 := by
      by_contra h
      exact hx (origin_cdf_continuous_off_atom t x h)
    subst x
    have hfun : (fun q => empiricalCDF (rowOutcomes reciprocalWitness t q) 0) =
        (fun _ => (1 : ℝ)) := funext (fun q => (reciprocal_atom_values q t).1)
    rw [hfun, origin_cdf]
    norm_num

/-- P022-T1: the deviation events at η=1/2 have probability one, and
limsup N P(event)=+∞ for each marginal. Lemma 2, p. 860. -/
theorem reciprocal_tail_diverges (t : Bool) :
    scaledProbabilityLimsup reciprocalWitness (fun q π => (1 / 2 : ℝ) ≤
      cdfDistance (lawCDF originLaw t) (sampledCDF reciprocalWitness t q π)) = ⊤ := by
  have hp : ∀ q, designProbability (reciprocalWitness.design q) (fun π => (1 / 2 : ℝ) ≤
      cdfDistance (lawCDF originLaw t) (sampledCDF reciprocalWitness t q π)) = 1 := by
    intro q
    unfold designProbability
    simp only [reciprocal_finite_errors.2 q t, show (1 / 2 : ℝ) ≤ 1 by norm_num, if_true]
    exact (design_constant _ 1).1
  unfold scaledProbabilityLimsup
  simp_rw [hp, mul_one]
  apply Filter.Tendsto.limsup_eq
  apply ENNReal.tendsto_ofReal_atTop.comp
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp hshift

/-- P022-T1, witness A for the false Lemma 2: every printed hypothesis
holds with θ=1,ρ=1/2; both population distances and every sample distance
equal 1 in every row, and the scaled tail limits at η=1/2 are +∞.
Lemma 2, p. 860; P022-E001. -/
theorem lemma2_counterexample :
    Conditions123 reciprocalWitness originLaw 1 (1 / 2) ∧
    (∀ q t, cdfDistance (lawCDF originLaw t)
      (empiricalCDF (rowOutcomes reciprocalWitness t q)) = 1) ∧
    (∀ q t π, cdfDistance (lawCDF originLaw t)
      (sampledCDF reciprocalWitness t q π) = 1) ∧
    (∀ t, scaledProbabilityLimsup reciprocalWitness (fun q π =>
      (1 / 2 : ℝ) ≤ cdfDistance (lawCDF originLaw t)
        (sampledCDF reciprocalWitness t q π)) = ⊤) ∧
    ¬Lemma2Conclusions reciprocalWitness originLaw 1 (1 / 2) := by
  refine ⟨reciprocal_conditions123, reciprocal_finite_errors.1,
    reciprocal_finite_errors.2, reciprocal_tail_diverges, ?_⟩
  intro h
  rcases h.2 with ⟨K1, K0, _hpos, _hanti, hG, _hF⟩
  have ht := hG (1 / 2) (by norm_num)
  rw [reciprocal_tail_diverges true] at ht
  simpa using ht

/-- Explicit admissible K(η)=2 ceil(4/min(η,1)) in the corrected Lemma 2,
P022-E001. Unlike the printed proof, this choice is universal. -/
def correctedPartitionInteger (η : ℝ) : ℕ := 2 * Nat.ceil (4 / min η 1)

/-- Finite lemma for P022-T2: the explicit corrected partition integer
is positive and nonincreasing on positive tolerances. -/
theorem corrected_partition_integer_properties :
    (∀ η, 0 < η → 0 < correctedPartitionInteger η) ∧
    (∀ a b, 0 < a → a ≤ b → correctedPartitionInteger b ≤ correctedPartitionInteger a) := by
  constructor
  · intro η hη
    have hd : 0 < (4 : ℝ) / min η 1 := div_pos (by norm_num) (lt_min hη (by norm_num))
    have hn : 0 < Nat.ceil ((4 : ℝ) / min η 1) := by
      apply Nat.pos_of_ne_zero
      intro h
      have hz := Nat.ceil_eq_zero.mp h
      linarith
    unfold correctedPartitionInteger
    omega
  · intro a b ha hab
    unfold correctedPartitionInteger
    apply Nat.mul_le_mul_left 2
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_left (by norm_num) (lt_min ha (by norm_num)) (min_le_min hab le_rfl)


/-- Finite lemma for (11) and (13): population variance is the second
moment minus squared mean. Finite population definitions, p. 851. -/
theorem finite_variance_second_moment {N : ℕ} (hN : 0 < N) (v : Fin N → ℝ) :
    finiteVariance v = finiteMean (fun i => v i ^ 2) - finiteMean v ^ 2 := by
  letI : NeZero N := ⟨by omega⟩
  unfold finiteVariance finiteMean
  calc
    (𝔼 i, (v i - (𝔼 j, v j)) ^ 2) =
        𝔼 i, (v i ^ 2 - 2 * (𝔼 j, v j) * v i + (𝔼 j, v j) ^ 2) := by
      apply Finset.expect_congr rfl
      intro i _
      ring
    _ = (𝔼 i, v i ^ 2) - (𝔼 i, v i) ^ 2 := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty]
      ring

/-- Finite lemma for P022-T4: the population variance of a CDF indicator
equals G_N(x)(1-G_N(x)). Corrected equation (11), p. 861. -/
theorem indicator_population_variance {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (x : ℝ) :
    finiteVariance (fun i => if y i ≤ x then 1 else 0) =
      empiricalCDF y x * (1 - empiricalCDF y x) := by
  rw [finite_variance_second_moment hN]
  have hs : (fun i : Fin N => (if y i ≤ x then (1 : ℝ) else 0) ^ 2) =
      (fun i => if y i ≤ x then (1 : ℝ) else 0) := by
    funext i; split_ifs <;> norm_num
  rw [hs]
  unfold empiricalCDF
  ring

/-- Finite lemma for Lemma 1 and Neyman's inequality: finite covariance
obeys Cauchy-Schwarz with the paper's 1/N variances. pp. 852–853. -/
theorem finite_covariance_cauchy {N : ℕ} (v w : Fin N → ℝ) :
    |finiteCovariance v w| ≤ Real.sqrt (finiteVariance v * finiteVariance w) := by
  have hv : 0 ≤ finiteVariance v := Finset.expect_nonneg (fun i _ => sq_nonneg _)
  have hw : 0 ≤ finiteVariance w := Finset.expect_nonneg (fun i _ => sq_nonneg _)
  have hc := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun i => v i - finiteMean v) (fun i => w i - finiteMean w)
  change finiteCovariance v w ^ 2 ≤ finiteVariance v * finiteVariance w at hc
  have hs := Real.sq_sqrt (mul_nonneg hv hw)
  have hn := Real.sqrt_nonneg (finiteVariance v * finiteVariance w)
  nlinarith [sq_abs (finiteCovariance v w), abs_nonneg (finiteCovariance v w)]

/-- Finite lemma for P022-T8: correct quadrature weights with total mass
one and the correct weighted marginal means make centered and raw covariance
formulas identical. P022-E002; equations (8)–(9), p. 854. -/
theorem centered_quadrature {P : ℕ} (w x y : Fin P → ℝ) (μ ν : ℝ)
    (hw : (∑ i, w i) = 1) (hx : (∑ i, w i * x i) = μ)
    (hy : (∑ i, w i * y i) = ν) :
    (∑ i, w i * (x i - μ) * (y i - ν)) = (∑ i, w i * x i * y i) - μ * ν := by
  have heq : ∀ i, w i * (x i - μ) * (y i - ν) =
      w i * x i * y i - ν * (w i * x i) - μ * (w i * y i) + μ * ν * w i := by
    intro i; ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hw, hx, hy]
  ring

/-- Finite lemma for P022-T3 and Lemma 2: Chebyshev/Markov applied to the
squared deviation under the finite randomization distribution. p. 861. -/
theorem finite_squared_markov (d : Design) (f : Assignment d → ℝ) (ε : ℝ) (hε : 0 < ε) :
    designProbability d (fun π => ε ≤ |f π|) ≤
      designExpectation d (fun π => f π ^ 2) / ε ^ 2 := by
  classical
  unfold designProbability designExpectation
  rw [Finset.expect_div]
  apply Finset.expect_le_expect
  intro π _
  split_ifs with h
  · apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    nlinarith [sq_abs (f π), sq_nonneg (|f π| - ε)]
  · positivity

/-- Finite lemma for Corollary 1: at positive threshold β, the empirical
square tail is at most β^(-1/2) times the empirical third absolute moment.
P022-T17(ii), Corollary 1, p. 856. -/
theorem third_moment_tail_bound {N : ℕ} (y : Fin N → ℝ) (β : ℝ) (hβ : 0 < β) :
    finiteMean (fun i => if β ≤ y i ^ 2 then y i ^ 2 else 0) ≤
      finiteMean (fun i => |y i| ^ 3) / Real.sqrt β := by
  unfold finiteMean
  rw [Finset.expect_div]
  apply Finset.expect_le_expect
  intro i _
  split_ifs with h
  · apply (le_div_iff₀ (Real.sqrt_pos.mpr hβ)).2
    have hs : Real.sqrt β ≤ |y i| := by
      simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt h
    have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg (y i))
    calc
      y i ^ 2 * Real.sqrt β = Real.sqrt β * y i ^ 2 := by ring
      _ ≤ |y i| * y i ^ 2 := hp
      _ = |y i| ^ 3 := by rw [← sq_abs (y i)]; ring
  · positivity

/-- H_N^H=min(G_N,F_N) and H_N^L=max(0,G_N+F_N-1), with hatted
analogues, proof of Proposition 2, pp. 863–864. -/
def frechetCDF (G F : ℝ → ℝ) (B : BoundSide) (x y : ℝ) : ℝ :=
  if B = .H then min (G x) (F y) else max 0 (G x + F y - 1)

/-- The last (seventh) term of the decomposition of N(V̂_N^H-V_N^H),
p. 864, an iterated integral on [-C,C]². -/
def lastIntegralTerm (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (π : Assignment d) : ℝ :=
  (2 * d.N / ((d.N : ℝ) - 1)) *
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      frechetCDF (empiricalCDF (observedTreatment d y1 π))
        (empiricalCDF (observedControl d y0 π)) .H x y -
      frechetCDF (empiricalCDF y1) (empiricalCDF y0) .H x y)

/-- The seven terms on p. 864, labeled T_1,...,T_7 by P022-T6.
Fin 7 uses zero-based labels. The second and fourth terms use squared
means, whereas the first and third use second moments. -/
def sevenTerms (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (π : Assignment d) : Fin 7 → ℝ :=
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  let β1 := (d.N : ℝ) * ((d.m : ℝ) - 1) / (d.m * ((d.N : ℝ) - 1))
  let β0 := (d.N : ℝ) * ((d.k : ℝ) - 1) / (((d.N : ℝ) - 1) * d.k)
  fun j => match j.val with
  | 0 => ((d.N : ℝ) - d.m) / ((d.m : ℝ) - 1) *
      (finiteMean (fun i => a i ^ 2) - β1 * finiteMean (fun i => y1 i ^ 2))
  | 1 => ((d.N : ℝ) - d.m) / ((d.m : ℝ) - 1) *
      (finiteMean a ^ 2 - β1 * finiteMean y1 ^ 2)
  | 2 => ((d.N : ℝ) - d.k) / ((d.k : ℝ) - 1) *
      (finiteMean (fun i => b i ^ 2) - β0 * finiteMean (fun i => y0 i ^ 2))
  | 3 => ((d.N : ℝ) - d.k) / ((d.k : ℝ) - 1) *
      (finiteMean b ^ 2 - β0 * finiteMean y0 ^ 2)
  | 4 => (2 * d.N / ((d.N : ℝ) - 1)) * C *
      (finiteMean a - finiteMean y1 + finiteMean b - finiteMean y0)
  | 5 => (2 * d.N / ((d.N : ℝ) - 1)) *
      (finiteMean a * finiteMean b - finiteMean y1 * finiteMean y0)
  | _ => lastIntegralTerm d y1 y0 C π

/-- N(V̂_N^H-V_N^H)=T_1-T_2+T_3-T_4+T_5-T_6+T_7,
decomposition on p. 864. -/
def sevenTotal (T : Fin 7 → ℝ) : ℝ :=
  T 0 - T 1 + T 2 - T 3 + T 4 - T 5 + T 6

/-- Corrected allocation (ν1,ν2,ν3,ν4,ν5+ν6,ν7+ν8,ε1/2),
P022-E006; corrected proof, pp. 865–868. -/
def correctedAllocation (ν : Fin 8 → ℝ) (ε1 : ℝ) : Fin 7 → ℝ :=
  fun j => match j.val with
  | 0 => ν 0 | 1 => ν 1 | 2 => ν 2 | 3 => ν 3
  | 4 => ν 4 + ν 5 | 5 => ν 6 + ν 7 | _ => ε1 / 2

/-- Finite lemma for P022-T6(a): the corrected allocation sums to ε1
when the first eight ν's sum to ε1/2. pp. 865–868. -/
theorem corrected_allocation_sum (ν : Fin 8 → ℝ) (ε1 : ℝ)
    (hν : (∑ i, ν i) = ε1 / 2) :
    (∑ j, correctedAllocation ν ε1 j) = ε1 := by
  simp [Fin.sum_univ_succ] at hν ⊢
  simp [correctedAllocation]
  linarith

/-- Finite lemma for P022-T6(a): the magnitude of the signed seven-term
sum is bounded by the sum of magnitudes, decomposition on p. 864. -/
theorem seven_total_abs_le (T : Fin 7 → ℝ) :
    |sevenTotal T| ≤ ∑ j, |T j| := by
  simp [sevenTotal, Fin.sum_univ_succ]
  linarith [abs_sub (T 0) (T 1), abs_add_le (T 0 - T 1) (T 2),
    abs_sub (T 0 - T 1 + T 2) (T 3),
    abs_add_le (T 0 - T 1 + T 2 - T 3) (T 4),
    abs_sub (T 0 - T 1 + T 2 - T 3 + T 4) (T 5),
    abs_add_le (T 0 - T 1 + T 2 - T 3 + T 4 - T 5) (T 6)]

/-- P022-T6(a), event inclusion: if positive term tolerances sum to at
most ε, a signed seven-term deviation ≥ε forces some term past its tolerance.
This is the finite budget step in the corrected proof, pp. 865–868. -/
theorem seven_term_budget (T a : Fin 7 → ℝ) (ε : ℝ)
    (ha : ∀ j, 0 < a j) (hbudget : (∑ j, a j) ≤ ε)
    (hlarge : ε ≤ |sevenTotal T|) : ∃ j, a j ≤ |T j| := by
  by_contra h
  push_neg at h
  have hsum : (∑ j, |T j|) < ∑ j, a j :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h j)
  have hn := seven_total_abs_le T
  linarith


/-- The coefficients c_1,...,c_8 of the printed bounds (17)–(22),
pp. 865–867, with C⁴/ν_i² factored out. -/
def termRateCoefficient (θ ρ : ℝ) : Fin 8 → ℝ := fun i => match i.val with
  | 0 => (1 - θ * ρ) ^ 3 / (θ ^ 3 * ρ ^ 3)
  | 1 => 4 * (1 - θ * ρ) ^ 3 / (θ ^ 3 * ρ ^ 3)
  | 2 => (1 - θ * (1 - ρ)) ^ 3 / (θ ^ 3 * (1 - ρ) ^ 3)
  | 3 => 4 * (1 - θ * (1 - ρ)) ^ 3 / (θ ^ 3 * (1 - ρ) ^ 3)
  | 4 => 4 * (1 - θ * ρ) / (θ * ρ)
  | 5 => 4 * (1 - θ * (1 - ρ)) / (θ * (1 - ρ))
  | 6 => 4 * (1 - θ * ρ) / (θ * ρ)
  | _ => 4 * (1 - θ * (1 - ρ)) / (θ * (1 - ρ))


/-- The unshifted four-corner cycle in P022-T7: (0,0),(0,1),(1,0),(1,1),
with n=N,m=floor(N/2). P022-E006; proof defect on p. 868. -/
def cornerWitness : ExperimentSequence :=
  { reciprocalWitness with
    y1 := fun i => if i % 4 < 2 then 0 else 1
    y0 := fun i => if i % 2 = 0 then 0 else 1 }

/-- Uniform law on the four corners, the weak limit in P022-T7. -/
def cornerLaw : JointLaw := ⟨
  (1 / 4 : ℝ≥0∞) • Measure.dirac (0, 0) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (0, 1) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (1, 0) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (1, 1), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem,
      Set.mem_univ, smul_eq_mul, mul_one]
    have hq : (1 / 4 : ℝ≥0∞) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
      simpa using (ENNReal.coe_div (p := (1 : ℝ≥0)) (r := 4) (by norm_num)).symm
    rw [hq]
    norm_cast
    norm_num⟩


/-- A simpler concrete witness for the tolerance defect alone: all fixed
potential outcomes are zero, n=N,m=floor(N/2), C=1. This does not address
the separate wrong-V_N defect. -/
def zeroWitness : ExperimentSequence :=
  { reciprocalWitness with y1 := fun _ => 0, y0 := fun _ => 0 }

/-- Finite/limit lemma for P022-T7(a): with ε1=1, the printed last-term
event has probability 1 and limsup N P=+∞, for any nested population
sequence and any real-valued array. Equation (23), p. 868. -/
theorem zero_tolerance_tail (S : ExperimentSequence)
    (f : (q : ℕ) → Assignment (S.design q) → ℝ) :
    scaledProbabilityLimsup S (fun q π => (0 : ℝ) ≤ |f q π|) = ⊤ := by
  have hp : ∀ q, designProbability (S.design q) (fun π => (0 : ℝ) ≤ |f q π|) = 1 := by
    intro q
    unfold designProbability
    simp only [abs_nonneg, ite_true]
    exact (design_constant _ 1).1
  unfold scaledProbabilityLimsup
  simp_rw [hp, mul_one, S.size]
  apply Filter.Tendsto.limsup_eq
  apply ENNReal.tendsto_ofReal_atTop.comp
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    ((tendsto_add_atTop_iff_nat 4).2 tendsto_id)

/-- P022-T7(a), complete concrete counterexample to (23) as printed:
the zero-outcome sequence satisfies all Proposition 2 assumptions with
θ=1,ρ=1/2,C=1, yet the allowed ε=3,ε1=ε2=ε3=1 makes its scaled tail
limsup +∞. This supplementary witness addresses only the tolerance error. -/
theorem equation23_counterexample :
    Conditions123 zeroWitness originLaw 1 (1 / 2) ∧
    (∀ i, |zeroWitness.y1 i| ≤ 1 ∧ |zeroWitness.y0 i| ≤ 1) ∧
    scaledProbabilityLimsup zeroWitness (fun q π => (1 - 1 : ℝ) ≤
      |lastIntegralTerm (zeroWitness.design q) (rowOutcomes zeroWitness true q)
        (rowOutcomes zeroWitness false q) 1 π|) = ⊤ := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · simpa [zeroWitness] using reciprocal_allocation_limit.1
    · exact reciprocal_allocation_limit.2
    · intro f
      have heq : ∀ q, finiteMean (fun i : Fin (zeroWitness.design q).N =>
          f (zeroWitness.y1 i.val, zeroWitness.y0 i.val)) = f (0, 0) := by
        intro q
        change finiteMean (fun _ : Fin (q + 4) => f (0, 0)) = f (0, 0)
        exact finiteMean_const (by change 0 < q + 4; omega) _
      simp_rw [heq]
      simp [originLaw, ProbabilityMeasure.coe_mk]
    · intro t x _hx
      have heq : ∀ q, empiricalCDF (rowOutcomes zeroWitness t q) x =
          if 0 ≤ x then 1 else 0 := by
        intro q
        cases t <;>
          change finiteMean (fun _ : Fin (q + 4) => if (0 : ℝ) ≤ x then 1 else 0) = _ <;>
          exact finiteMean_const (by omega) _
      simp_rw [heq, origin_cdf]
      exact tendsto_const_nhds
  · intro i
    norm_num [zeroWitness]
  · simpa using zero_tolerance_tail zeroWitness (fun q π =>
      lastIntegralTerm (zeroWitness.design q) (rowOutcomes zeroWitness true q)
        (rowOutcomes zeroWitness false q) 1 π)

/-- Finite randomization lemma for (1): at any fixed position of a uniform
permutation, the expected potential outcome is its population mean.
This uses permutation invariance, not a named sampling axiom. p. 851. -/
theorem permutation_eval_mean {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (i : Fin N) :
    (𝔼 π : Equiv.Perm (Fin N), y (π i)) = finiteMean y := by
  classical
  letI : NeZero N := ⟨by omega⟩
  have hsame : ∀ j : Fin N,
      (𝔼 π : Equiv.Perm (Fin N), y (π i)) = (𝔼 π : Equiv.Perm (Fin N), y (π j)) := by
    intro j
    apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
    intro π
    simp [Equiv.Perm.mul_apply]
  have hperm : ∀ π : Equiv.Perm (Fin N), (𝔼 j, y (π j)) = finiteMean y := by
    intro π
    exact Fintype.expect_equiv π (fun j => y (π j)) y (by intro j; rfl)
  calc
    (𝔼 π : Equiv.Perm (Fin N), y (π i)) =
        𝔼 j : Fin N, 𝔼 π : Equiv.Perm (Fin N), y (π j) := by
      simp_rw [← hsame]
      exact (Fintype.expect_const _).symm
    _ = 𝔼 π : Equiv.Perm (Fin N), 𝔼 j : Fin N, y (π j) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 _π : Equiv.Perm (Fin N), finiteMean y := by simp_rw [hperm]
    _ = finiteMean y := Fintype.expect_const _

/-- Finite randomization lemma for (1): both observed arm means are
unbiased for their finite-population means, with the paper's exact design.
Section 2, p. 851. -/
theorem observed_means_unbiased (d : Design) (y : Fin d.N → ℝ) :
    designExpectation d (fun π => finiteMean (observedTreatment d y π)) = finiteMean y ∧
    designExpectation d (fun π => finiteMean (observedControl d y π)) = finiteMean y := by
  have hN : 0 < d.N := by have := d.population_min; omega
  letI : NeZero d.m := ⟨by have := d.treatment_min; omega⟩
  letI : NeZero d.k := ⟨by have := d.control_min; omega⟩
  constructor
  · unfold designExpectation observedTreatment finiteMean
    rw [Finset.expect_comm]
    simp_rw [permutation_eval_mean hN]
    exact Fintype.expect_const _
  · unfold designExpectation observedControl finiteMean
    rw [Finset.expect_comm]
    simp_rw [permutation_eval_mean hN]
    exact Fintype.expect_const _

/-- P022-T13, the unbiasedness assertion immediately after (1), p. 851:
E_X(τ̂_N)=τ_N under the actual finite uniform randomization. -/
theorem difference_in_means_unbiased (d : Design) (y1 y0 : Fin d.N → ℝ) :
    designExpectation d (estimatedEffect d y1 y0) = averageEffect d y1 y0 := by
  unfold designExpectation estimatedEffect
  rw [Finset.expect_sub_distrib]
  exact congrArg₂ (fun a b : ℝ => a - b)
    (observed_means_unbiased d y1).1 (observed_means_unbiased d y0).2

/-- Finite randomization lemma for P022-T4: E_X(Ĝ_N(x))=G_N(x) and
E_X(F̂_N(x))=F_N(x), the first identities in (11)–(12), p. 861. -/
theorem sampled_cdfs_unbiased (d : Design) (y1 y0 : Fin d.N → ℝ) (x : ℝ) :
    designExpectation d (fun π => empiricalCDF (observedTreatment d y1 π) x) =
      empiricalCDF y1 x ∧
    designExpectation d (fun π => empiricalCDF (observedControl d y0 π) x) =
      empiricalCDF y0 x := by
  constructor
  · exact (observed_means_unbiased d (fun i => if y1 i ≤ x then 1 else 0)).1
  · exact (observed_means_unbiased d (fun i => if y0 i ≤ x then 1 else 0)).2


/-- All probability couplings with the finite empirical marginal laws,
"given only G_N and F_N" in Lemma 1, p. 853. This supplements the finite
multiset formulation with arbitrary Borel couplings of those marginals. -/
def empiricalCompatibleLaws {N : ℕ} (y1 y0 : Fin N → ℝ) : Set JointLaw :=
  {H | ∀ x, lawCDF H true x = empiricalCDF y1 x ∧
    lawCDF H false x = empiricalCDF y0 x}


/-- Finite lemma for P022-T14: the Cauchy-Schwarz covariance term is at
most the arithmetic-mean term, 2 sqrt(AB)≤A+B. Section 2.1, p. 852. -/
theorem sqrt_product_le_arithmetic (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    2 * Real.sqrt (A * B) ≤ A + B := by
  have hs := Real.sq_sqrt (mul_nonneg hA hB)
  have hn := Real.sqrt_nonneg (A * B)
  nlinarith [sq_nonneg (A - B)]

/-- Finite coefficient lemma for P022-T17(iv): with the printed θ,ρ,
the product ab equals 1+(1-θ)/(θ²ρ(1-ρ)) and is at least 1.
Corollary 1, p. 856; positivity of the coefficient product. -/
theorem allocation_coefficient_product (θ ρ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ((1 - θ * ρ) / (θ * ρ)) * ((1 - θ * (1 - ρ)) / (θ * (1 - ρ))) =
      1 + (1 - θ) / (θ ^ 2 * ρ * (1 - ρ)) ∧
    1 ≤ ((1 - θ * ρ) / (θ * ρ)) * ((1 - θ * (1 - ρ)) / (θ * (1 - ρ))) := by
  have heq : ((1 - θ * ρ) / (θ * ρ)) * ((1 - θ * (1 - ρ)) / (θ * (1 - ρ))) =
      1 + (1 - θ) / (θ ^ 2 * ρ * (1 - ρ)) := by
    have ht : θ ≠ 0 := ne_of_gt hθ
    have hr : ρ ≠ 0 := ne_of_gt hρ
    have hc : 1 - ρ ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hn : 0 ≤ (1 - θ) / (θ ^ 2 * ρ * (1 - ρ)) :=
    div_nonneg (by linarith) (by positivity)
  linarith

end
end AronowAudit.P022

