import Mathlib
import SAP.P018a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

/-- A dyad specified by distinct endpoints. -/
def wholeDyad {N : ℕ} (i j : Fin N) (h : i ≠ j) : Dyad N :=
  ⟨{i,j}, by simp [dyads, Finset.mem_powersetCard, h]⟩

/-- Finite-record regularity. Empty blocks are allowed. The total count is
guarded separately wherever it is used as a denominator. -/
def WholeRecordRegular {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : Prop :=
  IsProbabilityMeasure R.μ ∧
  (∀ d : Dyad N, ∀ t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ d : Dyad N, ∀ t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C)

/-- The finite normal-equation contract, with a nonzero normalization c.
Weights are arbitrary fixed real numbers. -/
def wholeRecordContract {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (c : ℝ) : Prop :=
  let G := recordWeightedGram R w
  let H := c⁻¹ • meanMat (repeatedLaw R N) G
  let S := fun ω => ∑ d : Dyad N,
    recordWeightedBlockScore R w (recordWeightedBeta R w) ω d
  meanVec (repeatedLaw R N) S = 0 ∧
  meanMat (repeatedLaw R N) (fun ω => c⁻¹ • G ω) = H ∧
  ((N : ℝ)/c^2) • sandwich H⁻¹ (varMat (repeatedLaw R N) S) =
    varMat (repeatedLaw R N) (fun ω => H⁻¹.mulVec ((Real.sqrt N/c) • S ω)) ∧
  (∀ ω, (G ω).det ≠ 0 →
    Real.sqrt N • (recordWeightedOLS R w ω - recordWeightedBeta R w) =
      (c⁻¹ • G ω)⁻¹.mulVec ((Real.sqrt N/c) • S ω))

/-- Sparse *covariance*, with the separate, conditional conversion to raw
moments only when each block is centred. -/
def wholeRecordSparse {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (β : Vec k) : Prop :=
  let P := repeatedLaw R N
  let q := fun ω d => recordWeightedBlockScore R w β ω d
  (∀ d f : Dyad N, ¬overlap d f → covMat P (fun ω => q ω d) (fun ω => q ω f) = 0) ∧
  varMat P (fun ω => ∑ d : Dyad N, q ω d) =
    ∑ d : Dyad N, (varMat P (fun ω => q ω d) +
      ∑ f ∈ neighbors d, covMat P (fun ω => q ω d) (fun ω => q ω f)) ∧
  ((∀ d : Dyad N, meanVec P (fun ω => q ω d) = 0) →
    (∀ d f : Dyad N, covMat P (fun ω => q ω d) (fun ω => q ω f) =
      meanMat P (fun ω => outer (q ω d) (q ω f))) ∧
    varMat P (fun ω => ∑ d : Dyad N, q ω d) =
      meanMat P (fun ω => meat members (q ω)))

/-- Identical sign-model records, including the singleton-record case. -/
def wholeRepeatedSign (m : ℕ) : RepeatedKernel Bool 1 :=
  ⟨fairLaw, fun _ _ => m, fun _ _ _ _ _ => ![1],
    fun _ _ _ u v => signValue u + signValue v⟩

/-- The two-regressor check model: independent uniform Z and fair sign W,
X=(1,Z_i+Z_j), Y=W_i+W_j, and unit weights. -/
def wholeMixedKernel : Kernel (ℝ × Bool) 2 :=
  ⟨uniformUnitLaw.prod fairLaw, fun u v => ![1,u.1+v.1],
    fun u v => signValue u.2+signValue v.2⟩

def T12Checks : Prop :=
  (∀ N m : ℕ, 3 ≤ N → 0 < m → repeatedTarget (wholeRepeatedSign m) N = !![4]) ∧
  (∀ N : ℕ, 3 ≤ N → weightedTarget signKernel (fun _ : Dyad N => 1) = !![4]) ∧
  Standing wholeMixedKernel ∧
  populationGram wholeMixedKernel = !![1,0;0,2/3] ∧
  populationBeta wholeMixedKernel = 0 ∧
  (∀ N : ℕ, 3 ≤ N → weightedTarget wholeMixedKernel (fun _ : Dyad N => 1) =
    !![4,0;0,3*(N : ℝ)/((N : ℝ)-1)])

/-- P018-T12; p. 568 (PDF p. 5), V_r; p. 576 (PDF p. 13), V_w.
The corrected repeated and weighted targets use normalized expected Gram
matrices and the unconditional variance of the total score. They are exact
covariances, with centred total scores, expected normalized Grams and exact
linearization on every nonsingular sample. Block covariances have the sparse
form; raw moments may replace them if every block has mean zero. Singleton
records and unit weights reduce to equation (1), either normalization gives
the same repeated target, and the scalar and two-regressor model checks have
the stated values. The usual measure-theoretic conditions are assumed. -/
def T12WholeStatement : Prop :=
  (∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    WholeRecordRegular R N → 2 ≤ N → 0 < repeatedL R N →
    (repeatedH R N).det ≠ 0 →
    wholeRecordContract (N := N) R (fun _ _ => 1) (repeatedL R N)) ∧
  (∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    WholeRecordRegular R N → 2 ≤ N →
    ∀ w : (d : Dyad N) → Fin (R.T N d) → ℝ,
    (recordWeightedH R w).det ≠ 0 → wholeRecordContract R w (Dreal N)) ∧
  (∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    WholeRecordRegular R N → ∀ w β, wholeRecordSparse (N := N) R w β) ∧
  (∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k),
    Standing K → 2 ≤ N →
    repeatedTarget (singleRecord K) N = trueTarget K N ∧
    weightedTarget K (fun _ : Dyad N => 1) = trueTarget K N) ∧
  (∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    2 ≤ N → 0 < repeatedL R N →
    (meanMat (repeatedLaw R N) (repeatedGram R)).det ≠ 0 →
    repeatedTarget R N = ((N : ℝ)/(Dreal N)^2) •
      sandwich ((Dreal N)⁻¹ • meanMat (repeatedLaw R N) (repeatedGram R))⁻¹
        (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
          repeatedBlockScore R (repeatedBeta R N) ω d))) ∧ T12Checks

/-- A deterministic, common-record, bounded repeated-data counterexample to
the sparse raw-moment prescription in the opening repair of T2. -/
def wholeRepairWitness : RepeatedKernel Unit 1 :=
  ⟨Measure.dirac (), fun _ d =>
    if (firstUnit d).val = 0 ∧ (secondUnit d).val = 1 then 2
    else if (firstUnit d).val = 2 ∧ (secondUnit d).val = 3 then 3 else 1,
    fun _ _ _ _ _ => ![1],
    fun _ _ t _ _ => if t.val = 0 then 0 else if t.val = 1 then 1 else -2⟩

def T2WitnessInput : Prop :=
  RepeatedStanding wholeRepairWitness ∧
  (∀ N d, wholeRepairWitness.T N d ≤ 3) ∧
  (∃ fY : ℕ → ℝ, ∀ N d (t : Fin (wholeRepairWitness.T N d)) u v,
    wholeRepairWitness.Y N d t u v = fY t.val) ∧
  repeatedL wholeRepairWitness 4 = 9 ∧
  (∀ ω : Fin 4 → Unit, repeatedGram wholeRepairWitness ω = !![9]) ∧
  (repeatedH wholeRepairWitness 4).det = 1

def T2WitnessProjection : Prop :=
  repeatedBeta wholeRepairWitness 4 = 0 ∧
  (∀ (ω : Fin 4 → Unit) (d : Dyad 4),
    repeatedBlockScore wholeRepairWitness (repeatedBeta wholeRepairWitness 4) ω d =
      if (firstUnit d).val = 0 ∧ (secondUnit d).val = 1 then ![1]
      else if (firstUnit d).val = 2 ∧ (secondUnit d).val = 3 then ![-1] else 0) ∧
  (∀ ω : Fin 4 → Unit,
    (∑ d : Dyad 4, repeatedBlockScore wholeRepairWitness
      (repeatedBeta wholeRepairWitness 4) ω d) = 0)

def T2WitnessFailure : Prop :=
  let P := repeatedLaw wholeRepairWitness 4
  let q := fun ω d => repeatedBlockScore wholeRepairWitness
    (repeatedBeta wholeRepairWitness 4) ω d
  varMat P (fun ω => ∑ d : Dyad 4, q ω d) = 0 ∧
  meanMat P (fun ω => meat members (q ω)) = !![2] ∧
  varMat P (fun ω => ∑ d : Dyad 4, q ω d) ≠
    meanMat P (fun ω => meat members (q ω))

/-- P018-T2; p. 566 (PDF p. 3), equation (2); p. 573 (PDF p. 10), equation (6).
The printed claim is false: the opening repair's sparse unconditional
raw-score-moment replacement for repeated blocks fails under S6/S9. With
constant iid units and intercept-only common responses 0,1,-2, give dyad
{1,2} two records, {3,4} three, and the other four dyads one. The Gram is 9,
the population slope is zero, and the only nonzero block scores are +1 and
-1 on disjoint dyads. The total-score variance is zero but the sparse raw
meat is 2. This refutes the repeated-block prescription, not the valid
single-record assertions (i)-(v). The usual measure-theoretic conditions
are assumed and are satisfied by this finite deterministic model. -/
def T2WholeStatement : Prop := T2WitnessInput ∧ T2WitnessProjection ∧ T2WitnessFailure

/-- Sigma-algebra generated by one regressor row. -/
def wholeRowSigma {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d : Dyad N) : MeasurableSpace (Fin N → U) :=
  MeasurableSpace.comap (fun ω => design K ω d) inferInstance

/-- Conditional covariance for two record residuals given the entire design. -/
def wholeRepeatedDesignSigma {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) : MeasurableSpace (Fin N → U) :=
  MeasurableSpace.comap (fun ω => fun (d : Dyad N) (t : Fin (R.T N d)) =>
    repeatedX R ω d t) inferInstance

def wholeRepeatedResidual {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (ω : Fin N → U) (d : Dyad N) (t : Fin (R.T N d)) : ℝ :=
  repeatedY R ω d t - dot (repeatedX R ω d t) (repeatedBeta R N)

/-- Literal conditional middle factor in the printed repeated display;
the diagonal block is included once and the sum is over ordered overlaps. -/
def wholePrintedRepeatedMeat {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : Mat k :=
  let P := repeatedLaw R N
  let e := wholeRepeatedResidual R
  let m := fun d t => MeasureTheory.condExp (wholeRepeatedDesignSigma (N := N) R) P (fun ω => e ω d t)
  meanMat P (fun ω => ∑ d : Dyad N, ∑ f : Dyad N,
    if overlap d f then ∑ t, ∑ u,
      (MeasureTheory.condExp (wholeRepeatedDesignSigma (N := N) R) P (fun v => (e v d t-m d t v)*(e v f u-m f u v)) ω) •
        outer (repeatedX R ω d t) (repeatedX R ω f u) else 0)

/-- Literal conditional weighted middle factor, with weights on both sides. -/
def wholePrintedWeightedMeat {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) : Mat k :=
  let P := unitSampleLaw K N
  let e := fun ω d => response K ω d - dot (design K ω d) (weightedPopulationBeta K w)
  let m := fun d => MeasureTheory.condExp (designSigma (N := N) K) P (fun ω => e ω d)
  meanMat P (fun ω => ∑ d : Dyad N, ∑ f : Dyad N,
    if overlap d f then
      (w d*w f*MeasureTheory.condExp (designSigma (N := N) K) P (fun v => (e v d-m d v)*(e v f-m f v)) ω) •
        outer (design K ω d) (design K ω f) else 0)

def T1Conditional : Prop :=
  (∀ N : ℕ, 3 ≤ N → ∀ d : Dyad N,
    MeasureTheory.condExp (wholeRowSigma nonlinearKernel d) (unitSampleLaw nonlinearKernel N)
      (fun ω => response nonlinearKernel ω d) =ᵐ[unitSampleLaw nonlinearKernel N]
        (fun ω => (design nonlinearKernel ω d 1-2)^2)) ∧
  ¬(∃ b : Vec 2, ∀ᵐ uv ∂ uniformUnitLaw.prod uniformUnitLaw,
    nonlinearKernel.Y uv.1 uv.2 = dot (nonlinearKernel.X uv.1 uv.2) b)

def T1ScoreFacts : Prop :=
  (∀ z t : ℝ, populationResidual nonlinearKernel z t = (z+t)^2-2/3) ∧
  (∀ N : ℕ, 3 ≤ N →
    (∀ d : Dyad N,
      (∫ ω, epsilon nonlinearKernel ω d ∂ unitSampleLaw nonlinearKernel N) = 0 ∧
      (∫ ω, design nonlinearKernel ω d 1*epsilon nonlinearKernel ω d
        ∂ unitSampleLaw nonlinearKernel N) = 0 ∧
      meanVec (unitSampleLaw nonlinearKernel N) (fun ω =>
        score (design nonlinearKernel ω d) (epsilon nonlinearKernel ω d)) = 0) ∧
    (∀ d f : Dyad N, ¬overlap d f → meanMat (unitSampleLaw nonlinearKernel N)
      (fun ω => outer (score (design nonlinearKernel ω d) (epsilon nonlinearKernel ω d))
        (score (design nonlinearKernel ω f) (epsilon nonlinearKernel ω f))) = 0) ∧
    (∀ d f : Dyad N, d ≠ f → overlap d f → meanMat (unitSampleLaw nonlinearKernel N)
      (fun ω => outer (score (design nonlinearKernel ω d) (epsilon nonlinearKernel ω d))
        (score (design nonlinearKernel ω f) (epsilon nonlinearKernel ω f))) = nonlinearGamma))

def T1PrintedZeros : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    (∀ d : Dyad N, conditionalResidualCov nonlinearKernel d d =ᵐ[unitSampleLaw nonlinearKernel N] 0) ∧
    (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm nonlinearKernel d f) = 0 ∧
    wholePrintedRepeatedMeat (singleRecord nonlinearKernel) N = 0 ∧
    wholePrintedWeightedMeat nonlinearKernel (fun _ : Dyad N => 1) = 0

def T1VarianceDisplay : Prop :=
  (∀ N : ℕ, 3 ≤ N → varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) =
    !![2*(N : ℝ)*((N : ℝ)-1)*(2*(N : ℝ)+3)/45,
       4*(N : ℝ)*((N : ℝ)-1)*(2*(N : ℝ)+3)/45;
       4*(N : ℝ)*((N : ℝ)-1)*(2*(N : ℝ)+3)/45,
       4*(N : ℝ)*((N : ℝ)-1)*(158*(N : ℝ)+115)/945]) ∧
  Tendsto (fun N : ℕ => ((N : ℝ)/(Dreal N)^2) •
    varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel)) atTop
      (𝓝 ((4 : ℝ) • nonlinearGamma)) ∧
  nonlinearVstar = (4 : ℝ) • sandwich nonlinearQ⁻¹ nonlinearGamma

/-- P018-T1; p. 566 (PDF p. 3), equation (2); p. 573 (PDF p. 10), equation (6)
and Sigma; pp. 568, 576, V_r and V_w.
For iid uniform units, X=(1,2+Z_i+Z_j) and Y=(Z_i+Z_j)^2 satisfy the bounded
dyadic projection assumptions and almost-sure sample rank. The conditional
mean is quadratic and not affine. All printed conditional covariance meats,
including the singleton repeated and unit-weight extensions, are zero.
The centred scores have the displayed H, overlapping Gamma, exact nonzero
finite variance and positive leading limit. The true target tends to
4 Q^{-1} Gamma Q^{-1}=V_*, the scaled estimator has that Gaussian limit,
and the sandwich converges in probability to V_*. The usual
measure-theoretic conditions are assumed. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  (∀ z : Fin 3 → ℝ,
    (Matrix.det (!![1,2+z 0+z 1;1,2+z 0+z 2] : Mat 2)) = z 2-z 1) ∧
  T1Conditional ∧ T1ScoreFacts ∧ T1PrintedZeros ∧ T1VarianceDisplay

/-- Unit sign sum, actual fitted meat and actual scalar sandwich. -/
def wholeSignSum {N : ℕ} (ω : Fin N → Bool) : ℝ := ∑ i, signValue (ω i)
def wholeSignMeat {N : ℕ} (ω : Fin N → Bool) : ℝ :=
  meat members (fun d => score (design signKernel ω d)
    (fittedResidual (design signKernel ω) (response signKernel ω) d)) 0 0
def wholeSignVariance {N : ℕ} (ω : Fin N → Bool) : ℝ :=
  sampleVariance members (design signKernel ω) (response signKernel ω) 0 0
def wholeSignLinear {N : ℕ} (a : Fin N → ℝ) (ω : Fin N → Bool) : ℝ :=
  ∑ i, a i*signValue (ω i)

def T3Fit : Prop :=
  populationGram signKernel = !![1] ∧
  (∀ N : ℕ, 4 ≤ N →
    (∀ ω : Fin N → Bool,
      sampleGram (design signKernel ω) = !![Dreal N] ∧ 0 < Dreal N ∧
      sampleOLS (design signKernel ω) (response signKernel ω) = ![2*wholeSignSum ω/(N : ℝ)] ∧
      (∀ d : Dyad N, epsilon signKernel ω d = response signKernel ω d ∧
        fittedResidual (design signKernel ω) (response signKernel ω) d =
          signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) -
            2*wholeSignSum ω/(N : ℝ) ∧
        |fittedResidual (design signKernel ω) (response signKernel ω) d| ≤ 4)) ∧
    varMat (unitSampleLaw signKernel N) (scoreSum signKernel) = !![(N : ℝ)*((N : ℝ)-1)^2] ∧
    printedSigma signKernel N = !![(N : ℝ)*((N : ℝ)-1)^2])

def T3Overlap : Prop := ∀ N : ℕ, ∀ r : Dyad N → ℝ,
  (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then r d*r f else 0) =
    (∑ i : Fin N, (∑ d : Dyad N, if i ∈ members d then r d else 0)^2) - ∑ d : Dyad N, (r d)^2

def T3SampleFormulas : Prop := ∀ N : ℕ, 4 ≤ N →
  (∀ ω : Fin N → Bool,
    wholeSignMeat ω = ((N : ℝ)-2)*((N : ℝ)-3)*((N : ℝ)-(wholeSignSum ω)^2/(N : ℝ)) ∧
    wholeSignVariance ω = wholeSignMeat ω/(Dreal N)^2 ∧
    (N : ℝ)*wholeSignVariance ω =
      (4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)-1)^2)*(1-(wholeSignSum ω)^2/(N : ℝ)^2)) ∧
  (∫ ω, wholeSignMeat ω ∂ unitSampleLaw signKernel N) - (N : ℝ)*((N : ℝ)-1)^2 =
    (-4*(N : ℝ)+6)*((N : ℝ)-1) ∧
  ((N : ℝ)/(Dreal N)^2)*((∫ ω, wholeSignMeat ω ∂ unitSampleLaw signKernel N) -
    (N : ℝ)*((N : ℝ)-1)^2) = (-16*(N : ℝ)+24)/((N : ℝ)*((N : ℝ)-1)) ∧
  (∫ ω, (N : ℝ)*wholeSignVariance ω ∂ unitSampleLaw signKernel N) =
    4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)*((N : ℝ)-1))

def T3MeanLimits : Prop :=
  Tendsto (fun N : ℕ => (∫ ω, wholeSignMeat ω ∂ unitSampleLaw signKernel N) -
    (N : ℝ)*((N : ℝ)-1)^2) atTop atBot ∧
  Tendsto (fun N : ℕ => ((N : ℝ)/(Dreal N)^2)*
    ((∫ ω, wholeSignMeat ω ∂ unitSampleLaw signKernel N) - (N : ℝ)*((N : ℝ)-1)^2))
    atTop (𝓝 0) ∧
  Tendsto (fun N : ℕ => ∫ ω, (N : ℝ)*wholeSignVariance ω ∂ unitSampleLaw signKernel N)
    atTop (𝓝 4)

/-- Fourth mixed sign moment, including coincident indices. -/
def WholeFourthSignMoment : Prop := ∀ N : ℕ, ∀ i j k l : Fin N,
  (∫ ω, signValue (ω i)*signValue (ω j)*signValue (ω k)*signValue (ω l)
    ∂ unitSampleLaw signKernel N) =
    (if i=j ∧ k=l then 1 else 0) + (if i=k ∧ j=l then 1 else 0) +
      (if i=l ∧ j=k then 1 else 0) - (if i=j ∧ j=k ∧ k=l then 2 else 0)

def T3LinearCovariance : Prop := ∀ N : ℕ, ∀ a b c d : Fin N → ℝ,
  ProbabilityTheory.covariance (fun ω => wholeSignLinear a ω*wholeSignLinear b ω)
    (fun ω => wholeSignLinear c ω*wholeSignLinear d ω) (unitSampleLaw signKernel N) =
    dot a c*dot b d + dot a d*dot b c - 2*∑ i, a i*b i*c i*d i

def T3SignMoments : Prop :=
  (∀ N : ℕ,
    (∫ ω, (wholeSignSum ω)^4 ∂ unitSampleLaw signKernel N) = 3*(N : ℝ)^2-2*(N : ℝ) ∧
    ProbabilityTheory.variance (fun ω => (wholeSignSum ω)^2) (unitSampleLaw signKernel N) =
      2*(N : ℝ)*((N : ℝ)-1)) ∧
  (∀ N : ℕ, 4 ≤ N →
    ProbabilityTheory.variance (fun ω => (N : ℝ)*wholeSignVariance ω) (unitSampleLaw signKernel N) =
      32*((N : ℝ)-2)^2*((N : ℝ)-3)^2/((N : ℝ)^3*((N : ℝ)-1)^3)) ∧
  Tendsto (fun N : ℕ => ProbabilityTheory.variance (fun ω => (N : ℝ)*wholeSignVariance ω)
    (unitSampleLaw signKernel N)) atTop (𝓝 0)

/-- Real six-endpoint arrays give exactly the disjoint-union configuration
excluded by the six printed dependence cases. Indices are zero based here. -/
def T3FittedCovariances : Prop :=
  (∀ N : ℕ, ∀ hN : 6 ≤ N,
    let d12 := wholeDyad (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ (by intro h; have he : (0 : ℕ) = 1 := congrArg Fin.val h; omega)
    let d13 := wholeDyad (⟨0, by omega⟩ : Fin N) ⟨2, by omega⟩ (by intro h; have he : (0 : ℕ) = 2 := congrArg Fin.val h; omega)
    let d45 := wholeDyad (⟨3, by omega⟩ : Fin N) ⟨4, by omega⟩ (by intro h; have he : (3 : ℕ) = 4 := congrArg Fin.val h; omega)
    let d46 := wholeDyad (⟨3, by omega⟩ : Fin N) ⟨5, by omega⟩ (by intro h; have he : (3 : ℕ) = 5 := congrArg Fin.val h; omega)
    let e := fun ω d => fittedResidual (design signKernel ω) (response signKernel ω) d
    ProbabilityTheory.covariance (fun ω => e ω d12*e ω d13) (fun ω => e ω d45*e ω d46)
      (unitSampleLaw signKernel N) = 16*((N : ℝ)+6)/(N : ℝ)^3 ∧
    0 < 16*((N : ℝ)+6)/(N : ℝ)^3 ∧
    ProbabilityTheory.covariance (fun ω => epsilon signKernel ω d12*epsilon signKernel ω d13)
      (fun ω => epsilon signKernel ω d45*epsilon signKernel ω d46) (unitSampleLaw signKernel N) = 0 ∧
    overlap d12 d13 ∧ overlap d45 d46 ∧
    ({d12,d13,d45,d46} : Finset (Dyad N)).card = 4 ∧
    Disjoint (members d12 ∪ members d13) (members d45 ∪ members d46)) ∧
  (∀ i j : Fin 8, ∀ hij : i ≠ j, ∀ ω : Fin 8 → Bool,
    fittedResidual (design signKernel ω) (response signKernel ω) (wholeDyad i j hij) =
      signResidual8 (fun l => signValue (ω l)) i j) ∧
  (∀ f g : (Fin 8 → ℝ) → ℝ,
    fairCov8 f g = ProbabilityTheory.covariance
      (fun ω => f (fun i => signValue (ω i))) (fun ω => g (fun i => signValue (ω i)))
        (unitSampleLaw signKernel 8))

def T3InverseDet : Prop :=
  (populationGram inverseKernel).det =
    2*ProbabilityTheory.variance (fun t => Real.exp (-t)) paretoUnitLaw ∧
  0 < ProbabilityTheory.variance (fun t => Real.exp (-t)) paretoUnitLaw

def T3InverseAllSizes : Prop := ∀ N : ℕ, 3 ≤ N →
  (∀ᵐ ω ∂ unitSampleLaw inverseKernel N, (sampleGram (design inverseKernel ω)).det ≠ 0) ∧
  (∀ m : ℕ, 1 ≤ m → ENNReal.ofReal (Real.exp (2*m)/(4*(m : ℝ)^N)) ≤
    ∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm
      (((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹)) ∂ unitSampleLaw inverseKernel N) ∧
  (∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm
    (((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹)) ∂ unitSampleLaw inverseKernel N) = ∞

/-- P018-T3; pp. 573-574 (PDF pp. 10-11), Appendix B.
In the intercept fair-sign model the fit, residual bound, ordered-overlap
identity, exact meat, target, means, fourth moments and scaled variance have
the displayed formulas. The raw mean error diverges while its normalized
version vanishes, and the sandwich remains consistent. Products of fitted
residuals on disjoint endpoint unions have the stated positive covariance,
while another covariance is negative; these are actual OLS residuals and
the disjoint configuration lies outside the six printed cases. The
deterministic missing-N and spike examples invalidate the printed moment
inferences. The bounded inverse-design example has determinant twice
Var(exp(-T))>0, almost-sure rank for every N>=3, inverse convergence in
probability and the displayed infinite extended inverse-norm expectation
for every N>=3. The usual measure-theoretic conditions are assumed. -/
def T3WholeStatement : Prop :=
  T3Statement ∧ T3Fit ∧ T3Overlap ∧ T3SampleFormulas ∧ T3MeanLimits ∧
    T3LinearCovariance ∧ T3SignMoments ∧ T3FittedCovariances ∧ T3InverseDet ∧ T3InverseAllSizes

/-- Sign coordinates and the joint Gaussian polynomial limit. -/
def wholePairZ {N : ℕ} (ω : Fin N → Bool × Bool) (i : Fin N) : ℝ := signValue (ω i).1
def wholePairW {N : ℕ} (ω : Fin N → Bool × Bool) (i : Fin N) : ℝ := signValue (ω i).2
def wholeDegeneracyAtom : Fin 8 → Bool × Bool :=
  ![(true,true),(true,false),(false,true),(false,false),
    (true,true),(true,false),(false,true),(false,false)]
def wholeSecondOrderMap (x : Vec 2) : Vec 2 := ![2*x 0*x 1,4*((x 0)^2+(x 1)^2-1)]
def wholeSecondOrderLaw : Measure (Vec 2) :=
  (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map wholeSecondOrderMap
def wholeSecondOrderStatistic (N : ℕ) (ω : Fin N → Bool × Bool) : Vec 2 :=
  ![(N : ℝ)*sampleOLS (design signPairKernel ω) (response signPairKernel ω) 1,
    (N : ℝ)^2*sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1]

def T7Rank : Prop := ∀ N : ℕ, 3 ≤ N →
  (∀ ω : Fin N → Bool × Bool,
    (sampleGram (design signPairKernel ω)).det = 0 ↔
      ∃ b : Bool, ∀ i, (ω i).1 = b) ∧
  unitSampleLaw signPairKernel N {ω | (sampleGram (design signPairKernel ω)).det = 0} =
    ENNReal.ofReal ((2 : ℝ)/(2 : ℝ)^N)

def T7Moments : Prop :=
  meanVec (signPairKernel.μ.prod signPairKernel.μ)
    (fun uv => score (signPairKernel.X uv.1 uv.2) (signPairKernel.Y uv.1 uv.2)) = 0 ∧
  (∀ u v, populationResidual signPairKernel u v = signPairKernel.Y u v) ∧
  (∀ N : ℕ, 3 ≤ N → ∀ d f : Dyad N, d ≠ f → overlap d f →
    (∫ ω, (epsilon signPairKernel ω d)^2 ∂ unitSampleLaw signPairKernel N) = 2 ∧
    (∫ ω, epsilon signPairKernel ω d*epsilon signPairKernel ω f ∂ unitSampleLaw signPairKernel N) = 1 ∧
    meanMat (unitSampleLaw signPairKernel N) (fun ω =>
      outer (design signPairKernel ω d) (design signPairKernel ω f)) = !![1,1;1,1]) ∧
  scoreH signPairKernel = (2 : ℝ) • (!![1,1;1,2] : Mat 2) ∧
  (∀ N : ℕ, 3 ≤ N → varMat (unitSampleLaw signPairKernel N) (scoreSum signPairKernel) =
    (2*Dreal N) • (!![1,1;1,2] : Mat 2) +
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • (!![1,1;1,1] : Mat 2)) ∧
  (∀ N : ℕ, 3 ≤ N → ∀ d f : Dyad N, d ≠ f → overlap d f →
    meanMat (unitSampleLaw signPairKernel N) (fun ω => outer
      (score (design signPairKernel ω d) (epsilon signPairKernel ω d))
      (score (design signPairKernel ω f) (epsilon signPairKernel ω f))) = !![1,1;1,1])

def T7Atom : Prop :=
  meat eightMembers (fun d => score (degeneracyX d)
    (fittedResidual degeneracyX degeneracyY d)) = !![240,160;160,64] ∧
  unitSampleLaw signPairKernel 8 {wholeDegeneracyAtom} = ENNReal.ofReal ((4 : ℝ)⁻¹^8) ∧
  0 < unitSampleLaw signPairKernel 8 {wholeDegeneracyAtom} ∧
  sampleGram (design signPairKernel wholeDegeneracyAtom) = !![28,24;24,48] ∧
  sampleOLS (design signPairKernel wholeDegeneracyAtom) (response signPairKernel wholeDegeneracyAtom) = 0 ∧
  meat members (fun d => score (design signPairKernel wholeDegeneracyAtom d)
    (fittedResidual (design signPairKernel wholeDegeneracyAtom)
      (response signPairKernel wholeDegeneracyAtom) d)) = !![240,160;160,64] ∧
  sampleVariance members (design signPairKernel wholeDegeneracyAtom)
    (response signPairKernel wholeDegeneracyAtom) = !![3/8,-1/48;-1/48,-13/288]

def T7SlopeApproximation : Prop := inProbability (unitSampleLaw signPairKernel) (fun N ω =>
  (N : ℝ)*sampleOLS (design signPairKernel ω) (response signPairKernel ω) 1 -
    2*((∑ i, wholePairZ ω i)/Real.sqrt N)*
      ((∑ i, wholePairZ ω i*wholePairW ω i)/Real.sqrt N))

def T7JointLimit : Prop :=
  weakLimit (unitSampleLaw signPairKernel) wholeSecondOrderStatistic wholeSecondOrderLaw

/-- P018-T7; pp. 565-567 (PDF pp. 2-4), Lemma 1 and Proposition 1.
The bounded iid sign-pair model has Q=[[1,1],[1,2]], beta=0, the stated
residual and score moments, and rank failure probability 2^(1-N). Its exact
target tends to diag(4,0). The specified eight-unit sample has positive
probability, the displayed Gram, OLS coefficient, meat and negative slope
variance. Jointly (N beta_hat_slope,N^2 V_hat_22) tends to
(2AB,4(A^2+B^2-1)) for independent standard normals A,B. The negative
variance probability tends to 1-exp(-1/2)>0; on such samples no real square
root exists. The pivot completed by zero when V_hat_22<=0 has no standard
normal limit. Nevertheless N V_hat tends in probability to diag(4,0) and
N V_hat-V_N tends to zero. The usual measure-theoretic conditions are
assumed; the ordinary inverse is used on full-rank samples and the matrix
inverse supplies the zero completion on singular samples. -/
def T7WholeStatement : Prop :=
  T7Statement ∧ T7Rank ∧ T7Moments ∧
  (populationGram signPairKernel).det = 1 ∧
  (populationGram signPairKernel)⁻¹ = !![2,-1;-1,1] ∧
  (∀ N : ℕ, ∀ ω : Fin N → Bool × Bool, ∀ d : Dyad N,
    |fittedResidual (design signPairKernel ω) (response signPairKernel ω) d| ≤ 4) ∧
  Tendsto (trueTarget signPairKernel) atTop (𝓝 (!![4,0;0,0] : Mat 2)) ∧
  T7Atom ∧ T7JointLimit ∧
  (((gaussianReal 0 1).prod (gaussianReal 0 1)) {x | x.1^2+x.2^2 < 1}).toReal =
    1-Real.exp (-1/2) ∧ 0 < 1-Real.exp (-1/2) ∧
  (∀ N : ℕ, ∀ ω : Fin N → Bool × Bool,
    sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1 < 0 →
    ¬∃ r : ℝ, r^2 = sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1) ∧
  (∀ N : ℕ, ∀ ω : Fin N → Bool × Bool,
    sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1 ≤ 0 →
    coefficientError signPairKernel ω 1 /
      Real.sqrt (sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1) = 0) ∧
  ¬weakLimit (unitSampleLaw signPairKernel) (fun N ω => coefficientError signPairKernel ω 1 /
    Real.sqrt (sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1))
      (gaussianReal 0 1) ∧
  inProbability (unitSampleLaw signPairKernel) (fun N ω =>
    (N : ℝ) • sampleVariance members (design signPairKernel ω) (response signPairKernel ω) -
      trueTarget signPairKernel N)

end SAP.P018a
