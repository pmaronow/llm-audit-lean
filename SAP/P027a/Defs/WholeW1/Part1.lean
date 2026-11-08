import Mathlib
import SAP.P027a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

/-- The normalized Lebesgue law on the half-open start interval. All uses below
have a strictly positive finite length. -/
def wholeStartMeasure (L : ℝ) : Measure ℝ :=
  (ENNReal.ofReal L)⁻¹ • volume.restrict (Set.Ico 0 L)

/-- Exact continuous-start realization of a four-phase, eight-unit design.
The statistic identity identifies the entire sample law, including all moments. -/
def FourPhaseStartWhole (D : Design (Fin 8) (Fin 4)) (x : Fin 8 → ℝ)
    (a b : ℝ) : Prop :=
  let L := 2 * (a + b)
  let ν := wholeStartMeasure L
  let cell := fun g : Fin 4 => Set.Ico (fourLeft a b g)
    (fourLeft a b g + if g.val % 2 = 0 then a else b)
  let s := fun u k => decide (systematicSelected x 2 u k)
  0 < L ∧ IsProbabilityMeasure ν ∧
  (∀ u ∈ Set.Ico 0 L, ∃! g : Fin 4, u ∈ cell g) ∧
  (∀ g, ν (cell g) = ENNReal.ofReal (D.weight g)) ∧
  (∀ g u, u ∈ cell g → s u = D.selected g) ∧
  (∀ F : ((Fin 8 → Bool) → ℝ),
    Integrable (fun u => F (s u)) ν ∧
    (∫ u, F (s u) ∂ν) = expect D (fun g => F (D.selected g)))

/-- Extra explicit arithmetic of the eight-unit periodic witness. Indices are
zero-based, so the low-size units have even indices. -/
def Periodic8WholeDetails : Prop :=
  (∑ k, periodicSize8 k) = 48 ∧
  (∀ k, cumulativeLeft periodicSize8 k =
    (![0,2,12,14,24,26,36,38] : Fin 8 → ℝ) k) ∧
  (∀ k, pi periodic8 k = printedPPS 2 periodicSize8 k) ∧
  (∀ k, alternating8 k = periodicSize8 k / 4 -
    (∑ l, periodicSize8 l / 4) / 8) ∧
  (∀ g : Fin 4, (∑ k, if periodic8.selected g k then alternating8 k else 0) =
    (![(-2),2,(-2),2] : Fin 4 → ℝ) g) ∧
  biasA periodic8 alternating8 =
    -(∑ g : Fin 4, (∑ k, if periodic8.selected g k then alternating8 k else 0)^2) ∧
  variance periodic8 (htTotal periodic8 alternating8) = 576/5 ∧
  expect periodic8 (htVarianceEstimator periodic8 alternating8) = 496/5 ∧
  expect periodic8 (htVarianceEstimator periodic8 alternating8) =
    variance periodic8 (htTotal periodic8 alternating8) + biasA periodic8 alternating8 ∧
  (expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) -
    variance periodic8 (htMean periodic8 alternating8)) = biasA periodic8 alternating8/64 ∧
  (expect periodic8 (fun g => htVarianceEstimator periodic8 alternating8 g/64) -
    variance periodic8 (htMean periodic8 alternating8)) /
      variance periodic8 (htMean periodic8 alternating8) = -5/36 ∧
  variance periodic8 (htMean periodic8 alternating8) ≤
    expect periodic8 (fun g => c2Estimator periodic8 alternating8 g/64) ∧
  (∀ g k, periodic8.selected g k = true →
    alternating8 k / (pi periodic8 k / 2) = htTotal periodic8 alternating8 g)

/-- The periodic population has q=2r phases and m copies of each phase.
Its ordinary list index is `phaseIndex k = 2i+b+qj`; its group consists of the
indices g,g+q,...,g+(m-1)q (with the one-based shift understood). -/
def PeriodicSizesWhole : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r), 0 < m →
  let K := (Σ _ : Fin r × Fin 2, Fin m)
  let N : ℝ := m * (2*r)
  (∑ k : K, phaseSize k) = 6*N ∧
  (∑ k : K, phaseSize k) / N = 6 ∧
  (∑ k : K, (phaseSize k-6)^2) = 16*N ∧
  (∑ k : K, (phaseSize k-6)^2)/(N-1) = 16*N/(N-1) ∧
  (∀ k : K, pi (phaseOriginal r m hr) k =
    (m:ℝ)*phaseSize k/(∑ l : K, phaseSize l))

/-- Extra identities and genuine fixed-fraction nonvanishing, for the alternating
family. The sequence uses m+1, so every population is nonempty. -/
def AlternatingFamilyWholeDetails : Prop :=
  (∀ (r m : ℕ) (hr : 0 < r), 0 < m →
    let D := phaseOriginal r m hr
    let z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ :=
      fun k => if k.1.2 = 0 then -1 else 1
    let q : ℝ := 2*r
    let N : ℝ := m*q
    (∀ g, groupTotal (fun _ : Fin r × Fin 2 => m) z g =
      if g.2 = 0 then -(m:ℝ) else m) ∧
    biasA D z = -N^2/q ∧ biasA D z/N^2 = -1/q ∧
    expect D (fun ω => htVarianceEstimator D z ω/N^2) -
      variance D (htMean D z) = biasA D z/N^2) ∧
  (∀ row : Fin 6,
    let m := ppsConfigurationM row
    let r := if row.val % 2 = 0 then 2 else 10
    let D := phaseOriginal r m (by dsimp [r]; split <;> norm_num)
    let z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ :=
      fun k => if k.1.2 = 0 then -1 else 1
    ppsConfigurationN row = m*(2*r) ∧
    expect D (fun ω => htVarianceEstimator D z ω/(ppsConfigurationN row : ℝ)^2) -
      variance D (htMean D z) = if row.val % 2 = 0 then -1/4 else -1/20) ∧
  (∀ (r : ℕ) (hr : 0 < r),
    let A := fun j : ℕ => biasA (phaseOriginal r (j+1) hr)
      (fun k => if k.1.2 = 0 then (-1:ℝ) else 1)
    ¬ Tendsto A atTop (𝓝 0) ∧
    ¬ Tendsto (fun j : ℕ => A j / (((j:ℝ)+1)*(2*r))^2) atTop (𝓝 0))

/-- P027-T1, Supplement pp. A3–A4 and Table A3 (p. A8), with A from main
p. 234: the full eight-unit periodic witness has A=-16, the stated samplewise
values and moments, downward bias -1/4 and relative bias -5/36; C2 remains
conservative and WR is zero. The same alternating populations at every listed
size have A=-N²/q and mean-scale bias -1/q, which do not vanish at fixed q.
The cumulative-size uniform-start law and demeaning are included explicitly.
The usual measure-theoretic conditions are assumed. -/
def T1WholeStatement : Prop :=
  Periodic8Witness ∧ FourPhaseStartWhole periodic8 periodicSize8 2 10 ∧
  Periodic8WholeDetails ∧ PeriodicStartLaw ∧ PeriodicInclusions ∧
  PeriodicSizesWhole ∧ AlternatingFamily ∧ AlternatingFamilyWholeDetails

/-- Additional finite-population formulas in T2, beyond `PeriodicBiasClaim`.
The mean-scale bias is the actual difference of design quantities. -/
def PeriodicFiniteWholeExtras : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r), 0 < m →
  ∀ z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ, (∑ k, z k) = 0 →
  let D := phaseOriginal r m hr
  let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
  let S := ∑ g, Y g^2
  let N : ℝ := m*(2*r)
  let B := expect D (fun g => htVarianceEstimator D z g/N^2) -
    variance D (htMean D z)
  biasA D z = (∑ g, ∑ h, if g ≠ h then Y g * Y h else 0) ∧
  biasA D z = (∑ g, Y g)^2 - S ∧
  biasA D z ≤ 0 ∧ (biasA D z = 0 ↔ ∀ g, Y g = 0) ∧
  expect D (htVarianceEstimator D z) =
    ∑ g, (1/phaseProb r g-1)*Y g^2 ∧
  B = biasA D z/N^2 ∧ B = -S/N^2 ∧ B ≤ 0 ∧
  (B = 0 ↔ ∀ g, Y g = 0)

/-- T2's outcome-model formulas with no extra existence guards: finite second
moments of the errors already imply integrability of all displayed quantities. -/
def PeriodicOutcomeWhole : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
  (r m : ℕ) (hr : 0 < r) (_hm : 0 < m) (β σ2 : ℝ), 0 ≤ σ2 →
  ∀ ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ, NoiseMoments μ ε σ2 →
  let D := phaseOriginal r m hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let q : ℝ := 2*r
  let N : ℝ := m*q
  let M := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  let V := fun ξ => variance D (htTotal D (z ξ))
  let H := fun ξ => expect D (htVarianceEstimator D (z ξ))
  (∀ g, Integrable (fun ξ => Y ξ g^2) μ ∧
    outcomeE μ (fun ξ => Y ξ g^2) = M) ∧
  outcomeE μ (fun ξ => biasA D (z ξ)) = -q*M ∧
  outcomeE μ V = (9/5)*q^2*M ∧ outcomeE μ H = outcomeE μ V-q*M ∧
  outcomeE μ (fun ξ => biasA D (z ξ)/N^2) = -16*β^2/q-σ2*(1-1/q)/N ∧
  (0 < M → (outcomeE μ H-outcomeE μ V)/outcomeE μ V = -5/(9*q))

/-- Signal/noise representations, integrability, and ratios of outcome-averaged
bias to outcome-averaged variance on both scales. This is not an expectation of
a populationwise relative bias. -/
def PeriodicOutcomeWholeExtras : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
  (r m : ℕ) (hr : 0 < r) (_hm : 0 < m) (β σ2 : ℝ), 0 ≤ σ2 →
  ∀ ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ, NoiseMoments μ ε σ2 →
  let D := phaseOriginal r m hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let q : ℝ := 2*r
  let N : ℝ := m*q
  let M := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  let V := fun ξ => variance D (htTotal D (z ξ))
  let H := fun ξ => expect D (htVarianceEstimator D (z ξ))
  let Vm := fun ξ => variance D (htMean D (z ξ))
  let Hm := fun ξ => expect D (fun g => htVarianceEstimator D (z ξ) g/N^2)
  (∀ ξ k, z ξ k = β*(phaseSize k-6)+ε k ξ-(∑ l, ε l ξ)/N) ∧
  (∀ ξ g, Y ξ g = (m:ℝ)*β*(if g.2 = 0 then -4 else 4) +
    (∑ j : Fin m, ε ⟨g,j⟩ ξ) - (m:ℝ)*(∑ l, ε l ξ)/N) ∧
  Integrable V μ ∧ Integrable H μ ∧ Integrable (fun ξ => biasA D (z ξ)) μ ∧
  Integrable Vm μ ∧ Integrable Hm μ ∧
  outcomeE μ (fun ξ => H ξ-V ξ) = -q*M ∧
  (0 < M →
    0 < outcomeE μ V ∧ 0 < outcomeE μ Vm ∧
    outcomeE μ (fun ξ => H ξ-V ξ)/outcomeE μ V = -5/(9*q) ∧
    outcomeE μ (fun ξ => Hm ξ-Vm ξ)/outcomeE μ Vm = -5/(9*q))

/-- Calibration is derived from the actual divisor-(N-1) size variance and the
printed beta formula, rather than postulated as an equality of squares. -/
def PeriodicCalibrationWhole : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
  (r m : ℕ) (hr : 0 < r) (_hm : 0 < m) (ρ : ℝ), |ρ| ≤ 1 →
  ∀ ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ,
  NoiseMoments μ ε (900*(1-ρ^2)) →
  let N : ℝ := m*(2*r)
  let sx := Real.sqrt ((∑ k : (Σ _ : Fin r × Fin 2, Fin m), (phaseSize k-6)^2)/(N-1))
  let β := ρ*(30/sx)
  0 < sx ∧ β^2 = 900*ρ^2*(N-1)/(16*N) ∧
  outcomeE μ (fun ξ => biasA (phaseOriginal r m hr)
    (centeredOutcomes phaseSize β ε ξ)/N^2) = calibratedMeanBias (2*r) ρ N ∧
  (ρ ≠ 0 → calibratedMeanBias (2*r) ρ N ≤ -450*ρ^2/(2*r) ∧
    -450*ρ^2/(2*r) < 0)

/-- T2's fixed-q limit and exact rational numerical specializations. -/
def PeriodicLimitWhole : Prop :=
  (∀ (r : ℕ), 0 < r → ∀ ρ : ℝ,
    Tendsto (fun m : ℕ => calibratedMeanBias (2*r) ρ ((m:ℝ)*(2*r))) atTop
      (𝓝 (-900*ρ^2/(2*r)))) ∧
  (-5/(9*4):ℝ) = -5/36 ∧ (-5/(9*20):ℝ) = -1/36 ∧
  (-900*(99/100)^2/4:ℝ) = -220.5225

/-- P027-T2, Supplement pp. A3–A4, Section C, and main p. 234:
the centered periodic cumulative-size PPS design has q disjoint phases with the
stated probabilities, A=-sum(T_g²), and exactly the stated nonpositive design
bias and relative-bias bounds. Under mean-zero uncorrelated finite-variance
errors the second moments and both ratios of outcome-averaged quantities are
as displayed. The printed calibration follows from the empirical size variance;
at fixed q and nonzero rho its bias is uniformly separated from zero and tends
to -900 rho²/q. Demeaning does not cancel the bias. Ratios have the positive
variance guards in the claim. The usual measure-theoretic conditions are assumed. -/
def T2WholeStatement : Prop :=
  PeriodicStartLaw ∧ PeriodicInclusions ∧ PeriodicSizesWhole ∧ PeriodicBiasClaim ∧
  PeriodicFiniteWholeExtras ∧ PeriodicOutcomeWhole ∧ PeriodicOutcomeWholeExtras ∧
  PeriodicCalibrationWhole ∧ PeriodicLimitWhole

/-- Probability tables, exact zero-pair lists, and the induced totalling map for
T3's two three-unit witnesses. -/
def ClusterDesignWholeDetails : Prop :=
  Valid cluster3 ∧ Valid cluster2 ∧
  (∀ k, pi cluster3 k = 1/2) ∧ (∀ k, pi cluster2 k = 1/2) ∧
  (∀ k l, joint cluster3 k l = if (k.val < 2 ↔ l.val < 2) then 1/2 else 0) ∧
  (∀ k l, joint cluster2 k l = if k = l then 1/2 else 0) ∧
  (∀ g, cluster3.selected g 0 = cluster3.selected g 1) ∧
  expect cluster3 (fun g => if cluster3.selected g 0 = cluster3.selected g 1 then 0 else 1) = 0 ∧
  (Finset.univ.filter (fun kl : Fin 3 × Fin 3 =>
    kl.1 ≠ kl.2 ∧ joint cluster3 kl.1 kl.2 = 0)) =
      {((0:Fin 3),2),(2,0),(1,2),(2,1)} ∧
  (Finset.univ.filter (fun kl : Fin 2 × Fin 2 =>
    kl.1 ≠ kl.2 ∧ joint cluster2 kl.1 kl.2 = 0)) = {((0:Fin 2),1),(1,0)} ∧
  (Finset.univ.filter (fun kl : Fin 3 × Fin 3 =>
    kl.1 ≠ kl.2 ∧ joint cluster3 kl.1 kl.2 = 0)).card = 4 ∧
  (Finset.univ.filter (fun kl : Fin 2 × Fin 2 =>
    kl.1 ≠ kl.2 ∧ joint cluster2 kl.1 kl.2 = 0)).card = 2 ∧
  (∀ g k,
    cluster3.selected g k = cluster2.selected g (if k.val < 2 then 0 else 1)) ∧
  (∀ k, totalledOnes k = if k = 0 then allOnes3 0+allOnes3 1 else allOnes3 2) ∧
  (∀ k, totalledMixed k = if k = 0 then mixed3 0+mixed3 1 else mixed3 2)

/-- T3's full before/after samplewise table and the omitted positive-witness
moments. The mixed-witness moment table is already in `T3Statement`. -/
def ClusterValuesWholeDetails : Prop :=
  (∀ g : Fin 2,
    htTotal cluster3 allOnes3 g = (if g = 0 then 4 else 2) ∧
    htTotal cluster2 totalledOnes g = (if g = 0 then 4 else 2) ∧
    htVarianceEstimator cluster3 allOnes3 g = (if g = 0 then 8 else 2) ∧
    htVarianceEstimator cluster2 totalledOnes g = (if g = 0 then 8 else 2) ∧
    quadraticCorrection cluster3 allOnes3 g = 4 ∧
    quadraticCorrection cluster2 totalledOnes g = (if g = 0 then 8 else 2) ∧
    c2Estimator cluster3 allOnes3 g = (if g = 0 then 12 else 6) ∧
    c2Estimator cluster2 totalledOnes g = (if g = 0 then 16 else 4)) ∧
  expect cluster3 (htTotal cluster3 allOnes3) = 3 ∧
  expect cluster2 (htTotal cluster2 totalledOnes) = 3 ∧
  expect cluster3 (htVarianceEstimator cluster3 allOnes3) = 5 ∧
  expect cluster2 (htVarianceEstimator cluster2 totalledOnes) = 5 ∧
  biasA cluster2 totalledOnes = 4 ∧
  (0:ℝ) ≤ 8 ∧ (0:ℝ) ≤ 9 ∧ (0:ℝ) ≤ 9/8 ∧ (0:ℝ) ≤ 49/16 ∧
  (8:ℝ) < 9 ∧ (9/8:ℝ) < 49/16

/-- P027-T3, main p. 237, Section 3.1, with C2 from Section 3.2:
the full probability tables, zero-pair lists and before/after estimator values
for the two cluster witnesses. Totalling preserves the total and its variance
but raises the conservative C2 biases from 8 to 9 and from 9/8 to 49/16,
although the ordered zero-pair count falls from four to two.
The usual measure-theoretic conditions are assumed. -/
def T3WholeStatement : Prop :=
  T3Statement ∧ ClusterDesignWholeDetails ∧ ClusterValuesWholeDetails

end
end SAP.P027a
