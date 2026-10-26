import AronowAudit.P001.P001_Foundations

/-! # P001-T50: three corrected displays

(a) Example 3.1.3, p. 94 (PDF p. 112), with Definition 3.1.2, p. 93;
(b) the variance functional `T_V(F)`, p. 118, repeated in Example 3.3.5, p. 119;
(c) Example 3.3.4, last line, p. 119 (PDF p. 137).

One conjunction joins the normalized equal-probability unit law (repeated responses
keep their multiplicity), the population `(3,4,3,10)` with mean `5` and variance
`17/2`, the minus-sign variance identity and the size `2(EZ)²` of the printed plus-sign error,
and the empirical-law mean/variance over the actual observations.
-/

namespace AronowAudit.P001.Wave1.FinitePopulationPlugin

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-- The conjunction of the finite-population, variance-functional, and empirical-variance identities. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ), MemLp Z 2 μ →
    (∀ (N : ℕ) (hN : 0 < N) (x : Fin N → ℝ),
      (∀ t : ℝ, fprob (uniformFiniteLaw N hN) (fun i => x i = t) =
        ((Finset.univ.filter (fun i => x i = t)).card : ℝ) / (N : ℝ)) ∧
      fmean (uniformFiniteLaw N hN) x = (∑ i, x i) / (N : ℝ) ∧
      fvar (uniformFiniteLaw N hN) x =
        (∑ i, (x i - (∑ j, x j) / (N : ℝ)) ^ 2) / (N : ℝ)) ∧
    (fprob (uniformFiniteLaw 4 (by norm_num))
        (fun i => (![3, 4, 3, 10] : Fin 4 → ℝ) i = 3) = 1 / 2 ∧
      fprob (uniformFiniteLaw 4 (by norm_num))
        (fun i => (![3, 4, 3, 10] : Fin 4 → ℝ) i = 4) = 1 / 4 ∧
      fprob (uniformFiniteLaw 4 (by norm_num))
        (fun i => (![3, 4, 3, 10] : Fin 4 → ℝ) i = 10) = 1 / 4 ∧
      fmean (uniformFiniteLaw 4 (by norm_num)) ![3, 4, 3, 10] = 5 ∧
      fvar (uniformFiniteLaw 4 (by norm_num)) ![3, 4, 3, 10] = 17 / 2) ∧
    (var μ Z = mean μ (fun ω => (Z ω) ^ 2) - (mean μ Z) ^ 2) ∧
    (mean μ (fun ω => (Z ω) ^ 2) + (mean μ Z) ^ 2 - var μ Z = 2 * (mean μ Z) ^ 2) ∧
    (∀ (x : ℕ → ℝ) (n : ℕ), 0 < n →
      let ν := empirical (fun i (_ : Unit) => x i) n ()
      IsProbabilityMeasure ν ∧
      mean ν id = (∑ i ∈ Finset.range n, x i) / (n : ℝ) ∧
      var ν id = (∑ i ∈ Finset.range n, (x i) ^ 2) / (n : ℝ) -
        ((∑ i ∈ Finset.range n, x i) / (n : ℝ)) ^ 2)

/-- N1 = Target: equal unit masses `1/N`, counts `2,1,1` at `3,4,10`, mean `5`,
centered squares `4,1,4,25`; `E[(Z-m)²] = E[Z²] - m²`, so the plus sign overstates by
`2m²`; the empirical Dirac law has mass one and moments equal to the sample averages. -/
def N1 : Prop := Target.{u}

/- Satisfiable instance of the hypotheses: `Ω = Unit`, `μ = dirac ()`, `Z = 0`;
or `Ω = Fin 4` with uniform mass and `Z = ![3,4,3,10]`. -/

end
end AronowAudit.P001.Wave1.FinitePopulationPlugin
