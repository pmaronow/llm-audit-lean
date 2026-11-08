import AronowAudit.P001.P001_Foundations

/-! # Blueprint: P001-T55 — the book's sampling-variance estimate of the sample mean

Record 49 of dossier group P001c (`AronowAudit.P001.sample_mean_variance_estimate_scale_supporting`,
resolution `repair_and_prove`). Definition 3.2.32 and footnote 23, pp. 113–114; the sample-mean
example of Section 3.2.6 and Theorem 3.2.33, pp. 114–115 (PDF pp. 132–133), where `V̂[X̄]` is the
*unbiased* sample variance divided by `n`.

The frozen `sampleMeanVarianceEstimate` is the `n`-denominator plug-in variance divided by `n`,
a different object (for data `(0, 2)`: plug-in variance `1`, unbiased variance `2`). The repair
leaves it untouched and uses `vhat n = sampleVariance X n / (n - 1)`, which equals `s²ₙ / n` for
`n ≥ 2`; at `n = 0, 1` the totalized value is `0` and is not claimed to estimate anything.

Map-P001c report, record 49; both referees accepted without fixes.

Final declaration (writer): `AronowAudit.P001.Wave1.sample_mean_unbiased_variance_contract`
in `AronowAudit/P001/Wave1/UnbiasedMeanVariance.lean`.
-/

namespace AronowAudit.P001.Wave1.UnbiasedMeanVariance

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-- Frozen target (map-P001c `sample_mean_unbiased_variance_contract`): measurability,
nonnegativity, the finite residual-sum and scaling identities for `n ≥ 2`, unbiasedness
`E[vhat n] = σ²/n` for `n ≥ 2`, the root-`n` CLT identifying the target `σ²`, variance and
standard-error consistency, and both centered forms of footnote 23. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → MemLp (X 0) 2 μ → ∀ (hv : 0 < var μ (X 0)),
    let vhat : ℕ → Ω → ℝ := fun n ω => sampleVariance X n ω / ((n : ℝ) - 1)
    (∀ n, Measurable (vhat n)) ∧
    (∀ n ω, 0 ≤ vhat n ω) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ ω,
      vhat n ω = (∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω) ^ 2) /
        ((n : ℝ) * ((n : ℝ) - 1)) ∧
      (n : ℝ) * vhat n ω = ((n : ℝ) / ((n : ℝ) - 1)) * sampleVariance X n ω) ∧
    (∀ n : ℕ, 2 ≤ n → mean μ (vhat n) = var μ (X 0) / (n : ℝ)) ∧
    CD μ (fun n ω => Real.sqrt n * (sampleMean X n ω - mean μ (X 0)))
      (gaussianReal 0 ⟨var μ (X 0), le_of_lt hv⟩) ∧
    VarianceConsistent μ vhat (var μ (X 0)) ∧
    SEConsistent μ vhat (var μ (X 0)) ∧
    CP μ (fun n ω => (n : ℝ) * vhat n ω - var μ (X 0)) 0 ∧
    CP μ (fun n ω => Real.sqrt n * Real.sqrt (vhat n ω) - Real.sqrt (var μ (X 0))) 0

/-- N1 (paper-proof step "for `n ≥ 1`, `∑_{i<n}(Xᵢ - X̄ₙ)² = ∑Xᵢ² - 2X̄ₙ∑Xᵢ + n X̄ₙ² =
∑Xᵢ² - n X̄ₙ² = n vₙ`"): the plug-in variance times `n` is the centered sum of squares.
Purely algebraic; no probability. -/
def N1 : Prop :=
  ∀ {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω), 0 < n →
    (n : ℝ) * sampleVariance X n ω =
      ∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω) ^ 2

/-- N2 (paper-proof step "put `aₙ = n/(n-1)`; then `aₙ → 1`; for `ε > 0`, eventually the event
`{|aₙvₙ - σ²| ≥ ε}` is contained in `{|vₙ - σ²| ≥ ε/4}`, whose probability tends to zero"): a
deterministic scaling sequence tending to one preserves convergence in probability. No
measurability is needed (`prob` is monotone on arbitrary sets). -/
def N2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (c : ℝ) (a : ℕ → ℝ),
    CP μ Z c → Tendsto a atTop (nhds 1) → CP μ (fun n ω => a n * Z n ω) c

/-- The nodes suffice. Expectation and consistency of the plug-in variance come from the proved
`sample_variance_unbiased_factor_and_consistency`, the CLT from the proved
`central_limit_finite_variance`, the scaling `n · vhat n = (n/(n-1)) · vₙ` is a field identity
valid for every `n` (also `n = 0, 1` with totalized division), `n/(n-1) → 1` is
`tendsto_natCast_div_add_atTop`, the SE clause is the proved
`variance_se_consistency_equivalence`, and the centered forms are the proved
`sample_mean_variance_estimate_scale`. -/
theorem assemble (h1 : N1.{u}) (h2 : N2.{u}) : Target.{u} := by
  intro Ω _ μ _ X hiid h2X hv vhat
  obtain ⟨hEv, hCPv⟩ := sample_variance_unbiased_factor_and_consistency μ X hiid h2X hv
  have hmeasX : ∀ i, Measurable (X i) := hiid.1
  have hsvm : ∀ n, Measurable (sampleVariance X n) := by
    intro n
    unfold sampleVariance sampleMean
    exact ((Finset.measurable_sum _ fun i _ => (hmeasX i).pow_const 2).div_const _).sub
      (((Finset.measurable_sum _ fun i _ => hmeasX i).div_const _).pow_const 2)
  have hsvnn : ∀ n ω, 0 ≤ sampleVariance X n ω := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleVariance, sampleMean]
    · have hid := h1 X n ω hn
      have hsum : 0 ≤ ∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      by_contra hneg
      have hlt : sampleVariance X n ω < 0 := lt_of_not_ge hneg
      nlinarith
  have hvm : ∀ n, Measurable (vhat n) := fun n => (hsvm n).div_const _
  have hvnn : ∀ n ω, 0 ≤ vhat n ω := by
    intro n ω
    show 0 ≤ sampleVariance X n ω / ((n : ℝ) - 1)
    by_cases hn : 2 ≤ n
    · have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (hsvnn n ω) (by linarith)
    · interval_cases n <;> simp [sampleVariance, sampleMean]
  have hfin : ∀ n : ℕ, 2 ≤ n → ∀ ω,
      vhat n ω = (∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω) ^ 2) /
        ((n : ℝ) * ((n : ℝ) - 1)) ∧
      (n : ℝ) * vhat n ω = ((n : ℝ) / ((n : ℝ) - 1)) * sampleVariance X n ω := by
    intro n hn ω
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hid := h1 X n ω (by omega)
    refine ⟨?_, ?_⟩
    · show sampleVariance X n ω / ((n : ℝ) - 1) = _
      rw [← hid]
      field_simp
    · show (n : ℝ) * (sampleVariance X n ω / ((n : ℝ) - 1)) = _
      ring
  have hmean : ∀ n : ℕ, 2 ≤ n → mean μ (vhat n) = var μ (X 0) / (n : ℝ) := by
    intro n hn
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hE := hEv n (by omega)
    show ∫ ω, sampleVariance X n ω / ((n : ℝ) - 1) ∂μ = _
    rw [integral_div]
    change mean μ (sampleVariance X n) / ((n : ℝ) - 1) = _
    rw [hE]
    field_simp
  have hscale : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) atTop (nhds 1) := by
    simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (𝕜 := ℝ) (-1)
  have hfun : (fun (n : ℕ) (ω : Ω) => (n : ℝ) * vhat n ω) =
      fun (n : ℕ) (ω : Ω) => (n : ℝ) / ((n : ℝ) - 1) * sampleVariance X n ω := by
    funext n ω
    show (n : ℝ) * (sampleVariance X n ω / ((n : ℝ) - 1)) = _
    ring
  have hVC : VarianceConsistent μ vhat (var μ (X 0)) := by
    unfold VarianceConsistent
    rw [hfun]
    exact h2 μ (sampleVariance X) (var μ (X 0)) _ hCPv hscale
  have hSE : SEConsistent μ vhat (var μ (X 0)) :=
    (variance_se_consistency_equivalence μ vhat hvnn (var μ (X 0)) hv.le).mp hVC
  have hcent := sample_mean_variance_estimate_scale μ vhat hvm (var μ (X 0))
  exact ⟨hvm, hvnn, hfin, hmean, central_limit_finite_variance μ X hiid h2X hv, hVC, hSE,
    hcent.1.mp hVC, hcent.2.mp hSE⟩

/- Satisfiable instance of the hypotheses (both referees): IID fair Bernoulli coordinates
`Xᵢ ∈ {0, 1}` on `{0,1}^ℕ` with the product law (`Var X₀ = 1/4 > 0`), or IID `Xᵢ ∈ {0, 2}`
with equal masses (`Var X₀ = 1`). On the sample `(0, 2)`: plug-in variance `1`, unbiased
variance `2`, `vhat 2 = 1`, `2 · vhat 2 = 2` (historical object: `1`). -/

end
end AronowAudit.P001.Wave1.UnbiasedMeanVariance
