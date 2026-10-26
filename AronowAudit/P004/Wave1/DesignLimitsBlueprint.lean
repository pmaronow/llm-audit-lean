import AronowAudit.P004.P004_Spatial

/-! # Limit lemmas for the finite design laws (P004)

The statements concern finite-design probability, expectation, L² norms,
convergence in probability, and standard-normal limits for sample-size-indexed
product laws. The probability bounds use Markov and Chebyshev inequalities
and monotonicity. CDF convergence uses event inclusions and continuity of the
Gaussian CDF.

For random-radius coverage, the radius is bounded between fixed radii outside
an event of probability tending to zero; the CLT applies at their endpoints.
The scale parameter σ must be positive. For approximation by fixed-radius
arrays, Markov's inequality controls the squared error. Each radius has its
own eventual sample-size threshold: first take the sample-size limit, then
the radius limit, and finally let the CDF tolerance tend to zero.
-/

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Every design law in the sequence has interior coin probabilities. -/
abbrev AdmissibleSeq (p : ∀ N, Fin N → ℝ) : Prop := ∀ N i, 0 < p N i ∧ p N i < 1

/-- Standard Gaussian CDF and quantile facts. -/
def NF : Prop :=
  Continuous normalCDF ∧ StrictMono normalCDF ∧ normalCDF 0 = 1/2 ∧
  (∀ x, normalCDF (-x) = 1 - normalCDF x) ∧
  (∀ a, 0 < a → a < 1 → normalCDF (normalQuantile a) = a) ∧
  Tendsto normalCDF atTop (nhds 1) ∧ Tendsto normalCDF atBot (nhds 0)

/-- DL1 (Markov and Chebyshev on a finite design): `P(ε<|U|) ≤ E|U|/ε` and `≤ E U²/ε²`. -/
def DL1 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), (∀ i, 0 < p i ∧ p i < 1) → ∀ (U : Assignment N → ℝ) (ε : ℝ),
    0 < ε →
    prob p (fun z => ε < |U z|) ≤ expect p (fun z => |U z|) / ε ∧
    prob p (fun z => ε < |U z|) ≤ expect p (fun z => (U z)^2) / ε^2

/-- DL2 (convergence in probability from vanishing first absolute or second moments). -/
def DL2 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p → ∀ U : ∀ N, Assignment N → ℝ,
    (Tendsto (fun N => expect (p N) (fun z => |U N z|)) atTop (nhds 0) → InProb p U) ∧
    (Tendsto (fun N => expect (p N) (fun z => (U N z)^2)) atTop (nhds 0) → InProb p U)

/-- DL3 (domination outside a vanishing bad event): if eventually `|U| ≤ |W|` on `Good`,
`P(¬Good) → 0` and `W → 0` in probability, then `U → 0` in probability. -/
def DL3 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p → ∀ (U W : ∀ N, Assignment N → ℝ)
    (Good : ∀ N, Assignment N → Prop),
    Tendsto (fun N => prob (p N) (fun z => ¬ Good N z)) atTop (nhds 0) →
    (∀ᶠ N in atTop, ∀ z, Good N z → |U N z| ≤ |W N z|) → InProb p W → InProb p U

/-- DL4 (algebra of convergence to zero in probability, and deterministic sequences). -/
def DL4 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p →
    (∀ U V : ∀ N, Assignment N → ℝ, InProb p U → InProb p V →
      InProb p (fun N z => U N z + V N z)) ∧
    (∀ (c : ℝ) (U : ∀ N, Assignment N → ℝ), InProb p U → InProb p (fun N z => c * U N z)) ∧
    (∀ a : ℕ → ℝ, Tendsto a atTop (nhds 0) → InProb p (fun N _ => a N))

/-- DL5 (Slutsky, additive form): a standard-normal limit is unchanged by adding a sequence
that tends to zero in probability. -/
def DL5 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p → ∀ T U : ∀ N, Assignment N → ℝ,
    NormalLimit p T → InProb p U → NormalLimit p (fun N z => T N z + U N z)

/-- Approximation by fixed-radius limits: if for each fixed `r` the
approximants have the standard normal limit and are eventually within `η r`
in `L²`, with an `r`-dependent threshold and `η r → 0`, then the original
sequence has the standard normal limit. -/
def DL6 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p → ∀ (T : ∀ N, Assignment N → ℝ)
    (Tr : ℕ → ∀ N, Assignment N → ℝ) (η : ℕ → ℝ),
    Tendsto η atTop (nhds 0) → (∀ r, NormalLimit p (Tr r)) →
    (∀ r, ∀ᶠ N in atTop, l2Norm (p N) (fun z => T N z - Tr r N z) ≤ η r) →
    NormalLimit p T

/-- DL7 (deterministic rescaling): `Z_N ⇒ N(0,1)` and `a_N → 1` imply `a_N Z_N ⇒ N(0,1)`.
Eventually `a_N > 0`; sandwich `x / a_N` between `x ± δ` and use continuity of `normalCDF`. -/
def DL7 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p → ∀ (Z : ∀ N, Assignment N → ℝ) (a : ℕ → ℝ),
    NormalLimit p Z → Tendsto a atTop (nhds 1) → NormalLimit p (fun N z => a N * Z N z)

/-- Random-radius coverage: if `T_N/σ ⇒ N(0,1)` and `W_N → w > 0`
in probability, then `P(|T_N| ≤ c √W_N) → 2Φ(c√w/σ) − 1` for `σ > 0` and `c > 0`.
Sandwich the event between fixed-radius events, apply the CLT at their
endpoints, then let the radius tolerance tend to zero. -/
def DL8 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p → ∀ (T W : ∀ N, Assignment N → ℝ) (σ w c : ℝ),
    0 < σ → 0 < w → 0 < c →
    NormalLimit p (fun N z => T N z / σ) → InProb p (fun N z => W N z - w) →
    Tendsto (fun N => prob (p N) (fun z => |T N z| ≤ c * Real.sqrt (W N z))) atTop
      (nhds (2 * normalCDF (c * Real.sqrt w / σ) - 1))

/-- DL9 (continuous mapping for finitely many deterministic limits in probability). -/
def DL9 : Prop :=
  ∀ (p : ∀ N, Fin N → ℝ), AdmissibleSeq p → ∀ {m : ℕ} (U : Fin m → ∀ N, Assignment N → ℝ)
    (c : Fin m → ℝ) (F : (Fin m → ℝ) → ℝ), ContinuousAt F c →
    (∀ k, InProb p (fun N z => U k N z - c k)) →
    InProb p (fun N z => F (fun k => U k N z) - F c)

end
end AronowAudit.P004.Wave1.DesignLimits
