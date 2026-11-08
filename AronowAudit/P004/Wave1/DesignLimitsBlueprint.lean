import AronowAudit.P004.P004_Spatial

/-! # Shared blueprint module: limit lemmas for the finite design laws (P004, wave 1)

Shared by the T36 (`ObservationalCoverage`) and T44 (`NedHeadline`) blueprints. Every node is
a generic statement about the project's own finite-design probability `prob`, expectation
`expect`, `l2Norm`, `InProb` and `NormalLimit` (sample-size-indexed product laws `p N`), so no
general limit theorem is assumed: each is an elementary consequence of Chebyshev/Markov,
monotonicity of probabilities, and continuity of the Gaussian CDF.

Paper-proof sources (map-P004 REPORT): record 5 "Finite-law probability limits ... prove
Chebyshev and union bounds for its finite design, and prove CDF convergence under vanishing
errors or positive random radii by elementary event inclusions", record 5 "for any ε>0,
outside an event of probability tending to zero, its random root-N radius lies between ...
Sandwich the event between the corresponding fixed-radius events", record 7 "Markov on the
squared error gives P(|T_N−T_N^r|>ε)≤4η_r²/ε² ... First fix ε and r, take the N limit in the
projected CLT, then let r→∞, and finally let ε↓0", and the referee fixes: the random-radius
helper requires `σ > 0` (referee 1); the approximation lemma quantifies each fixed radius with
an `N`-threshold depending on it (referee 2; here radii are indexed by `ℕ`, callers reindex to
"sufficiently large").

Useful existing lemmas: `expect_mono`, `design_weight_nonneg`, `design_normalized`,
`expect_const`, `CLTCompletion.designMeasure_apply`, `CLTCompletion.designMeasure_integral`;
for Gaussian facts `AronowAudit.P053.NormalCompletion.{cdf_continuousAt,
strictMono_normal_cdf, normal_cdf_neg, normal_cdf_zero, normalCritical_cdf, exists_cdf_eq,
standardNormalCDF_eq_cdf}` (`P053_NormalQuantiles.lean`; `normalCDF` here is definitionally
`P053.standardNormalCDF`, and `normalQuantile a = P053.normalCritical (2 - 2a)`).
-/

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Every design law in the sequence has interior coin probabilities. -/
abbrev AdmissibleSeq (p : ∀ N, Fin N → ℝ) : Prop := ∀ N i, 0 < p N i ∧ p N i < 1

/-- NF (standard Gaussian facts; adapters from `P053_NormalQuantiles.lean`). -/
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

/-- DL6 (approximation by fixed-radius limits; paper proof, record 7, "Remove localization
without a growing-degree CLT"): if for each fixed `r` the approximants have the standard
normal limit and are eventually (with an `r`-dependent threshold) within `η r` in `L²`, with
`η r → 0`, then the original sequence has the standard normal limit. -/
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

/-- DL8 (random-radius coverage; paper proof, record 5, "Sandwich the event between the
corresponding fixed-radius events, use the CLT at their endpoints, then let ε↓0"; referee-1
fix: `σ > 0`): if `T_N/σ ⇒ N(0,1)` and `W_N → w > 0` in probability, then
`P(|T_N| ≤ c √W_N) → 2Φ(c√w/σ) − 1` for `c > 0`. Uses NF. -/
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
