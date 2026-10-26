import AronowAudit.P004.Wave1.FiniteConditioningBlueprint
import AronowAudit.P004.Wave1.DesignLimitsBlueprint
import AronowAudit.P004.P004_DependencyCompletion
import AronowAudit.P004.P004_VarianceComponentsCompletion

/-! # NED limit results under uniform spacing (P004-T44)

Supplement A Lemma C.4 and Proposition 5 (Appendix C pp. 28–29) concern HT unbiasedness,
`Var(HT) = O(1/N)`, the root-`N` negligible Hájek remainder, and the standardized Hájek CLT.
The hypotheses here include the NED conditions, metric node distances, and corrected
uniform spacing `QuadraticSpacing`, namely `C_b(1+s²)` for `s ≥ 0` (P004-E018).
Well-definedness is required eventually; finite unbiasedness needs no spatial regularity.

The argument uses common bounded scores with local `L²` errors `Kψ(t)`, dyadic counts
`10 C_b` and `37 C_b 4^k`, covariance row sums, and the ratio good event. The localization
error is `E_r = C_b K² A² [10 + 74/(1-2^(2-e))] r^(2-2e)`. Fixed-radius dependency-graph
CLTs and CDF sandwiches yield the limit as `r → ∞`. Each fixed radius has its own
sample-size threshold. The final transfer divides the unscaled remainder by `sqrt V_N`,
using `|Δ_N/√V_N| ≤ |√N Δ_N|/√v`.
-/

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- The four headline conclusions under the corrected standing
hypotheses (uniform `QuadraticSpacing`, metric node distances, eventual well-definedness). -/
def Target : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ)
    (_hp : 0 < p ∧ p < 1) (_hd : 0 ≤ d) (_hb : BoundedOutcomes P)
    (_hWD : ∀ᶠ N in atTop, WellDefined (P N) d) (_hNED : NEDConditions P p d)
    (_hmetric : MetricNodeDistances P) (_hspacing : QuadraticSpacing P),
    (∀ N, expect (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)) =
      ame (fun _ => p) (circleAverage (P N) d)) ∧
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹) ∧
    InProb (fun _ _ => p) (fun N z => Real.sqrt N *
      (linearHajek (fun _ => p) (circleAverage (P N) d) z - hajek (circleAverage (P N) d) z)) ∧
    (Nondegenerate (fun N => variance (fun _ => p)
        (linearHajek (fun _ => p) (circleAverage (P N) d))) →
      NormalLimit (fun _ _ => p) (fun N z =>
        (hajek (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)) /
          Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))))

/-- The standing hypotheses of the target, bundled. -/
structure Standing {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) (p d : ℝ) : Prop where
  hp : 0 < p ∧ p < 1
  hd : 0 ≤ d
  hb : BoundedOutcomes P
  hWD : ∀ᶠ N in atTop, WellDefined (P N) d
  hNED : NEDConditions P p d
  hmetric : MetricNodeDistances P
  hspacing : QuadraticSpacing P

/-- A pseudometric on the node indices; distinct indices may have distance zero. -/
def MetricD {N : ℕ} (D : Fin N → Fin N → ℝ) : Prop :=
  (∀ i j, 0 ≤ D i j) ∧ (∀ i, D i i = 0) ∧ (∀ i j, D i j = D j i) ∧
  (∀ i j k, D i k ≤ D i j + D j k)

/-- A finite family of scores with local `L²` projection errors `Kc ψ(t)` on a
pseudometric index set with uniform quadratic spacing and a power envelope
`ψ(t) ≤ A t^(-e)` for `t ≥ 1`, where `e > 4`. -/
structure LocalFamily {N : ℕ} (p : ℝ) (X : Fin N → Assignment N → ℝ)
    (D : Fin N → Fin N → ℝ) (ψ : ℝ → ℝ) (Kc Cb A e : ℝ) : Prop where
  hp : 0 < p ∧ p < 1
  hD : MetricD D
  hspacing : ∀ i s, 0 ≤ s → ((ball D i s).card : ℝ) ≤ Cb * (1 + s^2)
  hCb : 0 < Cb
  hψ : ∀ s, 0 ≤ s → 0 ≤ ψ s
  hψanti : AntitoneOn ψ (Set.Ici 0)
  he : 4 < e
  hA : 0 ≤ A
  henv : ∀ t, 1 ≤ t → ψ t ≤ A * t ^ (-e)
  hKc : 0 ≤ Kc
  hNED : ∀ i t, 0 ≤ t → l2Norm (fun _ => p)
    (fun z => X i z - conditionOn (fun _ => p) (ball D i t) (X i) z) ≤ Kc * ψ t

/-- ENV: for `0 ≤ e`, extend an eventual power bound on a nonnegative antitone `ψ`
to every `t ≥ 1` by enlarging the constant over the bounded initial interval. -/
def ENV : Prop :=
  ∀ (ψ : ℝ → ℝ) (e C S : ℝ), (∀ s, 0 ≤ s → 0 ≤ ψ s) → AntitoneOn ψ (Set.Ici 0) → 0 ≤ e →
    0 < S → (∀ s, S ≤ s → ψ s ≤ C * s ^ (-e)) →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t, 1 ≤ t → ψ t ≤ A * t ^ (-e)

/-- DY: under uniform quadratic spacing, weights bounded by
`A (D i j / (3r))^(-e)` beyond radius `3r`, with `r ≥ 1` and `e > 4`, have
total at most `37 Cb r² A / (1 - 2^(2-e))`. -/
def DY : Prop :=
  ∀ {N : ℕ} (D : Fin N → Fin N → ℝ) (i : Fin N) (Cb r e A : ℝ) (c : Fin N → ℝ),
    0 < Cb → 1 ≤ r → 4 < e → 0 ≤ A →
    (∀ s, 0 ≤ s → ((ball D i s).card : ℝ) ≤ Cb * (1 + s^2)) →
    (∀ j, 3 * r < D i j → 0 ≤ c j ∧ c j ≤ A * (D i j / (3 * r)) ^ (-e)) →
    ∑ j ∈ Finset.univ.filter (fun j => 3 * r < D i j), c j ≤
      37 * Cb * r^2 * A / (1 - (2:ℝ) ^ (2 - e))

/-- COVSUM: the variance of the sum of uniformly bounded scores in a
`LocalFamily` is at most `N (10 Cb M² + 74 Cb M Kc A / (1 - 2^(2-e)))`. -/
def COVSUM : Prop :=
  ∀ {N : ℕ} (p : ℝ) (X : Fin N → Assignment N → ℝ) (D : Fin N → Fin N → ℝ) (ψ : ℝ → ℝ)
    (Kc Cb A e M : ℝ), LocalFamily p X D ψ Kc Cb A e → 0 ≤ M → (∀ i z, |X i z| ≤ M) →
    variance (fun _ => p) (fun z => ∑ i, X i z) ≤
      N * (10 * Cb * M^2 + 74 * Cb * M * Kc * A / (1 - (2:ℝ) ^ (2 - e)))

/-- LOCERR: for a `LocalFamily` and `ρ ≥ 1`, the second moment of the sum
of the radius-`ρ` projection errors is at most
`N Cb Kc² A² (10 + 74 / (1 - 2^(2-e))) ρ^(2-2e)`. -/
def LOCERR : Prop :=
  ∀ {N : ℕ} (p : ℝ) (X : Fin N → Assignment N → ℝ) (D : Fin N → Fin N → ℝ) (ψ : ℝ → ℝ)
    (Kc Cb A e ρ : ℝ), LocalFamily p X D ψ Kc Cb A e → 1 ≤ ρ →
    expect (fun _ => p) (fun z =>
        (∑ i, (X i z - conditionOn (fun _ => p) (ball D i ρ) (X i) z))^2) ≤
      N * (Cb * Kc^2 * A^2 * (10 + 74 / (1 - (2:ℝ) ^ (2 - e))) * ρ ^ (2 - 2 * e))

/-- PROJCLT: a normal-limit statement for fixed-radius projections of centered
scores with eventual uniform bounds on scores and radius-`2ρ` ball sizes,
pseudometric distances, and an eventual positive linear lower bound on the
variance of the projected sum. -/
def PROJCLT : Prop :=
  ∀ (p : ℝ), 0 < p ∧ p < 1 → ∀ (X : ∀ N, Fin N → Assignment N → ℝ)
    (D : ∀ N, Fin N → Fin N → ℝ) (ρ Cb M v : ℝ),
    (∀ N, MetricD (D N)) → 0 ≤ ρ →
    (∀ᶠ N in atTop, ∀ i, ((ball (D N) i (2 * ρ)).card : ℝ) ≤ Cb) →
    (∀ᶠ N in atTop, ∀ i z, |X N i z| ≤ M) →
    (∀ N i, expect (fun _ => p) (X N i) = 0) → 0 < v →
    (∀ᶠ N in atTop, v * N ≤ variance (fun _ => p)
      (fun z => ∑ i, conditionOn (fun _ => p) (ball (D N) i ρ) (X N i) z)) →
    NormalLimit (fun _ _ => p) (fun N z =>
      (∑ i, conditionOn (fun _ => p) (ball (D N) i ρ) (X N i) z) /
        Real.sqrt (variance (fun _ => p)
          (fun z => ∑ i, conditionOn (fun _ => p) (ball (D N) i ρ) (X N i) z)))

/-- LOCCLT: a normal-limit statement for centered NED scores with eventual
uniform boundedness and quadratic spacing, pseudometric distances, a power
envelope with `e > 4`, and an eventual positive linear variance lower bound. -/
def LOCCLT : Prop :=
  ∀ (p : ℝ), 0 < p ∧ p < 1 → ∀ (X : ∀ N, Fin N → Assignment N → ℝ)
    (D : ∀ N, Fin N → Fin N → ℝ) (ψ : ℝ → ℝ) (Kc Cb A e M v : ℝ),
    (∀ N, MetricD (D N)) →
    (∀ᶠ N in atTop, ∀ i s, 0 ≤ s → ((ball (D N) i s).card : ℝ) ≤ Cb * (1 + s^2)) →
    0 < Cb → (∀ s, 0 ≤ s → 0 ≤ ψ s) → AntitoneOn ψ (Set.Ici 0) → 4 < e → 0 ≤ A →
    (∀ t, 1 ≤ t → ψ t ≤ A * t ^ (-e)) → 0 ≤ Kc →
    (∀ N i t, 0 ≤ t → l2Norm (fun _ => p)
      (fun z => X N i z - conditionOn (fun _ => p) (ball (D N) i t) (X N i) z) ≤ Kc * ψ t) →
    (∀ᶠ N in atTop, ∀ i z, |X N i z| ≤ M) →
    (∀ N i, expect (fun _ => p) (X N i) = 0) → 0 < v →
    (∀ᶠ N in atTop, v * N ≤ variance (fun _ => p) (fun z => ∑ i, X N i z)) →
    NormalLimit (fun _ _ => p) (fun N z =>
      (∑ i, X N i z) / Real.sqrt (variance (fun _ => p) (fun z => ∑ i, X N i z)))

/-- RATIO: when both normalized arm counts differ from one by at most `1/2`,
the Hájek linearization error is bounded by twice the sum of the products of
each arm’s absolute normalized centered score and absolute count deviation. -/
def RATIO : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N), 0 < N → 0 < p ∧ p < 1 →
    |armCount z true / (N * p) - 1| ≤ 1/2 → |armCount z false / (N * (1 - p)) - 1| ≤ 1/2 →
    |linearHajek (fun _ => p) R z - hajek R z| ≤
      2 * (|(∑ i, bit (z i) * (R i z - barMu (fun _ => p) R true)) / (N * p)| *
            |armCount z true / (N * p) - 1| +
          |(∑ i, (1 - bit (z i)) * (R i z - barMu (fun _ => p) R false)) / (N * (1 - p))| *
            |armCount z false / (N * (1 - p)) - 1|)

/-- DEN: exact second moments of the two normalized arm-count deviations
under independent Bernoulli assignment. -/
def DEN : Prop :=
  ∀ (N : ℕ) (p : ℝ), 0 < N → 0 < p ∧ p < 1 →
    expect (fun _ : Fin N => p) (fun z => (armCount z true / (N * p) - 1)^2) =
      (1 - p) / (N * p) ∧
    expect (fun _ : Fin N => p) (fun z => (armCount z false / (N * (1 - p)) - 1)^2) =
      p / (N * (1 - p))

/-- The `O(1/N)` HT variance bound under `Standing`, the second clause of `Target`. -/
def H2 : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ), Standing P p d →
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹)

/-- Convergence in probability of the root-`N` Hájek linearization error to zero
under `Standing`, the third clause of `Target`. -/
def H3 : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ), Standing P p d →
    InProb (fun _ _ => p) (fun N z => Real.sqrt N *
      (linearHajek (fun _ => p) (circleAverage (P N) d) z - hajek (circleAverage (P N) d) z))

/-- The normal-limit statement for the centered linear Hájek estimator under
`Standing` and nondegenerate variance. -/
def H4 : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ), Standing P p d →
    Nondegenerate (fun N => variance (fun _ => p)
        (linearHajek (fun _ => p) (circleAverage (P N) d))) →
    NormalLimit (fun _ _ => p) (fun N z =>
      (linearHajek (fun _ => p) (circleAverage (P N) d) z -
          ame (fun _ => p) (circleAverage (P N) d)) /
        Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))))

/-- The component bounds imply the result. Clause 1 is the proved `ht_unbiased`; clause 4 transfers the
linear-score limit H4 to the exact standardized Hájek ratio with the
scaling `|Δ_N/√V_N| ≤ |√N Δ_N|/√v` (DL4, DL3) and Slutsky (DL5). -/
theorem assemble (h2 : H2.{u}) (h3 : H3.{u}) (h4 : H4.{u}) (dl3 : DL3) (dl4 : DL4)
    (dl5 : DL5) : Target.{u} := by
  intro Space _ _ P p d hp hd hb hWD hNED hmetric hspacing
  have hS : Standing P p d := ⟨hp, hd, hb, hWD, hNED, hmetric, hspacing⟩
  have hadm : AdmissibleSeq (fun (_ : ℕ) (_ : Fin _) => p) := fun _ _ => hp
  refine ⟨fun N => ht_unbiased _ _ (fun _ => hp), h2 P p d hS, h3 P p d hS, fun hv => ?_⟩
  obtain ⟨v, hv0, hvN⟩ := hv
  have hW := (dl4 _ hadm).2.1 (1 / Real.sqrt v) _ (h3 P p d hS)
  have hU := dl3 _ hadm
    (fun N z => (hajek (circleAverage (P N) d) z -
        linearHajek (fun _ => p) (circleAverage (P N) d) z) /
      Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))))
    _ (fun _ _ => True) (by simp [prob, expect]) ?_ hW
  · have hlim := dl5 _ hadm _ _ (h4 P p d hS ⟨v, hv0, hvN⟩) hU
    have he : (fun N z =>
        (linearHajek (fun _ => p) (circleAverage (P N) d) z -
            ame (fun _ => p) (circleAverage (P N) d)) /
          Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))) +
        (hajek (circleAverage (P N) d) z - linearHajek (fun _ => p) (circleAverage (P N) d) z) /
          Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))) =
        fun N z => (hajek (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)) /
          Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))) := by
      funext N z
      rw [← add_div]
      ring_nf
    rw [he] at hlim
    exact hlim
  · filter_upwards [hvN] with N hvN' z _
    set V := variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))
    set L := linearHajek (fun _ => p) (circleAverage (P N) d) z
    set H := hajek (circleAverage (P N) d) z
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hNV : 0 < (N : ℝ) * V := lt_of_lt_of_le hv0 hvN'
    have hV : 0 < V := by
      by_contra hcon
      have hle : V ≤ 0 := not_lt.mp hcon
      nlinarith
    have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
    have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
    have key : Real.sqrt v ≤ Real.sqrt N * Real.sqrt V := by
      rw [← Real.sqrt_mul hN0]
      exact Real.sqrt_le_sqrt hvN'
    rw [abs_div, abs_of_pos hsV, abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hsv),
      abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm L H, div_le_iff₀ hsV]
    have hHL : 0 ≤ |H - L| := abs_nonneg _
    calc |H - L| = 1 / Real.sqrt v * |H - L| * Real.sqrt v := by field_simp
      _ ≤ 1 / Real.sqrt v * |H - L| * (Real.sqrt N * Real.sqrt V) := by
          apply mul_le_mul_of_nonneg_left key
          positivity
      _ = 1 / Real.sqrt v * (Real.sqrt N * |H - L|) * Real.sqrt V := by ring

end
end AronowAudit.P004.Wave1.NedHeadline
