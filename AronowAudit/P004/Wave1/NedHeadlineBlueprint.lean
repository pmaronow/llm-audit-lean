import AronowAudit.P004.Wave1.FiniteConditioningBlueprint
import AronowAudit.P004.Wave1.DesignLimitsBlueprint
import AronowAudit.P004.P004_DependencyCompletion
import AronowAudit.P004.P004_VarianceComponentsCompletion

/-! # Blueprint: repair and proof of `AronowAudit.P004.ned_headline_results` (P004-T44)

Dossier group P004, record 7. The held declaration (a `sorry` draft) packages Supplement A
Lemma C.4 and Proposition 5 (Appendix C pp. 28–29): HT unbiasedness, `Var(HT) = O(1/N)`, the
root-`N` negligible Hájek remainder, and the standardized Hájek CLT under the NED conditions,
the metric standing assumption and the corrected uniform spacing `QuadraticSpacing`.

Resolution: `repair_and_prove`. Both referees reclassified the mapper's `author_decision`:
finding P004-E018 (`sol.smallest_repair`/`corrected_text`) fixes the single radius-uniform
constant, i.e. `QuadraticSpacing` (`C_b(1+s²)`); the printed page reads `s ≥ 0`. The only
statement change from the held draft is the mapper's (accepted) relaxation of `∀ N,
WellDefined` to `∀ᶠ N, WellDefined` (finite unbiasedness needs no spatial regularity).
Referee fixes applied: the last transfer step divides the UNSCALED remainder by `sqrt V_N`
(referees 1 and 2: `|Δ_N/√V_N| ≤ |√N Δ_N|/√v`), see `assemble`; the approximation lemma
`DesignLimits.DL6` quantifies each fixed radius with its own `N` threshold (referee 2).

Paper proof: map-P004 REPORT, record 7 (common bounded scores with local `L²` errors `Kψ(t)`;
dyadic counts `10 C_b` and `37 C_b 4^k`; covariance row sums; the ratio good event; the
localization error `E_r = C_b K² A² [10 + 74/(1-2^(2-e))] r^(2-2e)`; the fixed-radius
dependency-graph CLT `corrected_dependency_clt`; CDF sandwiches as `r → ∞`).

Node graph (leaves unless "uses"): shared `FiniteConditioning.FC1`-`FC9`, shared
`DesignLimits.DL1`-`DL6`; record nodes `ENV`, `DY`, `COVSUM` (uses DY, FC), `LOCERR` (uses
DY, FC), `PROJCLT` (uses FC1, FC3, FC5, FC9, `corrected_dependency_clt`), `LOCCLT` (uses
PROJCLT, LOCERR, DL6, FC7), `RATIO`, `DEN`, `H2` (uses ENV, COVSUM, FC8), `H3` (uses ENV,
COVSUM, FC7, FC8, RATIO, DEN, DL1-DL3), `H4` (uses ENV, LOCCLT, FC8). `assemble` (proved
here) needs `H2`, `H3`, `H4`, `DL3`, `DL4`, `DL5` and the proved `ht_unbiased`.

The final declaration (writer) is `AronowAudit.P004.Wave1.ned_headline_under_uniform_spacing`
in `AronowAudit/P004/Wave1/NedHeadline.lean`. Do not cite the drafts `ned_headline_results`,
`hajek_linearization`, `hajek_central_limit` or `bernoulli_denominator_rate`.
-/

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- Frozen target: the four headline conclusions under the audit-corrected standing
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

/-- Fidelity check (proved): the repaired target implies the held contract verbatim. -/
example (h : Target.{u}) : type_of% @AronowAudit.P004.ned_headline_results.{u} := by
  intro Space _ _ P p d hp hd hb hWD hNED hmetric hspacing
  exact h P p d hp hd hb (Filter.Eventually.of_forall hWD) hNED hmetric hspacing

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

/-- A metric on the node indices. -/
def MetricD {N : ℕ} (D : Fin N → Fin N → ℝ) : Prop :=
  (∀ i j, 0 ≤ D i j) ∧ (∀ i, D i i = 0) ∧ (∀ i j, D i j = D j i) ∧
  (∀ i j k, D i k ≤ D i j + D j k)

/-- A finite family of scores with local `L²` projection errors `Kc ψ(t)` on a metric index
set with uniform quadratic spacing and a power envelope `ψ(t) ≤ A t^(-e)` for `t ≥ 1`. -/
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

/-- ENV (paper proof: "ψ(t)≤A t^(−e) for all t≥1, e>4. Such A exists by enlarging its
eventual power-bound constant over 1≤t≤S, using ψ(t)≤ψ(1)"). -/
def ENV : Prop :=
  ∀ (ψ : ℝ → ℝ) (e C S : ℝ), (∀ s, 0 ≤ s → 0 ≤ ψ s) → AntitoneOn ψ (Set.Ici 0) → 0 ≤ e →
    0 < S → (∀ s, S ≤ s → ψ s ≤ C * s ^ (-e)) →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t, 1 ≤ t → ψ t ≤ A * t ^ (-e)

/-- DY (paper proof: "For annulus 3·2^k<D≤6·2^k, k≥0, its count is at most 37C_b4^k ... This
counts each annulus by its enclosing ball; it never subtracts two upper envelopes"), at a
general base radius `r ≥ 1`: a nonnegative weight decaying like `(d_ij/(3r))^(-e)` beyond
`3r` has total at most `37 C_b r² A/(1−2^(2−e))`. -/
def DY : Prop :=
  ∀ {N : ℕ} (D : Fin N → Fin N → ℝ) (i : Fin N) (Cb r e A : ℝ) (c : Fin N → ℝ),
    0 < Cb → 1 ≤ r → 4 < e → 0 ≤ A →
    (∀ s, 0 ≤ s → ((ball D i s).card : ℝ) ≤ Cb * (1 + s^2)) →
    (∀ j, 3 * r < D i j → 0 ≤ c j ∧ c j ≤ A * (D i j / (3 * r)) ^ (-e)) →
    ∑ j ∈ Finset.univ.filter (fun j => 3 * r < D i j), c j ≤
      37 * Cb * r^2 * A / (1 - (2:ℝ) ^ (2 - e))

/-- COVSUM (paper proof: "|Cov(X_i,X_j)|≤2MKψ(D/3). For D≤3 use M² instead. The near ball has
at most 10C_b nodes ... every absolute covariance row sum is bounded by
V=10C_bM²+74C_bMKA/(1−2^(2−e))<∞ ... Thus Var(ΣX_i)≤NV"). Uses DY (`r = 1`), FC5, FC6, FC7,
`GraphCompletion.expect_mul_of_disjoint_depends`, `variance_sum`. -/
def COVSUM : Prop :=
  ∀ {N : ℕ} (p : ℝ) (X : Fin N → Assignment N → ℝ) (D : Fin N → Fin N → ℝ) (ψ : ℝ → ℝ)
    (Kc Cb A e M : ℝ), LocalFamily p X D ψ Kc Cb A e → 0 ≤ M → (∀ i z, |X i z| ≤ M) →
    variance (fun _ => p) (fun z => ∑ i, X i z) ≤
      N * (10 * Cb * M^2 + 74 * Cb * M * Kc * A / (1 - (2:ℝ) ^ (2 - e)))

/-- LOCERR (paper proof: "For D=d_ij≤3r, Cauchy–Schwarz gives |Cov(R_i^r,R_j^r)|≤K²ψ(r)². For
D>3r put t=D/3>r ... |Cov(R_i^r,R_j^r)|≤2K²ψ(r)ψ(D/3) ... Therefore ||S_N−S_N^r||₂²≤NE_r"):
the localization error of the radius-`ρ` projections. Uses DY (`r = ρ`), FC3, FC4, FC6, FC7,
`GraphCompletion.expect_mul_of_disjoint_depends`. -/
def LOCERR : Prop :=
  ∀ {N : ℕ} (p : ℝ) (X : Fin N → Assignment N → ℝ) (D : Fin N → Fin N → ℝ) (ψ : ℝ → ℝ)
    (Kc Cb A e ρ : ℝ), LocalFamily p X D ψ Kc Cb A e → 1 ≤ ρ →
    expect (fun _ => p) (fun z =>
        (∑ i, (X i z - conditionOn (fun _ => p) (ball D i ρ) (X i) z))^2) ≤
      N * (Cb * Kc^2 * A^2 * (10 + 74 / (1 - (2:ℝ) ^ (2 - e))) * ρ ^ (2 - 2 * e))

/-- PROJCLT (paper proof: "For each fixed r, the projected array has a genuine dependency graph
connecting nodes at distance≤2r ... Closed degree is bounded ... independently of N for this
FIXED r ... Finite prefixes may be absorbed by enlarging the summand and degree bounds ... All
hypotheses of the already proved corrected_dependency_clt are now verified"). Uses FC1, FC3,
FC5, FC9, `CLTCompletion.finiteGraph_to_measureGraph`, `CLTCompletion.designMeasure_integral`,
`CLTCompletion.designMeasure_apply`, `corrected_dependency_clt` (pattern: `ht_clt_shift`). -/
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

/-- LOCCLT (generic NED CLT on spacing graphs; paper proof: "Let σ_N,r=||S_N^r||₂ ... |σ_N,r−
σ_N|≤√(NE_r) ... Choose r sufficiently large that η_r<1/2 ... ||T_N−T_N^r||₂≤2η_r ... First fix
ε and r, take the N limit in the projected CLT, then let r→∞"). Uses PROJCLT (radii
`ρ_r = r₀ + r` with `E_{ρ_r} ≤ v/4`), LOCERR, DL6, FC3, FC7. -/
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

/-- RATIO (paper proof: "on Q_a≥1/2 the exact identity (a+Δ)/(1+δ)=a+Δ−aδ+(aδ²−Δδ)/(1+δ)
shows that the ratio remainder is O_p(1/N)"), in the form used: on the good denominator event
the linearization error is at most `2(|B₁||C₁−1| + |B₀||C₀−1|)`, with `B_a, C_a` those of the
proved `hajek_ratio_identity`. -/
def RATIO : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N), 0 < N → 0 < p ∧ p < 1 →
    |armCount z true / (N * p) - 1| ≤ 1/2 → |armCount z false / (N * (1 - p)) - 1| ≤ 1/2 →
    |linearHajek (fun _ => p) R z - hajek R z| ≤
      2 * (|(∑ i, bit (z i) * (R i z - barMu (fun _ => p) R true)) / (N * p)| *
            |armCount z true / (N * p) - 1| +
          |(∑ i, (1 - bit (z i)) * (R i z - barMu (fun _ => p) R false)) / (N * (1 - p))| *
            |armCount z false / (N * (1 - p)) - 1|)

/-- DEN (paper proof: "the denominator variances follow directly from independent Bernoulli
counts"): exact second moments of the two normalized arm counts. -/
def DEN : Prop :=
  ∀ (N : ℕ) (p : ℝ), 0 < N → 0 < p ∧ p < 1 →
    expect (fun _ : Fin N => p) (fun z => (armCount z true / (N * p) - 1)^2) =
      (1 - p) / (N * p) ∧
    expect (fun _ : Fin N => p) (fun z => (armCount z false / (N * (1 - p)) - 1)^2) =
      p / (N * (1 - p))

/-- H2 (clause 2; paper proof: "Applied to the centered HT scores, this proves Var(HT)≤V/N
eventually, i.e. the stated IsBigO"). Use the unnormalized HT scores
`residualContrast (fun _ => p) R (fun _ _ => 0) i` (bound `CLTCompletion.raw_contrast_abs_le`,
NED transfer FC8 with `|α| ≤ 1/min(p,1−p)`), `CLTCompletion.circleAverage_abs_le`, ENV,
COVSUM, `variance_div`, `Asymptotics.IsBigO.of_bound`. -/
def H2 : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ), Standing P p d →
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹)

/-- H3 (clause 3; paper proof: "Hájek remainder ... This proves exactly the InProb remainder
conclusion"; implemented via RATIO on the good event `|C_a−1|≤1/2`, Chebyshev with DEN for the
bad event, and Markov for `2√N(|B₁||C₁−1|+|B₀||C₀−1|)` with `E|B_a||C_a−1| ≤ ||B_a||·||C_a−1||`,
`E B_a = 0`, `Var(N B_a) = O(N)` by COVSUM). Uses RATIO, DEN, COVSUM, ENV, FC7, FC8, DL1-DL3. -/
def H3 : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ), Standing P p d →
    InProb (fun _ _ => p) (fun N z => Real.sqrt N *
      (linearHajek (fun _ => p) (circleAverage (P N) d) z - hajek (circleAverage (P N) d) z))

/-- H4 (the linear-score CLT; paper proof: "Now take X_i from the linear-Hájek scores ...
S_N=Σ_iX_i=Σ_iW_i and linearHajek−AME=S_N/N. This is the corrected τ_i/N centering of E017").
Apply LOCCLT to `X_i = N · centeredSummand (fun _ => p) R μ̄₁ μ̄₀ i` (mean zero and sum
`N(linearHajek − AME)` by the proved `centered_summand_identity`), with the bound from
`circleAverage_abs_le`/`barMu`, the NED transfer FC8, ENV, and the floor
`Var(ΣX) = N² Var(linearHajek) ≥ v N`. -/
def H4 : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ), Standing P p d →
    Nondegenerate (fun N => variance (fun _ => p)
        (linearHajek (fun _ => p) (circleAverage (P N) d))) →
    NormalLimit (fun _ _ => p) (fun N z =>
      (linearHajek (fun _ => p) (circleAverage (P N) d) z -
          ame (fun _ => p) (circleAverage (P N) d)) /
        Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))))

/-- The nodes suffice (proved). Clause 1 is the proved `ht_unbiased`; clause 4 transfers the
linear-score limit H4 to the exact standardized Hájek ratio with the referee-corrected
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
