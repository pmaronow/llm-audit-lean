import AronowAudit.P018.P018_Audit

/-!
# P018-T10 (Corollary 2): weighted sandwich consistency for one common directed kernel

The model uses one measurable ordered-pair data kernel `(X, Y)`, evaluated in
orientation `(u,v)` or `(v,u)` (`dir`), with at most one record per orientation
(`dir` injective). This is the directed-pair reading of p. 567 and Appendix D,
p. 575, with common functions of the two sampled units as in the standing model on
p. 566. Allowing an arbitrary kernel for each record `(N, d, t)` can leave block
scores with non-zero means. Normalized weights `w/a_N` are arbitrary, deterministic,
positive and uniformly bounded, and the normalized expected weighted Gram has a
positive definite limit (corrected Corollary 2).

Rescaling by `a_N` leaves the estimator unchanged. By iid exchangeability every
record has the same `Q = E[XX']`, `r = E[XY]`, so `H_N = c_N Q`, `Q` is nonsingular
and `β_N = Q⁻¹ r =: β` for `N ≥ 2`; hence every weighted block score is centred.
Local dependence (two-unit supports, `≤ N³` overlapping dyad pairs,
`≤ 12 N⁵` dependent pairs of overlap products) gives `O(1/N)` variances for the
normalized Gram, score and meat. Chebyshev, inverse continuity, the normal equations,
the residual substitution bound and the sandwich difference identity yield consistency.

`Target` follows from `CoreTarget` (the same statement for already-normalized
weights `v`, bundled in `Setting`) by exact rescaling. Generic statements `G1`–`G8`
are probability and counting facts; model statements `M0`–`M11` are implications
between the intermediate predicates used by `assemble`.
-/

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-! ## Target -/

/-- **Target (P018-T10, corrected Corollary 2, common directed kernel).** -/
def Target : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R → (∀ N d, R.T N d ≤ 2) →
    ∀ (X : U → U → Vec k) (Y : U → U → ℝ)
      (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool),
    (∀ N d, Function.Injective (dir N d)) →
    (∀ N d (t : Fin (R.T N d)) u₁ u₂,
      R.X N d t u₁ u₂ = (if dir N d t then X u₂ u₁ else X u₁ u₂) ∧
      R.Y N d t u₁ u₂ = (if dir N d t then Y u₂ u₁ else Y u₁ u₂)) →
    ∀ (w : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (a : ℕ → ℝ), (∀ N, 0 < a N) →
    (∃ C : ℝ, ∀ N d t, 0 < w N d t / a N ∧ w N d t / a N ≤ C) →
    ∀ (H : Mat k), H.PosDef →
    Tendsto (fun N : ℕ => recordWeightedH R (fun d t => w N d t / a N)) atTop (𝓝 H) →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • recordWeightedVariance R (w N) ω - recordWeightedTarget R (w N))

/-! ## Objects of the normalized problem -/

/-- Hypotheses of the normalized problem (`v = w/a_N`, bound `C`, limit `H`). -/
def Setting {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k) : Prop :=
  RepeatedStanding R ∧ (∀ N d, Function.Injective (dir N d)) ∧
  (∀ N d (t : Fin (R.T N d)) u₁ u₂,
    R.X N d t u₁ u₂ = (if dir N d t then X u₂ u₁ else X u₁ u₂) ∧
    R.Y N d t u₁ u₂ = (if dir N d t then Y u₂ u₁ else Y u₁ u₂)) ∧
  (∀ N d t, 0 < v N d t ∧ v N d t ≤ C) ∧ H.PosDef ∧
  Tendsto (fun N : ℕ => recordWeightedH R (v N)) atTop (𝓝 H)

/-- `Q = E[X(U,V) X(U,V)']` for iid `U, V`. -/
def popQ {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U) (X : U → U → Vec k) :
    Mat k :=
  meanMat (μ.prod μ) (fun uv => outer (X uv.1 uv.2) (X uv.1 uv.2))

/-- `r = E[X(U,V) Y(U,V)]` for iid `U, V`. -/
def popR {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U) (X : U → U → Vec k)
    (Y : U → U → ℝ) : Vec k :=
  meanVec (μ.prod μ) (fun uv => score (X uv.1 uv.2) (Y uv.1 uv.2))

/-- The common population coefficient `β = Q⁻¹ r`. -/
def popBeta {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U) (X : U → U → Vec k)
    (Y : U → U → ℝ) : Vec k :=
  (popQ μ X)⁻¹.mulVec (popR μ X Y)

/-- `c_N = D⁻¹ Σ_{d,t} v_{dt}`, the normalized total weight. -/
def weightMass {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (N : ℕ) : ℝ :=
  (Dreal N)⁻¹ * ∑ d : Dyad N, ∑ t, v N d t

/-- The normalized sample weighted Gram `D⁻¹ X'WX`. -/
def normGram {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (N : ℕ) (ω : Fin N → U) : Mat k :=
  (Dreal N)⁻¹ • recordWeightedGram R (v N) ω

/-- The scaled meat `(N/D²) meat(q(b))` at a coefficient `b`. -/
def scaledMeatAt {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (N : ℕ) (b : Vec k) (ω : Fin N → U) :
    Mat k :=
  ((N : ℝ) / (Dreal N) ^ 2) • meat members (recordWeightedBlockScore R (v N) b ω)

/-- The deterministic scaled score covariance `(N/D²) Var(Σ_d q_d(β))`. -/
def targetMeat {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (N : ℕ) : Mat k :=
  ((N : ℝ) / (Dreal N) ^ 2) •
    varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, recordWeightedBlockScore R (v N) β ω d)

/-- Unit support of an ordered dyad pair's overlap product (empty if they do not overlap). -/
def pairSupport {N : ℕ} (P : Dyad N × Dyad N) : Finset (Fin N) :=
  if overlap P.1 P.2 then members P.1 ∪ members P.2 else ∅

/-! ## Intermediate predicates -/

/-- Records are measurable and uniformly bounded a.e. under iid sampling. -/
def RecordRegular {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) : Prop :=
  (∀ N (d : Dyad N) (t : Fin (R.T N d)),
    Measurable (fun ω : Fin N → U => repeatedX R ω d t) ∧
    Measurable (fun ω : Fin N → U => repeatedY R ω d t)) ∧
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N (d : Dyad N) (t : Fin (R.T N d)),
    ∀ᵐ ω ∂(repeatedLaw R N), ‖repeatedX R ω d t‖ ≤ B ∧ |repeatedY R ω d t| ≤ B

/-- The common kernel is measurable, bounded a.e., and has an intercept coordinate. -/
def KernelRegular {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U)
    (X : U → U → Vec k) (Y : U → U → ℝ) : Prop :=
  Measurable (fun uv : U × U => X uv.1 uv.2) ∧ Measurable (fun uv : U × U => Y uv.1 uv.2) ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ uv ∂(μ.prod μ), ‖X uv.1 uv.2‖ ≤ B ∧ |Y uv.1 uv.2| ≤ B) ∧
  (∃ j : Fin k, ∀ u₁ u₂, X u₁ u₂ j = 1)

/-- Every record has the common moments `Q` and `r`. -/
def RecordMoments {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) : Prop :=
  ∀ N (d : Dyad N) (t : Fin (R.T N d)),
    meanMat (repeatedLaw R N) (fun ω => outer (repeatedX R ω d t) (repeatedX R ω d t)) =
      popQ R.μ X ∧
    meanVec (repeatedLaw R N) (fun ω => score (repeatedX R ω d t) (repeatedY R ω d t)) =
      popR R.μ X Y

/-- Population design: `Q` nonsingular, `H_N = c_N Q` and `β_N = β` for `N ≥ 2`,
`c_N → c > 0` and `H = c Q`. -/
def PopDesign {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ)
    (H : Mat k) : Prop :=
  (popQ R.μ X).det ≠ 0 ∧
  (∀ N, 2 ≤ N → recordWeightedH R (v N) = weightMass R v N • popQ R.μ X ∧
    recordWeightedBeta R (v N) = popBeta R.μ X Y) ∧
  ∃ c : ℝ, 0 < c ∧ H = c • popQ R.μ X ∧ Tendsto (weightMass R v) atTop (𝓝 c)

/-- Every weighted block score at `β` has mean zero. -/
def Centered {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) :
    Prop :=
  ∀ N (d : Dyad N),
    meanVec (repeatedLaw R N) (fun ω => recordWeightedBlockScore R (v N) (popBeta R.μ X Y) ω d)
      = 0

/-- Normalized sample Gram consistency. -/
def GramLLN {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) : Prop :=
  inProbability (repeatedLaw R) (fun N ω => normGram R v N ω - recordWeightedH R (v N))

/-- Normalized score at `β` vanishes in probability. -/
def ScoreLLN {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R)
    (fun N ω => (Dreal N)⁻¹ • ∑ d : Dyad N, recordWeightedBlockScore R (v N) β ω d)

/-- Coefficient consistency. -/
def CoefConsistent {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R) (fun N ω => recordWeightedOLS R (v N) ω - β)

/-- The scaled meat at `β` concentrates around its mean. -/
def MeatLLN {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R) (fun N ω =>
    scaledMeatAt R v N β ω - meanMat (repeatedLaw R N) (scaledMeatAt R v N β))

/-- Replacing `β` by the fitted coefficient changes the scaled meat negligibly. -/
def SubstitutionNull {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R) (fun N ω =>
    scaledMeatAt R v N (recordWeightedOLS R (v N) ω) ω - scaledMeatAt R v N β ω)

/-- The normalized problem: `Target` for already-normalized weights. -/
def CoreTarget : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • recordWeightedVariance R (v N) ω - recordWeightedTarget R (v N))

/-! ## Generic propositions -/

/-- Two distinct coordinates of an iid product have the product law,
as required by Appendix A's iid unit sampling. -/
def G1 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ}
    (i j : Fin N), i ≠ j →
      (Measure.pi (fun _ : Fin N => μ)).map (fun ω => (ω i, ω j)) = μ.prod μ

/-- Measurable, square-integrable functions of disjoint finite coordinate sets
of an iid product have covariance zero. -/
def G2 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ}
    (S T : Finset (Fin N)) (Z W : (Fin N → U) → ℝ), Disjoint S T →
    Measurable Z → Measurable W →
    (∀ ω ω', (∀ i ∈ S, ω i = ω' i) → Z ω = Z ω') →
    (∀ ω ω', (∀ i ∈ T, ω i = ω' i) → W ω = W ω') →
    MemLp Z 2 (Measure.pi (fun _ : Fin N => μ)) → MemLp W 2 (Measure.pi (fun _ : Fin N => μ)) →
    covariance Z W (Measure.pi (fun _ : Fin N => μ)) = 0

/-- For measurable functions of an iid sample with specified coordinate supports
and almost-sure absolute bound `B`, the variance of their sum is at most
`2B²` times the number of ordered pairs with intersecting supports. -/
def G3 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ}
    {E : Type} [Fintype E] (σ : E → Finset (Fin N)) (Z : E → (Fin N → U) → ℝ) (B : ℝ),
    (∀ e, Measurable (Z e)) →
    (∀ e ω ω', (∀ i ∈ σ e, ω i = ω' i) → Z e ω = Z e ω') →
    (∀ e, ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => μ)), |Z e ω| ≤ B) →
    variance (fun ω => ∑ e, Z e ω) (Measure.pi (fun _ : Fin N => μ)) ≤
      2 * B ^ 2 * ∑ e, ((Finset.univ.filter (fun e' => (σ e ∩ σ e').Nonempty)).card : ℝ)

/-- There are at most `N³` ordered overlapping dyad pairs and at most `12N⁵`
ordered pairs of overlap products with intersecting supports. -/
def G4 : Prop :=
  ∀ N : ℕ,
    (∑ d : Dyad N, ((Finset.univ.filter
        (fun f : Dyad N => (members d ∩ members f).Nonempty)).card : ℝ)) ≤ (N : ℝ) ^ 3 ∧
    (∑ P : Dyad N × Dyad N, ((Finset.univ.filter
        (fun P' : Dyad N × Dyad N => (pairSupport P ∩ pairSupport P').Nonempty)).card : ℝ)) ≤
      12 * (N : ℝ) ^ 5

/-- For square-integrable matrix or vector entries on changing probability spaces,
entrywise variances tending to zero imply convergence in probability of the
centered matrices or vectors. -/
def G5 : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)],
    (∀ F : ∀ N, Ω N → Mat k, (∀ N a b, MemLp (fun ω => F N ω a b) 2 (μ N)) →
      (∀ a b, Tendsto (fun N => variance (fun ω => F N ω a b) (μ N)) atTop (𝓝 0)) →
      inProbability μ (fun N ω => F N ω - meanMat (μ N) (F N))) ∧
    (∀ F : ∀ N, Ω N → Vec k, (∀ N a, MemLp (fun ω => F N ω a) 2 (μ N)) →
      (∀ a, Tendsto (fun N => variance (fun ω => F N ω a) (μ N)) atTop (𝓝 0)) →
      inProbability μ (fun N ω => F N ω - meanVec (μ N) (F N)))

/-- Convergence in probability is preserved under sums and eventual equality.
Deterministic null matrix sequences converge in probability. If a random matrix
converges in probability to a constant and a random vector converges in probability
to zero, their product converges in probability to zero. -/
def G6 : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)],
    (∀ f g : ∀ N, Ω N → Mat k, inProbability μ f → inProbability μ g →
      inProbability μ (fun N ω => f N ω + g N ω)) ∧
    (∀ f g : ∀ N, Ω N → Vec k, inProbability μ f → inProbability μ g →
      inProbability μ (fun N ω => f N ω + g N ω)) ∧
    (∀ A : ℕ → Mat k, Tendsto A atTop (𝓝 0) → inProbability μ (fun N (_ : Ω N) => A N)) ∧
    (∀ f g : ∀ N, Ω N → Mat k, (∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ ω, f N ω = g N ω) →
      inProbability μ f → inProbability μ g) ∧
    (∀ f g : ∀ N, Ω N → Vec k, (∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ ω, f N ω = g N ω) →
      inProbability μ f → inProbability μ g) ∧
    (∀ (A : ∀ N, Ω N → Mat k) (A0 : Mat k) (s : ∀ N, Ω N → Vec k),
      inProbability μ (fun N ω => A N ω - A0) → inProbability μ s →
      inProbability μ (fun N ω => (A N ω).mulVec (s N ω)))

/-- The totalized matrix inverse preserves deterministic convergence and
convergence in probability to a nonsingular limit. -/
def G7 : Prop :=
  ∀ {k : ℕ} (G0 : Mat k), G0.det ≠ 0 →
    (∀ G : ℕ → Mat k, Tendsto G atTop (𝓝 G0) → Tendsto (fun N => (G N)⁻¹) atTop (𝓝 G0⁻¹)) ∧
    (∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] (μ : ∀ N, Measure (Ω N))
      [∀ N, IsProbabilityMeasure (μ N)] (G : ∀ N, Ω N → Mat k),
      inProbability μ (fun N ω => G N ω - G0) →
      inProbability μ (fun N ω => (G N ω)⁻¹ - G0⁻¹))

/-- If the random and deterministic bread matrices converge to the same limit
in probability and deterministically, respectively, the deterministic meat is bounded,
and the random meat approaches it in probability, the sandwich difference tends
to zero in probability. -/
def G8 : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    (Bn Mn : ∀ N, Ω N → Mat k) (B0 T : ℕ → Mat k) (B : Mat k),
    inProbability μ (fun N ω => Bn N ω - B) → Tendsto B0 atTop (𝓝 B) →
    (∃ c : ℝ, ∀ N, ‖T N‖ ≤ c) →
    inProbability μ (fun N ω => Mn N ω - T N) →
    inProbability μ (fun N ω => sandwich (Bn N ω) (Mn N ω) - sandwich (B0 N) (T N))

/-! ## Model implications -/

/-- `G1` and `RepeatedStanding` imply measurability and uniform almost-sure
boundedness of the records under the sample law. -/
def M0 : Prop :=
  G1.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R → RecordRegular R

/-- The normalized setting implies measurability, almost-sure boundedness,
and an intercept coordinate for the common kernel. -/
def M1 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → KernelRegular R.μ X Y

/-- `G1` and the normalized setting with a regular common kernel imply that
every record has the common moments `Q` and `r`. -/
def M2 : Prop :=
  G1.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → KernelRegular R.μ X Y → RecordMoments R X Y

/-- Under the normalized setting, record regularity and common record moments imply
`PopDesign`: `Q` is nonsingular, `H_N = c_N Q` and `β_N = β` for `N ≥ 2`,
and `c_N` has a positive limit `c` with `H = c Q`. -/
def M3 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → RecordMoments R X Y → PopDesign R X Y v H

/-- Under the normalized setting, record regularity, common moments and
`PopDesign` imply that every weighted block score at `β` has mean zero. -/
def M4 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → RecordMoments R X Y → PopDesign R X Y v H →
      Centered R X Y v

/-- `G3`, `G4` and `G5` imply normalized sample Gram consistency under
the normalized setting and record regularity. -/
def M5 : Prop :=
  G3.{u} → G4 → G5.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → GramLLN R v

/-- `G3`, `G4` and `G5` imply that the normalized score at `β` vanishes
in probability under the normalized setting, record regularity and centered block scores. -/
def M6 : Prop :=
  G3.{u} → G4 → G5.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → Centered R X Y v →
      ScoreLLN R v (popBeta R.μ X Y)

/-- `G6` and `G7` imply coefficient consistency under the normalized setting,
`PopDesign`, normalized Gram consistency and a normalized score vanishing in probability. -/
def M7 : Prop :=
  G6.{u} → G7.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → PopDesign R X Y v H → GramLLN R v →
      ScoreLLN R v (popBeta R.μ X Y) → CoefConsistent R v (popBeta R.μ X Y)

/-- `G2`, the normalized setting, record regularity and centered block scores
imply that the expected scaled meat at `β` equals the scaled score covariance for `N ≥ 2`. -/
def M8 : Prop :=
  G2.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → Centered R X Y v →
      ∀ N, 2 ≤ N → meanMat (repeatedLaw R N) (scaledMeatAt R v N (popBeta R.μ X Y)) =
        targetMeat R v (popBeta R.μ X Y) N

/-- `G3`, `G4` and `G5` imply concentration of the scaled meat at `β`
around its mean under the normalized setting and record regularity. -/
def M9 : Prop :=
  G3.{u} → G4 → G5.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → MeatLLN R v (popBeta R.μ X Y)

/-- `G4`, `G6`, the normalized setting, record regularity and coefficient
consistency imply that replacing `β` by the fitted coefficient changes the scaled meat
by a quantity tending to zero in probability. -/
def M10 : Prop :=
  G4 → G6.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → CoefConsistent R v (popBeta R.μ X Y) →
      SubstitutionNull R v (popBeta R.μ X Y)

/-- `G3`, `G4`, the normalized setting and record regularity imply a uniform
bound on the deterministic scaled score covariance at `β`. -/
def M11 : Prop :=
  G3.{u} → G4 → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R →
      ∃ c : ℝ, ∀ N, ‖targetMeat R v (popBeta R.μ X Y) N‖ ≤ c

/-! ## Rescaling identities -/

theorem Dreal_ne_zero {N : ℕ} (hN : 2 ≤ N) : Dreal N ≠ 0 := by
  unfold Dreal
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (N : ℝ) ≠ 0 := by linarith
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  exact div_ne_zero (mul_ne_zero h0 h1) two_ne_zero

/-- Exact rescaling of the fitted sandwich: `N V̂ = (D⁻¹G)⁻¹ ((N/D²) meat) (D⁻¹G)⁻¹`. -/
theorem variance_rescale {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) (hN : 2 ≤ N) :
    (N : ℝ) • recordWeightedVariance R w ω =
      sandwich ((Dreal N)⁻¹ • recordWeightedGram R w ω)⁻¹
        (((N : ℝ) / (Dreal N) ^ 2) •
          meat members (recordWeightedBlockScore R w (recordWeightedOLS R w ω) ω)) := by
  have hD := Dreal_ne_zero hN
  rw [matrix_inverse_scale_total _ _ (inv_ne_zero hD), inv_inv]
  unfold recordWeightedVariance sandwich
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  field_simp

/-- The corrected target as a sandwich with the scaled score covariance. -/
theorem target_rescale {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (hβ : recordWeightedBeta R w = β) :
    recordWeightedTarget R w =
      sandwich (recordWeightedH R w)⁻¹ (((N : ℝ) / (Dreal N) ^ 2) •
        varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, recordWeightedBlockScore R w β ω d)) := by
  unfold recordWeightedTarget sandwich
  rw [hβ]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

/-! ## Assembly -/

/-- The generic and model implications yield sandwich consistency for normalized weights. -/
theorem assemble_core (g1 : G1.{u}) (g2 : G2.{u}) (g3 : G3.{u}) (g4 : G4) (g5 : G5.{u})
    (g6 : G6.{u}) (g7 : G7.{u}) (g8 : G8.{u}) (m0 : M0.{u}) (m1 : M1.{u}) (m2 : M2.{u})
    (m3 : M3.{u}) (m4 : M4.{u}) (m5 : M5.{u}) (m6 : M6.{u}) (m7 : M7.{u}) (m8 : M8.{u})
    (m9 : M9.{u}) (m10 : M10.{u}) (m11 : M11.{u}) : CoreTarget.{u} := by
  intro U _ k R X Y dir v C H hS
  have hP : ∀ N, IsProbabilityMeasure (repeatedLaw R N) := fun N => by
    have := hS.1.1
    unfold repeatedLaw
    infer_instance
  obtain ⟨gAddM, -, gDet, gEqM, -, -⟩ := g6 (repeatedLaw R)
  have hreg := m0 g1 R hS.1
  have hker := m1 R X Y dir v C H hS
  have hmom := m2 g1 R X Y dir v C H hS hker
  have hpop := m3 R X Y dir v C H hS hreg hmom
  have hcent := m4 R X Y dir v C H hS hreg hmom hpop
  have hgram := m5 g3 g4 g5 R X Y dir v C H hS hreg
  have hscore := m6 g3 g4 g5 R X Y dir v C H hS hreg hcent
  have hcoef := m7 g6 g7 R X Y dir v C H hS hpop hgram hscore
  have hsub := m10 g4 g6 R X Y dir v C H hS hreg hcoef
  have hmeat := m9 g3 g4 g5 R X Y dir v C H hS hreg
  have hmeanmeat := m8 g2 R X Y dir v C H hS hreg hcent
  have hTb := m11 g3 g4 R X Y dir v C H hS hreg
  set β := popBeta R.μ X Y with hβdef
  have hHdet : H.det ≠ 0 := hS.2.2.2.2.1.det_pos.ne'
  obtain ⟨gInvDet, gInvProb⟩ := g7 H hHdet
  -- the meat converges to the deterministic target meat
  have hM : inProbability (repeatedLaw R) (fun N ω =>
      scaledMeatAt R v N (recordWeightedOLS R (v N) ω) ω - targetMeat R v β N) := by
    apply gEqM _ _ ⟨2, fun N hN ω => ?_⟩ (gAddM _ _ hsub hmeat)
    rw [hmeanmeat N hN]
    abel
  -- the random bread converges to `H⁻¹`
  have hG : inProbability (repeatedLaw R) (fun N ω => normGram R v N ω - H) := by
    apply gEqM _ _ ⟨0, fun N _ ω => ?_⟩
      (gAddM _ _ hgram (gDet _ (tendsto_sub_nhds_zero_iff.mpr hS.2.2.2.2.2)))
    abel
  have hB := gInvProb (repeatedLaw R) (normGram R v) hG
  have hB0 := gInvDet (fun N => recordWeightedH R (v N)) hS.2.2.2.2.2
  have hsand := g8 (repeatedLaw R) (fun N ω => (normGram R v N ω)⁻¹)
    (fun N ω => scaledMeatAt R v N (recordWeightedOLS R (v N) ω) ω)
    (fun N => (recordWeightedH R (v N))⁻¹) (targetMeat R v β) H⁻¹ hB hB0 hTb hM
  apply gEqM _ _ ⟨2, fun N hN ω => ?_⟩ hsand
  rw [variance_rescale R (v N) ω hN, target_rescale R (v N) β ((hpop.2.1 N hN).2)]
  rfl

/-- Rescaling by `a_N` yields the corrected consistency statement. -/
theorem assemble (g1 : G1.{u}) (g2 : G2.{u}) (g3 : G3.{u}) (g4 : G4) (g5 : G5.{u})
    (g6 : G6.{u}) (g7 : G7.{u}) (g8 : G8.{u}) (m0 : M0.{u}) (m1 : M1.{u}) (m2 : M2.{u})
    (m3 : M3.{u}) (m4 : M4.{u}) (m5 : M5.{u}) (m6 : M6.{u}) (m7 : M7.{u}) (m8 : M8.{u})
    (m9 : M9.{u}) (m10 : M10.{u}) (m11 : M11.{u}) : Target.{u} := by
  intro U _ k R hR _hDir X Y dir hdir hCommon w a ha hw H hH hlim
  obtain ⟨C, hC⟩ := hw
  have hcore := assemble_core g1 g2 g3 g4 g5 g6 g7 g8 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
    R X Y dir (fun N d t => w N d t / a N) C H ⟨hR, hdir, hCommon, hC, hH, hlim⟩
  have hfun : (fun (N : ℕ) (ω : Fin N → U) =>
      (N : ℝ) • recordWeightedVariance R (w N) ω - recordWeightedTarget R (w N)) =
      (fun (N : ℕ) (ω : Fin N → U) =>
        (N : ℝ) • recordWeightedVariance R (fun d t => w N d t / a N) ω -
        recordWeightedTarget R (fun d t => w N d t / a N)) := by
    funext N ω
    have hv : (fun d t => w N d t / a N) = (fun d t => (a N)⁻¹ * w N d t) := by
      funext d t
      rw [div_eq_inv_mul]
    obtain ⟨-, hvar, htar⟩ := weighted_scale_invariance R (w N) (a N)⁻¹ (inv_pos.mpr (ha N)) ω
    rw [hv, hvar, htar]
  rw [hfun]
  exact hcore

end

end AronowAudit.P018.Wave1.WeightedConsistency
