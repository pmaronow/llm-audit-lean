import AronowAudit.P002.P002_Audit

/-!
# P002-T9: corrected eigenvalue display in the proof of Lemma 19

Supplement p. 42, first display in the proof of Lemma 19, with the corrected
constant `min(1, e)`. The statement uses the fitted-minus-pooled coefficient error,
one common vanishing error for both arms, and every strict subsequence. It includes
the Supplement p. 27 independent coupling as an explicit finite-event
factorization; `RandomizationSequence` specifies only marginal laws. The proof
below uses only the marginals.

The argument combines a without-replacement exponential bound (S), obtained from
independent Bernoulli sampling by conditioning on the count (the binomial mode has
mass at least `1/(N+1)`) and Hoeffding's inequality; entrywise tail bounds for both
arm Gram matrices; first Borel–Cantelli along strictly increasing sizes; and a
uniform entrywise quadratic perturbation bound around the population Gram matrix.
The population Rayleigh bound is `min(1,e)`.

The sampling bound (S) includes the explicit hypothesis `0 < r`.
-/

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- Corrected eigenvalue bound in the proof of Lemma 19, Supplement p. 42. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sizes : ℕ → ℕ), StrictMono sizes →
    ∀ (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
      (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B → (0 < r ∧ r ≤ 1/2) →
    (∀ n, Xi (P n) δ e A B r) →
    RandomizationSequence (fun n => (P n).pop) μ Z →
    (∀ (I : Finset ℕ) (E : ∀ n, Finset (Fin (sizes n)) → Prop),
      μ {ω | ∀ n ∈ I, E n (Z n ω)} = ∏ n ∈ I, μ {ω | E n (Z n ω)}) →
    ∀ (sub : ℕ → ℕ), StrictMono sub →
    ∀ᵐ ω ∂μ, ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
      ∀ᶠ j in atTop, ∀ a : Bool,
        let N := sub j
        let S := Z N ω
        let q := observedW (P N).pop (late (P N).pop) S
        let b := fitted (P N) q S a - ols (P N).x Finset.univ q
        (min 1 e + err j) * normSq b ≤
          dotProduct b (gram (P N).x (if a then S else Sᶜ) *ᵥ b)

/-! ## Statements used by the nodes -/

/-- Bernoulli conditioning: for
`0 < m < N` and `p = m/N`, the uniform `m`-subset probability of any event is at most
`N+1` times its probability under independent Bernoulli(`p`) inclusion. Every
`m`-subset has Bernoulli weight `p^m(1-p)^(N-m)`, and `m` is a mode of
Binomial(`N`,`p`), so that weight times `choose N m` is at least `1/(N+1)`. -/
def BinomialConditioning : Prop :=
  ∀ (N m : ℕ), 0 < m → m < N → ∀ (E : Finset (Fin N) → Prop),
    (((Finset.univ.powersetCard m).filter E).card : ℝ) / (N.choose m : ℝ) ≤
      ((N : ℝ) + 1) * ∑ B : Finset (Fin N),
        if E B then ((m : ℝ) / N) ^ B.card * (1 - (m : ℝ) / N) ^ (N - B.card) else 0

/-- Hoeffding's lemma for a centred Bernoulli variable (two-point form).
Hoeffding 1963, Lemma 1, applied to a two-point law through Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`. -/
def TwoPointHoeffding : Prop :=
  ∀ (p c : ℝ), 0 ≤ p → p ≤ 1 →
    p * Real.exp (c * (1 - p)) + (1 - p) * Real.exp (-(c * p)) ≤ Real.exp (c ^ 2 / 8)

/-- Exact factorization of the weighted Bernoulli moment generating function over units
by expansion over subsets (`Fintype.prod_add`). -/
def BernoulliMGF : Prop :=
  ∀ (N : ℕ) (p θ : ℝ) (a : Fin N → ℝ),
    ∑ B : Finset (Fin N), p ^ B.card * (1 - p) ^ (N - B.card) *
        Real.exp (θ * (∑ i ∈ B, a i - p * ∑ i, a i)) =
      ∏ i, (p * Real.exp (θ * (a i * (1 - p))) + (1 - p) * Real.exp (-(θ * (a i * p))))

/-- Two-sided Hoeffding inequality for an independent Bernoulli(`p`) inclusion vector,
written with the explicit finite product weights. Each factor in `BernoulliMGF` is
bounded by `TwoPointHoeffding` at `c = θ a_i`; Chernoff at `θ = 4s/∑a²` and a union
with `-a` give the two-sided bound. -/
def BernoulliHoeffding : Prop :=
  ∀ (N : ℕ) (p : ℝ) (a : Fin N → ℝ) (s : ℝ), 0 ≤ p → p ≤ 1 → 0 ≤ s →
    0 < ∑ i, a i ^ 2 →
    ∑ B : Finset (Fin N),
        (if s ≤ |∑ i ∈ B, a i - p * ∑ i, a i| then p ^ B.card * (1 - p) ^ (N - B.card) else 0) ≤
      2 * Real.exp (-2 * s ^ 2 / ∑ i, a i ^ 2)

/-- The without-replacement exponential bound (S), with the explicit hypothesis `0 < r`. The
zero-sum-of-squares case is included (the event is then empty). -/
def SamplingBound : Prop :=
  ∀ (N m : ℕ) (r C t : ℝ) (a : Fin N → ℝ), 1 ≤ m → m < N → 0 < r → r * N ≤ m → 0 < C →
    (∑ i, a i ^ 2) / N ≤ C → 0 < t →
    (((Finset.univ.powersetCard m).filter
        (fun T => t ≤ |groupMean T a - mean a|)).card : ℝ) / (N.choose m : ℝ) ≤
      2 * ((N : ℝ) + 1) * Real.exp (-2 * r ^ 2 * N * t ^ 2 / C)

/-- Every augmented Gram entry `x̃_is x̃_it` has population mean square at most
`max 1 A` under Xi (fourth moments and Cauchy–Schwarz; the intercept entry is `1`). -/
def EntryMeanSquare : Prop :=
  ∀ (n k : ℕ) (P : CovPopulation n k) (δ e A B r : ℝ), Xi P δ e A B r →
    ∀ s t : Option (Fin k),
      mean (fun i => (augmented P.x i s * augmented P.x i t) ^ 2) ≤ max 1 A

/-- Entrywise exponential tail bound for both observed arm Gram matrices (both arm sizes
are at least `r n`; the control arm uses the complement bijection between `n1`- and
`(n-n1)`-subsets). -/
def EntryTail : Prop :=
  ∀ (n k : ℕ) (P : CovPopulation n k) (δ e A B r : ℝ), 0 < A → 0 < r → Xi P δ e A B r →
    ∀ (a : Bool) (s t : Option (Fin k)) (τ : ℝ), 0 < τ →
      probability P.pop (fun S =>
          τ ≤ |gram P.x (if a then S else Sᶜ) s t - gram P.x Finset.univ s t|) ≤
        2 * ((n : ℝ) + 1) * Real.exp (-2 * r ^ 2 * n * τ ^ 2 / max 1 A)

/-- Summability of the tail bounds along any strictly increasing size sequence. -/
def SummableTail : Prop :=
  ∀ (sizes sub : ℕ → ℕ), StrictMono sizes → StrictMono sub → ∀ c : ℝ, 0 < c →
    Summable (fun j => 2 * ((sizes (sub j) : ℝ) + 1) * Real.exp (-c * sizes (sub j)))

/-- First Borel–Cantelli lemma in the form used here: summable tail bounds at every
positive threshold give almost-sure convergence to zero (thresholds `1/(q+1)`). -/
def BorelCantelliZero : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (D : ℕ → Ω → ℝ) (bound : ℝ → ℕ → ℝ),
    (∀ τ : ℝ, 0 < τ → Summable (bound τ)) →
    (∀ τ : ℝ, 0 < τ → ∀ j, μ {ω | τ ≤ |D j ω|} ≤ ENNReal.ofReal (bound τ j)) →
    ∀ᵐ ω ∂μ, Tendsto (fun j => D j ω) atTop (nhds 0)

/-- Almost-sure entrywise convergence of both observed arm Gram matrices to the
population Gram matrix along every strict subsequence (marginal laws only). -/
def AEEntrywise : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sizes : ℕ → ℕ), StrictMono sizes →
    ∀ (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
      (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ),
    0 < A → 0 < r → (∀ n, Xi (P n) δ e A B r) →
    RandomizationSequence (fun n => (P n).pop) μ Z →
    ∀ (sub : ℕ → ℕ), StrictMono sub →
    ∀ᵐ ω ∂μ, ∀ (a : Bool) (s t : Option (Fin k)),
      Tendsto (fun j => gram (P (sub j)).x (if a then Z (sub j) ω else (Z (sub j) ω)ᶜ) s t -
        gram (P (sub j)).x Finset.univ s t) atTop (nhds 0)

/-- Deterministic entrywise quadratic perturbation bound:
`|b'(H-G)b| ≤ D (Σ|b_s|)² ≤ (k+1) D ‖b‖²` (triangle inequality, Cauchy–Schwarz). -/
def EntrywiseQuadraticBound : Prop :=
  ∀ (k : ℕ) (H G : Matrix (Option (Fin k)) (Option (Fin k)) ℝ) (D : ℝ),
    (∀ s t, |H s t - G s t| ≤ D) →
    ∀ b : Option (Fin k) → ℝ,
      |dotProduct b (H *ᵥ b) - dotProduct b (G *ᵥ b)| ≤ ((k : ℝ) + 1) * D * normSq b

/-- Uniform quadratic-form transfer:
with `D_j` the maximal entry error over both arms and `d = k+1`,
`|b'(H-G)b| ≤ d D_j ‖b‖²`; put `err j = -d D_j`. -/
def QuadraticFromEntrywise : Prop :=
  ∀ (k : ℕ) (H : ℕ → Bool → Matrix (Option (Fin k)) (Option (Fin k)) ℝ)
    (G : ℕ → Matrix (Option (Fin k)) (Option (Fin k)) ℝ) (c : ℝ),
    (∀ a s t, Tendsto (fun j => H j a s t - G j s t) atTop (nhds 0)) →
    (∀ j (b : Option (Fin k) → ℝ), c * normSq b ≤ dotProduct b (G j *ᵥ b)) →
    ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
      ∀ j a (b : Option (Fin k) → ℝ), (c + err j) * normSq b ≤ dotProduct b (H j a *ᵥ b)

/-! ## Nodes -/

/-- Node 1 (Bernoulli conditioning and binomial mode mass). -/
def N1 : Prop := BinomialConditioning
/-- Node 2 (Hoeffding's lemma, two-point form; standard input). -/
def N2 : Prop := TwoPointHoeffding
/-- Node 3 (factorization of the weighted Bernoulli moment generating function). -/
def N3 : Prop := BernoulliMGF
/-- Node 4 (finite Bernoulli Hoeffding inequality, Chernoff step). -/
def N4 : Prop := TwoPointHoeffding → BernoulliMGF → BernoulliHoeffding
/-- Node 5 (without-replacement exponential bound (S) with `0 < r`). -/
def N5 : Prop := BinomialConditioning → BernoulliHoeffding → SamplingBound
/-- Node 6 (augmented Gram entry mean squares under Xi). -/
def N6 : Prop := EntryMeanSquare
/-- Node 7 (finite tail bound for sampled Gram entries). -/
def N7 : Prop := SamplingBound → EntryMeanSquare → EntryTail
/-- Node 8 (summability along strictly increasing sizes). -/
def N8 : Prop := SummableTail
/-- Node 9 (first Borel–Cantelli, generic). -/
def N9 : Prop := BorelCantelliZero.{u}
/-- Node 10 (almost-sure entrywise convergence: marginal transfer
through `RandomizationSequence`, Borel–Cantelli, finite intersection over entries). -/
def N10 : Prop := EntryTail → SummableTail → BorelCantelliZero.{u} → AEEntrywise.{u}
/-- Node 11 (deterministic entrywise quadratic bound). -/
def N11 : Prop := EntrywiseQuadraticBound
/-- Node 12 (uniform quadratic-form transfer: finite maximum of
the entry errors, `err j = -(k+1) D_j`). -/
def N12 : Prop := EntrywiseQuadraticBound → QuadraticFromEntrywise

/-- The nodes suffice. The coefficient vector is arbitrary in the quadratic bound, so the
actual fitted-minus-pooled error needs no additional assumption. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9.{u}) (h10 : N10.{u}) (h11 : N11) (h12 : N12) : Target.{u} := by
  intro Ω _ μ _ sizes hsizes k P Z δ e A B r _hk _hδ _he hA _hB hr hP hZ _hInd sub hsub
  have hae : AEEntrywise.{u} := h10 (h7 (h5 h1 (h4 h2 h3)) h6) h8 h9
  have hω := hae μ sizes hsizes k P Z δ e A B r hA hr.1 hP hZ sub hsub
  filter_upwards [hω] with ω hω
  have hG : ∀ j (b : Option (Fin k) → ℝ),
      min 1 e * normSq b ≤ dotProduct b (gram (P (sub j)).x Finset.univ *ᵥ b) := by
    intro j b
    obtain ⟨hD, -, -, -, -, -, -, hx, -, hray⟩ := hP (sub j)
    have hn : 0 < sizes (sub j) := by have := hD.1; omega
    have hg := (corrected_augmented_gram (P (sub j)).x hn e hx hray).2.2.2 b
    rw [gram_quadratic]
    simpa [groupMean, mean] using hg
  obtain ⟨err, herr, hb⟩ := h12 h11 k
    (fun j a => gram (P (sub j)).x (if a then Z (sub j) ω else (Z (sub j) ω)ᶜ))
    (fun j => gram (P (sub j)).x Finset.univ) (min 1 e) hω hG
  exact ⟨err, herr, Filter.Eventually.of_forall (fun j a => hb j a _)⟩

end
end AronowAudit.P002.Wave1.E61Eigenvalue
