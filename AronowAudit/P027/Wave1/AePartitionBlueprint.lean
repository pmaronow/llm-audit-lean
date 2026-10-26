import AronowAudit.P027.P027_Audit

/-! # Probability-zero co-selection and totalling (P027-T4)

Main p. 237 defines a cluster by `Pr(I_k ≠ I_l) = 0`; `liftDesign`
imposes equal indicators on every atom, including zero-weight atoms. For an
arbitrary design on `Σ g, Fin (n g)` with nonempty fibres, positive marginals,
and probability-zero disagreement, the representative-member group design has
the same atoms and weights. First and joint inclusion probabilities agree
exactly. The HT total and uncorrected HT variance estimator agree on every
positive-weight atom; the actual design variance of the HT total and `A` agree.
No samplewise conclusion is claimed on zero-weight atoms.
-/

namespace AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- Totalling preserves inclusion probabilities, sample statistics on the support,
actual design variance, and `A` under probability-zero co-selection. -/
def Target : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω]
    (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω), Positive D →
    (∀ (g : G) (i j : Fin (n g)),
      expect D (fun ω =>
        if D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩ then 0 else 1) = 0) →
    ∀ (y : (Σ g, Fin (n g)) → ℝ),
    let Dc : Design G Ω :=
      { weight := D.weight
        nonneg := D.nonneg
        total := D.total
        selected := fun ω g => D.selected ω ⟨g,⟨0, hn g⟩⟩ }
    Positive Dc ∧
    (∀ (g : G) (i : Fin (n g)), pi D ⟨g,i⟩ = pi Dc g) ∧
    (∀ (g h : G) (i : Fin (n g)) (j : Fin (n h)),
      joint D ⟨g,i⟩ ⟨h,j⟩ = joint Dc g h) ∧
    (∀ ω : Ω, 0 < D.weight ω →
      htTotal D y ω = htTotal Dc (groupTotal n y) ω ∧
      htVarianceEstimator D y ω =
        htVarianceEstimator Dc (groupTotal n y) ω) ∧
    variance D (htTotal D y) =
      variance Dc (htTotal Dc (groupTotal n y)) ∧
    biasA D y = biasA Dc (groupTotal n y)

/-- The representative-member group design: same atoms and weights as `D`; group
`g` is selected when its member `0` is. Definitionally the `Dc` of `Target`. -/
def repDesign {G Ω : Type} [Fintype G] [Fintype Ω] (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω) : Design G Ω where
  weight := D.weight
  nonneg := D.nonneg
  total := D.total
  selected ω g := D.selected ω ⟨g,⟨0, hn g⟩⟩

/-- N1: If w_ω > 0 and two members disagree at ω, the disagreement
summand equals w_ω > 0, contradicting the zero sum. Thus zero expected
disagreement forces all members of a group to agree on every positive-weight atom. -/
def N1 : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (n : G → ℕ) (D : Design (Σ g, Fin (n g)) Ω),
    (∀ (g : G) (i j : Fin (n g)),
      expect D (fun ω =>
        if D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩ then 0 else 1) = 0) →
    ∀ ω : Ω, 0 < D.weight ω → ∀ (g : G) (i j : Fin (n g)),
      D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩

/-- N2: Agreement with the representative on the support gives
π_D(g,i) = Σ_ω w_ω J_g(ω) = π_Dc(g). Applying the same support argument to
products gives π_D((g,i),(h,j)) = π_Dc(g,h), including g = h. Thus first and
joint inclusion probabilities transfer exactly. -/
def N2 : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω),
    (∀ ω : Ω, 0 < D.weight ω → ∀ (g : G) (i : Fin (n g)),
      D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,⟨0, hn g⟩⟩) →
    (∀ (g : G) (i : Fin (n g)), pi D ⟨g,i⟩ = pi (repDesign n hn D) g) ∧
    (∀ (g h : G) (i : Fin (n g)) (j : Fin (n h)),
      joint D ⟨g,i⟩ ⟨h,j⟩ = joint (repDesign n hn D) g h)

/-- N3: On a positive-weight atom, sum first within each fibre. The pair
coefficient is constant across members of fibres g,h whenever π_kl > 0.
The HT total and uncorrected HT variance estimator of the original units equal
those of the group totals on every positive-weight atom. Equivalently, compare
with `liftDesign (repDesign n hn D) n` and apply `aggregation_total_preserved`
and `aggregation_ht_estimator_preserved`; `Positive D` and the `pi` identities
give the required `Positive (repDesign n hn D)`. -/
def N3 : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω), Positive D →
    (∀ ω : Ω, 0 < D.weight ω → ∀ (g : G) (i : Fin (n g)),
      D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,⟨0, hn g⟩⟩) →
    (∀ (g : G) (i : Fin (n g)), pi D ⟨g,i⟩ = pi (repDesign n hn D) g) →
    (∀ (g h : G) (i : Fin (n g)) (j : Fin (n h)),
      joint D ⟨g,i⟩ ⟨h,j⟩ = joint (repDesign n hn D) g h) →
    ∀ (y : (Σ g, Fin (n g)) → ℝ) (ω : Ω), 0 < D.weight ω →
      htTotal D y ω = htTotal (repDesign n hn D) (groupTotal n y) ω ∧
      htVarianceEstimator D y ω =
        htVarianceEstimator (repDesign n hn D) (groupTotal n y) ω

/-- N4: Two designs with the same weights, possibly on different unit types,
give equal design expectations and actual design variances to sample statistics
that agree on the positive-weight support. Contributions at zero-weight atoms
vanish. Subtract the common mean, square, and sum with the same weights to obtain
the variance identity. -/
def N4 : Prop :=
  ∀ {U U' Ω : Type} [Fintype U] [Fintype U'] [Fintype Ω]
    (D : Design U Ω) (D' : Design U' Ω), (∀ ω, D.weight ω = D'.weight ω) →
    ∀ (f f' : Ω → ℝ), (∀ ω, 0 < D.weight ω → f ω = f' ω) →
      expect D f = expect D' f' ∧ variance D f = variance D' f'

/-- N5: No two members of the same group have joint probability zero,
because q_gg = p_g > 0. Thus the distinct-unit zero-pair condition is exactly
g ≠ h and q_gh = 0, giving A_D(y) = A_Dc(Y). Equivalently, `biasA` depends on
the design only through `joint`, so compare with
`liftDesign (repDesign n hn D) n` and apply `aggregation_A_preserved`. -/
def N5 : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω), Positive D →
    (∀ (g : G) (i : Fin (n g)), pi D ⟨g,i⟩ = pi (repDesign n hn D) g) →
    (∀ (g h : G) (i : Fin (n g)) (j : Fin (n h)),
      joint D ⟨g,i⟩ ⟨h,j⟩ = joint (repDesign n hn D) g h) →
    ∀ (y : (Σ g, Fin (n g)) → ℝ),
      biasA D y = biasA (repDesign n hn D) (groupTotal n y)

/-- The nodes suffice: N1 gives agreement with the representative on the support,
N2 the inclusion identities (hence positivity of the group design from `hD`), N3
the samplewise identities, N4 (same weights) the variance identity, N5 `A`. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) : Target := by
  intro G Ω _ _ n hn D hD hco y
  have hs : ∀ ω : Ω, 0 < D.weight ω → ∀ (g : G) (i : Fin (n g)),
      D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,⟨0, hn g⟩⟩ :=
    fun ω hω g i => h1 n D hco ω hω g i ⟨0, hn g⟩
  obtain ⟨hpi, hjoint⟩ := h2 n hn D hs
  have hpos : Positive (repDesign n hn D) := by
    intro g
    rw [← hpi g ⟨0, hn g⟩]
    exact hD ⟨g, ⟨0, hn g⟩⟩
  have hsamp := h3 n hn D hD hs hpi hjoint y
  have hvar := (h4 D (repDesign n hn D) (fun _ => rfl) (htTotal D y)
    (htTotal (repDesign n hn D) (groupTotal n y)) (fun ω hω => (hsamp ω hω).1)).2
  exact ⟨hpos, hpi, hjoint, hsamp, hvar, h5 n hn D hD hpi hjoint y⟩


end
end AronowAudit.P027.Wave1.AePartition
