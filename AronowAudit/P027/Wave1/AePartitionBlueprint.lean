import AronowAudit.P027.P027_Audit

/-! # Blueprint: probability-zero co-selection bridge for totalling (P027-T4)

Dossier group P027, record 5 (`aggregation_ht_estimator_preserved`, resolution
`bridge`), shared with record 6 (`aggregation_total_preserved`, associate-only).
Main p. 237 defines a cluster by `Pr(I_k ≠ I_l) = 0`; the existing `liftDesign`
imposes equal indicators on every atom, including zero-weight atoms. This bridge
starts from an arbitrary original design on `Σ g, Fin (n g)` with nonempty fibres,
positive marginals and the literal probability-zero disagreement condition, builds
the representative-member group design (same atoms and weights), and proves that
first/joint inclusion probabilities agree exactly, that the HT total and the
uncorrected HT variance estimator agree on every positive-weight atom, and that the
actual design variance of the HT total and `A` agree. No conclusion is claimed on
zero-weight atoms (both referees: that restriction is necessary).

Map-P027 report, record 5 (statement and paper proof); accepted by both referees
without fixes. Final declaration (writer):
`AronowAudit.P027.Wave1.aggregation_ae_partition_bridge` in
`AronowAudit/P027/Wave1/AePartition.lean`.
-/

namespace AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- Frozen target (map-P027 record 5, `aggregation_ae_partition_bridge`). -/
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

/-- N1 (paper-proof step "If w_ω > 0 and the two members disagreed at ω, that
summand would equal w_ω > 0, contradicting the sum being zero"): zero expected
disagreement forces agreement of all members of a group on every positive-weight
atom. -/
def N1 : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (n : G → ℕ) (D : Design (Σ g, Fin (n g)) Ω),
    (∀ (g : G) (i j : Fin (n g)),
      expect D (fun ω =>
        if D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩ then 0 else 1) = 0) →
    ∀ ω : Ω, 0 < D.weight ω → ∀ (g : G) (i j : Fin (n g)),
      D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,j⟩

/-- N2 (paper-proof step "π_D(g,i) = Σ_ω w_ω J_g(ω) = π_Dc(g); the same support
argument applied to products gives π_D((g,i),(h,j)) = π_Dc(g,h), including g = h"):
agreement with the representative on the support transfers first and joint
inclusion probabilities exactly. -/
def N2 : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω] (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω),
    (∀ ω : Ω, 0 < D.weight ω → ∀ (g : G) (i : Fin (n g)),
      D.selected ω ⟨g,i⟩ = D.selected ω ⟨g,⟨0, hn g⟩⟩) →
    (∀ (g : G) (i : Fin (n g)), pi D ⟨g,i⟩ = pi (repDesign n hn D) g) ∧
    (∀ (g h : G) (i : Fin (n g)) (j : Fin (n h)),
      joint D ⟨g,i⟩ ⟨h,j⟩ = joint (repDesign n hn D) g h)

/-- N3 (paper-proof step "On a positive-weight atom, sum first within each fibre ...
the pair coefficient is constant across members of fibres g,h whenever π_kl > 0"):
on every positive-weight atom the HT total and the uncorrected HT variance
estimator of the original units equal those of the group totals. (Equivalently:
compare with `liftDesign (repDesign n hn D) n` and use the proved
`aggregation_total_preserved` and `aggregation_ht_estimator_preserved`; `Positive D`
and the `pi` identities give the `Positive (repDesign n hn D)` those helpers take.) -/
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

/-- N4 (paper-proof step "Their values agree at positive-weight atoms and both other
contributions are multiplied by zero. Subtract that common mean, square, and sum
with the same weights"): two designs with the same weights, possibly on different
unit types, give equal design expectations and equal actual design variances to
sample statistics that agree on the positive-weight support. -/
def N4 : Prop :=
  ∀ {U U' Ω : Type} [Fintype U] [Fintype U'] [Fintype Ω]
    (D : Design U Ω) (D' : Design U' Ω), (∀ ω, D.weight ω = D'.weight ω) →
    ∀ (f f' : Ω → ℝ), (∀ ω, 0 < D.weight ω → f ω = f' ω) →
      expect D f = expect D' f' ∧ variance D f = variance D' f'

/-- N5 (paper-proof step "no two members of the same group have joint probability
zero, because q_gg = p_g > 0. Hence the distinct-unit zero-pair condition is exactly
g ≠ h and q_gh = 0 ... giving A_D(y) = A_Dc(Y)"): `A` is preserved. (Equivalently:
`biasA` depends on the design only through `joint`, so compare with
`liftDesign (repDesign n hn D) n` and use the proved `aggregation_A_preserved`.) -/
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

/-- Nonvacuity (both referees' null-atom instance): `G = Fin 2`, `n = (2,1)`,
`Ω = Fin 3` with weights `(1/2, 1/2, 0)`; atom 0 selects both members of group 0,
atom 1 the member of group 1, the null atom 2 only member 0 of group 0. -/
def nullAtomDesign : Design (Σ g : Fin 2, Fin (if g = 0 then 2 else 1)) (Fin 3) where
  weight ω := if ω = 2 then 0 else 1/2
  nonneg ω := by split <;> norm_num
  total := by simp [Fin.sum_univ_succ]; norm_num
  selected ω k := decide ((ω = 0 ∧ k.1 = 0) ∨ (ω = 1 ∧ k.1 = 1) ∨
    (ω = 2 ∧ k.1 = 0 ∧ k.2.val = 0))

/-- The null-atom design satisfies every hypothesis of `Target` (positive marginals
and zero disagreement probability; `hn` holds since `n = (2,1)`), while the two
members of group 0 genuinely disagree on the null atom. -/
example : Positive nullAtomDesign ∧
    (∀ (g : Fin 2) (i j : Fin (if g = 0 then 2 else 1)),
      expect nullAtomDesign (fun ω => if nullAtomDesign.selected ω ⟨g,i⟩ =
        nullAtomDesign.selected ω ⟨g,j⟩ then 0 else 1) = 0) ∧
    nullAtomDesign.selected 2 ⟨0, ⟨0, by decide⟩⟩ ≠
      nullAtomDesign.selected 2 ⟨0, ⟨1, by decide⟩⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨g, i⟩
    fin_cases g <;> simp [pi, expect, indicator, nullAtomDesign, Fin.sum_univ_succ]
  · intro g i j
    fin_cases g <;> simp [expect, nullAtomDesign, Fin.sum_univ_succ]
  · simp [nullAtomDesign]

end
end AronowAudit.P027.Wave1.AePartition
