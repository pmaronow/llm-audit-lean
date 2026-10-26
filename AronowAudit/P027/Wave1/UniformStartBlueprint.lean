import AronowAudit.P027.P027_Audit
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Continuous uniform-start law of the periodic PPS design (P027-T2)

Supplement pp. A3–A4: sizes alternate 2, 10; systematic PPS uses cumulative
sizes with one uniform start on `[0, 6q)`, where `q = 2r`.

The result describes the cumulative left endpoints of the units, the half-open
phase-interval partition of `[0, 12r)`, and the normalized uniform-start law.
Every start in phase interval `I_g` selects exactly phase `g` of `phaseOriginal`.
The interval masses are `phaseProb`, and the selected-subset law agrees with the
finite phase law for every real sample statistic `F`.
-/

namespace AronowAudit.P027.Wave1.UniformStart

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The continuous uniform-start law agrees with the finite phase law. -/
def Target : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r), 0 < m →
    let K := (Σ _ : Fin r × Fin 2, Fin m)
    let L : ℝ := 12 * (r : ℝ)
    let left : K → ℝ := fun k =>
      ∑ a : K, if phaseIndex a < phaseIndex k then phaseSize a else 0
    let s : ℝ → K → Bool := fun u k => decide
      (∃ j : Fin m, left k ≤ u + (j : ℝ) * L ∧
        u + (j : ℝ) * L < left k + phaseSize k)
    let ν : Measure ℝ :=
      (ENNReal.ofReal L)⁻¹ • (volume.restrict (Set.Ico (0 : ℝ) L))
    IsProbabilityMeasure ν ∧
    (∀ k : K, left k = phaseStartLeft k.1 + L * (k.2 : ℝ)) ∧
    (∀ u : ℝ, u ∈ Set.Ico (0 : ℝ) L →
      ∃! g : Fin r × Fin 2,
        u ∈ Set.Ico (phaseStartLeft g)
          (phaseStartLeft g + (if g.2 = 0 then 2 else 10))) ∧
    (∀ (g : Fin r × Fin 2) (u : ℝ),
      u ∈ Set.Ico (phaseStartLeft g)
        (phaseStartLeft g + (if g.2 = 0 then 2 else 10)) →
      s u = (phaseOriginal r m hr).selected g) ∧
    (∀ g : Fin r × Fin 2,
      ν (Set.Ico (phaseStartLeft g)
        (phaseStartLeft g + (if g.2 = 0 then 2 else 10))) =
          ENNReal.ofReal (phaseProb r g)) ∧
    (∀ F : (K → Bool) → ℝ,
      Integrable (fun u => F (s u)) ν ∧
      (∫ u, F (s u) ∂ν) =
        expect (phaseOriginal r m hr)
          (fun g => F ((phaseOriginal r m hr).selected g)))

/-- Cumulative-size left endpoint `Σ_{a before k} x_a` of unit `k` (zero-based list
order `phaseIndex`). Definitionally the `left` of `Target`. -/
def unitLeft (r m : ℕ) (k : Σ _ : Fin r × Fin 2, Fin m) : ℝ :=
  ∑ a : (Σ _ : Fin r × Fin 2, Fin m), if phaseIndex a < phaseIndex k then phaseSize a else 0

/-- First-block start interval of phase `g`: `[12i, 12i+2)` (low) or
`[12i+2, 12(i+1))` (high). -/
def phaseInterval {r : ℕ} (g : Fin r × Fin 2) : Set ℝ :=
  Set.Ico (phaseStartLeft g) (phaseStartLeft g + (if g.2 = 0 then 2 else 10))

/-- Systematic selection from start `u` with spacing `12r = (Σ x)/m`.
Definitionally the `s` of `Target`. -/
def sysSel (r m : ℕ) (u : ℝ) (k : Σ _ : Fin r × Fin 2, Fin m) : Bool :=
  decide (∃ j : Fin m, unitLeft r m k ≤ u + (j : ℝ) * (12 * (r : ℝ)) ∧
    u + (j : ℝ) * (12 * (r : ℝ)) < unitLeft r m k + phaseSize k)

/-- Uniform start law on `[0, 12r)`. Definitionally the `ν` of `Target`. -/
def startMeasure (r : ℕ) : Measure ℝ :=
  (ENNReal.ofReal (12 * (r : ℝ)))⁻¹ • (volume.restrict (Set.Ico (0 : ℝ) (12 * (r : ℝ))))

/-- N1: Each full block of q units has r pairs (2,10), with total size
12r = L. In block j, the i preceding pairs have total size 12i; a high unit
has the additional preceding low size 2. Thus the cumulative left endpoint
of `((i,b),j)` is `12i + 2b + 12rj`. -/
def N1 : Prop :=
  ∀ (r m : ℕ) (k : Σ _ : Fin r × Fin 2, Fin m),
    unitLeft r m k = phaseStartLeft k.1 + 12 * (r : ℝ) * (k.2 : ℝ)

/-- N2: Over i = 0,…,r−1 the phase intervals form a disjoint partition
of `[0, 12r)`. Half-open endpoints give exact uniqueness even at a boundary:
each phase interval lies in `[0, 12r)`, and each start there lies in exactly one. -/
def N2 : Prop :=
  ∀ r : ℕ,
    (∀ g : Fin r × Fin 2, phaseInterval g ⊆ Set.Ico (0 : ℝ) (12 * (r : ℝ))) ∧
    (∀ u : ℝ, u ∈ Set.Ico (0 : ℝ) (12 * (r : ℝ)) → ∃! g : Fin r × Fin 2, u ∈ phaseInterval g)

/-- N3: For a start `u ∈ I_g`, the point u+Lj' belongs to block j',
while the interval for unit (h,j) belongs to block j. The point lies in that
unit's interval exactly when j' = j and u ∈ I_h. Disjointness of the phase
intervals then gives h = g. Thus `u + j'·12r` lies in the cumulative interval
of `(h, j)` iff `j' = j` and `h = g`. -/
def N3 : Prop :=
  ∀ (r : ℕ) (g h : Fin r × Fin 2) (u : ℝ), u ∈ phaseInterval g → ∀ (j j' : ℕ),
    (phaseStartLeft h + 12 * (r : ℝ) * (j : ℝ) ≤ u + (j' : ℝ) * (12 * (r : ℝ)) ∧
      u + (j' : ℝ) * (12 * (r : ℝ)) <
        phaseStartLeft h + 12 * (r : ℝ) * (j : ℝ) + (if h.2 = 0 then 2 else 10)) ↔
    (j' = j ∧ h = g)

/-- N4: Let ν = (ofReal L)⁻¹ · volume restricted to [0,L). Since L > 0,
ν(ℝ) = 1. Each I_g lies in [0,L) and has length 2 or 10, so
ν(I_g) = length(I_g)/L = 1/(6r) or 5/(6r). The complement of [0,L) is ν-null. -/
def N4 : Prop :=
  ∀ r : ℕ, 0 < r →
    IsProbabilityMeasure (startMeasure r) ∧
    startMeasure r (Set.Ico (0 : ℝ) (12 * (r : ℝ)))ᶜ = 0 ∧
    ∀ g : Fin r × Fin 2, startMeasure r (phaseInterval g) = ENNReal.ofReal (phaseProb r g)

/-- N5: On the conull partition, u ↦ F(s(u)) equals the finite sum
Σ_g 1_(I_g)(u) F(...). Each summand is measurable and integrable because it is
constant on a measurable finite-measure interval. More generally, a function
constant on each cell of a finite measurable partition of a conull set is
integrable, with integral `Σ_i ν(I_i) c_i`. No measurability of `f` is assumed. -/
def N5 : Prop :=
  ∀ {X ι : Type} [MeasurableSpace X] [Fintype ι] (ν : Measure X) [IsFiniteMeasure ν]
    (S : Set X), ν Sᶜ = 0 →
    ∀ (I : ι → Set X), (∀ i, MeasurableSet (I i)) → (∀ i, I i ⊆ S) →
    (∀ u ∈ S, ∃! i, u ∈ I i) →
    ∀ (f : X → ℝ) (c : ι → ℝ), (∀ i, ∀ u ∈ I i, f u = c i) →
      Integrable f ν ∧ ∫ u, f u ∂ν = ∑ i, (ν (I i)).toReal * c i

/-- The nodes suffice. The selection clause combines N1 (prefix formula), N3 (block
localisation) and the proved `phase_inclusions`; the statistic clause applies N5 to
the cells `I_g`, with N2 (partition), N4 (masses, null complement) and selection. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) : Target := by
  intro r m hr hm
  obtain ⟨hsub, huniq⟩ := h2 r
  obtain ⟨hprob, hcompl, hmass⟩ := h4 r hr
  have hsel : ∀ (g : Fin r × Fin 2) (u : ℝ), u ∈ phaseInterval g →
      sysSel r m u = (phaseOriginal r m hr).selected g := by
    intro g u hu
    funext k
    rw [(phase_inclusions r m hr).2.2.1 g k]
    unfold sysSel
    apply decide_eq_decide.mpr
    rw [h1 r m k]
    constructor
    · rintro ⟨j, hj⟩
      exact ((h3 r g k.1 u hu k.2.val j.val).1 hj).2.symm
    · intro hgk
      exact ⟨k.2, (h3 r g k.1 u hu k.2.val k.2.val).2 ⟨rfl, hgk.symm⟩⟩
  refine ⟨hprob, h1 r m, huniq, hsel, hmass, ?_⟩
  intro F
  have := hprob
  obtain ⟨hint, heq⟩ := h5 (startMeasure r) (Set.Ico (0 : ℝ) (12 * (r : ℝ))) hcompl
    phaseInterval (fun _ => measurableSet_Ico) hsub huniq
    (fun u => F (sysSel r m u)) (fun g => F ((phaseOriginal r m hr).selected g))
    (fun g u hu => by simp only [hsel g u hu])
  refine ⟨hint, heq.trans ?_⟩
  unfold expect
  apply Finset.sum_congr rfl
  intro g _
  have hp : 0 ≤ phaseProb r g := by unfold phaseProb; split <;> positivity
  rw [hmass g, ENNReal.toReal_ofReal hp]
  rfl

end
end AronowAudit.P027.Wave1.UniformStart
