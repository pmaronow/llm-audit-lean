/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Function classes for empirical-process theory

`IsEnvelope F G` says that `|f x| ≤ G x` for every `f ∈ F` and every `x`.
`IsEnvelope.mono` restricts this bound to a subclass.

`supNormOver F z` is the supremum of `ENNReal.ofReal |z f|` over `f ∈ F`,
valued in `[0, ∞]`. The empty class gives zero. `le_supNormOver` bounds each
member's absolute value by this supremum.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Chapter 19.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open scoped ENNReal

variable {Ω : Type*}

/-- A function `G : Ω → ℝ` is an **envelope** for a class `F` if
`|f x| ≤ G x` for every `f ∈ F` and every `x ∈ Ω`.

The envelope's role is to control the tail behaviour of the empirical
process: vdV §19.2 + Lem 19.34 use `G ∈ L^2(P)` (or similar) as a
hypothesis for Donsker-class results.

vdV §19.2: `G_n`'s sample paths are uniformly bounded when `F` has an
integrable envelope; envelope-driven tail conditions appear throughout §19. -/
def IsEnvelope (F : Set (Ω → ℝ)) (G : Ω → ℝ) : Prop :=
  ∀ f ∈ F, ∀ x, |f x| ≤ G x


lemma IsEnvelope.mono {F F' : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hG : IsEnvelope F G) (hF' : F' ⊆ F) : IsEnvelope F' G :=
  fun f hf x => hG f (hF' hf) x

/-- The **sup-norm** `‖z‖_F = sup_{f ∈ F} |z f|` of an evaluator
`z : (Ω → ℝ) → ℝ` over a class `F`, measured in `ℝ≥0∞` to handle
the unbounded case cleanly.

Edge: `F = ∅ ⇒ 0` (the supremum over an empty index is `⊥ = 0` in
`ℝ≥0∞`).

Used to state the `‖P_n − P‖_F` form of Glivenko–Cantelli conclusions
and the asymptotic-tightness side of Donsker's theorem. -/
noncomputable def supNormOver (F : Set (Ω → ℝ)) (z : (Ω → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ F, ENNReal.ofReal |z f|

lemma le_supNormOver {F : Set (Ω → ℝ)} {z : (Ω → ℝ) → ℝ}
    {f : Ω → ℝ} (hf : f ∈ F) :
    ENNReal.ofReal |z f| ≤ supNormOver F z :=
  le_iSup₂ (f := fun f _ => ENNReal.ofReal |z f|) f hf


end AsymptoticStatistics.EmpiricalProcess
