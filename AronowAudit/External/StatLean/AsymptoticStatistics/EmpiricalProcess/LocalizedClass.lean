/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.LpSeminorm
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.PointwiseDense
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Localization foundations for the §19.2 chaining argument

The (unrestricted and localized) **difference classes**
`F − F := {f − g : f, g ∈ F}` and
`F_{δq} := {f − g : f, g ∈ F, ‖f − g‖_{L²(P)} ≤ δq}`, their elementary
membership facts, and the bracketing-entropy-integral proportionality for the
difference class (vdV Lemma 19.31).

These definitions lie below both the Donsker-via-bracketing assembly
(`DonskerBracketing.lean`) and the localized chaining bound
(`ChainingAssembly.lean`), so both modules can use them without a cyclic
dependency.

vdV §19.2 chaining localization; vdV Lemma 19.31.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Localization foundations (vdV §19.2 chaining localization)

The vdV §19.2 chaining proof of asymptotic equicontinuity localizes to the
shrinking **difference slice** `F_{δq} := {f − g : f, g ∈ F, ‖f − g‖_{L²(P)} ≤ δq}`
(the class of differences with small `L²(P)`-radius), and bounds the maximal
empirical-process oscillation over it by the bracketing-entropy integral of the
full difference class `F − F`. These definitions name those two classes and
record their elementary membership facts; the entropy wrapper at the end ties
the `F − F` entropy to `F`'s own entropy via vdV Lemma 19.31. -/

/-- The **(unrestricted) difference class** `F − F := {f − g : f, g ∈ F}`.

This is the index set of the localized empirical process in the vdV §19.2
chaining argument before the `L²`-radius restriction is imposed; its bracketing
entropy is controlled by `F`'s via vdV Lemma 19.31. The local helper
`cover_lift_difference_class` constructs the paired brackets used by
`bracketingEntropyIntegral_diff_le_class`. -/
def differenceClass (F : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  {h : Ω → ℝ | ∃ f g, f ∈ F ∧ g ∈ F ∧ h = fun x => f x - g x}

omit [MeasurableSpace Ω] in
/-- **Envelope of the difference class.** If `Φ` is an envelope for `F`
(`|f x| ≤ Φ x` for every `f ∈ F`), then `2Φ` is an envelope for the difference
class `differenceClass F = {f − g : f, g ∈ F}`: for `h = f − g`,
`|h x| = |f x − g x| ≤ |f x| + |g x| ≤ Φ x + Φ x = 2 Φ x` (`abs_sub`). -/
lemma isEnvelope_differenceClass_two {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    (hΦ : IsEnvelope F Φ) : IsEnvelope (differenceClass F) (fun x => 2 * Φ x) := by
  rintro h ⟨f, g, hf, hg, rfl⟩ x
  calc |f x - g x| ≤ |f x| + |g x| := abs_sub (f x) (g x)
    _ ≤ Φ x + Φ x := by gcongr <;> [exact hΦ f hf x; exact hΦ g hg x]
    _ = 2 * Φ x := by ring

/-- The **localized difference class** `F_{δq} := {f − g : f, g ∈ F,
‖f − g‖_{L²(P)} ≤ δq}` — the differences `f − g` of class members whose
`L²(P)`-radius is at most `δq`.

This is the shrinking slice the vdV §19.2 chaining argument localizes to:
the bad event `{‖fhat n − ghat n‖_{L²(P)} > δq}` is pushed to `μ`-measure 0 by
the `L²`-consistency hypothesis, and on its complement the random pair
`(fhat n ξ − ghat n ξ)` lands in `localizedDifferenceClass F P δq`, where the
maximal-inequality bound applies. -/
def localizedDifferenceClass (F : Set (Ω → ℝ)) (P : Measure Ω) (δq : ℝ) :
    Set (Ω → ℝ) :=
  {h : Ω → ℝ | ∃ f ∈ F, ∃ g ∈ F,
      h = (fun x => f x - g x) ∧ eLpNorm' h 2 P ≤ ENNReal.ofReal δq}

/-- **L1 (membership ⇒ radius bound).** Every `h ∈ localizedDifferenceClass F P δq`
has `L²(P)`-radius at most `δq`. Immediate from the radius conjunct of the
membership predicate. -/
lemma localizedDifferenceClass_hF_L2 {F : Set (Ω → ℝ)} {P : Measure Ω} {δq : ℝ}
    {h : Ω → ℝ} (hh : h ∈ localizedDifferenceClass F P δq) :
    eLpNorm' h 2 P ≤ ENNReal.ofReal δq := by
  obtain ⟨_f, _hf, _g, _hg, _heq, hradius⟩ := hh
  exact hradius

/-- **L1′ (localized slice ⊆ full difference class).** Forgetting the radius
restriction lands in `differenceClass F`. The cover-lift / entropy bounds are
stated for `differenceClass F`, so the localized slice inherits them by
monotonicity (`bracketingEntropyIntegral_mono_class`). -/
lemma localizedDifferenceClass_subset {F : Set (Ω → ℝ)} {P : Measure Ω} {δq : ℝ} :
    localizedDifferenceClass F P δq ⊆ differenceClass F := by
  rintro h ⟨f, hf, g, hg, heq, _⟩
  exact ⟨f, g, hf, hg, heq⟩

/-- **L2 (`eLpNorm`-form membership).** A difference `f − g` of class members
whose `L²(P)`-radius is `≤ δq` lies in `localizedDifferenceClass F P δq`. This is
the def-native form (matching the `eLpNorm` radius spelling used by the bracket
lemmas, e.g. `chain_head_dyadic_bound`'s `hF_L2`). -/
lemma mem_localizedDifferenceClass {F : Set (Ω → ℝ)} {P : Measure Ω} {δq : ℝ}
    {f g : Ω → ℝ} (hf : f ∈ F) (hg : g ∈ F)
    (hradius : eLpNorm' (fun x => f x - g x) 2 P ≤ ENNReal.ofReal δq) :
    (fun x => f x - g x) ∈ localizedDifferenceClass F P δq :=
  ⟨f, hf, g, hg, rfl, hradius⟩


/-- **vdV Lemma 19.31, raw-cover-data core**.

The size-`k → k²` cover-lifting map: a concrete size-`k` `(η/2)`-bracketing
cover of `F` (raw `Fin k`-indexed data, **not** the size-quantified
`HasFiniteBracketingCover` predicate) is lifted to a concrete size-`k * k`
`η`-bracketing cover of the difference class `differenceClass F`, via the
pairing `[l_i - u_j, u_i - l_j]` indexed by `Fin (k * k)` through
`finProdFinEquiv`.

This raw-data form is exactly the `hlift` hypothesis of
`bracketingEntropyIntegral_diff_le` (`Bracketing.lean`), which feeds the lift the
*minimal* cover at each scale and reads off the size-`k²` output to bound the
bracketing number; the size `k * k` must therefore be preserved syntactically
(the `HasFiniteBracketingCover` predicate would hide it behind an existential). -/
private lemma cover_lift_difference_class
    {F : Set (Ω → ℝ)} {P : Measure Ω} {η : ℝ} (hη : 0 < η) (k : ℕ)
    (h : ∃ l u : Fin k → Ω → ℝ,
        (∀ i, IsEpsBracket (η / 2) (l i) (u i) 2 P) ∧
        (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)) :
    ∃ l u : Fin (k * k) → Ω → ℝ,
        (∀ i, IsEpsBracket η (l i) (u i) 2 P) ∧
        (∀ hd ∈ differenceClass F, ∃ i, ∀ x, l i x ≤ hd x ∧ hd x ≤ u i x) := by
  -- vdV Lemma 19.31. Pair the `(η/2)`-brackets of `F` into `η`-brackets of
  -- `F - F` via `[l_i - u_j, u_i - l_j]`, indexed by `Fin (k * k)` through
  -- `finProdFinEquiv`. Algebra: `(u_i - l_j) - (l_i - u_j) =
  -- (u_i - l_i) + (u_j - l_j)`; triangle in L² gives the η bound.
  obtain ⟨l, u, hbr, hcov⟩ := h
  have hη2 : (0 : ℝ) ≤ η / 2 := by linarith
  refine ⟨
    fun ij x => l (finProdFinEquiv.symm ij).1 x - u (finProdFinEquiv.symm ij).2 x,
    fun ij x => u (finProdFinEquiv.symm ij).1 x - l (finProdFinEquiv.symm ij).2 x,
    ?_, ?_⟩
  · -- each pair `[l i - u j, u i - l j]` is an η-bracket in L²(P)
    intro ij
    set p := finProdFinEquiv.symm ij
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      have h1 := (hbr p.1).isBracket x
      have h2 := (hbr p.2).isBracket x
      linarith
    · exact (hbr p.1).measurable_lower.sub (hbr p.2).measurable_upper
    · exact (hbr p.1).measurable_upper.sub (hbr p.2).measurable_lower
    · exact (hbr p.1).memLp_lower.sub (hbr p.2).memLp_upper
    · exact (hbr p.1).memLp_upper.sub (hbr p.2).memLp_lower
    · -- size bound: triangle + the two (η/2)-bracket bounds
      have hexpand :
          (fun x => (u p.1 x - l p.2 x) - (l p.1 x - u p.2 x)) =
          (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) := by
        funext x; ring
      rw [hexpand]
      have hmeas1 : AEStronglyMeasurable (fun x => u p.1 x - l p.1 x) P :=
        ((hbr p.1).memLp_upper.sub (hbr p.1).memLp_lower).aestronglyMeasurable
      have hmeas2 : AEStronglyMeasurable (fun x => u p.2 x - l p.2 x) P :=
        ((hbr p.2).memLp_upper.sub (hbr p.2).memLp_lower).aestronglyMeasurable
      have htri : eLpNorm (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) 2 P ≤
          eLpNorm (fun x => u p.1 x - l p.1 x) 2 P +
            eLpNorm (fun x => u p.2 x - l p.2 x) 2 P :=
        eLpNorm_add_le  one_le_two
      have hi : eLpNorm (fun x => u p.1 x - l p.1 x) 2 P < ENNReal.ofReal (η / 2) :=
        (hbr p.1).size_lt
      have hj : eLpNorm (fun x => u p.2 x - l p.2 x) 2 P < ENNReal.ofReal (η / 2) :=
        (hbr p.2).size_lt
      have hsum :
          ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add hη2 hη2]
        congr 1; ring
      calc eLpNorm (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) 2 P
          ≤ eLpNorm (fun x => u p.1 x - l p.1 x) 2 P +
              eLpNorm (fun x => u p.2 x - l p.2 x) 2 P := htri
        _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := ENNReal.add_lt_add hi hj
        _ = ENNReal.ofReal η := hsum
  · -- cover: every `hd = f - g` lies in some bracket `[l i - u j, u i - l j]`
    rintro hd ⟨f, g, hf, hg, h_eq⟩
    obtain ⟨i, hfi⟩ := hcov f hf
    obtain ⟨j, hgj⟩ := hcov g hg
    refine ⟨finProdFinEquiv (i, j), fun x => ?_⟩
    simp only [Equiv.symm_apply_apply, h_eq]
    refine ⟨?_, ?_⟩
    · have h1 := (hfi x).1
      have h2 := (hgj x).2
      linarith
    · have h1 := (hfi x).2
      have h2 := (hgj x).1
      linarith


/-- **L4 wrapper: entropy-integral proportionality for the difference class.**

Instantiates the abstract `bracketingEntropyIntegral_diff_le` (`Bracketing.lean`)
at the concrete difference class `G = differenceClass F`, supplying the
cover-lifting hypothesis from `cover_lift_difference_class` (vdV Lemma 19.31's
raw `k → k²` map). Conclusion:
`J_{[]}(δ, F − F, L²(P)) ≤ 2√2 · J_{[]}(δ, F, L²(P))`.

The `2√2` factor decomposes as `√2` (cost of squaring the count, vdV Lemma 19.31
`N(η, F−F) ≤ N(η/2, F)²`) times `2` (the Jacobian of the `ε ↦ ε/2` scale change
folded into the entropy integral). The hypothesis `hcover` (`F` has a finite
`(ε/2)`-bracketing cover at every scale) is the genuine class input; under
`bracketingEntropyIntegral 1 F P < ⊤` it is discharged at the needed scales by
`hasFiniteBracketingCover_of_entropyIntegral_lt_top` (`Bracketing.lean`), so the
downstream localization consumer supplies it from `h_int`, not as a standing
hypothesis. -/
lemma bracketingEntropyIntegral_diff_le_class
    {F : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F (ε / 2) 2 P) :
    bracketingEntropyIntegral δ (differenceClass F) P
      ≤ ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δ F P :=
  bracketingEntropyIntegral_diff_le hδ hcover
    (fun _ε hε k hk => cover_lift_difference_class hε k hk)

/-! ## Pointwise-density closure of the difference class (S6)

This reusable closure remains available to consumers that need VW pointwise density.
The finite-entropy localized chaining bounds derive the measurability they use directly
from class-member measurability and therefore carry no pointwise-density hypothesis. -/


end AsymptoticStatistics.EmpiricalProcess
