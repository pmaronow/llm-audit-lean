import Mathlib
import SAP.P016b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators Classical
open MeasureTheory
noncomputable section

/-- P016-T12; p. 397 (PDF p. 3), first paragraph, second and third sentences.
The mean contrast is effect increasing on nonempty groups, whereas both KS
statistics fail this directional condition. Every statistic calibrated under a
positive finite assignment law has valid inclusive upper, lower, and doubled
minimum tails, at weak and strict cutoffs. For the uniform two-of-four design
and outcomes (0,1,2,3), the KS scores are (1,1/2,1/2,1/2,1/2,1), the upper
p values are (1/3,1,1,1,1,1/3), and the rejection probabilities are 0, 1/3,
and 1 on the stated threshold ranges. -/
def T12WholeStatement : Prop :=
  (∀ n : ℕ, EffectIncreasingOnGroups (meanDifference (n := n))) ∧
  (¬ EffectIncreasingOnGroups (ks (n := 4)) ∧
   ¬ EffectIncreasingOnGroups (signedKS (n := 4))) ∧
  ExactValidity ∧
  (∀ k : Fin 6, ks u4 (complete4 k) =
    (![1,1/2,1/2,1/2,1/2,1] : Fin 6 → ℝ) k) ∧
  (∀ k : Fin 6,
    upperP (uniformLaw (Fin 6)) (fun j => ks u4 (complete4 j)) k =
      (![1/3,1,1,1,1,1/3] : Fin 6 → ℝ) k) ∧
  (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    mass (uniformLaw (Fin 6)) (fun k => upperP (uniformLaw (Fin 6))
      (fun j => ks u4 (complete4 j)) k ≤ α) =
      if α < 1/3 then 0 else if α < 1 then 1/3 else 1)

/-- Tie-free exchangeable ranks and raw weak-cutoff size, for every nonnegative
threshold whose two integer rank tails are disjoint, including admissible
thresholds at or above one. Positive B is the empirical-tail denominator domain. -/
def NoTiesWholeLaw : Prop :=
  ∀ (B : ℕ), 0 < B → ∀ (μ : Measure (ReferenceVector B)) [IsProbabilityMeasure μ],
    Exchangeable μ → (∀ᵐ t ∂μ, Function.Injective t) →
    ∀ (α : ℝ), 0 ≤ α → ∀ (c : ℕ), c = Nat.floor (α*B/2) → 2*c < B →
      (∀ k : Fin (B+1), μ.real {t | (∑ b : Fin B,
        if t b.succ < t 0 then (1 : ℕ) else 0) = k.val} = 1/(B+1)) ∧
      (∀ᵐ t ∂μ, lowerCount (fun b => t b.succ) (t 0) =
        (∑ b : Fin B, if t b.succ < t 0 then (1 : ℕ) else 0) ∧
        upperCount (fun b => t b.succ) (t 0) = B-lowerCount (fun b => t b.succ) (t 0)) ∧
      μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ α} = 2*(c+1)/(B+1)

/-- Each attained SSR value of the balanced power-of-two design has exactly
two assignments in its fiber; PowerTwoDesign identifies them as complements. -/
def PowerTwoMultiplicity : Prop :=
  let y : Outcome 16 := fun i => (2 : ℝ)^i.val
  ∀ v ∈ Finset.univ.image (fun z : Balanced 16 8 => rss y z.val),
    (Finset.univ.filter (fun z : Balanced 16 8 => rss y z.val = v)).card = 2

/-- The archived weak .05 cutoff has the stated mixture probability at every
positive reference count, with natural division B/40 as its integer cutoff. -/
def PowerTwoWeakAll : Prop :=
  let y : Outcome 16 := fun i => (2 : ℝ)^i.val
  ∀ B : ℕ, 0 < B →
    uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
      rawP (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) ≤ 1/20) =
      binomialMixture 6435 B (B/40)

/-- Exact open rational intervals certify every printed decimal prefix of the
finite-design probabilities. The endpoints are consecutive decimals at the
precision displayed, rather than equalities to terminating decimal numbers. -/
def PowerTwoDecimalValues : Prop :=
  (0.051792651792 < binomialMixture 6435 1000 25 ∧
    binomialMixture 6435 1000 25 < 0.051792651793) ∧
  (0.050039580346 < binomialMixture 6435 10000 250 ∧
    binomialMixture 6435 10000 250 < 0.050039580347) ∧
  (0.049794649794 < binomialMixture 6435 1000 24 ∧
    binomialMixture 6435 1000 24 < 0.049794649795) ∧
  (0.049839600344 < binomialMixture 6435 10000 249 ∧
    binomialMixture 6435 10000 249 < 0.049839600345) ∧
  (0.001846625 < binomialMixture 6435 1000 0 ∧
    binomialMixture 6435 1000 0 < 0.001846626)

/-- P016-T13; p. 400 (PDF p. 6), Section 2.2, and p. 397 (PDF p. 3),
validity parenthesis; archived simulation weak-cutoff rule.
Tie-free exchangeable scores have uniform ranks and raw weak-cutoff rejection
probability 2(c+1)/(B+1) whenever c=floor(alpha B/2) and 2c<B. At .05 the
sizes for B=1000 and 10000 exceed .05. In the uniform eight-of-sixteen design
with fixed outcomes 2^i, the SSR has the stated moment formula and 6435 values,
each on a complementary pair. Independent uniform observed and reference draws
give the exact binomial-mixture rejection laws and bounds, including every
positive B for the weak .05 rule. All five reported decimal prefixes are
certified by open rational intervals. The strict .05 sizes are below .05,
and raw p=0 has the stated positive power-sum probability. These witnesses
concern the archived weak cutoff; they do not refute the printed strict rule. -/
def T13WholeStatement : Prop :=
  NoTiesWholeLaw ∧
  (∀ (μ : Measure (ReferenceVector 1000)) [IsProbabilityMeasure μ],
    Exchangeable μ → (∀ᵐ t ∂μ, Function.Injective t) →
      μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20} = 4/77 ∧
      1/20 < μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20}) ∧
  (∀ (μ : Measure (ReferenceVector 10000)) [IsProbabilityMeasure μ],
    Exchangeable μ → (∀ᵐ t ∂μ, Function.Injective t) →
      μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20} = 502/10001 ∧
      1/20 < μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20}) ∧
  PowerTwoDesign ∧ PowerTwoMultiplicity ∧ PowerTwoSampled ∧ PowerTwoWeakAll ∧
  (52/1001 : ℝ) = 4/77 ∧
  (4/77 : ℝ)-2/6435 = 2326/45045 ∧ (1/20 : ℝ) < 2326/45045 ∧
  PowerTwoDecimalValues

/-- P016-T16; p. 398 (PDF p. 4), last paragraph; footnote 3, p. 396
(PDF p. 2); p. 400 (PDF p. 6), Section 2.2, first paragraph.
Under additive and nonzero multiplicative hypotheses, control outcomes and
control empirical distributions stay fixed. Treated outcomes have the stated
parameter dependence, with nonzero response for the multiplicative comparison.
The sample ECDF counts observations at or below its argument. Empirical
distributions are asserted on their nonempty-sample domains. The joint family
with separate parameter indices contains the truth (1/2,2), which belongs to
no member of the printed diagonal family. -/
def T16WholeStatement : Prop := T16Statement

end
end SAP.P016b
