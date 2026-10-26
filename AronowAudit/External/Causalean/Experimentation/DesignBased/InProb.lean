/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Convergence in probability for finite randomization designs

A lightweight convergence-in-probability layer for the finite-design probability model, used to
analyze ratio (Hájek) estimators.  Along a sequence of designs `D m : FiniteDesign (Ω m)`, a
sequence of statistics `X m : Ω m → ℝ` converges in probability to a target sequence `c : ℕ → ℝ`
(`TendstoInProb D X c`) if the tail probabilities `Pr(|X m − c m| ≥ ε)` vanish for every `ε > 0`.

The substrate provides:
* `tendstoInProb_of_var` — the Chebyshev consistency engine: if the design variance of `X m`
  vanishes, then `X m → E[X m]` in probability;
* `TendstoInProb.sub` — closure under differences.
-/

module
public import AronowAudit.External.Causalean.Experimentation.DesignBased.Risk
public import AronowAudit.External.Causalean.Stat.FiniteDesign.Chebyshev
public import AronowAudit.External.Causalean.Stat.FiniteDesign.FiniteDesignMeasure
public import AronowAudit.External.Causalean.Stat.Limit.StochasticOrder
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Convergence in probability for finite designs

Finite-design convergence in probability tracks vanishing assignment-tail probabilities along a
sequence of randomization designs.

The predicate `FiniteDesign.TendstoInProb` states convergence of statistics `X m` to targets `c m`
using the design probabilities of absolute-deviation events. The theorem `tendstoInProb_of_var`
turns vanishing randomization variance into convergence to the design mean via Chebyshev's
inequality. The closure results `TendstoInProb.sub` and `TendstoInProb.add` handle differences
and sums.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]

/-- For [a sequence of finite assignment spaces](hyp:Ω), [a sequence of finite randomization
designs](hyp:D), [a sequence of real-valued statistics](hyp:X), and [a sequence of real-valued
targets](hyp:c), the [assertion of convergence in probability](goal) means that, for every positive
$\varepsilon$, the probability that the statistic differs from its target by at least
$\varepsilon$ tends to zero as the sequence index tends to infinity. -/
def TendstoInProb (D : ∀ m, FiniteDesign (Ω m)) (X : ∀ m, Ω m → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun m => (D m).Pr (fun z => ε ≤ |X m z - c m|)) atTop (𝓝 0)


/-- Under [a sequence of finite-design laws](hyp:D), if [a deterministic real sequence](hyp:a)
[converges to a constant](hyp:c,ha), then [the corresponding constant-on-assignment statistics
converge in finite-design probability](goal). -/
theorem deterministic_tendstoInProb (D : ∀ n, FiniteDesign (Ω n)) (a : ℕ → ℝ) (c : ℝ)
    (ha : Tendsto a atTop (𝓝 c)) :
    TendstoInProb D (fun n _ => a n) (fun _ => c) := by
  intro ε hε
  have hev : ∀ᶠ n in atTop, |a n - c| < ε := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 ha ε hε)
  apply tendsto_order.2
  constructor
  · intro u hu
    filter_upwards [] with n
    exact hu.trans_le ((D n).Pr_nonneg _)
  · intro u hu
    filter_upwards [hev] with n hn
    have hz : (D n).Pr (fun _ => ε ≤ |a n - c|) = 0 := by
      unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
      simp [not_le.mpr hn]
    rw [hz]
    exact hu


/-- **Chebyshev consistency engine.** Along [a sequence of finite designs `D`](hyp:D), for
[statistics `X`](hyp:X), if [the design variance of `X m` tends to zero as `m → ∞`](hyp:hvar), then
[`X m` converges in probability to its design mean `E[X m]`](goal). -/
theorem tendstoInProb_of_var (D : ∀ m, FiniteDesign (Ω m)) (X : ∀ m, Ω m → ℝ)
    (hvar : Tendsto (fun m => (D m).Var (X m)) atTop (𝓝 0)) :
    TendstoInProb D X (fun m => (D m).E (X m)) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hupper : Tendsto (fun m => (D m).Var (X m) / ε ^ 2) atTop (𝓝 0) := by
    simpa using hvar.div_const (ε ^ 2)
  refine squeeze_zero (fun m => ?_) (fun m => ?_) hupper
  · exact (D m).Pr_nonneg _
  · exact (D m).chebyshev (X m) hε

/-- Union bound for two events: `Pr(P ∨ Q) ≤ Pr P + Pr Q`. -/
lemma Pr_or_le {Ω' : Type*} [Fintype Ω'] (D : FiniteDesign Ω') (P Q : Ω' → Prop)
    [DecidablePred P] [DecidablePred Q] :
    D.Pr (fun z => P z ∨ Q z) ≤ D.Pr P + D.Pr Q := by
  unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (D.p_nonneg z)
  by_cases hP : P z <;> by_cases hQ : Q z <;> simp [hP, hQ]

/-- Along a sequence of finite designs, if [the statistics `X m` converge in probability to
`a m`](hyp:hX) and [the statistics `Y m` converge in probability to `b m`](hyp:hY), then [the
difference `X m − Y m` converges in probability to `a m − b m`](goal): convergence in probability
is closed under differences. -/
theorem TendstoInProb.sub {D : ∀ m, FiniteDesign (Ω m)} {X Y : ∀ m, Ω m → ℝ} {a b : ℕ → ℝ}
    (hX : TendstoInProb D X a) (hY : TendstoInProb D Y b) :
    TendstoInProb D (fun m z => X m z - Y m z) (fun m => a m - b m) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- The combined tail bound: split each event into the two half-deviation events.
  have hbound : ∀ m,
      (D m).Pr (fun z => ε ≤ |(X m z - Y m z) - (a m - b m)|)
        ≤ (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
          + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|) := by
    intro m
    have hmono : (D m).Pr (fun z => ε ≤ |(X m z - Y m z) - (a m - b m)|)
        ≤ (D m).Pr (fun z => (ε / 2 ≤ |X m z - a m|) ∨ (ε / 2 ≤ |Y m z - b m|)) := by
      apply (D m).Pr_mono
      intro z hz
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      have htri : |(X m z - Y m z) - (a m - b m)| ≤ |X m z - a m| + |Y m z - b m| := by
        have : (X m z - Y m z) - (a m - b m) = (X m z - a m) - (Y m z - b m) := by ring
        rw [this]
        exact abs_sub _ _
      linarith
    exact le_trans hmono (Pr_or_le (D m) _ _)
  have hupper : Tendsto
      (fun m => (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
        + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|)) atTop (𝓝 0) := by
    have := (hX (ε / 2) hε2).add (hY (ε / 2) hε2)
    simpa using this
  refine squeeze_zero (fun m => (D m).Pr_nonneg _) hbound hupper

/-- Convergence in probability is closed under sums. -/
theorem TendstoInProb.add {D : ∀ m, FiniteDesign (Ω m)} {X Y : ∀ m, Ω m → ℝ} {a b : ℕ → ℝ}
    (hX : TendstoInProb D X a) (hY : TendstoInProb D Y b) :
    TendstoInProb D (fun m z => X m z + Y m z) (fun m => a m + b m) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hbound : ∀ m,
      (D m).Pr (fun z => ε ≤ |(X m z + Y m z) - (a m + b m)|)
        ≤ (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
          + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|) := by
    intro m
    have hmono : (D m).Pr (fun z => ε ≤ |(X m z + Y m z) - (a m + b m)|)
        ≤ (D m).Pr (fun z => (ε / 2 ≤ |X m z - a m|) ∨ (ε / 2 ≤ |Y m z - b m|)) := by
      apply (D m).Pr_mono
      intro z hz
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      have htri : |(X m z + Y m z) - (a m + b m)| ≤ |X m z - a m| + |Y m z - b m| := by
        have : (X m z + Y m z) - (a m + b m) = (X m z - a m) + (Y m z - b m) := by ring
        rw [this]
        exact abs_add_le _ _
      linarith
    exact le_trans hmono (Pr_or_le (D m) _ _)
  have hupper : Tendsto
      (fun m => (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
        + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|)) atTop (𝓝 0) := by
    have := (hX (ε / 2) hε2).add (hY (ε / 2) hε2)
    simpa using this
  refine squeeze_zero (fun m => (D m).Pr_nonneg _) hbound hupper


end FiniteDesign
end DesignBased
end Experimentation
end Causalean
