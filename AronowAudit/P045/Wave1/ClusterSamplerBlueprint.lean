import AronowAudit.P045.P045_Spillover
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# P045-T29: a counterexample to the cluster-sampler law

The proposition says that for every `n > 0`, every `SimpleGraph (Fin n)`, and
`0 ≤ p ≤ 1`, the coded sampler's terminal centre law (singleton-number rule,
`ε = 3`, an infinite real `tsum` over trace lengths) is normalized, its centres
form a 3-net with probability one, and the treatment law is the centre-law mixture.
`Target` is its negation; the counterexample concerns the second conjunct.

Take `n = 4`, `G = SimpleGraph.pathGraph 4` (edges 0-1-2-3), and `p = 1/2`.
Its extended distance is `pathDistance`. The 3-nets are exactly `{1}`, `{2}`, `{0,3}`.
Every nonzero-mass terminating trace is `[1]`, `[2]`, `[3,0]`, or
`0^(r+1) ++ [j]` (`j ≠ 0`, mass `(1/4)^(r+2)`). The terminal masses of the three
nets are `1/4, 1/4, 1/3`, respectively. The series are summable, with a geometric
series for `{0,3}`, and the net probability is `5/6 ≠ 1`.

The propositions below express the distance, trace, and summation identities,
with dependencies as hypotheses.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- The negation of the documented cluster-sampler proposition. -/
def Target : Prop :=
  ¬ ∀ {n : ℕ}, 0 < n → ∀ (G : SimpleGraph (Fin n)) (p : ℝ), 0 ≤ p → p ≤ 1 →
    (∑ S : Finset (Fin n), terminalCentres G.edist 3 true S)=1 ∧
    prob (terminalCentres G.edist 3 true) (epsilonNet G.edist 3)=1 ∧
    (∀ z : Assignment n, clusteredTreatment G.edist true p z =
      ∑ S : Finset (Fin n), terminalCentres G.edist 3 true S * clusterProb G.edist S p z)

/-- The four-path's extended graph distance is `pathDistance`: the consecutive path
gives a walk of length |i-j|, while every edge changes the integer label by exactly one. -/
def N1 : Prop :=
  ∀ i j : Fin 4, (SimpleGraph.pathGraph 4).edist i j = pathDistance i j

/-- The 3-nets of the four-path under `pathDistance` are exactly `{1}`, `{2}`, `{0,3}`.
The bad sets `{0,1}` and `{0,2}` fail separation. The set `{0,3}` is separated by
distance 3 and covers; each singleton `{1}` or `{2}` covers every other vertex
within distance 2. Thus the net probability of any centre law `T` is
`T {1} + T {2} + T {0,3}`. -/
def N2 : Prop :=
  ∀ T : Finset (Fin 4) → ℝ,
    prob T (epsilonNet (pathDistance (n := 4)) 3) = T {1} + T {2} + T {0, 3}

/-- Prefixing a second `0` to a trace that starts with `0` multiplies its mass by `1/4`.
The prefix states become `∅, {0}, {0}, …`; both draws `∅ → 0` and `{0} → 0` have
probability `1/4` (`four_path_coded_draws`), and `{0}` is nonterminal
(`four_path_marking_certificate`). -/
def N3 : Prop :=
  ∀ rest : List (Fin 4),
    traceMass (pathDistance (n := 4)) 3 true (0 :: 0 :: rest) =
      1/4 * traceMass (pathDistance (n := 4)) 3 true (0 :: rest)

/-- The three non-retry terminating traces are `[1]`, `[2]`, and `[3,0]`, each with
mass `1/4`. A first centre 1 or 2 marks all four vertices; a first centre 3 is
followed by 0. The finite calculation is analogous to `singleton_draw_bad_trace`. -/
def N4 : Prop :=
  traceMass (pathDistance (n := 4)) 3 true [1] = 1/4 ∧
    traceMass (pathDistance (n := 4)) 3 true [2] = 1/4 ∧
    traceMass (pathDistance (n := 4)) 3 true [3, 0] = 1/4

/-- Content of node N5: every nonzero-mass coded trace on the four-path is `[1]`, `[2]`,
`[3,0]` or a retry trace `0^(r+1) ++ [j]` with `j ≠ 0`. -/
def TraceClassification : Prop :=
  ∀ cs : List (Fin 4), traceMass (pathDistance (n := 4)) 3 true cs ≠ 0 →
    cs = [1] ∨ cs = [2] ∨ cs = [3, 0] ∨
      ∃ r : ℕ, ∃ j : Fin 4, j ≠ 0 ∧ cs = List.replicate (r+1) 0 ++ [j]

/-- Exhaustive classification of nonzero-mass coded traces on the four-path.
A terminal proper prefix or an impossible transition gives zero mass. Strong induction
on length splits by the first two entries, with N3 for `0 :: 0 :: _`. From state `{3}`,
only vertex `0` has nonzero draw probability. -/
def N5 : Prop :=
  N3 → TraceClassification

/-- Content of node N6: the length-`t` inner sums of `terminalCentres` at `{1}` and `{2}`. -/
def SingletonNetSums : Prop :=
  ∀ t : ℕ,
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({1} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) =
        (if t = 1 then (1/4 : ℝ) else 0) ∧
      (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({2} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) =
        (if t = 1 then (1/4 : ℝ) else 0)

/-- The length-`t` inner sums of `terminalCentres` at the singleton nets `{1}` and `{2}`.
The only trace with centre set `{a}` and nonzero mass is `[a]`, of length one.
N5 restricts the support of the finite sum. -/
def N6 : Prop :=
  N4 → TraceClassification → SingletonNetSums

/-- Content of node N7: the length-`t` inner sums of `terminalCentres` at `{0,3}`. -/
def PairNetSums : Prop :=
  ∀ t : ℕ,
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({0, 3} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) =
      (if t = 2 then (1/4 : ℝ) else 0) + (if 2 ≤ t then (1/4 : ℝ)^t else 0)

/-- The length-`t` inner sums of `terminalCentres` at the net `{0,3}`.
The contributions are `[3,0]` at `t = 2`, and the retry trace `0^(t-1) ++ [3]`
with mass `(1/4)^t` for every `t ≥ 2` (`four_path_repeat_trace_mass`).
N5 restricts the support of the finite sum. -/
def N7 : Prop :=
  N4 → TraceClassification → PairNetSums

/-- The three net masses of the terminal centre law. The singleton series have finite
support; the `{0,3}` series has a summable geometric tail, giving
`{0,3}: 1/12 + 1/4 = 1/3`, `{1}: 1/4`, and `{2}: 1/4`. -/
def N8 : Prop :=
  SingletonNetSums → PairNetSums →
    terminalCentres (pathDistance (n := 4)) 3 true {1} = 1/4 ∧
      terminalCentres (pathDistance (n := 4)) 3 true {2} = 1/4 ∧
      terminalCentres (pathDistance (n := 4)) 3 true {0, 3} = 1/3

/-- The nodes suffice: at the four-path the second conjunct would give
`1/4 + 1/4 + 1/3 = 1`. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) : Target := by
  intro h
  have key := (h (n := 4) (by norm_num) (SimpleGraph.pathGraph 4) (1/2) (by norm_num)
    (by norm_num)).2.1
  have hd : (SimpleGraph.pathGraph 4).edist = pathDistance :=
    funext fun i => funext fun j => h1 i j
  rw [hd, h2] at key
  have hc : TraceClassification := h5 h3
  obtain ⟨e1, e2, e3⟩ := h8 (h6 h4 hc) (h7 h4 hc)
  rw [e1, e2, e3] at key
  norm_num at key

end

end AronowAudit.P045.Wave1.ClusterSampler
