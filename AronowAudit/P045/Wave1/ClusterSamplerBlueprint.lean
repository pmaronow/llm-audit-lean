import AronowAudit.P045.P045_Spillover
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Blueprint: refutation of `AronowAudit.P045.cluster_sampler_as_documented` (P045-T29)

Record: P045-T29 / `AronowAudit.P045.cluster_sampler_as_documented`; resolution `refute`.
Frozen contract (P045_Spillover.lean:4713): for every `n > 0`, every `SimpleGraph (Fin n)`
and `0 ≤ p ≤ 1`, the coded sampler's terminal centre law (singleton-number rule, `ε = 3`,
an infinite real `tsum` over trace lengths) is normalized, its centres form a 3-net with
probability one, and the treatment law is the centre-law mixture.

`Target` is the negation of exactly that contract; the `example` checks by `Iff.rfl` that it
is the negation of the frozen type. The assembly refutes the second conjunct.

Witness (paper proof, record 13): `n = 4`, `G = SimpleGraph.pathGraph 4` (edges 0-1-2-3),
`p = 1/2`. Its `edist` is `pathDistance`. The 3-nets of the four-path are exactly `{1}`,
`{2}`, `{0,3}`; every nonzero-mass terminating trace is `[1]`, `[2]`, `[3,0]` or
`0^(r+1) ++ [j]` (`j ≠ 0`, mass `(1/4)^(r+2)`). Hence the terminal masses of the three
nets are `1/4, 1/4, 1/3` (each series is summable, the `{0,3}` one geometric), and the
net probability is `5/6 ≠ 1`. The drafted `cluster_sampler_counterexample` (ends in
`sorry`) must not be used.

Node dependencies are explicit implications, so every node can be proved independently.
Writers prove `theorem nk_proof : Nk` in `AronowAudit/P045/Wave1/ClusterSampler/Nk.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.ClusterSampler

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`cluster_sampler_as_documented`. -/
def Target : Prop :=
  ¬ ∀ {n : ℕ}, 0 < n → ∀ (G : SimpleGraph (Fin n)) (p : ℝ), 0 ≤ p → p ≤ 1 →
    (∑ S : Finset (Fin n), terminalCentres G.edist 3 true S)=1 ∧
    prob (terminalCentres G.edist 3 true) (epsilonNet G.edist 3)=1 ∧
    (∀ z : Assignment n, clusteredTreatment G.edist true p z =
      ∑ S : Finset (Fin n), terminalCentres G.edist 3 true S * clusterProb G.edist S p z)

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P045.cluster_sampler_as_documented) := Iff.rfl

/-- **Node N1** (paper proof, record 13, first paragraph: "Its extended graph distance
equals |i-j|: the consecutive path gives a walk of that length, while every edge changes
the integer label by exactly one"): the four-path's graph distance is `pathDistance`.
Lemmas: `SimpleGraph.pathGraph_adj`, `SimpleGraph.edist_self`,
`SimpleGraph.edist_eq_one_iff_adj`, `SimpleGraph.edist_eq_two_iff`,
`SimpleGraph.two_lt_edist_iff`, `SimpleGraph.Walk.edist_le`, `SimpleGraph.edist_comm`. -/
def N1 : Prop :=
  ∀ i j : Fin 4, (SimpleGraph.pathGraph 4).edist i j = pathDistance i j

/-- **Node N2** (paper proof, record 13, last paragraph: "The bad sets {0,1},{0,2} ...
fail separation. The set {0,3} is separated by distance 3 and covers ... Each singleton
{1} or {2} covers all other vertices within distance 2"): the 3-nets of the four-path
under `pathDistance` are exactly `{1}`, `{2}`, `{0,3}`, so the net probability of any
centre law `T` is `T {1} + T {2} + T {0,3}`. Pure finite combinatorics (`decide`). -/
def N2 : Prop :=
  ∀ T : Finset (Fin 4) → ℝ,
    prob T (epsilonNet (pathDistance (n := 4)) 3) = T {1} + T {2} + T {0, 3}

/-- **Node N3** (paper proof, record 13, second paragraph: "Drawing 0 retries the
unchanged state"): peeling one retry. Prefixing a second `0` to a trace that starts with
`0` multiplies its mass by `1/4`: the prefix states become `∅, {0}, {0}, …`, both draws
`∅ → 0` and `{0} → 0` have probability `1/4` (`four_path_coded_draws`), and `{0}` is
nonterminal (`four_path_marking_certificate`). -/
def N3 : Prop :=
  ∀ rest : List (Fin 4),
    traceMass (pathDistance (n := 4)) 3 true (0 :: 0 :: rest) =
      1/4 * traceMass (pathDistance (n := 4)) 3 true (0 :: rest)

/-- **Node N4** (paper proof, record 13, second paragraph: "A first center 1 or 2 marks
all four vertices, giving a terminal trace [1] or [2], each of mass 1/4. A first center 3
... [3,0] terminates with mass 1/4"): the three non-retry terminating traces.
Pattern: the proof of `singleton_draw_bad_trace`. -/
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

/-- **Node N5** (paper proof, record 13, third paragraph: "every trace with nonzero mass
is exactly one of [1], [2], [3,0], or a list of r+1 copies of 0 followed by j∈{1,2,3}
... Lists with a terminal proper prefix or an impossible transition have traceMass=0"):
exhaustive classification of nonzero-mass coded traces on the four-path. Suggested route:
strong induction on the length, case on the first two entries; `N3` for the `0 :: 0 :: _`
case; a terminal proper prefix kills the `if`; from state `{3}` the coded draw of any
`j ≠ 0` is `0` (unique unmarked vertex `0`). -/
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

/-- **Node N6** (paper proof, record 13, fourth paragraph: "at t=1 only [1],[2]
contribute"): the length-`t` inner sums of `terminalCentres` at the singleton nets `{1}`
and `{2}` (the only trace with that centre set and nonzero mass is `[a]`, length one).
Route: `N5` restricts the support, `List.ofFn_injective`, `Fintype.sum_eq_single`. -/
def N6 : Prop :=
  N4 → TraceClassification → SingletonNetSums

/-- Content of node N7: the length-`t` inner sums of `terminalCentres` at `{0,3}`. -/
def PairNetSums : Prop :=
  ∀ t : ℕ,
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({0, 3} : Finset (Fin 4)) then
        traceMass (pathDistance (n := 4)) 3 true (List.ofFn z) else 0) =
      (if t = 2 then (1/4 : ℝ) else 0) + (if 2 ≤ t then (1/4 : ℝ)^t else 0)

/-- **Node N7** (paper proof, record 13, fourth paragraph: "at t=2 [3,0] and [0,j]
contribute; at every t≥3 only [0] repeated t-1 times followed by a j≠0 contributes"): the
length-`t` inner sums of `terminalCentres` at the net `{0,3}`: the trace `[3,0]` at
`t = 2`, and the retry trace `0^(t-1) ++ [3]` (mass `(1/4)^t`,
`four_path_repeat_trace_mass`) for every `t ≥ 2`. Route: `N5` restricts the support;
`Fintype.sum_eq_add` at `t = 2`, `Fintype.sum_eq_single` for `t ≥ 3`. -/
def N7 : Prop :=
  N4 → TraceClassification → PairNetSums

/-- **Node N8** (paper proof, record 13, fourth-fifth paragraphs: "The tail is bounded by
3(1/4)^t, a summable geometric sequence ... {0,3}:1/12+1/4=1/3; {1}:1/4; {2}:1/4"):
the three net masses of the terminal centre law, with the `tsum`s justified by
summability (finite support, resp. a geometric tail). Lemmas: `tsum_ite_eq`,
`Summable.tsum_add`, `Summable.sum_add_tsum_nat_add`, `summable_geometric_of_lt_one`,
`tsum_geometric_of_lt_one`. -/
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

/-- Nonvacuity record: the witness meets the contract's hypotheses (`0 < 4`,
`0 ≤ 1/2 ≤ 1`, and `pathGraph 4` is a genuine simple graph). -/
example : 0 < (4 : ℕ) ∧ (0 : ℝ) ≤ 1/2 ∧ (1/2 : ℝ) ≤ 1 := by norm_num

end

end AronowAudit.P045.Wave1.ClusterSampler
