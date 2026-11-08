import SAP.P044.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

noncomputable section

def T9Statement : Prop :=
  (∀ {N : ℕ} (y : Fin N → Assignment N → ℝ),
    Interference y ↔ ¬NoInterference y) ∧
  (∀ {N : ℕ} (y : Fin N → Assignment N → ℝ),
    NoInterference y ↔ ∀ i z z', z i = z' i → y i z = y i z') ∧
  (∀ {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N),
    peerCount A z i = (Finset.univ.filter (fun j => A i j = true ∧ z j = true)).card) ∧
  (∀ {N : ℕ} (A : Adjacency N) (i : Fin N)
    (hdiag : A i i = false) (z z' : Assignment N)
    (hother : ∀ j, j ≠ i → z j = z' j),
    peerCount A z i = peerCount A z' i) ∧
  (∀ {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N),
    (exposure A z i = .d11 ↔ z i = true ∧ 0 < peerCount A z i) ∧
    (exposure A z i = .d10 ↔ z i = true ∧ peerCount A z i = 0) ∧
    (exposure A z i = .d01 ↔ z i = false ∧ 0 < peerCount A z i) ∧
    (exposure A z i = .d00 ↔ z i = false ∧ peerCount A z i = 0)) ∧
  (∀ {N : ℕ} (i : Fin N) (z : Assignment N),
    insertOwn i (z i) (fun j => z j.val) = z)

def T10Statement : Prop :=
  (∀ {N : ℕ} {C : Type*} [DecidableEq C]
    (s : ℝ) (t : Fin N → ℝ) (c : Fin N → C) (i j : Fin N) (h : c i ≠ c j),
    blockEdgeProbability s t c i j = 0) ∧
  (∀ {Ω C : Type*} {N : ℕ} [Fintype Ω] [DecidableEq C]
    (P : FiniteDesign Ω) (G : Ω → SimpleGraph (Fin N)) [∀ ω, DecidableRel (G ω).Adj]
    (c : Ω → Fin N → C)
    (hzero : ∀ i j, (∑ ω, if (G ω).Adj i j ∧ c ω i ≠ c ω j then P.mass ω else 0) = 0),
    ∀ ω, 0 < P.mass ω → ∀ i j, (G ω).Adj i j → c ω i = c ω j) ∧
  (∀ {N : ℕ} {C : Type*} (hN : 0 < N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (c : Fin N → C)
    (hdegree : ∀ i, 0 < G.degree i) (hwithin : ∀ i j, G.Adj i j → c i = c j),
    (∑ i, G.degree i) = 2 * G.edgeFinset.card ∧
    N ≤ 2 * G.edgeFinset.card ∧ 0 < G.edgeFinset.card ∧
    (withinEdges G c).card = G.edgeFinset.card ∧
    ((withinEdges G c).card : ℝ) / G.edgeFinset.card = 1 ∧
    ((withinEdges G c).card : ℝ) / G.edgeFinset.card - 7/10 = 3/10) ∧
  (∀ {Ω C : Type*} {N : ℕ} [Fintype Ω]
    (hN : 0 < N) (P : FiniteDesign Ω) (G : Ω → SimpleGraph (Fin N))
    [∀ ω, DecidableRel (G ω).Adj] (c : Ω → Fin N → C)
    (hdegree : ∀ ω i, 0 < (G ω).degree i)
    (hwithin : ∀ ω i j, (G ω).Adj i j → c ω i = c ω j),
    expect P.mass (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ) / (G ω).edgeFinset.card) = 1 ∧
    expect P.mass (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ)) /
      expect P.mass (fun ω => ((G ω).edgeFinset.card : ℝ)) = 1 ∧
    expect P.mass (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ) / (G ω).edgeFinset.card) - 7/10 = 3/10 ∧
    expect P.mass (fun ω => ((withinEdges (G ω) (c ω)).card : ℝ)) /
      expect P.mass (fun ω => ((G ω).edgeFinset.card : ℝ)) - 7/10 = 3/10)

def T13Statement : Prop :=
  ∀ (N : ℕ) (A : Adjacency N) (_hdiag : ∀ i, A i i = false),
    0 < N → ¬ (∀ i : Fin N, baselineLaw (degreeScale A i : ℝ) = halfNormalLaw)

end
end SAP.P044
