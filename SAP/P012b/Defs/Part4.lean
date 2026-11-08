import SAP.P012b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P012b

open Finset Filter
open scoped Topology
noncomputable section

def T16Statement : Prop :=
  (∀ (T : ℕ → ℝ)
    (hp : ∀ n, 0 < T n) (hm : Monotone T),
    ¬ Tendsto T atTop (𝓝 0)) ∧
    (∀ (ε : ℝ),
    ¬ ∃ T : ℝ, T*(ε*Real.log 1) = 1) ∧
    (∀ (ε T₁ : ℝ) (hε : 0 < ε)
    (hfirst : 1/(ε*Real.log 2) ≤ T₁),
    (∀ n, 0 < cooling ε T₁ n) ∧ Antitone (cooling ε T₁) ∧
    StrictAntiOn (cooling ε T₁) (Set.Ici 1) ∧ Tendsto (cooling ε T₁) atTop (𝓝 0)) ∧
    (∀ (ε D t : ℝ) (hε : 0 < ε) (ht : 2 ≤ t)
      (hD : 0 ≤ D*ε) (hdepth : D*ε ≤ 1),
      Real.exp (-D / (1/(ε*Real.log t))) = Real.exp (-D*ε*Real.log t) ∧
      Real.exp (-D / (1/(ε*Real.log t))) = 1/(t^(D*ε)) ∧
      1/t ≤ Real.exp (-D / (1/(ε*Real.log t)))) ∧
    (∀ (ε D : ℝ) (hε : 0 < ε)
    (hD : 0 ≤ D*ε) (hdepth : D*ε ≤ 1) (first : ℝ),
    Tendsto (fun N : ℕ => first + ∑ n ∈ range N,
      Real.exp (-D / (1/(ε*Real.log ((n:ℝ)+2))))) atTop atTop)

def T17Statement : Prop :=
  ∀ (D : Data) (H : State) (hD : Admissible D)
    (hH : GraphCompatible D H),
    InducedCompatible D (induced D H) ∧
    ((∀ i ∈ D.sampled, graphDegree (induced D H) (s i) = D.degree i) ↔
      H.vertices = sampledVertices D)

def T18Statement : Prop :=
  ∀ (D₁ D₂ : Data) (H K : State)
    (hD₁ : Admissible D₁) (hD₂ : Admissible D₂)
    (hH : Compatible D₁ H) (hK : Compatible D₂ K)
    (hv : H.vertices = K.vertices) (he : H.edges = K.edges)
    (hz : ∀ v ∈ H.vertices, H.trait v = K.trait v),
    homophily H = homophily K

def T19Statement : Prop :=
  ¬ (∀ (D : Data) (H K : State)
    (hD : Admissible D) (hH : Compatible D H) (hP : Proposal D false H K),
    Compatible D K)

def T20Statement : Prop :=
  ∀ Dsex Dcrack Dhome : Data, ¬ printed_table_intervals Dsex Dcrack Dhome
end
end SAP.P012b
