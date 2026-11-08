import SAP.P045b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P045b
open Finset
open scoped BigOperators
noncomputable section

def T25Statement : Prop :=
  ¬ ∀ n : ℕ, 0 < n → ∀ p : ℝ, 0 < p → p < 1 →
    ∀ y : Fin n → Assignment n → ℝ, ∀ b : Bool,
    condMean (bernoulli p) (armExists b) (armMean y b) =
      mean (fun i => marginal (bernoulli p) y i b)

def T26Statement : Prop :=
  ¬ ∀ {G C : ℕ}, 2 ≤ C → C ≤ G →
    ∀ (n m : Fin G → ℕ), (∀ g, 0 < m g ∧ m g < n g) →
    ∀ (a b : (g : Fin G) → Fin (n g) → ℝ),
    let law := selectedLaw n C (fun g => crMass (n g) (m g))
    let point := selectedMean C (fun g => directGroup (a g) (b g))
    let vest := directVarianceEstimate C a b
    ((∃ d : ℝ, ∀ g i, a g i=b g i+d) → expect law vest=variance law point) ∧
    variance law point ≤ expect law vest

def T27Statement : Prop :=
  ¬ ∀ {n : ℕ} (A : Network n) (z : Assignment n) (i : Fin n),
    badAllControl A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j=false

def T29Statement : Prop :=
  ¬ ∀ {n : ℕ}, 0 < n → ∀ (G : SimpleGraph (Fin n)) (p : ℝ), 0 ≤ p → p ≤ 1 →
      (∑ S : Finset (Fin n), terminalCentres G.edist 3 true S) = 1 ∧
      prob (terminalCentres G.edist 3 true) (epsilonNet G.edist 3) = 1 ∧
      (∀ z : Assignment n, clusteredTreatment G.edist true p z =
        ∑ S : Finset (Fin n), terminalCentres G.edist 3 true S * clusterProb G.edist S p z)

def T30Statement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (p : Design (Assignment n)) (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (k : Δ) (hk : ∀ i, 0 < exposureProb p.mass D i k),
    expect p.mass (htTotal p.mass D y k) = ∑ i, y i k ∧
    (∀ l : Δ, (∀ i, 0 < exposureProb p.mass D i l) →
      expect p.mass (htContrast p.mass D y k l)=effect y k l)

def T31Statement : Prop :=
  ∀ {Nc : ℕ} (hN : 0 < Nc)
    (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ),
    indirectHousehold m y=contagion m y true+otherMechanisms m y false ∧
    indirectHousehold m y=contagion m y false+otherMechanisms m y true ∧
    (∀ i, m i true=m i false → ∀ z, y i z (m i true)-y i z (m i false)=0)

end
end SAP.P045b
