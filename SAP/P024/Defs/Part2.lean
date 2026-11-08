import SAP.P024.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
noncomputable section

def subsetExposure {K : ℕ} (s : Finset (Fin K)) (j : Fin K) : Bool := decide (j ∈ s)

def bernoulliMass {K : ℕ} (p : ℝ) (s : Finset (Fin K)) : ℝ :=
  (∏ j ∈ s, p) * (∏ j ∈ Finset.univ \ s, (1-p))

/-- Full independent common-probability assignment, specified by its joint masses. -/
def independentClusterLaw {K : ℕ} (d : Design (Finset (Fin K))) (p : ℝ) : Prop :=
  ∀ s, d.mass s = bernoulliMass p s

def completeClusterLaw {K : ℕ} (d : Design (Finset (Fin K))) (m : ℕ) : Prop :=
  ∀ s, d.mass s = if s.card = m then 1/(Nat.choose K m : ℝ) else 0

def bernoulliDesign (K : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Design (Finset (Fin K)) where
  mass := bernoulliMass p
  nonneg := fun s => mul_nonneg
    (Finset.prod_nonneg (fun _ _ => hp0)) (Finset.prod_nonneg (fun _ _ => by linarith))
  total := by
    have h := Finset.prod_add (fun (_ : Fin K) => p) (fun _ => 1-p) Finset.univ
    simpa [bernoulliMass] using h.symm

/-- Positive cluster sizes and fixed individual potential outcomes. -/
structure ClusterPopulation (K : ℕ) where
  size : Fin K → ℕ
  positive : ∀ j, 0 < size j
  y0 : (j : Fin K) → Fin (size j) → ℝ
  y1 : (j : Fin K) → Fin (size j) → ℝ

def clusterMean0 {K : ℕ} (P : ClusterPopulation K) (j : Fin K) : ℝ :=
  (∑ i, P.y0 j i) / P.size j
def clusterMean1 {K : ℕ} (P : ClusterPopulation K) (j : Fin K) : ℝ :=
  (∑ i, P.y1 j i) / P.size j
def clusterWeight {K : ℕ} (P : ClusterPopulation K) (j : Fin K) : ℝ :=
  (P.size j : ℝ) / ∑ l, (P.size l : ℝ)
def populationEffect {K : ℕ} (P : ClusterPopulation K) : ℝ :=
  clusterEffect (fun j => P.size j) (clusterMean0 P) (clusterMean1 P)

/-- Observed individual means on nonempty arms, with an explicit arbitrary extension. -/
def populationEstimator {K : ℕ} (P : ClusterPopulation K)
    (empty : Finset (Fin K) → ℝ) (s : Finset (Fin K)) : ℝ :=
  if s = ∅ ∨ s = Finset.univ then empty s
  else clusterDIM (fun j => P.size j) (clusterMean0 P) (clusterMean1 P) (subsetExposure s)

def maxClusterWeight {k : ℕ} (P : ClusterPopulation (k+2)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (clusterWeight P)

/-- In a population of K=k+2 clusters, the first has K squared individuals. -/
def dominantPopulation (k : ℕ) : ClusterPopulation (k+2) where
  size := fun j => if j.val = 0 then (k+2)^2 else 1
  positive := fun j => by split_ifs <;> positivity
  y0 := fun j _ => if j.val = 0 then 1/2 else 1/4
  y1 := fun j _ => if j.val = 0 then 3/4 else 1/2

def dominantValue (K m : ℝ) (largeTreated : Bool) : ℝ :=
  if largeTreated then 1/4+(1/4)*K^2/(K^2+m-1)
  else 1/4-(1/4)*K^2/(K^2+K-m-1)

abbrev NonemptyAllocations (k : ℕ) :=
  {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ}

/-- Fair independent assignment conditioned on nonempty arms: uniform proper nonempty subsets. -/
def conditionalNonemptyDesign (k : ℕ) : Design (NonemptyAllocations k) := by
  letI : Nonempty (NonemptyAllocations k) :=
    ⟨⟨{0}, by
      constructor
      · simp
      · intro h
        have hc := congrArg Finset.card h
        simp at hc⟩⟩
  exact uniformDesign _

def halfClusterDesign (n : ℕ) :
    Design {s : Finset (Fin (2*n+2)) // s.card=n+1} := by
  have hc : 0 < Fintype.card {s : Finset (Fin (2*n+2)) // s.card=n+1} := by
    simpa using (Nat.choose_pos (by omega : n+1 ≤ 2*n+2))
  letI : Nonempty {s : Finset (Fin (2*n+2)) // s.card=n+1} := Fintype.card_pos_iff.mp hc
  exact uniformDesign _

def halfDominantRatio (n : ℕ) : ℝ :=
  (2*n+2 : ℝ)^2 / ((2*n+2 : ℝ)^2+(n+1)-1)

end
end SAP.P024
