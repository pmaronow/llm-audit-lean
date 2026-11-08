import SAP.P013a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def VectorIndependent {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (A B : Finset (Fin N)) : Prop :=
  ∀ a b : Fin N → Fin K,
    probability P (fun z => (∀ i ∈ A, D z i = a i) ∧ (∀ j ∈ B, D z j = b j)) =
      probability P (fun z => ∀ i ∈ A, D z i = a i) *
      probability P (fun z => ∀ j ∈ B, D z j = b j)

def PrintedNoEdge {N : ℕ} (h : Fin N → Fin N → Bool) (A B : Finset (Fin N)) : Prop :=
  ¬ ∃ i j, h i j = true ∧
    ((i ∈ A ∧ j ∉ B) ∨ (j ∈ A ∧ i ∉ B) ∨
      (i ∉ A ∧ j ∈ B) ∨ (j ∉ A ∧ i ∈ B))

def PrintedDependency {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (h : Fin N → Fin N → Bool) : Prop :=
  ∀ A B, Disjoint A B → PrintedNoEdge h A B → VectorIndependent P D A B

def CorrectedNoEdge {N : ℕ} (h : Fin N → Fin N → Bool) (A B : Finset (Fin N)) : Prop :=
  ¬ ∃ i j, h i j = true ∧
    ((i ∈ A ∧ j ∈ B) ∨ (j ∈ A ∧ i ∈ B) ∨
      (i ∈ A ∧ j ∈ B) ∨ (j ∈ A ∧ i ∈ B))

def GenuineDependency {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (h : Fin N → Fin N → Bool) : Prop :=
  ∀ A B, Disjoint A B → CorrectedNoEdge h A B → VectorIndependent P D A B

def RowBound {N : ℕ} (h : Fin N → Fin N → Bool) (m : ℕ) : Prop :=
  ∀ i, ∑ j, (if h i j = true then 1 else 0 : ℕ) ≤ m

def PairIndependent {N K : ℕ} {P : Design Ω} (F : Population P N K) (i j : Fin N) : Prop :=
  ∀ d e, jointPi F i j d e = pi F i d * pi F j e

def graphPairIndicator {N : ℕ} (h : Fin N → Fin N → Bool) (i j : Fin N) : ℕ :=
  if i = j ∨ h i j = true ∨ h j i = true then 1 else 0

def sharedDesign : Design (Fin 2) where
  weight := fun _ => 1/2
  positive := by intro z; norm_num
  total := by norm_num [Fin.sum_univ_succ]

def sharedPopulation (N : ℕ) : Population sharedDesign N 2 where
  exposure := fun z _ => z
  outcome := fun _ _ => 0

def independentProduct (P : Design Ω) (Q : Design Ξ) : Design (Ω × Ξ) where
  weight z := P.weight z.1 * Q.weight z.2
  positive z := mul_pos (P.positive z.1) (Q.positive z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← mul_sum, Q.total, mul_one, P.total]

def replicateDesign (P : Design Ω) (R : ℕ) : Design (Fin R → Ω) where
  weight z := ∏ r, P.weight (z r)
  positive z := prod_pos fun r _ => P.positive (z r)
  total := by
    classical
    simpa [Fintype.piFinset_univ, P.total] using
      (sum_prod_piFinset (univ : Finset Ω) (fun _ : Fin R => P.weight))

def replicateCount {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (R : ℕ) (zs : Fin R → Ω) (i : Fin N) :=
  ∑ r, indicator F.exposure i d (zs r)

def simulatedPi {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (R : ℕ) (zs : Fin R → Ω) (i : Fin N) :=
  (replicateCount F d R zs i + 1) / (R+1 : ℕ)

def simulatedHTTotal {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (R : ℕ) (z : Ω × (Fin R → Ω)) :=
  ∑ i, indicator F.exposure i d z.1 * observed F z.1 i / simulatedPi F d R z.2 i

def IsMinimumPi {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) (p0 : ℝ) : Prop :=
  (∃ i, pi F i d = p0) ∧ ∀ i, p0 ≤ pi F i d

def cancellationFactor {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :=
  (∑ i, |F.outcome i d|) / |potentialTotal F d|

def signedReplicationDesign : Design (Fin 4) where
  weight := ![2/9, 4/9, 1/9, 2/9]
  positive := by intro z; fin_cases z <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def signedReplicationPopulation (a : ℝ) : Population signedReplicationDesign 2 2 where
  exposure z i := if i = 0 then (if z.val < 2 then 0 else 1) else
    (if z.val % 2 = 0 then 0 else 1)
  outcome i d := if d = 0 then 0 else if i = 0 then a else -1

def signedOneReplicate (a : ℝ) (z : Fin 4 × Fin 4) : ℝ :=
  ∑ i, indicator (signedReplicationPopulation a).exposure i 1 z.1 *
    observed (signedReplicationPopulation a) z.1 i /
    ((indicator (signedReplicationPopulation a).exposure i 1 z.2 + 1)/2)
end
end SAP.P013a
