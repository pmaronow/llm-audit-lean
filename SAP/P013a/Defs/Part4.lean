import SAP.P013a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def pairEpsilon (N : ℕ) : ℝ := 1/(N : ℝ)^2

def pairSplitProbability (N : ℕ) : ℝ := 1-2*pairEpsilon N

def pairAtomDesign (N : ℕ) (hN : 4 ≤ N) : Design (Fin 4) where
  weight := ![pairEpsilon N, 1/2-pairEpsilon N, 1/2-pairEpsilon N, pairEpsilon N]
  positive := by
    have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have he : 0 < pairEpsilon N := by unfold pairEpsilon; positivity
    have hel : pairEpsilon N < 1/2 := by
      unfold pairEpsilon
      apply (div_lt_iff₀ (by nlinarith : 0 < (N : ℝ)^2)).2
      nlinarith
    intro a
    fin_cases a <;> simp <;> linarith
  total := by
    simp [Fin.sum_univ_succ]
    ring

def pairIndex (r : ℕ) (i : Fin (2*r)) : Fin r := ⟨i.val/2, by omega⟩

def pairExposure (a : Fin 4) (second : Bool) : Fin 2 :=
  if second then (if a.val % 2 = 0 then 0 else 1) else (if a.val < 2 then 0 else 1)

def pairedDesign (r : ℕ) (hr : 2 ≤ r) : Design (Fin r → Fin 4) :=
  replicateDesign (pairAtomDesign (2*r) (by omega)) r

def pairedPopulation (r : ℕ) (hr : 2 ≤ r) : Population (pairedDesign r hr) (2*r) 2 where
  exposure z i := pairExposure (z (pairIndex r i)) (decide (i.val % 2 = 1))
  outcome i _ := if i.val % 2 = 0 then 1 else -1

def pairScore (a : Fin 4) : ℝ :=
  4*((pairExposure a false).val-(pairExposure a true).val : ℤ)

def pairVarianceScore (N : ℕ) (a : Fin 4) : ℝ :=
  if pairExposure a false = pairExposure a true then 2/pairEpsilon N
  else 16-4/pairSplitProbability N

def allPairsSplit (r : ℕ) (z : Fin r → Fin 4) : Prop :=
  ∀ a, pairExposure (z a) false ≠ pairExposure (z a) true

def blockEnd (r : ℕ) : ℕ := if r=0 then 0 else 2^(2^r)

def blockIndex (i : ℕ) : ℕ := sInf {r : ℕ | 1 ≤ r ∧ i ≤ blockEnd r}

def blockOutcome (i : ℕ) (d : Fin 2) : ℝ :=
  if blockIndex i % 2 = 1 then 1 else
    if (i-blockEnd (blockIndex i-1)-1) % 2 = 0 then (if d=1 then 2 else 0)
    else (if d=1 then 0 else 2)

def blockDesign (N : ℕ) : Design (Fin N → Fin 2) := replicateDesign sharedDesign N

def blockPopulation (N : ℕ) : Population (blockDesign N) N 2 where
  exposure z i := z i
  outcome i d := blockOutcome (i.val+1) d

def blockBUnits (N : ℕ) : Finset (Fin N) := univ.filter (fun i => blockIndex (i.val+1) % 2 = 0)

def blockSign (i : ℕ) : ℝ := if (i-blockEnd (blockIndex i-1)-1) % 2 = 0 then 1 else -1

def rademacher (z : Fin 2) : ℝ := 2*(z.val : ℝ)-1

def TendsDistribution {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (X : ∀ n : ℕ, L n → ℝ) (μ : MeasureTheory.Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun t => ProbabilityTheory.cdf μ t) x →
    Tendsto (fun n : ℕ => probability (P n) (fun z => X n z ≤ x)) atTop (𝓝 (ProbabilityTheory.cdf μ x))

def Displays3 (x p : ℝ) : Prop := p - 1/2000 ≤ x ∧ x ≤ p + 1/2000

def completeProbability (U : Finset ℕ) (n : ℕ) (A : Finset ℕ → Prop) : ℝ :=
  by classical exact ((U.powersetCard n).filter A).card / (Nat.choose U.card n : ℝ)

def isolatedExposure (i : ℕ) (neighbors : Finset ℕ) (S : Finset ℕ) : Prop :=
  i ∈ S ∧ Disjoint S neighbors

def noExposure (i : ℕ) (neighbors : Finset ℕ) (S : Finset ℕ) : Prop :=
  i ∉ S ∧ Disjoint S neighbors
end
end SAP.P013a
