import SAP.P019a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a
open scoped BigOperators
noncomputable section
open Classical

def uniformFin (n : ℕ) (hn : 0 < n) : FiniteLaw (Fin n) where
  mass := fun _ => 1 / (n : ℝ)
  nonneg := by intro; positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp

/-- The exact Binomial(4,2/5) probability vector. -/
def ceilingBaseline : FiniteLaw (Fin 5) where
  mass := ![81/625, 216/625, 216/625, 96/625, 16/625]
  nonneg := by intro w; fin_cases w <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def printedAffected (w : Fin 5) : ℝ := (min (w.val + 1) 4 : ℕ)
def codedAffected (w : Fin 5) : ℝ := printedAffected w + 1
def unaffected (w : Fin 5) : ℝ := (w.val : ℝ) + 1

/-- Treatment-minus-control mean with independent affected status integrated out. -/
def ceilingBeta (response : Fin 5 → ℝ) (ρ : ℝ) : ℝ :=
  ceilingBaseline.mean (fun w => (1 - ρ) * unaffected w + ρ * response w) -
    ceilingBaseline.mean (fun w => (w.val : ℝ))

def fairBit {n : ℕ} (ω : Fin n) (k : ℕ) : Bool := decide ((ω.val / 2^k) % 2 = 1)

/-- Sixteen equiprobable atoms: independent X,C,W,Z; Y=XC and V=W+XZ. -/
def finiteSampleWitness : Study (Fin 16) where
  law := uniformFin 16 (by norm_num)
  W := fun ω => if fairBit ω 2 then 1 else 0
  X := fun ω => fairBit ω 0
  Y := fun ω => fairBit ω 0 && fairBit ω 1
  Z := fun ω => fairBit ω 3
  V := fun ω => (if fairBit ω 2 then 1 else 0) +
    (if fairBit ω 0 && fairBit ω 3 then 1 else 0)

/-- Zero completion of a one-observation cell mean. -/
def singletonMean {Ω : Type*} [Fintype Ω] (S : Study Ω) (z y : Bool) (ω : Ω) : ℝ :=
  if S.cell z y ω then (S.V ω : ℝ) else 0

/-- Eight equiprobable atoms: X=Y, with X, W and Z independent fair bits. -/
def distributionWitness : Study (Fin 8) where
  law := uniformFin 8 (by norm_num)
  W := fun ω => if fairBit ω 1 then 1 else 0
  X := fun ω => fairBit ω 0
  Y := fun ω => fairBit ω 0
  Z := fun ω => fairBit ω 2
  V := fun ω => (if fairBit ω 1 then 1 else 0) +
    (if fairBit ω 0 && fairBit ω 2 then 1 else 0)

/-- Sixteen equiprobable atoms: W=B+C, Y=X*1{C=Z}, V=W+XZ. -/
def diagnosisWitness : Study (Fin 16) where
  law := uniformFin 16 (by norm_num)
  W := fun ω => (if fairBit ω 0 then 1 else 0) + (if fairBit ω 1 then 1 else 0)
  X := fun ω => fairBit ω 2
  Y := fun ω => fairBit ω 2 && decide (fairBit ω 1 = fairBit ω 3)
  Z := fun ω => fairBit ω 3
  V := fun ω => (if fairBit ω 0 then 1 else 0) + (if fairBit ω 1 then 1 else 0) +
    (if fairBit ω 2 && fairBit ω 3 then 1 else 0)

end
end SAP.P019a
