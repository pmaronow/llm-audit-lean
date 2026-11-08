import SAP.P011b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-! Explicit finite probability laws. Indices start at zero.
The star sequence uses K = k+1 blocks, so n = 4K is positive.
Uniform leaf draws realize the Bernoulli probabilities exactly. -/

def emptyGraph (n : ℕ) : Graph n := ⟨fun _ _ => false, by simp⟩

def pathGraph : Graph 3 :=
  ⟨![![false,true,false], ![true,false,true], ![false,true,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

def starGraph : Graph 4 :=
  ⟨![![false,true,true,true], ![true,false,false,false],
      ![true,false,false,false], ![true,false,false,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

def localIndex {q blocks : ℕ} (hq : 0 < q) (i : Fin (q*blocks)) : Fin q :=
  ⟨i.val % q, Nat.mod_lt _ hq⟩

def blockIndex {q blocks : ℕ} (hq : 0 < q) (i : Fin (q*blocks)) : Fin blocks :=
  ⟨i.val / q, (Nat.div_lt_iff_lt_mul hq).mpr (by simpa [Nat.mul_comm] using i.isLt)⟩

def blockGraph {q : ℕ} (hq : 0 < q) (A : Graph q) (blocks : ℕ) : Graph (q*blocks) :=
  ⟨fun i j => decide (i.val / q = j.val / q) && A.val (localIndex hq i) (localIndex hq j), by
    constructor
    · intro i j
      dsimp only
      rw [A.property.1 (localIndex hq i) (localIndex hq j)]
      simp only [eq_comm]
    · intro i
      simp [A.property.2]⟩

def sign (b : Bool) : ℝ := if b then 1 else -1

def uniformLaw {Ω : Type} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (f : Ω → (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ((PMF.uniformOfFintype Ω).map f).toMeasure

def pathBlock (t U V : ℝ) : Fin 3 → ℝ := ![t+U, -2*t+3/5*U+4/5*V, t+V]

def pathModel (t : ℝ) (blocks : ℕ) : Model (3*blocks) where
  law := uniformLaw (fun u : Fin blocks → Fin 2 → Bool => fun i =>
    pathBlock t (sign (u (blockIndex (by decide) i) 0))
      (sign (u (blockIndex (by decide) i) 1)) (localIndex (by decide) i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := blockGraph (by decide) pathGraph blocks
  R := blockGraph (by decide) pathGraph blocks
  d := fun i => degree pathGraph (localIndex (by decide) i)

def signModel (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Bool => fun i => sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

def signFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => signModel (k+1)

def starLeaves (upper : Bool) (u : Fin 3 → Fin 4) : Fin 3 → ℝ :=
  fun j => if (u j).val < (if upper then (![3,1,2] : Fin 3 → ℕ) j else 1) then 1 else 0

def starBlock (upper : Bool) (u : Fin 3 → Fin 4) (v : Fin 48) : Fin 4 → ℝ :=
  let count : ℕ := ∑ j, if starLeaves upper u j = 1 then 1 else 0
  ![if v.val < (if upper then 18 else 33) + 4*count then 1 else 0,
    starLeaves upper u 0, starLeaves upper u 1, starLeaves upper u 2]

def starModel (upper : Bool) (blocks : ℕ) : Model (4*blocks) where
  law := uniformLaw (fun u : Fin blocks → ((Fin 3 → Fin 4) × Fin 48) => fun i =>
    starBlock upper (u (blockIndex (by decide) i)).1
      (u (blockIndex (by decide) i)).2 (localIndex (by decide) i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := blockGraph (by decide) starGraph blocks
  R := blockGraph (by decide) starGraph blocks
  d := fun i => degree starGraph (localIndex (by decide) i)

def starFamily (upper : Bool) : Family where
  size := fun k => 4*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => starModel upper (k+1)

def threePointModel (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Fin 3 => fun i => ((u i).val : ℝ))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

def threePointFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => threePointModel (k+1)

def completeGraph (n : ℕ) : Graph n :=
  ⟨fun i j => decide (i ≠ j), by constructor <;> intros <;> simp [ne_comm]⟩

def edge12 : Graph 3 :=
  ⟨![![false,true,false], ![true,false,false], ![false,false,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

def edge23 : Graph 3 :=
  ⟨![![false,false,false], ![false,false,true], ![false,true,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

def nonzeroRule {n : ℕ} (x : Fin n → ℝ) : Graph n :=
  fromUpper (fun e => decide (centered x e.val.1*centered x e.val.2 ≠ 0))

end
end SAP.P011b
