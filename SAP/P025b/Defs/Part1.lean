import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

/-! Finite weighted means, valid first cuts, and the exact Table 1 inputs.
Indices of observations are zero based; a cut is the prefix length. -/

def populationMean {n : ℕ} (y : Fin n → ℝ) : ℝ := (∑ i, y i) / n

def ratio {ι : Type*} [Fintype ι] (y a w : ι → ℝ) : ℝ :=
  (∑ i, a i * w i * y i) / (∑ i, a i * w i)

def weightBox {ι : Type*} (α β : ℝ) (w : ι → ℝ) : Prop :=
  ∀ i, 1 / β ≤ w i ∧ w i ≤ 1 / α

def normBox {ι : Type*} (γ : ℝ) (w : ι → ℝ) : Prop :=
  ∀ i, 1 ≤ w i ∧ w i ≤ γ

def lowerWeights {n : ℕ} (γ : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then γ else 1

def upperWeights {n : ℕ} (γ : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then 1 else γ

def lowerValue {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  ratio y a (lowerWeights γ k)

def upperValue {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  ratio y a (upperWeights γ k)

def lowerCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | lowerValue y a γ j.val ≤ y j} k

def upperCut {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) (k : Fin n) : Prop :=
  IsLeast {j : Fin n | upperValue y a γ j.val ≤ y j} k

def attainable {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : Set ℝ :=
  {v | ∃ w, weightBox α β w ∧ ratio y a w = v}

noncomputable def lowerEndpoint {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : ℝ :=
  sInf (attainable y a α β)

noncomputable def upperEndpoint {ι : Type*} [Fintype ι] (y a : ι → ℝ) (α β : ℝ) : ℝ :=
  sSup (attainable y a α β)

def separation {n : ℕ} (y a : Fin n → ℝ) (γ : ℝ) : Prop :=
  ∀ k : Fin n, y k ≠ upperValue y a γ k.val ∧
    y k ≠ lowerValue y a γ k.val

def binaryTwo : Fin 2 → ℝ := ![0, 1]

def binaryLower (p γ : ℝ) : ℝ := p / (γ*(1-p)+p)

def binaryUpper (p γ : ℝ) : ℝ := γ*p / ((1-p)+γ*p)

def normAttainable {ι : Type*} [Fintype ι] (y a : ι → ℝ) (γ : ℝ) : Set ℝ :=
  {v | ∃ w, normBox γ w ∧ ratio y a w = v}

def roundsTenth (x : ℝ) (t : ℕ) : Prop :=
  (t : ℝ)/10 - 1/20 ≤ x ∧ x < (t : ℝ)/10 + 1/20

abbrev TableCell := ℝ × ℝ × ℝ × Bool × ℕ × ℕ

def tableCells : List TableCell := [
  (44/48,917/1000,1,false,917,917),(44/48,917/1000,1,true,917,917),
  (44/48,917/1000,5/4,false,898,898),(44/48,917/1000,5/4,true,932,932),
  (44/48,917/1000,3/2,false,880,880),(44/48,917/1000,3/2,true,943,943),
  (44/48,917/1000,2,false,847,846),(44/48,917/1000,2,true,957,957),
  (44/48,917/1000,5/2,false,815,815),(44/48,917/1000,5/2,true,965,965),
  (44/48,917/1000,3,false,786,786),(44/48,917/1000,3,true,971,971),
  (44/48,917/1000,4,false,734,733),(44/48,917/1000,4,true,978,978),
  (108/160,675/1000,1,false,675,675),(108/160,675/1000,1,true,675,675),
  (108/160,675/1000,5/4,false,624,624),(108/160,675/1000,5/4,true,722,722),
  (108/160,675/1000,3/2,false,581,581),(108/160,675/1000,3/2,true,757,757),
  (108/160,675/1000,2,false,509,509),(108/160,675/1000,2,true,806,806),
  (108/160,675/1000,5/2,false,454,454),(108/160,675/1000,5/2,true,839,839),
  (108/160,675/1000,3,false,409,409),(108/160,675/1000,3,true,862,862),
  (108/160,675/1000,4,false,342,342),(108/160,675/1000,4,true,893,893),
  (291/579,503/1000,1,false,503,503),(291/579,503/1000,1,true,503,503),
  (291/579,503/1000,5/4,false,447,447),(291/579,503/1000,5/4,true,559,558),
  (291/579,503/1000,3/2,false,403,402),(291/579,503/1000,3/2,true,603,602),
  (291/579,503/1000,2,false,336,336),(291/579,503/1000,2,true,669,669),
  (291/579,503/1000,5/2,false,288,288),(291/579,503/1000,5/2,true,717,716),
  (291/579,503/1000,3,false,252,252),(291/579,503/1000,3,true,752,752),
  (291/579,503/1000,4,false,202,202),(291/579,503/1000,4,true,802,802)]

def cellPercent (p γ : ℝ) (high : Bool) : ℝ :=
  100 * (if high then binaryUpper p γ else binaryLower p γ)

end
end SAP.P025b
