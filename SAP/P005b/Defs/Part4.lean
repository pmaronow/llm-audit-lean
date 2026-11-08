import SAP.P005b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter


def T17Statement : Prop :=
  (∀ {n d m : ℕ} (P : Population n d)
    (hn : 2 ≤ n) (hm : 0 < m) (hmn : m < n) (hG : gram P = 1) (δ : Fin n → ℝ),
    let μ := populationSlope P δ
    (∀ i, (∑ j, (dot (P.x i) (fun k => P.x j k*δ j-μ k))^2) ≤
      ∑ j, (dot (P.x i) (P.x j)*δ j)^2) ∧
    ((1/(pC n m*m*n))^2 * ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) *
      (∑ i, ∑ j, (dot (P.x i) (P.x j)*δ j)^2)) =
      ((1/(pC n m*m*n))^2 * (n : ℝ)^2 * ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) *
        (∑ j, (1/(n : ℝ))*leverage P j*δ j^2)) ∧
    ((1/(pC n m*m*n))^2 * ((m : ℝ)*(n-m)/((n : ℝ)*(n-1))) *
      (∑ i, ∑ j, (dot (P.x i) (P.x j)*δ j)^2)) =
      1/(pT n m*pC n m*n*(n-1)) * popMean (fun j => leverage P j*δ j^2) ∧
    1/(pT n m*pC n m*n*(n-1)) * popMean (fun j => leverage P j*δ j^2) ≤
      kappa P/(pT n m*pC n m*(n-1)) * popMean (fun j => δ j^2)) ∧
  (∀ {n d : ℕ} (P : Population n d), 0 < n → gram P = 1 → ∀ a : Fin n → ℝ,
    (∑ i, ∑ j, (dot (P.x i) (P.x j) * a j)^2) =
      ∑ j, a j^2 * dot (P.x j) ((∑ i, Matrix.vecMulVec (P.x i) (P.x i)) *ᵥ P.x j) ∧
    (∑ j, a j^2 * dot (P.x j) ((∑ i, Matrix.vecMulVec (P.x i) (P.x i)) *ᵥ P.x j)) =
      (n : ℝ) * ∑ j, a j^2 * leverage P j) ∧
  (∀ {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (K : ℝ) (hT : popMean (fun i => P.yT i^2) ≤ K)
    (hC : popMean (fun i => P.yC i^2) ≤ K),
    popMean (fun i => (commonResidual P m P.yT i-commonResidual P m P.yC i)^2) ≤ 4*K) ∧
  (∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h :
      (∀ n, 3 ≤ n → d n ≤ n ∧ 0 < m n ∧ m n < n) ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ n, 3 ≤ n →
        popMean (fun i => (P n).yT i^2) ≤ K ∧
        popMean (fun i => (P n).yC i^2) ≤ K ∧
        ∀ k, popMean (fun i => (P n).x i k^2) ≤ K) ∧
      (∀ᶠ n in atTop, standardized (P n)) ∧
      (∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧
        ∀ n, 3 ≤ n → lo < pT n (m n) ∧ pT n (m n) < hi)),
    Asymptotics.IsBigO atTop
      (fun n => 1/(pT n (m n)*pC n (m n)*n*(n-1)) *
        popMean (fun i => leverage (P n) i *
          (commonResidual (P n) (m n) (P n).yT i-commonResidual (P n) (m n) (P n).yC i)^2))
      (fun n => kappa (P n)/n) ∧
    Asymptotics.IsBigO atTop
      (fun n => popMean (fun i =>
        (commonResidual (P n) (m n) (P n).yT i -
          commonResidual (P n) (m n) (P n).yC i)^2))
      (fun _ : ℕ => (1 : ℝ)))

def T18Statement : Prop :=
  (∀ {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (S : Finset (Fin n)) (hS : S.card = m)
    (eT eC : Fin n → ℝ)
    (he : pT n m • populationSlope P eT + pC n m • populationSlope P eC = 0),
    let A := populationSlope P (fun i => eT i-eC i)
    let B := populationSlope P eC
    let U := fun k => (∑ i ∈ S, P.x i k*(eT i-eC i))/(n : ℝ)
    B = -pT n m • A ∧
    U+B = (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) + (1/pT n m)*B k))/(n : ℝ)) ∧
    U+B = (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) - A k))/(n : ℝ)) ∧
    (1/pC n m)*dot (xMean P S) (U+B) =
      (1/pC n m)*dot (xMean P S)
        (fun k => (∑ i ∈ S, (P.x i k*(eT i-eC i) - A k))/(n : ℝ))) ∧
  (∀ {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (S : Finset (Fin n)) (hS : S ∈ design n m),
    let eT := commonResidual P m P.yT
    let eC := commonResidual P m P.yC
    let U := fun k => (∑ i ∈ S, P.x i k*(eT i-eC i))/(n : ℝ)
    let B := populationSlope P eC
    xMean P S-xMean P (control S) = (1/pC n m) • xMean P S ∧
    pT n m • populationSlope P eT+pC n m • populationSlope P eC = 0 ∧
    residualStarTerm P S eT eC = (1/pC n m)*dot (xMean P S) (U+B))

end
end SAP.P005b
