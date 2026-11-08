import SAP.P025a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

def T11Statement : Prop :=
  (∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y → ∀ γ : ℝ, 1 ≤ γ →
    (∀ k : Fin n,
      upperValue y (fun _ => 1) γ (k.val+1) - upperValue y (fun _ => 1) γ k.val =
        (1-γ)*(y k-upperValue y (fun _ => 1) γ k.val) /
          (∑ i : Fin n, upperWeights γ (k.val+1) i)) ∧
    (γ = 1 → ∀ k : ℕ,
      upperValue y (fun _ => 1) γ k = populationMean y ∧
      lowerValue y (fun _ => 1) γ k = populationMean y ∧
      (∀ w : Fin n → ℝ, normBox γ w ↔ w = fun _ => 1)) ∧
    (1 < γ →
      {k : Fin n | upperValue y (fun _ => 1) γ k.val ≥
          upperValue y (fun _ => 1) γ (k.val+1)} =
        {k : Fin n | upperValue y (fun _ => 1) γ k.val ≤ y k}) ∧
    (∀ k : Fin n, upperValue y (fun _ => 1) γ k.val ≤ y k →
      upperValue y (fun _ => 1) γ (k.val+1) ≤ y k) ∧
    (1 < γ → ∀ k : Fin n,
      upperValue y (fun _ => 1) γ (k.val+1) - upperValue y (fun _ => 1) γ k.val ≤ 0 ↔
        upperValue y (fun _ => 1) γ k.val ≤ y k)) ∧
  (∀ (c₁ c₂ p q u v a b : ℝ)
    (hc : 0 ≤ c₂) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) (huv : u < v),
    (c₂+a*p+a*q)*(c₂+b*p+a*q)*
      (pairObjective c₁ c₂ p q u v a a - pairObjective c₁ c₂ p q u v b a) =
        (a-b)*p*(c₂*u-c₁+a*q*(u-v)) ∧
    (c₂+b*p+b*q)*(c₂+b*p+a*q)*
      (pairObjective c₁ c₂ p q u v b b - pairObjective c₁ c₂ p q u v b a) =
        (a-b)*q*(c₁-c₂*v+b*p*(u-v)) ∧
    (c₂*u-c₁+a*q*(u-v))+(c₁-c₂*v+b*p*(u-v)) =
      (c₂+b*p+a*q)*(u-v) ∧
    (c₂*u-c₁+a*q*(u-v))+(c₁-c₂*v+b*p*(u-v)) < 0) ∧
  (∀ (c₁ c₂ p q u v a b : ℝ)
    (hc : 0 ≤ c₂) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) (huv : u < v),
    (a < b →
      (pairObjective c₁ c₂ p q u v a a > pairObjective c₁ c₂ p q u v b a ↔
        c₂*u-c₁+a*q*(u-v) < 0) ∧
      (pairObjective c₁ c₂ p q u v b b > pairObjective c₁ c₂ p q u v b a ↔
        c₁-c₂*v+b*p*(u-v) < 0) ∧
      (pairObjective c₁ c₂ p q u v a a > pairObjective c₁ c₂ p q u v b a ∨
        pairObjective c₁ c₂ p q u v b b > pairObjective c₁ c₂ p q u v b a)) ∧
    (a = b → pairObjective c₁ c₂ p q u v a a = pairObjective c₁ c₂ p q u v b a ∧
      pairObjective c₁ c₂ p q u v b b = pairObjective c₁ c₂ p q u v b a))

end
end SAP.P025a
