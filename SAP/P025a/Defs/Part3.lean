import SAP.P025a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

/-- The two threshold vectors, their values, their attained extrema, and the full image. -/
def correctedSampleBounds {n : ℕ} (y : Fin n → ℝ) (α β : ℝ)
    (kL kH : Fin n) : Prop :=
  lowerCut y (fun _ => 1) (β/α) kL ∧ upperCut y (fun _ => 1) (β/α) kH ∧
  weightBox α β (fun i : Fin n => (1/β)*lowerWeights (β/α) kL.val i) ∧
  weightBox α β (fun i : Fin n => (1/β)*upperWeights (β/α) kH.val i) ∧
  ratio y (fun _ => 1) (fun i => (1/β)*lowerWeights (β/α) kL.val i) =
    lowerValue y (fun _ => 1) (β/α) kL.val ∧
  ratio y (fun _ => 1) (fun i => (1/β)*upperWeights (β/α) kH.val i) =
    upperValue y (fun _ => 1) (β/α) kH.val ∧
  IsLeast (attainable y (fun _ => 1) α β) (lowerValue y (fun _ => 1) (β/α) kL.val) ∧
  IsGreatest (attainable y (fun _ => 1) α β) (upperValue y (fun _ => 1) (β/α) kH.val) ∧
  lowerEndpoint y (fun _ => 1) α β = lowerValue y (fun _ => 1) (β/α) kL.val ∧
  upperEndpoint y (fun _ => 1) α β = upperValue y (fun _ => 1) (β/α) kH.val ∧
  attainable y (fun _ => 1) α β = Set.Icc
    (lowerValue y (fun _ => 1) (β/α) kL.val) (upperValue y (fun _ => 1) (β/α) kH.val)

def T3Statement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y →
  ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
  upperValue y (fun _ => 1) (β/α) (n-1) ≤ y ⟨n-1, by omega⟩ ∧
  lowerValue y (fun _ => 1) (β/α) (n-1) ≤ y ⟨n-1, by omega⟩ ∧
  ∃ kL kH : Fin n, correctedSampleBounds y α β kL kH ∧
    (∀ z ∈ Set.Icc (lowerValue y (fun _ => 1) (β/α) kL.val)
        (upperValue y (fun _ => 1) (β/α) kH.val),
      ∃ t ∈ Set.Icc (0 : ℝ) 1,
        let w := fun i : Fin n => (1/β) * ((1-t)*lowerWeights (β/α) kL.val i +
          t*upperWeights (β/α) kH.val i)
        weightBox α β w ∧ ratio y (fun _ => 1) w = z) ∧
    (∀ k : Fin n,
      lowerValue y (fun _ => 1) (β/α) (k.val+1) - lowerValue y (fun _ => 1) (β/α) k.val =
        ((β/α)-1)*(y k-lowerValue y (fun _ => 1) (β/α) k.val) /
          (∑ i : Fin n, lowerWeights (β/α) (k.val+1) i) ∧
      upperValue y (fun _ => 1) (β/α) (k.val+1) - upperValue y (fun _ => 1) (β/α) k.val =
        (1-(β/α))*(y k-upperValue y (fun _ => 1) (β/α) k.val) /
          (∑ i : Fin n, upperWeights (β/α) (k.val+1) i)) ∧
    (let m := lowerValue y (fun _ => 1) (β/α) kL.val
     (∀ i : Fin n, i.val < kL.val → y i < m) ∧
     (∀ i : Fin n, kL.val ≤ i.val → m ≤ y i) ∧
     ∀ u : Fin n → ℝ, normBox (β/α) u →
       ratio y (fun _ => 1) u - m =
         (∑ i, (u i-lowerWeights (β/α) kL.val i)*(y i-m)) / (∑ i, u i) ∧
       (∀ i, 0 ≤ (u i-lowerWeights (β/α) kL.val i)*(y i-m)) ∧
       0 ≤ ratio y (fun _ => 1) u - m)

def T4Statement : Prop :=
  ∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j, 0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hαβ : α ≤ β) (hβ1 : β ≤ 1),
    ∃ kL kH : Fin J, lowerCut y mass (β/α) kL ∧ upperCut y mass (β/α) kH ∧
      IsLeast (attainable y mass α β) (lowerValue y mass (β/α) kL.val) ∧
      IsGreatest (attainable y mass α β) (upperValue y mass (β/α) kH.val) ∧
      lowerEndpoint y mass α β = lowerValue y mass (β/α) kL.val ∧
      upperEndpoint y mass α β = upperValue y mass (β/α) kH.val

end
end SAP.P025a
