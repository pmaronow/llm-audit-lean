import SAP.P016b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators Classical
noncomputable section

def T20Statement : Prop :=
  (∀ (y0 y1 Y τ : ℝ) (z : Bool),
    Y = bit z*y1+(1-bit z)*y0 → y1 = y0+τ → y0 = Y-bit z*τ) ∧
  (∀ (n : ℕ) (y : Outcome n) (z : Assignment n) (t t0 : ℝ),
    additiveAdjust (additiveGenerate y z t) z t0 = additiveGenerate y z (t-t0) ∧
    additiveAdjust (additiveGenerate y z t) z t = y) ∧
  (∀ (n : ℕ) (S : Fin n → Fin n → ℝ), (∀ i j, 0 ≤ S i j) →
    ∀ (β τ : ℝ), 0 < β →
    (∀ (v : Assignment n) (i : Fin n), 0 < modelMultiplier S β τ v i) ∧
    (∀ (y : Outcome n) (z : Assignment n),
      (∀ i, modelMultiplier S β τ (fun _ => false) i = 1) ∧
      modelMap S β τ y z (fun _ => false) = fun i => y i/modelMultiplier S β τ z i) ∧
    (∀ (y : Outcome n) (z w w' : Assignment n),
      modelMap S β τ y z z = y ∧
      modelMap S β τ (modelMap S β τ y z w) w w' = modelMap S β τ y z w') ∧
    (∀ (y0 : Outcome n) (y : Assignment n → Outcome n),
      (∀ z i, y z i = modelMultiplier S β τ z i*y0 i) →
      ∀ z, (fun i => y z i/modelMultiplier S β τ z i) = y0))

def T21Statement : Prop :=
  ∀ (P : FiniteLaw (Balanced 256 128)),
    (∀ z, P.weight z = 1/(Nat.choose 256 128 : ℝ)) →
    ∀ (S : Fin 256 → Fin 256 → ℝ), (∀ i j, S i j = S j i) →
    (∀ i j, S i j = 0 ∨ S i j = 1) →
    ∀ (y0 : Outcome 256) (T : Outcome 256 → Assignment 256 → ℝ),
    let Y := fun z : Balanced 256 128 => fun i => modelMultiplier S 2 (1/2) z.val i*y0 i
    let u := fun z : Balanced 256 128 => fun i => Y z i/modelMultiplier S 2 (1/2) z.val i
    let s := fun z : Balanced 256 128 => T (u z) z.val
    (∀ z, u z = y0) ∧
    (∀ p ∈ ({upperP P s,lowerP P s,fun z => doubledP (lowerP P s z) (upperP P s z)} :
      Finset (Balanced 256 128 → ℝ)),
      mass P (fun z => p z ≤ 1/20) ≤ 1/20 ∧ mass P (fun z => p z < 1/20) ≤ 1/20) ∧
    iidMass P 1001 (fun draw => rawP (fun b : Fin 1000 => s (draw b.succ)) (s (draw 0)) < 1/20) ≤
      50/1001 ∧ (50/1001 : ℝ) < 1/20 ∧
    iidMass P 10001 (fun draw => rawP (fun b : Fin 10000 => s (draw b.succ)) (s (draw 0)) < 1/20) ≤
      500/10001 ∧ (500/10001 : ℝ) < 1/20

end
end SAP.P016b
