import Mathlib
import SAP.P016a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016a
open scoped BigOperators
open Finset

def T6Statement : Prop :=
  (∀ {n : ℕ} (hn : 2 ≤ n)
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (assign : Ω → Assignment n)
    (Γ : Fin n → Fin n → ℝ) (hΓ : IsDistanceMatrix Γ) (g : Outcome n → Outcome n)
    (hg : ∀ ω, sampleVariance (g (exposureSum Γ (assign ω))) = 1)
    (y0 : Outcome n) (y : Ω → Outcome n) (b1 b2 : ℝ)
    (hy : ∀ ω i, y ω i = y0 i+b1*bit (assign ω i)+b2*g (exposureSum Γ (assign ω)) i),
    ∀ ω, applicationAdjust (y ω) (assign ω) (g (exposureSum Γ (assign ω))) b1 b2 = y0)
  ∧ (∀ (p : ℝ),
    printedReject p ↔ p < 1/20)

def T7Statement : Prop :=
  (Function.Injective complete4 ∧
    ∀ z : Assignment 4, groupSize z true = 2 ↔ ∃ k, complete4 k = z)
  ∧ ((∀ k : Fin 6, meanDifference u4 (complete4 k) = (![-2,-1,0,0,1,2] : Fin 6 → ℝ) k ∧
      meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k) =
        (![8,9,10,10,11,12] : Fin 6 → ℝ) k ∧
      mass (uniformLaw (Fin 6)) (fun j => |meanDifference u4 (complete4 j)| ≥
        |meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)|) = 0 ∧
      mass (uniformLaw (Fin 6)) (fun j => meanDifference u4 (complete4 j) ≥
        meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)) = 0 ∧
      mass (uniformLaw (Fin 6)) (fun j => |meanDifference u4 (complete4 j)| ≥
        |meanDifference u4 (complete4 k)|) = (![1/3,2/3,1,1,2/3,1/3] : Fin 6 → ℝ) k))
  ∧ (∀ (α : ℝ) (hα : 0 < α),
    mass (uniformLaw (Fin 6)) (fun k =>
      mass (uniformLaw (Fin 6)) (fun j => |meanDifference u4 (complete4 j)| ≥
        |meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)|) < α) = 1)
  ∧ (∀ (α : ℝ), 0 < α →
    mass (uniformLaw (Fin 6)) (fun k =>
      mass (uniformLaw (Fin 6)) (fun j => meanDifference u4 (complete4 j) ≥
        meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)) < α) = 1)
  ∧ (∀ k : Fin 6, additiveAdjust (additiveGenerate u4 (complete4 k) 10) (complete4 k) 10 = u4)
  ∧ (let y : Outcome 8 := fun i => i.val
    let sp := fun z : Balanced 8 4 => signedKS y z.val
    let dp := fun z : Balanced 8 4 => ks y z.val
    Fintype.card (Balanced 8 4) = 70 ∧
    (∀ z : Balanced 8 4,
      additiveAdjust (additiveGenerate y z.val (-100)) z.val (-100) = y ∧
      signedKS (additiveGenerate y z.val (-100)) z.val = 1 ∧
      ks (additiveGenerate y z.val (-100)) z.val = 1) ∧
    uniformMass (Balanced 8 4) (fun z => 1 ≤ sp z) = 1/70 ∧
    uniformMass (Balanced 8 4) (fun z => 1 ≤ dp z) = 1/35 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w => sp z ≤ sp w) < 1/20) = 1/70 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w => dp z ≤ dp w) < 1/20) = 1/35 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w =>
        signedKS (additiveGenerate y z.val (-100)) z.val ≤ sp w) < 1/20) = 1 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w =>
        ks (additiveGenerate y z.val (-100)) z.val ≤ dp w) < 1/20) = 1)
  ∧ (∀ (z : Balanced 8 4) (i j : Fin 8), z.val i = true → z.val j = false →
    additiveGenerate (fun k : Fin 8 => (k.val : ℝ)) z.val (-100) i <
      additiveGenerate (fun k : Fin 8 => (k.val : ℝ)) z.val (-100) j)
  ∧ ((1/70 : ℝ) < 1/20 ∧ (1/35 : ℝ) < 1/20)

def T8Statement : Prop :=
  (∀ {n : ℕ} (y : Outcome n) (z : Assignment n) (t t0 : ℝ),
    additiveAdjust (additiveGenerate y z t) z t0 = additiveGenerate y z (t-t0) ∧
    additiveAdjust (additiveGenerate y z t) z t = y)
  ∧ (∀ {n : ℕ} {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (assign : Ω → Assignment n) (y0 : Outcome n) (t : ℝ)
    (T : Outcome n → Ω → ℝ) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1),
    (∀ E : ℝ → Prop,
      mass P (fun ω => E (T (additiveAdjust (additiveGenerate y0 (assign ω) t) (assign ω) t) ω)) =
      mass P (fun ω => E (T y0 ω))) ∧
    mass P (fun ω => upperP P (fun w => T
      (additiveAdjust (additiveGenerate y0 (assign ω) t) (assign ω) t) w) ω ≤ α) ≤ α)
  ∧ (∀ {n : ℕ} (Y : Outcome n) (z : Assignment n)
    (h0 : 0 < groupSize z false) (h1 : 0 < groupSize z true) (t : ℝ),
    meanDifference Y z = meanDifference (additiveAdjust Y z t) z + t ∧
    (meanDifference Y z = meanDifference (additiveAdjust Y z t) z ↔ t = 0))

end SAP.P016a
