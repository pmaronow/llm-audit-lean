import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure FiniteDesign (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ w, 0 ≤ weight w
  total : ∑ w, weight w = 1

noncomputable def designMean {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) : ℝ := ∑ w, d.weight w * X w

noncomputable def inner {I : Type*} [Fintype I] (x y : I → ℝ) : ℝ :=
  ∑ i, x i * y i

noncomputable def cross {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y : Ω → I → ℝ) : ℝ :=
  designMean d (fun w => inner (x w) (y w))

noncomputable def treatmentProjection {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) : ℝ := cross d z t / cross d t t

noncomputable def residual {Ω I K : Type*} [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) (V : K → I → ℝ)
    (lam : K → ℝ) (p : ℝ) : Ω → I → ℝ := fun w i =>
  z w i - treatmentProjection d t z * t w i - p * ∑ k, lam k * V k i

def NormalEquations {Ω I K : Type*} [Fintype Ω] [Fintype I] [Fintype K]
    (d : FiniteDesign Ω) (t z : Ω → I → ℝ) (V : K → I → ℝ)
    (Y : Ω → I → ℝ) (τ : ℝ) (g : K → ℝ) (b : ℝ) : Prop :=
  let e := fun w i => Y w i - (τ * t w i + (∑ k, g k * V k i) + b * z w i)
  cross d t e = 0 ∧ (∀ k, cross d (fun _ => V k) e = 0) ∧ cross d z e = 0

noncomputable def blockDemean {B : ℕ} (x : (Fin B × Fin 4) → ℝ) :
    (Fin B × Fin 4) → ℝ := fun i => x i - (1/4:ℝ) * ∑ j, x (i.1,j)

noncomputable def blockResidual {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : FiniteDesign Ω) (T C : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (lam : K → ℝ) (p : ℝ) :=
  residual d (fun w => blockDemean (T w))
    (fun w => blockDemean (fun i => T w i * C w i))
    (fun k => blockDemean (X k)) lam p

def BlockModelBiasStatement(Ω K : Type*) [Fintype Ω] [Fintype K] : Prop :=
  ∀ {B : ℕ}
    (d : FiniteDesign Ω) (T C Y : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (a η μ : (Fin B × Fin 4) → ℝ)
    (lam : K → ℝ) (p τ₀ β τ b : ℝ) (g : K → ℝ)
    (hT : ∀ i, designMean d (fun w => T w i) = p)
    (hTC : ∀ i, designMean d (fun w => T w i * C w i) = p * μ i)
    (hspan : ∀ i, blockDemean μ i = ∑ k, lam k * blockDemean (X k) i)
    (hY : ∀ w i, Y w i = a i + T w i * (τ₀ + η i + β * C w i))
    (htt : cross d (fun w => blockDemean (T w)) (fun w => blockDemean (T w)) ≠ 0)
    (hK : 0 < cross d
      (residual d (fun w => blockDemean (T w))
        (fun w => blockDemean (fun i => T w i * C w i))
        (fun k => blockDemean (X k)) lam p)
      (residual d (fun w => blockDemean (T w))
        (fun w => blockDemean (fun i => T w i * C w i))
        (fun k => blockDemean (X k)) lam p))
    (hN : NormalEquations d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) (fun w => blockDemean (Y w)) τ g b),
    let r := residual d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) lam p
    b - β = cross d r (fun w i => T w i * η i) / cross d r r

def CommonInterceptStatement(Ω K : Type*) [Fintype Ω] [Fintype K] : Prop :=
  ∀ {B : ℕ}
    (d : FiniteDesign Ω) (T C Y : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (a μ : (Fin B × Fin 4) → ℝ)
    (lam : K → ℝ) (p τ₀ β τ b : ℝ) (g : K → ℝ)
    (hT : ∀ i, designMean d (fun w => T w i) = p)
    (hTC : ∀ i, designMean d (fun w => T w i * C w i) = p * μ i)
    (hspan : ∀ i, blockDemean μ i = ∑ k, lam k * blockDemean (X k) i)
    (hY : ∀ w i, Y w i = a i + T w i * (τ₀ + β * C w i))
    (htt : cross d (fun w => blockDemean (T w)) (fun w => blockDemean (T w)) ≠ 0)
    (hK : 0 < cross d (blockResidual d T C X lam p) (blockResidual d T C X lam p))
    (hN : NormalEquations d (fun w => blockDemean (T w))
      (fun w => blockDemean (fun i => T w i * C w i))
      (fun k => blockDemean (X k)) (fun w => blockDemean (Y w)) τ g b),
    b = β

/-- Expected-normal-equation bias and the common-intercept slope corollary. -/
def T43Statement (Ω K : Type*) [Fintype Ω] [Fintype K] : Prop :=
  BlockModelBiasStatement Ω K ∧ CommonInterceptStatement Ω K

end SAP.P037c
