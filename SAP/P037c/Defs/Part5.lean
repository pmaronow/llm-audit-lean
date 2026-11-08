import Mathlib
import SAP.P037c.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def SameControlCertificate(Ω : Type*) [Fintype Ω] : Prop :=
  ∀ {n p : ℕ} (hn : 0<n) (D0 : Fin n → Fin 4) (D : Ω → Fin n → Fin 4)
    (C : Matrix (Fin n) (Fin p) ℝ) (w0 : Fin n → ℝ) (w : Ω → Fin n → ℝ)
    (hw0 : ∀ i, 0<w0 i) (hw : ∀ z i, 0<w z i)
    (hX0 : Function.Injective (Matrix.mulVec (pooledExposureRow D0 C)))
    (hX : ∀ z, Function.Injective (Matrix.mulVec (pooledExposureRow (D z) C)))
    (y : Fin n → ℝ) (prob : Ω → ℝ) (hp : ∀ z, 0≤prob z) (ht : ∑ z, prob z=1),
    let b0 := (regressionMap w0 (pooledExposureRow D0 C)).mulVec y
    let row := fun k => pooledExposureRow (fun _ : Unit => k)
      (fun _ j => (∑ i, C i j)/(n:ℝ)) ()
    let m := fun k => dotProduct (row k) b0
    let residual := y-(Matrix.mulVec (pooledExposureRow D0 C)) b0
    let imputed := fun z i => y i+m (D z i)-m (D0 i)
    let L := fun z => regressionMap (w z) (pooledExposureRow (D z) C)
    (∀ k l, m k-m l=b0 (k.castAdd p)-b0 (l.castAdd p)) ∧
    (∀ z, (L z*pooledExposureRow (D z) C)=1 ∧
      (L z).mulVec (imputed z)=(L z).mulVec residual+b0) ∧
    (∀ z k, dotProduct (row k) ((L z).mulVec (imputed z))=
      dotProduct (row k) ((L z).mulVec residual)+m k) ∧
    (∀ k l,
      (let a := fun z => dotProduct (row k-row l) ((L z).mulVec (imputed z))
       let b := fun z => dotProduct (row k-row l) ((L z).mulVec residual)
       (∑ z, prob z*(a z)^2)-(∑ z, prob z*a z)^2=
       (∑ z, prob z*(b z)^2)-(∑ z, prob z*b z)^2))

def SameControlExtra(Ω : Type*) [Fintype Ω] : Prop :=
  ∀ {n p : ℕ} (hn : 0<n) (D0 : Fin n → Fin 4) (D : Ω → Fin n → Fin 4)
    (C : Matrix (Fin n) (Fin p) ℝ) (w0 : Fin n → ℝ) (w : Ω → Fin n → ℝ)
    (hw0 : ∀ i, 0<w0 i) (hw : ∀ z i, 0<w z i)
    (hX0 : Function.Injective (Matrix.mulVec (pooledExposureRow D0 C)))
    (hX : ∀ z, Function.Injective (Matrix.mulVec (pooledExposureRow (D z) C)))
    (y : Fin n → ℝ) (prob : Ω → ℝ) (hp : ∀ z, 0≤prob z) (ht : ∑ z, prob z=1),
    let b0 := (regressionMap w0 (pooledExposureRow D0 C)).mulVec y
    let row := fun k => pooledExposureRow (fun _ : Unit => k)
      (fun _ j => (∑ i, C i j)/(n:ℝ)) ()
    let m := fun k => dotProduct (row k) b0
    let residual := y-(Matrix.mulVec (pooledExposureRow D0 C)) b0
    let imputed := fun z i => y i+m (D z i)-m (D0 i)
    let L := fun z => regressionMap (w z) (pooledExposureRow (D z) C)
    (∀ z i, imputed z i=y i-b0 ((D0 i).castAdd p)+b0 ((D z i).castAdd p)) ∧
    (∀ z, imputed z=residual+(pooledExposureRow (D z) C).mulVec b0) ∧
    (∀ k,
      let a := fun z => dotProduct (row k) ((L z).mulVec (imputed z))
      let b := fun z => dotProduct (row k) ((L z).mulVec residual)
      (∑ z, prob z*(a z)^2)-(∑ z, prob z*a z)^2=
      (∑ z, prob z*(b z)^2)-(∑ z, prob z*b z)^2)

/-- Residual refits and constant-effect imputation agree with fixed controls. -/
def T34Statement (Ω : Type*) [Fintype Ω] : Prop :=
  SameControlCertificate Ω ∧ SameControlExtra Ω

end SAP.P037c
