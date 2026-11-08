import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def regressionMinimum {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℝ) (X : Matrix I K ℝ) (Y : I → ℝ) (b : K → ℝ) : Prop :=
  ∀ c : K → ℝ, (∑ i, w i*(Y i-X.mulVec b i)^2)≤
    (∑ i, w i*(Y i-X.mulVec c i)^2)

noncomputable def regressionMap {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    (w : I → ℝ) (X : Matrix I K ℝ) : Matrix K I ℝ :=
  (X.transpose*Matrix.diagonal w*X)⁻¹*X.transpose*Matrix.diagonal w

def pooledExposureRow {I : Type*} {p : ℕ} (D : I → Fin 4)
    (x : I → Fin p → ℝ) : Matrix I (Fin (4+p)) ℝ := fun i j =>
  if h : j.val<4 then (if D i=⟨j.val,h⟩ then 1 else 0)
  else x i ⟨j.val-4, by omega⟩

def separateExposureRow {I : Type*} {p : ℕ} (x : I → Fin p → ℝ)
    : Matrix I (Fin (1+p)) ℝ := fun i j =>
  if h : j.val=0 then 1 else x i ⟨j.val-1, by omega⟩

noncomputable def augmentedExposureMean {I : Type*} [Fintype I]
    (D : I → Fin 4) (w Y fitted : I → ℝ) (k : Fin 4) : ℝ :=
  (∑ i, ((if D i=k then w i*(Y i-fitted i) else 0)+fitted i))/(Fintype.card I:ℝ)

def RegressionMeanIdentities(I : Type*) [Fintype I] : Prop :=
  ∀ {p : ℕ} (hI : 0<Fintype.card I) (D : I → Fin 4)
    (w Y : I → ℝ) (hw : ∀ i, 0<w i) (x : I → Fin p → ℝ)
    (b : Fin (4+p) → ℝ) (s : Fin 4 → Fin (1+p) → ℝ)
    (hpooled : Function.Injective (Matrix.mulVec (pooledExposureRow D x)))
    (hseparate : ∀ k, Function.Injective
      (fun v => fun i : {i : I // D i=k} => (Matrix.mulVec (separateExposureRow x)) v i.val))
    (hb : regressionMinimum w (pooledExposureRow D x) Y b)
    (hs : ∀ k, regressionMinimum (fun i => if D i=k then w i else 0)
      (separateExposureRow x) Y (s k)),
    let pooledPred := fun k i => b (k.castAdd p) + ∑ j, x i j*b ⟨4+j.val, by omega⟩
    let separatePred := fun k i => s k ⟨0, by omega⟩+
      ∑ j, x i j*s k ⟨1+j.val, by omega⟩
    (∀ k, (∑ i, if D i=k then w i*(Y i-pooledPred k i) else 0)=0 ∧
      (∑ i, if D i=k then w i*(Y i-separatePred k i) else 0)=0) ∧
    (∀ k, augmentedExposureMean D w Y (pooledPred k) k=
      (∑ i, pooledPred k i)/(Fintype.card I:ℝ) ∧
      augmentedExposureMean D w Y (separatePred k) k=
        (∑ i, separatePred k i)/(Fintype.card I:ℝ)) ∧
    (∀ k l, ((∑ i, pooledPred k i)/(Fintype.card I:ℝ))-
      ((∑ i, pooledPred l i)/(Fintype.card I:ℝ))=b (k.castAdd p)-b (l.castAdd p))

def OneCovariateFormulas(I : Type*) [Fintype I] : Prop :=
  ∀ (hI : 0<Fintype.card I) (D : I → Fin 4) (w x Y : I → ℝ)
    (hw : ∀ i, 0<w i),
    let W := fun k => ∑ i, if D i=k then w i else 0
    let xb := fun k => (∑ i, if D i=k then w i*x i else 0)/W k
    let yb := fun k => (∑ i, if D i=k then w i*Y i else 0)/W k
    let Sxx := fun k => ∑ i, if D i=k then w i*(x i-xb k)^2 else 0
    let Sxy := fun k => ∑ i, if D i=k then w i*(x i-xb k)*(Y i-yb k) else 0
    let bk := fun k => Sxy k/Sxx k
    let beta := (∑ k : Fin 4, Sxy k)/(∑ k : Fin 4, Sxx k)
    let xbar := (∑ i, x i)/(Fintype.card I:ℝ)
    (∀ k, 0<Sxx k) →
      (∀ k c, regressionMinimum (fun i => if D i=k then w i else 0)
        (fun i => ![1,x i]) Y c ↔ c=![yb k-bk k*xb k,bk k]) ∧
      (∀ c, regressionMinimum w (pooledExposureRow D (fun i => ![x i])) Y c ↔
        c=![yb 0-beta*xb 0,yb 1-beta*xb 1,yb 2-beta*xb 2,yb 3-beta*xb 3,beta]) ∧
      (∀ k, (yb k-bk k*xb k+bk k*xbar)-(yb k-beta*xb k+beta*xbar)=
        (bk k-beta)*(xbar-xb k))

/-- Averaging predictions averages each fixed covariate over the same population. -/
def PredictionMeanIdentity (I : Type*) [Fintype I] : Prop :=
  ∀ {p : ℕ} (hI : 0<Fintype.card I) (α : Fin 4 → ℝ)
    (β : Fin p → ℝ) (x : I → Fin p → ℝ) (k : Fin 4),
    (∑ i, (α k+∑ j, x i j*β j))/(Fintype.card I:ℝ)=
      α k+∑ j, ((∑ i, x i j)/(Fintype.card I:ℝ))*β j

/-- Joint and separate WLS means, coefficient formulas, and equality characterization. -/
def T28Statement (I : Type*) [Fintype I] : Prop :=
  RegressionMeanIdentities I ∧ OneCovariateFormulas I ∧
  (∀ yb bk beta xb xbar : ℝ,
    (yb-bk*xb+bk*xbar)-(yb-beta*xb+beta*xbar)=(bk-beta)*(xbar-xb)) ∧
  PredictionMeanIdentity I ∧
  (∀ yb bk beta xb xbar : ℝ,
    ((yb-bk*xb+bk*xbar)=(yb-beta*xb+beta*xbar) ↔ bk=beta ∨ xbar=xb)) ∧
  ((2-5/4:ℝ)*(5/2-4)=-9/8 ∧ (5:ℝ)-49/8=-9/8)

end SAP.P037c
