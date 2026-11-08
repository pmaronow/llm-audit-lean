import SAP.P002a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

def T1Finite : Prop :=
    let P := negativeDeltaModel 1
    Theta P.pop (-1/2) (1/6) 2 ∧ Xi P (-1/2) (1/2) 2 2 (1/6) ∧
    late P.pop = 0 ∧ (assignments P.pop).card = 66 ∧
    S2 P.pop 0 true = 25/1188 ∧ S2 P.pop 0 false = 25/1188 ∧
    designVariance P.pop (tau P.pop 0) = 5/396 ∧
    designVariance P.pop (oracleTau P 0) = 36/55 ∧
    designVariance P.pop (tau P.pop 0) <
      (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*S2 P.pop 0 true +
        2/(12*controlSize P.pop)*S2 P.pop 0 false) ∧
    designVariance P.pop (oracleTau P 0) <
      (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*popVar (residual P true 0) +
        2/(12*controlSize P.pop)*popVar (residual P false 0))

def T1Sequence : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m),
    let P := negativeDeltaModel m
    Theta P.pop (-1/2) (1/6) 2 ∧ Xi P (-1/2) (1/2) 2 2 (1/6) ∧
    late P.pop = 0 ∧
    designVariance P.pop (tau P.pop 0) = 5/(36*(((12*m : ℕ) : ℝ)-1)) ∧
    designVariance P.pop (oracleTau P 0) = 36/(5*((12*m : ℕ) : ℝ)-5) ∧
    (1-(-1/2 : ℝ))*(controlSize P.pop/(((12*m : ℕ) : ℝ)*(P.pop.n1 : ℝ))*
        S2 P.pop 0 true +
      (P.pop.n1 : ℝ)/(((12*m : ℕ) : ℝ)*controlSize P.pop)*S2 P.pop 0 false) =
      (13/12)*designVariance P.pop (tau P.pop 0) ∧
    (1-(-1/2 : ℝ))*(controlSize P.pop/(((12*m : ℕ) : ℝ)*(P.pop.n1 : ℝ))*
        popVar (residual P true 0) +
      (P.pop.n1 : ℝ)/(((12*m : ℕ) : ℝ)*controlSize P.pop)*popVar (residual P false 0)) =
      (13/12)*designVariance P.pop (oracleTau P 0)

def T1Arithmetic : Prop :=
  (12/11 : ℝ)+12/11+2*(-1/2)*12/11=12/11 ∧
    (12/11 : ℝ)+12/11+(-1/2)*(10/2)*(12/11)+(-1/2)*(2/10)*(12/11)= -36/55 ∧
    ¬((12/11 : ℝ) ≤ -36/55)

def T1Statement : Prop :=
  T1Finite ∧ T1Sequence ∧ T1Arithmetic ∧ ∀ a : Bool, psi (negativeDeltaModel 1) a 0 = 0

def T2Raw : Prop :=
  ∀ {n : ℕ} (P : Population n) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hP : Theta P δ r A),
  (1-max δ 0) * (controlSize P/((n : ℝ)*(P.n1 : ℝ))*S2 P (late P) true +
      (P.n1 : ℝ)/((n : ℝ)*controlSize P)*S2 P (late P) false) ≤
      designVariance P (tau P (late P))

def T2Adjusted : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : Xi P δ e A B r),
  (1-max δ 0) * (controlSize P.pop/((n : ℝ)*(P.pop.n1 : ℝ))*
      popVar (residual P true (late P.pop)) +
      (P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop)*popVar (residual P false (late P.pop))) ≤
      designVariance P.pop (oracleTau P (late P.pop))

def T2Statement : Prop := T2Raw ∧ T2Adjusted

def PrintedLemma5 : Prop :=
  ∀ {n : ℕ} (P : Population n) (δ r A : ℝ),
    δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → Theta P δ r A →
    (1-δ) * (controlSize P/((n : ℝ)*(P.n1 : ℝ))*S2 P (late P) true +
      (P.n1 : ℝ)/((n : ℝ)*controlSize P)*S2 P (late P) false) ≤
      designVariance P (tau P (late P))

def PrintedE10 : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → Xi P δ e A B r →
    (1-δ) * (controlSize P.pop/((n : ℝ)*(P.pop.n1 : ℝ))*
      popVar (residual P true (late P.pop)) +
      (P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop)*popVar (residual P false (late P.pop))) ≤
      designVariance P.pop (oracleTau P (late P.pop))

def T3Statement : Prop := ¬ PrintedLemma5 ∧ ¬ PrintedE10

end
end SAP.P002a
