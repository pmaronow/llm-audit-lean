import SAP.P011b.Defs.Part9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

def integerPrograms {n : ℕ} (hn : 0 < n) (R : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) : Prop :=
  (∀ A, ProgramFeasible R d A ↔ Compatible R d A) ∧
  (∀ A, Maximizes R d (fun B => quadratic (adjacency B) (centered x)) A ↔
    Maximizes R d (fun B => V1 B x) A) ∧
  (∀ A, (n : ℝ)^2*V1 A x = (n : ℝ)*sampleVariance x+quadratic (adjacency A) (centered x)) ∧
  (∀ A, Maximizes R d (fun B => ∑ i, ∑ j, adjacency B i j) A → Maximizes R d (fun B => V2 B x) A) ∧
  (0 < sampleVariance x → ∀ A, Maximizes R d (fun B => V2 B x) A →
    Maximizes R d (fun B => ∑ i, ∑ j, adjacency B i j) A)

def sharpOracleBound {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (f : Graph n → ℝ) : Prop :=
  (∃ A, Maximizes R d f A) ∧
  (∀ A, Maximizes R d f A → f G ≤ f A ∧ (Maximizes R d f G → f G=f A))

def T27Statement {n : ℕ} (hn : 0 < n) (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (x : Fin n → ℝ) : Prop :=
  {A : Graph n | Compatible R d A}.Finite ∧
  {A : Graph n | Compatible R d A}.Nonempty ∧
  (∀ f : Graph n → ℝ, sharpOracleBound R G d hv f) ∧
  integerPrograms hn R d x ∧ T22Statement hn

def T28Statement {n : ℕ} (hn : 0 < n) (R G A : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (x : Fin n → ℝ)
    (hm : Maximizes R d (fun B => V2 B x) A) : Prop :=
  V2 G x ≤ V2 A x ∧ V2 A x ≤ V2prime d x ∧
  ((∀ i, degree A i = truncatedDegree d i) → V2 A x=V2prime d x)

end
end SAP.P011b
