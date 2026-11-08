import SAP.P011b.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

def helperDenominators {n : ℕ} (hn : 1 < n) (A : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) : Prop :=
  V1R A x-V1 A x = (∑ i, centered x i^2)/((n : ℝ)^2*((n : ℝ)-1)) ∧
  V1R A x-V1 A x = sampleVariance x/((n : ℝ)*((n : ℝ)-1)) ∧
  V2R A x = (n : ℝ)/((n : ℝ)-1)*V2 A x ∧ V2primeR d x = (n : ℝ)/((n : ℝ)-1)*V2prime d x

def helperCorrection {n : ℕ} (hn : 1 < n) (R : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) : Prop :=
  (∀ A, V1 A x ≤ V1R A x ∧ V2 A x ≤ V2R A x) ∧ V2prime d x ≤ V2primeR d x ∧
  ((0 < ∑ i, centered x i^2) →
    (∀ A, V1 A x < V1R A x ∧ V2 A x < V2R A x) ∧ V2prime d x < V2primeR d x) ∧
  (∀ A, (Maximizes R d (fun B => V1R B x) A ↔ Maximizes R d (fun B => V1 B x) A) ∧
    (Maximizes R d (fun B => V2R B x) A ↔ Maximizes R d (fun B => V2 B x) A)) ∧
  (∀ β c : ℝ, (∀ i, |x i-β| ≤ c) → ∀ A,
    0 ≤ (n : ℝ)*(V1R A x-V1 A x) ∧ (n : ℝ)*(V1R A x-V1 A x) ≤ 4*c^2/((n : ℝ)-1)) ∧
  (∀ A, ((∑ i, centered x i^2)/(n : ℝ)^2+quadratic (adjacency A) (centered x)/(n : ℝ)^2) = V1 A x ∧
    ((∑ i, centered x i^2)/(n : ℝ)^2*(1+(∑ i, ∑ j, adjacency A i j)/n)) = V2 A x) ∧
  ((∑ i, centered x i^2)/(n : ℝ)^2*(1+(∑ i, (truncatedDegree d i : ℝ))/n)) = V2prime d x

def T25Statement {n : ℕ} (hn : 1 < n) (R : Graph n) (d : Fin n → ℕ)
    (x : Fin n → ℝ) : Prop :=
  helperCorrection hn R d x ∧ ∀ A : Graph n, helperDenominators hn A d x

def helperExamples : Prop :=
  (let x : Fin 3 → ℝ := ![0,1,2]
   Compatible (emptyGraph 3) (fun _ => 0) (emptyGraph 3) ∧
   average x=1 ∧ (∑ i, centered x i^2)=2 ∧
   V1 (emptyGraph 3) x=2/9 ∧ V2 (emptyGraph 3) x=2/9 ∧ V2prime (fun _ => 0) x=2/9 ∧
   V1R (emptyGraph 3) x=1/3 ∧ V2R (emptyGraph 3) x=1/3 ∧ V2primeR (fun _ => 0) x=1/3 ∧
   V1 (emptyGraph 3) x ≠ V1R (emptyGraph 3) x ∧
   V2 (emptyGraph 3) x ≠ V2R (emptyGraph 3) x ∧
   V2prime (fun _ => 0) x ≠ V2primeR (fun _ => 0) x) ∧
  (let x : Fin 3 → ℝ := ![0,0,3]
   let d : Fin 3 → ℕ := ![1,1,0]
   Compatible (emptyGraph 3) d edge12 ∧ average x=1 ∧ (∑ i, centered x i^2)=6 ∧
   V1 edge12 x=8/9 ∧ V2 edge12 x=10/9 ∧ V2prime d x=10/9 ∧
   V1R edge12 x=11/9 ∧ V2R edge12 x=5/3 ∧ V2primeR d x=5/3 ∧
   V1 edge12 x ≠ V1R edge12 x ∧ V2 edge12 x ≠ V2R edge12 x ∧
   V2prime d x ≠ V2primeR d x) ∧
  (let x : Fin 3 → ℝ := ![0,1,2]
   Compatible (emptyGraph 3) (fun _ => 2) (completeGraph 3) ∧
   V1 (completeGraph 3) x=0 ∧ V1R (completeGraph 3) x=1/9 ∧
   V1 (completeGraph 3) x ≠ V1R (completeGraph 3) x)

def threePointScaling : Prop :=
  Scaling threePointFamily 1 1 (2/3) 2 ∧ Valid threePointFamily ∧
  (∀ k, Homoskedastic (threePointFamily.model k) ∧ beta (threePointFamily.model k)=1 ∧
    scaledTrue threePointFamily k=2/3)

def threePointWitness : Prop :=
  beta (threePointModel 3)=1 ∧ 3*var (threePointModel 3) (betaHat (threePointModel 3))=2/3 ∧
  Homoskedastic (threePointModel 3) ∧ Dependency (threePointModel 3) ∧
  probability (threePointModel 3) {y | y=(![0,1,2] : Fin 3 → ℝ)}=1/27

def helperDetails : Prop :=
  (let x : Fin 3 → ℝ := ![0,1,2]
   quadratic (adjacency (emptyGraph 3)) (centered x)=0 ∧
   (∑ i : Fin 3, ∑ j : Fin 3, adjacency (emptyGraph 3) i j)=0 ∧
   (∑ i : Fin 3, (truncatedDegree (fun _ => 0) i : ℝ))=0) ∧
  (let x : Fin 3 → ℝ := ![0,0,3]
   let d : Fin 3 → ℕ := ![1,1,0]
   centered x=(![-1,-1,2] : Fin 3 → ℝ) ∧
   quadratic (adjacency edge12) (centered x)=2 ∧
   (∑ i : Fin 3, ∑ j : Fin 3, adjacency edge12 i j)=2 ∧
   (∑ i : Fin 3, (truncatedDegree d i : ℝ))=2 ∧
   V1R edge12 x / V1 edge12 x=11/8 ∧
   V2R edge12 x / V2 edge12 x=3/2 ∧
   V2primeR d x / V2prime d x=3/2) ∧
  (let x : Fin 3 → ℝ := ![0,1,2]
   quadratic (adjacency (completeGraph 3)) (centered x)= -2 ∧
   ∀ C : ℝ, C*V1 (completeGraph 3) x < V1R (completeGraph 3) x)

def T26Statement : Prop := helperExamples ∧ threePointScaling ∧ threePointWitness ∧ helperDetails

end
end SAP.P011b
