import SAP.P011b.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

def correlationIdentity {n : ℕ} (hn : 0 < n) (m : Model n)
    (hdep : Dependency m) (hs : Homoskedastic m)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) : Prop :=
  (n : ℝ)*var m (betaHat m) = meanVariance m*
    (1+(∑ i, ∑ j, adjacency m.G i j*rho m i j)/n) ∧
  (∀ i j, rho m i j ≤ 1) ∧ (∀ y, V2star m y ≤ V2 m.G (weighted m y))

def pathCorrelations : Prop :=
  Homoskedastic (pathModel 0 1) ∧ Dependency (pathModel 0 1) ∧
  (∀ i, covariance (pathModel 0 1) i i=1) ∧
  rho (pathModel 0 1) 0 1=3/5 ∧ rho (pathModel 0 1) 1 2=4/5 ∧
  rho (pathModel 0 1) 0 2=0 ∧
  3*var (pathModel 0 1) (betaHat (pathModel 0 1))=29/15 ∧
  meanVariance (pathModel 0 1)*(1+
    (∑ i, ∑ j, adjacency (pathModel 0 1).G i j*rho (pathModel 0 1) i j)/3)=29/15

def T21Statement {n : ℕ} (hn : 0 < n) (m : Model n)
    (hdep : Dependency m) (hs : Homoskedastic m)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) : Prop :=
  correlationIdentity hn m hdep hs hL2 ∧ pathCorrelations

def T22Statement {n : ℕ} (hn : 0 < n) : Prop :=
  Function.Bijective (@fromUpper n) ∧
  (∀ a : Edge n → Bool, ∀ x : Fin n → ℝ,
    quadratic (adjacency (fromUpper a)) (centered x) =
      2*upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
  (∀ a : Edge n → Bool, ∀ i, degree (fromUpper a) i = upperDegree a i) ∧
  (∀ R : Graph n, ∀ d a, Compatible R d (fromUpper a) ↔
    (∀ e, toUpper R e = true → a e = true) ∧ ∀ i, upperDegree a i ≤ d i) ∧
  (∀ R : Graph n, ∀ d a x,
    Maximizes R d (fun B => V1 B x) (fromUpper a) ↔
    Compatible R d (fromUpper a) ∧
      ∀ b, Compatible R d (fromUpper b) →
        upperObjective b (fun e => centered x e.val.1*centered x e.val.2) ≤
        upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
  (∀ (a : Edge n → Bool) (x : Fin n → ℝ), (n : ℝ)^2*V1 (fromUpper a) x = (n : ℝ)*sampleVariance x+
    2*upperObjective a (fun e => centered x e.val.1*centered x e.val.2)) ∧
  (∀ a : Edge n → Bool, ∑ i, ∑ j, adjacency (fromUpper a) i j = 2*upperObjective a (fun _ => 1)) ∧
  Fintype.card (Edge n) = n*(n-1)/2

def variablesCounterexample : Prop :=
  average (![-2,1/2,3/2] : Fin 3 → ℝ) = 0 ∧
  (centered (![-2,1/2,3/2] : Fin 3 → ℝ) 0 * centered (![-2,1/2,3/2] : Fin 3 → ℝ) 1 = -1) ∧
  (centered (![-2,1/2,3/2] : Fin 3 → ℝ) 0 * centered (![-2,1/2,3/2] : Fin 3 → ℝ) 2 = -3) ∧
  (centered (![-2,1/2,3/2] : Fin 3 → ℝ) 1 * centered (![-2,1/2,3/2] : Fin 3 → ℝ) 2 = 3/4) ∧
  ¬ Compatible (emptyGraph 3) (fun _ => 1) (nonzeroRule (![-2,1/2,3/2] : Fin 3 → ℝ)) ∧
  Compatible (emptyGraph 3) (fun _ => 1) edge23 ∧
  upperSum (fun i j => centered (![-2,1/2,3/2] : Fin 3 → ℝ) i*
    centered (![-2,1/2,3/2] : Fin 3 → ℝ) j*adjacency edge23 i j) = 3/4 ∧
  ¬ Compatible edge12 (fun _ => 2) (nonzeroRule (![0,1,-1] : Fin 3 → ℝ))

def variablesOptimum (A : Graph 3) (hA : Compatible (emptyGraph 3) (fun _ => 1) A) : Prop :=
  upperSum (fun i j => centered (![-2,1/2,3/2] : Fin 3 → ℝ) i*
    centered (![-2,1/2,3/2] : Fin 3 → ℝ) j*adjacency A i j) ≤ 3/4 ∧
  (upperSum (fun i j => centered (![-2,1/2,3/2] : Fin 3 → ℝ) i*
    centered (![-2,1/2,3/2] : Fin 3 → ℝ) j*adjacency A i j) = 3/4 → A=edge23)

def variablesDetails : Prop :=
  (∀ e : Edge 3, toUpper (nonzeroRule (![-2,1/2,3/2] : Fin 3 → ℝ)) e=true) ∧
  (∀ i, degree (nonzeroRule (![-2,1/2,3/2] : Fin 3 → ℝ)) i=2) ∧
  average (![0,1,-1] : Fin 3 → ℝ)=0 ∧
  centered (![0,1,-1] : Fin 3 → ℝ) 0 * centered (![0,1,-1] : Fin 3 → ℝ) 1=0 ∧
  edge12.val 0 1=true ∧ (nonzeroRule (![0,1,-1] : Fin 3 → ℝ)).val 0 1=false

def T23Statement : Prop :=
  variablesCounterexample ∧ variablesDetails ∧
    ∀ A : Graph 3, ∀ hA : Compatible (emptyGraph 3) (fun _ => 1) A,
      variablesOptimum A hA

def T24Statement {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) : Prop :=
  (∀ A, ProgramFeasible R d A ↔ Compatible R d A) ∧ ProgramFeasible R d G

end
end SAP.P011b
