import Mathlib
import SAP.P011a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

def signFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => signModel (k+1)

def alternatingWeight (n : ℕ) : ℝ := (n : ℝ) / (2 * (((n+1)/2 : ℕ) : ℝ))

def alternatingOutcome (n : ℕ) (u : Fin n → Bool) : Fin n → ℝ :=
  fun i => (if i.val % 2 = 0 then 2 else 0) + sign (u i)

def alternatingModel (n : ℕ) : Model n where
  law := uniformLaw (alternatingOutcome n)
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => alternatingWeight n
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

def alternatingFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => alternatingModel (k+1)

def scaledTrue (F : Family) (k : ℕ) : ℝ := (F.size k : ℝ) * var (F.model k) (betaHat (F.model k))

def scaledOracle (F : Family) (k : ℕ) (y : Fin (F.size k) → ℝ) : ℝ :=
  (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y)

def meanVariance {n : ℕ} (m : Model n) : ℝ := (∑ i, covariance m i i) / n

def CliqueUnion {n : ℕ} (A : Graph n) : Prop :=
  ∀ i j k, (i=j ∨ A.val i j = true) → (j=k ∨ A.val j k = true) →
    i=k ∨ A.val i k = true

def centeringMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (1/(n : ℝ)) • (fun _ _ => 1)

def dataMatrix {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => x i*x j/n

def upperSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j with i < j, f i j

def maxAbs {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (Finset.univ.sup (fun i => (⟨|x i|, abs_nonneg (x i)⟩ : ℝ≥0)) : ℝ≥0)

def frobeniusSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, M i j^2

def cycleMajorantDifference : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![17/20,-1/4,1/4,-17/20], ![-1/4,3/20,-3/20,1/4],
    ![1/4,-3/20,3/20,-1/4], ![-17/20,1/4,-1/4,17/20]]

def CorrectedClass (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  (Valid F ∧ ((V = fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) ∨
    (V = fun k y => VYoung (F.model k).d (weighted (F.model k) y)) ∨
    (∃ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V1plus (F.model k).d B (weighted (F.model k) y)) (A k y)) ∧
      ((V = fun k y => V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∨
       (V = fun k y => min (V1plus (F.model k).d (A k y) (weighted (F.model k) y))
         (VYoung (F.model k).d (weighted (F.model k) y))))))) ∨
  (V = fun k y => VPositive (F.model k).G (weighted (F.model k) y)) ∨
  (Valid F ∧ (∀ k, (F.model k).R = emptyGraph (F.size k)) ∧
    ∃ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V1 B (weighted (F.model k) y)) (A k y)) ∧
      V = fun k y => V1 (A k y) (weighted (F.model k) y)) ∨
  (Valid F ∧ 0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop ∧
    ((V = fun k y => V1 (F.model k).G (weighted (F.model k) y)) ∨
      (∃ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => V1 B (weighted (F.model k) y)) (A k y)) ∧
        V = fun k y => V1 (A k y) (weighted (F.model k) y))))

def Tight (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
    probability (F.model k) {y | |T k y| > B} ≤ ε

def MeanModel {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ) : Prop :=
  (∀ i, Integrable (fun y => y i) m.law) ∧
  ∀ i, expectation m (fun y => y i) = (D *ᵥ γ) i

def trueResidual {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (γ : Fin p → ℝ) (y : Fin n → ℝ) : Fin n → ℝ := fun i => m.theta i*(y i-(D *ᵥ γ) i)

def fittedResidual {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (γhat : (Fin n → ℝ) → (Fin p → ℝ)) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => m.theta i*(y i-(D *ᵥ (γhat y)) i)

def VResidual {n : ℕ} (A : Graph n) (r : Fin n → ℝ) : ℝ := quadratic (oracleMatrix A) r/(n : ℝ)^2

def U {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  (∑ i, (weighted m y i-beta m)^2)/n

def gFactor {n : ℕ} (m : Model n) : ℝ := 1+(∑ i, ∑ j, adjacency m.G i j)/n

def varianceRemainder {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  sampleVariance (weighted m y)-meanVariance m-meanSpread m

def ols {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : Fin p → ℝ :=
  (Dᵀ*D)⁻¹ *ᵥ (Dᵀ *ᵥ y)

def unstableModel (blocks : ℕ) : Model (4*blocks) where
  law := uniformLaw (fun u : Fin (4*blocks) → Bool => fun i =>
    (if i.val%2=0 then 1 else (4*blocks : ℝ))*sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun i => 2*(![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
  G := emptyGraph (4*blocks)
  R := emptyGraph (4*blocks)
  d := fun _ => 0

def unstableFamily : Family where
  size := fun k => 4*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => unstableModel (k+1)

def fixedMeanModel (a b : ℝ) (s : ℕ → Bool) (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Bool => fun i => a*sign (s i.val)+b*sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

def mixtureModel (a b : ℝ) (n : ℕ) : Model n where
  law := uniformLaw (fun u : (Fin n → Bool) × (Fin n → Bool) =>
    fun i => a*sign (u.1 i)+b*sign (u.2 i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

def fixedMeanFamily (a b : ℝ) (s : ℕ → Bool) : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => fixedMeanModel a b s (k+1)

def mixtureFamily (a b : ℝ) : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => mixtureModel a b (k+1)

abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

structure DegreeProblem (n : ℕ) where
  forced : Finset (Edge n)
  cap : Fin n → ℕ
  weight : Edge n → ℚ

def edgeDegree {n : ℕ} (S : Finset (Edge n)) (i : Fin n) : ℕ :=
  (S.filter (fun e => e.val.1=i ∨ e.val.2=i)).card

def EdgeFeasible {n : ℕ} (P : DegreeProblem n) (S : Finset (Edge n)) : Prop :=
  P.forced ⊆ S ∧ ∀ i, edgeDegree S i ≤ P.cap i

def edgeObjective {n : ℕ} (P : DegreeProblem n) (S : Finset (Edge n)) : ℚ := ∑ e ∈ S, P.weight e

def remainingCap {n : ℕ} (P : DegreeProblem n) (i : Fin n) : ℕ :=
  min (P.cap i) (n-1)-edgeDegree P.forced i

def optionalEdges {n : ℕ} (P : DegreeProblem n) : Finset (Edge n) := Finset.univ \ P.forced

def denominatorLCM {n : ℕ} (P : DegreeProblem n) : ℕ :=
  (optionalEdges P).lcm (fun e => (P.weight e).den)

def integerWeight {n : ℕ} (P : DegreeProblem n) (e : Edge n) : ℤ :=
  (denominatorLCM P : ℤ)*(P.weight e).num/(P.weight e).den

def gadgetM {n : ℕ} (P : DegreeProblem n) : ℤ :=
  1 + (((optionalEdges P).sup (fun e => (integerWeight P e).natAbs) : ℕ) : ℤ)

abbrev GadgetVertex {n : ℕ} (P : DegreeProblem n) :=
  (Σ i : Fin n, Fin (remainingCap P i)) ⊕ ({e // e ∈ optionalEdges P} × Bool)

def endpoint {n : ℕ} (e : Edge n) (side : Bool) : Fin n := if side then e.val.2 else e.val.1

abbrev GadgetEdge {n : ℕ} (P : DegreeProblem n) :=
  {e // e ∈ optionalEdges P} ⊕
    (Σ e : {e // e ∈ optionalEdges P}, Σ side : Bool,
      Fin (remainingCap P (endpoint e.val side)))

def gadgetEnds {n : ℕ} {P : DegreeProblem n} : GadgetEdge P → GadgetVertex P × GadgetVertex P
  | .inl e => (.inr (e,false), .inr (e,true))
  | .inr ⟨e,side,slot⟩ => (.inr (e,side), .inl ⟨endpoint e.val side,slot⟩)

def gadgetWeight {n : ℕ} {P : DegreeProblem n} : GadgetEdge P → ℤ
  | .inl _ => 4*gadgetM P
  | .inr ⟨e,_,_⟩ => 2*gadgetM P+integerWeight P e.val

def IsMatching {n : ℕ} {P : DegreeProblem n} (J : Finset (GadgetEdge P)) : Prop :=
  ∀ e ∈ J, ∀ f ∈ J, e ≠ f →
    (gadgetEnds e).1 ≠ (gadgetEnds f).1 ∧ (gadgetEnds e).1 ≠ (gadgetEnds f).2 ∧
    (gadgetEnds e).2 ≠ (gadgetEnds f).1 ∧ (gadgetEnds e).2 ≠ (gadgetEnds f).2

def decodeMatching {n : ℕ} (P : DegreeProblem n) (J : Finset (GadgetEdge P)) : Finset (Edge n) :=
  (optionalEdges P).filter (fun e => ∃ he : e ∈ optionalEdges P,
    (∃ s, Sum.inr ⟨⟨e,he⟩,false,s⟩ ∈ J) ∧
    (∃ s, Sum.inr ⟨⟨e,he⟩,true,s⟩ ∈ J))

def fromUpper {n : ℕ} (a : Edge n → Bool) : Graph n :=
  ⟨fun (i j : Fin n) => if h : i < j then a ⟨(i,j),h⟩ else if h' : j < i then a ⟨(j,i),h'⟩ else false, by
    constructor
    · intro i j
      by_cases h : i < j
      · have h' : ¬ (j < i) := by omega
        simp [h,h']
      · by_cases h' : j < i
        · simp [h,h']
        · simp [h,h']
    · intro i; simp⟩

def toUpper {n : ℕ} (A : Graph n) : Edge n → Bool := fun e => A.val e.val.1 e.val.2

def upperObjective {n : ℕ} (a : Edge n → Bool) (w : Edge n → ℝ) : ℝ :=
  ∑ e, if a e then w e else 0

def RelaxedFeasible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (a : Edge n → ℝ) : Prop :=
  (∀ e, 0 ≤ a e ∧ a e ≤ 1) ∧ (∀ e, toUpper R e = true → a e = 1) ∧
  ∀ i, (∑ e, if e.val.1=i ∨ e.val.2=i then a e else 0) ≤ d i

def relaxedObjective {n : ℕ} (a w : Edge n → ℝ) : ℝ := ∑ e, w e*a e

def rho {n : ℕ} (m : Model n) (i j : Fin n) : ℝ :=
  if meanVariance m = 0 then 0 else covariance m i j/meanVariance m

def V2star {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  sampleVariance (weighted m y)/n * (1+(∑ i, ∑ j, adjacency m.G i j*rho m i j)/n)

def cycleSigns (u : Fin 16) (r : Fin 4) : ℝ :=
  if (u.val/2^r.val)%2=0 then -1 else 1

def cycleMean (f : (Fin 4 → ℝ) → ℝ) : ℝ := (∑ u : Fin 16, f (cycleSigns u))/16

def pathMean (f : ℝ → ℝ → ℝ) : ℝ := (f (-1) (-1)+f (-1) 1+f 1 (-1)+f 1 1)/4

end
end SAP.P011a
