import Mathlib
import SAP.P001a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a

/-- The mathematical content packaged for target P001-T17. -/
def T17Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
  (hiid : IID μ Z) (hlaw : μ.map (Z 0)=finiteLawMeasure placeboLaw),
  FCondIndep placeboLaw placeboW placeboD placeboX ∧
  FCondIndep placeboLaw (fun i => (2+placeboZ i,3+placeboZ i)) placeboD placeboX ∧
  placeboMoment.det=17/54 ∧
  (∀ a b c : ℝ, placeboRisk (29/68) 0 (4/17) ≤ placeboRisk a b c ∧
    (placeboRisk a b c=placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleF Z n ω/(n : ℝ)) atTop (nhds (64/531))) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleWald Z n ω/(n : ℝ)) atTop (nhds (18496/135315))) ∧
  (∀ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 → ∀ critical : ℕ → ℝ,
    (∀ n : ℕ, 3 < n → prob (fReference 1 (n-3)) (Set.Iic (critical n))=1-α) →
    Tendsto (fun n => prob μ {ω | critical n < placeboSampleF Z n ω}) atTop (nhds 1)) ∧
  (∀ c : ℝ, Tendsto (fun n => prob μ {ω | c < placeboSampleWald Z n ω}) atTop (nhds 1)) ∧
  240*placeboRisk (7/12) 0 0=175/3 ∧
  240*placeboRisk (29/68) 0 (4/17)=885/17 ∧
  ((240*placeboRisk (7/12) 0 0-240*placeboRisk (29/68) 0 (4/17))/
    (240*placeboRisk (29/68) 0 (4/17)/(240-3))=5056/177)) ∧

(FCondIndep placeboLaw placeboW placeboD placeboX ∧
   FCondIndep placeboLaw (fun i => (2+placeboZ i,3+placeboZ i)) placeboD placeboX ∧
   (∀ i : Fin 12,(1/8 : ℝ) < fcond placeboLaw placeboD placeboX (placeboX i) ∧
     fcond placeboLaw placeboD placeboX (placeboX i) < 1-1/8) ∧
   (∀ i : Fin 12,fcond placeboLaw
     (fun j => (placeboW j-fcond placeboLaw placeboW placeboX (placeboX i))^2)
     placeboX (placeboX i)=1/4) ∧
   placeboMoment.det=17/54 ∧
   (∀ a b c : ℝ,placeboRisk (29/68) 0 (4/17) ≤ placeboRisk a b c ∧
     (placeboRisk a b c=placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
   (∀ a b : ℝ,placeboRisk (7/12) 0 0 ≤ placeboRisk a b 0 ∧
     (placeboRisk a b 0=placeboRisk (7/12) 0 0 ↔ a=7/12 ∧ b=0)) ∧
   placeboRisk (7/12) 0 0=35/144 ∧ placeboRisk (29/68) 0 (4/17)=59/272 ∧
   placeboRisk (29/68) 0 (4/17) < placeboRisk (7/12) 0 0 ∧ (4/17 : ℝ)≠0)

/-- The mathematical content packaged for target P001-T18. -/
def T18Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hSupportD : 0 < prob μ {ω | D ω=1} ∧ prob μ {ω | D ω=1} < 1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : IsCEF μ X D (linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))),
  IsCEF μ (fun ω => (X ω,W ω)) D (fun xw => linearPredictor γ xw.1) ∧
   (∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2) ≤
       mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)) ∧
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0)) ∧

(FCondIndep placeboLaw placeboW placeboD placeboX ∧
  (4/17 : ℝ) ≠ 0 ∧
  ∀ a b c : ℝ, placeboRisk (29/68) 0 (4/17) ≤ placeboRisk a b c ∧
    (placeboRisk a b c = placeboRisk (29/68) 0 (4/17) ↔
      a = 29/68 ∧ b = 0 ∧ c = 4/17))

/-- The mathematical content packaged for target P001-T19. -/
def T19Statement : Prop :=
  Summable overlapT ∧ Summable overlapC ∧ (∑' k, overlapT k) = 1/2 ∧
   (∑' k, overlapC k) = 1/2 ∧ (∀ k, 0  <  overlapT k ∧ 0  <  overlapC k ∧
     0  <  overlapPropensity k ∧ overlapPropensity k  <  1) ∧
   ¬ ∃ ε : ℝ, 0  <  ε ∧ ∀ k, ε  <  overlapPropensity k ∧ overlapPropensity k  <  1-ε


end SAP.P001a
