import SAP.P001a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a.Bridge

theorem T13_correspondence : SAP.P001a.T13Statement.{u1,u2} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : AronowAudit.P001.IID μ Z)
   (hlaw : μ.map (Z 0) = AronowAudit.P001.matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => AronowAudit.P001.hotDeck (AronowAudit.P001.firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => AronowAudit.P001.bootVar AronowAudit.P001.hotDeck (AronowAudit.P001.firstSample Z n ω)) 2 μ),
  AronowAudit.P001.MatchingFailure μ Z false) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : AronowAudit.P001.IID μ Z) (hlaw : μ.map (Z 0)=AronowAudit.P001.matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => AronowAudit.P001.hotDeck (AronowAudit.P001.firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => AronowAudit.P001.bootVar AronowAudit.P001.hotDeck (AronowAudit.P001.firstSample Z n ω)) 2 μ),
  ∃ C : ℝ,0 ≤ C ∧ ∀ n : ℕ,
     AronowAudit.P001.mean μ (fun ω => ((n : ℝ)*AronowAudit.P001.bootVar AronowAudit.P001.hotDeck (AronowAudit.P001.firstSample Z n ω))^2) ≤ C) ∧

(0 < AronowAudit.P001.matchS ∧ AronowAudit.P001.matchS < 1 ∧ AronowAudit.P001.matchA < 3 ∧ AronowAudit.P001.matchB < 3/2 ∧ AronowAudit.P001.matchVB < AronowAudit.P001.matchV)) := Iff.rfl

theorem T14_correspondence : SAP.P001a.T14Statement.{u1} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : AronowAudit.P001.IID μ Z)
   (hlaw : μ.map (Z 0) = AronowAudit.P001.matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => AronowAudit.P001.hotDeck (AronowAudit.P001.firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => AronowAudit.P001.bootVar AronowAudit.P001.hotDeck (AronowAudit.P001.firstSample Z n ω)) 2 μ),
  AronowAudit.P001.MatchingFailure μ Z false) ∧

(∀ {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (r : Fin n → Bool),
  (∀ e : Fin n → Bool,AronowAudit.P001.hotDeck (fun j => (p j,r j,e j))-50=
     (∑ j,AronowAudit.P001.donorReuseWeight p r j*AronowAudit.P001.noise (e j))/(n : ℝ)) ∧
   IsProbabilityMeasure (AronowAudit.P001.signProductLaw n) ∧
   AronowAudit.P001.mean (AronowAudit.P001.signProductLaw n) (fun e => AronowAudit.P001.hotDeck (fun j => (p j,r j,e j)))=50 ∧
   AronowAudit.P001.var (AronowAudit.P001.signProductLaw n) (fun e => AronowAudit.P001.hotDeck (fun j => (p j,r j,e j)))=
     (∑ j,(AronowAudit.P001.donorReuseWeight p r j)^2)/(n : ℝ)^2)) := Iff.rfl

theorem T15_correspondence : SAP.P001a.T15Statement.{u1,u2} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : AronowAudit.P001.IID μ Z)
   (hlaw : μ.map (Z 0) = AronowAudit.P001.matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => AronowAudit.P001.causalMatch (AronowAudit.P001.firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => AronowAudit.P001.bootVar AronowAudit.P001.causalMatch (AronowAudit.P001.firstSample Z n ω)) 2 μ),
  AronowAudit.P001.MatchingFailure μ Z true) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : AronowAudit.P001.IID μ Z) (hlaw : μ.map (Z 0)=AronowAudit.P001.matchingUnitLaw),
  AronowAudit.P001.CP μ (fun n ω => AronowAudit.P001.estimatedMatchIntercept (AronowAudit.P001.firstSample Z n ω)) (1/4))) := Iff.rfl

theorem T16_correspondence : SAP.P001a.T16Statement.{u1,u2} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : AronowAudit.P001.IID μ Z) (hlaw : μ.map (Z 0)=AronowAudit.P001.matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => AronowAudit.P001.causalMatchEstimated (AronowAudit.P001.firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => AronowAudit.P001.bootVar AronowAudit.P001.causalMatchEstimated (AronowAudit.P001.firstSample Z n ω)) 2 μ),
  (∀ n,0 < n → AronowAudit.P001.mean μ (fun ω => AronowAudit.P001.causalMatchEstimated (AronowAudit.P001.firstSample Z n ω))=0) ∧
   Tendsto (fun (n : ℕ) => (n : ℝ)*AronowAudit.P001.var μ (fun ω => AronowAudit.P001.causalMatchEstimated (AronowAudit.P001.firstSample Z n ω))) atTop (nhds AronowAudit.P001.matchV) ∧
   Tendsto (fun (n : ℕ) => AronowAudit.P001.mean μ (fun ω => (n : ℝ)*AronowAudit.P001.bootVar AronowAudit.P001.causalMatchEstimated (AronowAudit.P001.firstSample Z n ω))) atTop (nhds AronowAudit.P001.matchVB) ∧
   0 < AronowAudit.P001.matchVB ∧ AronowAudit.P001.matchVB < AronowAudit.P001.matchV ∧
   ¬ AronowAudit.P001.CP μ (fun n ω => (n : ℝ)*AronowAudit.P001.bootVar AronowAudit.P001.causalMatchEstimated (AronowAudit.P001.firstSample Z n ω)) AronowAudit.P001.matchV) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : AronowAudit.P001.IID μ Z) (hlaw : μ.map (Z 0)=AronowAudit.P001.matchingUnitLaw),
  AronowAudit.P001.CP μ (fun n ω => AronowAudit.P001.estimatedMatchIntercept (AronowAudit.P001.firstSample Z n ω)) (1/4)) ∧

(∀ {n : ℕ} (s : Fin n → ℝ × Bool × Bool) (r : Fin n → Bool) (i : Fin n),
  AronowAudit.P001.nearestDonor (AronowAudit.P001.estimatedMatchScore s) r i=AronowAudit.P001.nearestDonor (fun j => (s j).1) r i) ∧

(∀ {n : ℕ} (s : Fin n → ℝ × Bool × Bool),
  AronowAudit.P001.causalMatchEstimated s=AronowAudit.P001.causalMatch s) ∧

(∀ {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (d : Fin n → Bool),
  (∀ e : Fin n → Bool,AronowAudit.P001.causalMatch (fun j => (p j,d j,e j))=
     -(∑ j,AronowAudit.P001.donorReuseWeight p (fun i => !(d i)) j*AronowAudit.P001.noise (e j))/(n : ℝ)) ∧
   IsProbabilityMeasure (AronowAudit.P001.signProductLaw n) ∧
   AronowAudit.P001.mean (AronowAudit.P001.signProductLaw n) (fun e => AronowAudit.P001.causalMatch (fun j => (p j,d j,e j)))=0 ∧
   AronowAudit.P001.var (AronowAudit.P001.signProductLaw n) (fun e => AronowAudit.P001.causalMatch (fun j => (p j,d j,e j)))=
     (∑ j,(AronowAudit.P001.donorReuseWeight p (fun i => !(d i)) j)^2)/(n : ℝ)^2)) := Iff.rfl

theorem T17_correspondence : SAP.P001a.T17Statement.{u1} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
  (hiid : AronowAudit.P001.IID μ Z) (hlaw : μ.map (Z 0)=AronowAudit.P001.finiteLawMeasure AronowAudit.P001.placeboLaw),
  AronowAudit.P001.FCondIndep AronowAudit.P001.placeboLaw AronowAudit.P001.placeboW AronowAudit.P001.placeboD AronowAudit.P001.placeboX ∧
  AronowAudit.P001.FCondIndep AronowAudit.P001.placeboLaw (fun i => (2+AronowAudit.P001.placeboZ i,3+AronowAudit.P001.placeboZ i)) AronowAudit.P001.placeboD AronowAudit.P001.placeboX ∧
  AronowAudit.P001.placeboMoment.det=17/54 ∧
  (∀ a b c : ℝ, AronowAudit.P001.placeboRisk (29/68) 0 (4/17) ≤ AronowAudit.P001.placeboRisk a b c ∧
    (AronowAudit.P001.placeboRisk a b c=AronowAudit.P001.placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => AronowAudit.P001.placeboSampleF Z n ω/(n : ℝ)) atTop (nhds (64/531))) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => AronowAudit.P001.placeboSampleWald Z n ω/(n : ℝ)) atTop (nhds (18496/135315))) ∧
  (∀ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 → ∀ critical : ℕ → ℝ,
    (∀ n : ℕ, 3 < n → AronowAudit.P001.prob (AronowAudit.P001.fReference 1 (n-3)) (Set.Iic (critical n))=1-α) →
    Tendsto (fun n => AronowAudit.P001.prob μ {ω | critical n < AronowAudit.P001.placeboSampleF Z n ω}) atTop (nhds 1)) ∧
  (∀ c : ℝ, Tendsto (fun n => AronowAudit.P001.prob μ {ω | c < AronowAudit.P001.placeboSampleWald Z n ω}) atTop (nhds 1)) ∧
  240*AronowAudit.P001.placeboRisk (7/12) 0 0=175/3 ∧
  240*AronowAudit.P001.placeboRisk (29/68) 0 (4/17)=885/17 ∧
  ((240*AronowAudit.P001.placeboRisk (7/12) 0 0-240*AronowAudit.P001.placeboRisk (29/68) 0 (4/17))/
    (240*AronowAudit.P001.placeboRisk (29/68) 0 (4/17)/(240-3))=5056/177)) ∧

(AronowAudit.P001.FCondIndep AronowAudit.P001.placeboLaw AronowAudit.P001.placeboW AronowAudit.P001.placeboD AronowAudit.P001.placeboX ∧
   AronowAudit.P001.FCondIndep AronowAudit.P001.placeboLaw (fun i => (2+AronowAudit.P001.placeboZ i,3+AronowAudit.P001.placeboZ i)) AronowAudit.P001.placeboD AronowAudit.P001.placeboX ∧
   (∀ i : Fin 12,(1/8 : ℝ) < AronowAudit.P001.fcond AronowAudit.P001.placeboLaw AronowAudit.P001.placeboD AronowAudit.P001.placeboX (AronowAudit.P001.placeboX i) ∧
     AronowAudit.P001.fcond AronowAudit.P001.placeboLaw AronowAudit.P001.placeboD AronowAudit.P001.placeboX (AronowAudit.P001.placeboX i) < 1-1/8) ∧
   (∀ i : Fin 12,AronowAudit.P001.fcond AronowAudit.P001.placeboLaw
     (fun j => (AronowAudit.P001.placeboW j-AronowAudit.P001.fcond AronowAudit.P001.placeboLaw AronowAudit.P001.placeboW AronowAudit.P001.placeboX (AronowAudit.P001.placeboX i))^2)
     AronowAudit.P001.placeboX (AronowAudit.P001.placeboX i)=1/4) ∧
   AronowAudit.P001.placeboMoment.det=17/54 ∧
   (∀ a b c : ℝ,AronowAudit.P001.placeboRisk (29/68) 0 (4/17) ≤ AronowAudit.P001.placeboRisk a b c ∧
     (AronowAudit.P001.placeboRisk a b c=AronowAudit.P001.placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
   (∀ a b : ℝ,AronowAudit.P001.placeboRisk (7/12) 0 0 ≤ AronowAudit.P001.placeboRisk a b 0 ∧
     (AronowAudit.P001.placeboRisk a b 0=AronowAudit.P001.placeboRisk (7/12) 0 0 ↔ a=7/12 ∧ b=0)) ∧
   AronowAudit.P001.placeboRisk (7/12) 0 0=35/144 ∧ AronowAudit.P001.placeboRisk (29/68) 0 (4/17)=59/272 ∧
   AronowAudit.P001.placeboRisk (29/68) 0 (4/17) < AronowAudit.P001.placeboRisk (7/12) 0 0 ∧ (4/17 : ℝ)≠0)) := Iff.rfl

theorem T18_correspondence : SAP.P001a.T18Statement.{u1} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hSupportD : 0 < AronowAudit.P001.prob μ {ω | D ω=1} ∧ AronowAudit.P001.prob μ {ω | D ω=1} < 1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : AronowAudit.P001.CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : AronowAudit.P001.IsCEF μ X D (AronowAudit.P001.linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => AronowAudit.P001.mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))),
  AronowAudit.P001.IsCEF μ (fun ω => (X ω,W ω)) D (fun xw => AronowAudit.P001.linearPredictor γ xw.1) ∧
   (∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     AronowAudit.P001.mean μ (fun ω => (D ω-AronowAudit.P001.linearPredictor γ (X ω))^2) ≤
       AronowAudit.P001.mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)) ∧
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (AronowAudit.P001.mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       AronowAudit.P001.mean μ (fun ω => (D ω-AronowAudit.P001.linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0)) ∧

(AronowAudit.P001.FCondIndep AronowAudit.P001.placeboLaw AronowAudit.P001.placeboW AronowAudit.P001.placeboD AronowAudit.P001.placeboX ∧
  (4/17 : ℝ) ≠ 0 ∧
  ∀ a b c : ℝ, AronowAudit.P001.placeboRisk (29/68) 0 (4/17) ≤ AronowAudit.P001.placeboRisk a b c ∧
    (AronowAudit.P001.placeboRisk a b c = AronowAudit.P001.placeboRisk (29/68) 0 (4/17) ↔
      a = 29/68 ∧ b = 0 ∧ c = 4/17))) := Iff.rfl

theorem T19_correspondence : SAP.P001a.T19Statement ↔
  (Summable AronowAudit.P001.overlapT ∧ Summable AronowAudit.P001.overlapC ∧ (∑' k, AronowAudit.P001.overlapT k) = 1/2 ∧
   (∑' k, AronowAudit.P001.overlapC k) = 1/2 ∧ (∀ k, 0  <  AronowAudit.P001.overlapT k ∧ 0  <  AronowAudit.P001.overlapC k ∧
     0  <  AronowAudit.P001.overlapPropensity k ∧ AronowAudit.P001.overlapPropensity k  <  1) ∧
   ¬ ∃ ε : ℝ, 0  <  ε ∧ ∀ k, ε  <  AronowAudit.P001.overlapPropensity k ∧ AronowAudit.P001.overlapPropensity k  <  1-ε) := Iff.rfl


end SAP.P001a.Bridge
