import SAP.P001a.Defs
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.GLP0011B1
import AronowAudit.P001.Wave1.Gap.GLP0012B2
import AronowAudit.P001.Wave1.Gap.GLP0012B4
import AronowAudit.P001.Wave1.Gap.GP0011B1
import AronowAudit.P001.Wave1.Gap.GP0011B2
import AronowAudit.P001.Wave1.Gap.GP0012B1
import AronowAudit.P001.Wave1.Gap.GP0012B2b
import AronowAudit.P001.Wave1.Gap.GP0013B1
import AronowAudit.P001.Wave1.Gap.GP0013B1c
import AronowAudit.P001.Wave1.Gap.GP0014B2
import AronowAudit.P001.Wave1.Gap.RepairT3
import AronowAudit.P001.Wave1.Gap.TailA.HotDeckL2
import AronowAudit.P001.Wave1.Gap.TailA.MatchingFinals
import AronowAudit.P001.Wave1.Gap.TailBRegularEfficiency
import AronowAudit.P001.Wave1.Gap.TailBSieveEscape
import AronowAudit.P001.Wave1.Gap.TailBStableGram
import AronowAudit.P001.Wave1.Gap.WLP001bB2
import AronowAudit.P001.Wave1.Gap.WLP001dB1
import AronowAudit.P001.Wave1.Gap.WP001dB1
import AronowAudit.P001.Wave1.Gap.WP001dB2
import AronowAudit.P001.Wave1.UnusedMixtureMle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a.Bridge

theorem T1_correspondence : SAP.P001a.T1Statement ↔
  (AronowAudit.P001.FiniteMomentLaw AronowAudit.P001.geoMass ∧ AronowAudit.P001.massMean AronowAudit.P001.geoMass = 1 ∧ AronowAudit.P001.massSecond AronowAudit.P001.geoMass = 3 ∧
   (∀ n, 2  ≤  n → AronowAudit.P001.FiniteMomentLaw (AronowAudit.P001.mixMass n) ∧ (∀ k, 0  <  AronowAudit.P001.mixMass n k) ∧
     AronowAudit.P001.massMean (AronowAudit.P001.mixMass n) = 1 + (n : ℝ)⁻¹^2 ∧
     AronowAudit.P001.massSecond (AronowAudit.P001.mixMass n) = 3 + (n : ℝ)⁻¹ + 2*(n : ℝ)⁻¹^2 ∧
     (AronowAudit.P001.massMean (AronowAudit.P001.mixMass n) - AronowAudit.P001.massMean AronowAudit.P001.geoMass) / ((n : ℝ)⁻¹^2) = 1) ∧
   Tendsto (fun (n : ℕ) => AronowAudit.P001.massSecond (AronowAudit.P001.mixMass n) - (AronowAudit.P001.massMean (AronowAudit.P001.mixMass n))^2) atTop (nhds 2) ∧
   Tendsto (fun n : ℕ => (n : ℝ)⁻¹^2) atTop (nhds 0) ∧
   (∀ ε : ℝ, 0  <  ε → ∀ᶠ n in atTop, ∀ x : ℝ,
     |(AronowAudit.P001.massCDF (AronowAudit.P001.mixMass n) x - AronowAudit.P001.massCDF AronowAudit.P001.geoMass x) / ((n : ℝ)⁻¹^2)|  <  ε)) := Iff.rfl

theorem T2_correspondence : SAP.P001a.T2Statement.{u1} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : AronowAudit.P001.IID μ X) (h2 : MemLp (X 0) 2 μ)
   (hv : 0  <  AronowAudit.P001.var μ (X 0)),
  (∀ n, 0  <  n → ∀ ω, AronowAudit.P001.mean (AronowAudit.P001.empirical X n ω) id = AronowAudit.P001.sampleMean X n ω) ∧
   AronowAudit.P001.CD μ (fun n ω => Real.sqrt n * (AronowAudit.P001.sampleMean X n ω - AronowAudit.P001.mean μ (X 0)))
     (gaussianReal 0 ⟨AronowAudit.P001.var μ (X 0), le_of_lt hv⟩)) ∧

SAP.P001a.T1Statement) := Iff.rfl

theorem T3_correspondence : SAP.P001a.T3Statement ↔
  (((¬ AronowAudit.P001.Wave1.pda_at_mean_printed_contract) ∧

(IsProbabilityMeasure AronowAudit.P001.gapJointLaw ∧
  AronowAudit.P001.HasJointPDF AronowAudit.P001.gapJointLaw (fun xy => AronowAudit.P001.gapPDF xy.1 *
    (if xy.2 ∈ Set.Icc (-1 : ℝ) 1 then 1/2 else 0)) ∧
  AronowAudit.P001.gapJointLaw = (AronowAudit.P001.gapJointLaw.map Prod.fst).prod (AronowAudit.P001.gapJointLaw.map Prod.snd) ∧
  AronowAudit.P001.HasPDF (AronowAudit.P001.gapJointLaw.map Prod.fst) AronowAudit.P001.gapPDF ∧
  AronowAudit.P001.gapJointLaw.map Prod.snd = AronowAudit.P001.uniformLaw (-1) 1 ∧
  (∀ᵐ xy ∂AronowAudit.P001.gapJointLaw, xy.1 ∈ Set.Icc (-2 : ℝ) 2 ∧ xy.2 ∈ Set.Icc (-1 : ℝ) 1) ∧
  AronowAudit.P001.mean AronowAudit.P001.gapJointLaw Prod.fst = 0 ∧ AronowAudit.P001.gapPDF 0 = 0 ∧
  AronowAudit.P001.IsCEF AronowAudit.P001.gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
  ContDiff ℝ 1 AronowAudit.P001.pdaBump ∧
  (∀ x, 0 < AronowAudit.P001.gapPDF x → AronowAudit.P001.pdaBump x = 0) ∧
  deriv (fun _ : ℝ => (0 : ℝ)) 0 = 0 ∧
  (∀ a : ℝ, AronowAudit.P001.IsCEF AronowAudit.P001.gapJointLaw Prod.fst Prod.snd (fun x => a*AronowAudit.P001.pdaBump x) ∧
    deriv (fun x => a*AronowAudit.P001.pdaBump x) (AronowAudit.P001.mean AronowAudit.P001.gapJointLaw Prod.fst) = a)) ∧

(IsProbabilityMeasure AronowAudit.P001.gapJointLaw ∧
   AronowAudit.P001.HasJointPDF AronowAudit.P001.gapJointLaw (fun xy => AronowAudit.P001.gapPDF xy.1 * (if xy.2∈Set.Icc (-1 : ℝ) 1 then 1/2 else 0)) ∧
   AronowAudit.P001.mean AronowAudit.P001.gapJointLaw Prod.fst=0 ∧ AronowAudit.P001.IsCEF AronowAudit.P001.gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
   AronowAudit.P001.IsCEF AronowAudit.P001.gapJointLaw Prod.fst Prod.snd AronowAudit.P001.pdaBump ∧
   ContDiff ℝ 1 AronowAudit.P001.pdaBump ∧ deriv AronowAudit.P001.pdaBump (AronowAudit.P001.mean AronowAudit.P001.gapJointLaw Prod.fst)=1 ∧
   deriv (fun _ : ℝ => (0 : ℝ)) (AronowAudit.P001.mean AronowAudit.P001.gapJointLaw Prod.fst)=0)) ∧

ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
({x : ℝ | 0 < AronowAudit.P001.gapPDF x} = Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2)) := Iff.rfl

theorem T4_correspondence : SAP.P001a.T4Statement.{u1} ↔
  (∀ {Ω : Type u1} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
  (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X)
  (hXi : ∀ k, Integrable (fun ω => X ω k) μ) (hY : Integrable Y μ)
  (f : (Fin K → ℝ) → ℝ) (hf : AronowAudit.P001.HasVectorPDF (μ.map X) f)
  (U : Set (Fin K → ℝ)) (hU : IsOpen U)
  (hmean : (fun k => AronowAudit.P001.mean μ (fun ω => X ω k)) ∈ U)
  (hpositive : ∀ x ∈ U, 0 < f x)
  (m m' : (Fin K → ℝ) → ℝ) (hm : AronowAudit.P001.IsCEF μ X Y m) (hm' : AronowAudit.P001.IsCEF μ X Y m')
  (hc : ContinuousOn m U) (hc' : ContinuousOn m' U)
  (k : Fin K) (a : ℝ)
  (hd : HasDerivAt (fun t => m (Function.update
    (fun j => AronowAudit.P001.mean μ (fun ω => X ω j)) k (AronowAudit.P001.mean μ (fun ω => X ω k)+t))) a 0),
  Set.EqOn m m' U ∧
  HasDerivAt (fun t => m' (Function.update
    (fun j => AronowAudit.P001.mean μ (fun ω => X ω j)) k (AronowAudit.P001.mean μ (fun ω => X ω k)+t))) a 0 ∧
  AronowAudit.P001.partialAt m (fun j => AronowAudit.P001.mean μ (fun ω => X ω j)) k =
    AronowAudit.P001.partialAt m' (fun j => AronowAudit.P001.mean μ (fun ω => X ω j)) k) := Iff.rfl

theorem T5_correspondence : SAP.P001a.T5Statement.{u1} ↔
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : ℕ → Ω → ℝ) (hiid : AronowAudit.P001.IID μ (fun i ω => (X i ω, Y i ω)))
   (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) = (AronowAudit.P001.uniformLaw 0 1).prod (gaussianReal 0 1))
   (fit : ℕ → Ω → Polynomial ℝ)
   (hfit : AronowAudit.P001.IsSieveLS X Y (fun (n : ℕ) => Nat.floor ((n : ℝ)^(3/4 : ℝ))) fit),
  Tendsto (fun (n : ℕ) => Nat.floor ((n : ℝ)^(3/4 : ℝ))) atTop atTop ∧
   Tendsto (fun (n : ℕ) => (Nat.floor ((n : ℝ)^(3/4 : ℝ)) : ℝ) / n) atTop (nhds 0) ∧
   ∀ δ : ℝ, 0  <  δ → δ  ≤  1 → ∀ ε : ℝ, 0  <  ε →
     1/2  ≤  Filter.liminf (fun t : ℕ =>
       AronowAudit.P001.prob μ {ω | ε  <  ∫ x in Set.Icc 0 δ, ((fit (t^4) ω).eval x)^2}) atTop) := Iff.rfl

theorem T6_correspondence : SAP.P001a.T6Statement.{u1,u2,u3,u4} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : ℕ → Ω → ℝ) (hiid : AronowAudit.P001.IID μ (fun i ω => (X i ω, Y i ω)))
   (a b V : ℝ) (hab : a  <  b) (hV : 0  ≤  V) (hY2 : MemLp (Y 0) 2 μ)
   (hsupp : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b)
   (m : ℝ → ℝ) (hm : ContinuousOn m (Set.Icc a b)) (hcef : AronowAudit.P001.IsCEF μ (X 0) (Y 0) m)
   (hvar : ∀ A : Set ℝ, MeasurableSet A →
     (∫ ω in (X 0) ⁻¹' A, (Y 0 ω-m (X 0 ω))^2 ∂μ)  ≤  V * AronowAudit.P001.prob μ ((X 0) ⁻¹' A))
   (p : ℕ → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k)
   (horth : ∀ j k, AronowAudit.P001.mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω)) = if j=k then 1 else 0)
   (J : ℕ → ℕ) (hJ : Tendsto J atTop atTop)
   (hrate : Tendsto (fun (n : ℕ) => ((J n+1 : ℕ) : ℝ)/n) atTop (nhds 0))
   (c : ℝ) (hc : 0  <  c)
   (hgram : Tendsto (fun (n : ℕ) => AronowAudit.P001.prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     c*(∑ k, (v k)^2)  ≤  (∑ i ∈ Finset.range n,
       (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2)/(n : ℝ)}) atTop (nhds 1))
   (fit : ℕ → Ω → Polynomial ℝ) (hfit : AronowAudit.P001.IsSieveLS X Y J fit),
  AronowAudit.P001.CP μ (fun n ω => ∫ x, ((fit n ω).eval x-m x)^2 ∂(μ.map (X 0))) 0) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : AronowAudit.P001.IID μ X) (p : ℕ → Polynomial ℝ)
   (horth : ∀ j k,AronowAudit.P001.mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (J : ℕ → ℕ) (zeta2 : ℕ → ℝ)
   (hrow : ∀ n,∀ᵐ ω ∂μ,(∑ k : Fin (J n+1),((p k).eval (X 0 ω))^2) ≤ zeta2 n)
   (hrate : Tendsto (fun (n : ℕ) => zeta2 n*((J n+1 : ℕ) : ℝ)/(n : ℝ)) atTop (nhds 0)),
  Tendsto (fun (n : ℕ) => AronowAudit.P001.prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     (1/2 : ℝ)*(∑ k,(v k)^2) ≤
       (∑ i∈Finset.range n,(∑ k : Fin (J n+1),v k*(p k).eval (X i ω))^2)/(n : ℝ)})
     atTop (nhds 1)) ∧

(∀ {Ω : Type u3} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : AronowAudit.P001.IID μ X) (a b : ℝ) (hab : a < b)
   (hlaw : μ.map (X 0)=AronowAudit.P001.uniformLaw a b) (p : ℕ → Polynomial ℝ)
   (hdeg : ∀ k,(p k).natDegree=k)
   (horth : ∀ j k,AronowAudit.P001.mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (J : ℕ → ℕ)
   (hrate : Tendsto (fun (n : ℕ) => (((J n+1 : ℕ) : ℝ)^3)/(n : ℝ)) atTop (nhds 0)),
  Tendsto (fun (n : ℕ) => AronowAudit.P001.prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     (1/2 : ℝ)*(∑ k,(v k)^2) ≤
       (∑ i∈Finset.range n,(∑ k : Fin (J n+1),v k*(p k).eval (X i ω))^2)/(n : ℝ)})
     atTop (nhds 1)) ∧

(∀ {Ω : Type u4} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : AronowAudit.P001.IID μ X) (hx : μ.map (X 0)=AronowAudit.P001.uniformLaw 0 1)
   (K n : ℕ) (hK : 0 < K) (hn : 0 < n) (p : Fin K → Polynomial ℝ)
   (hdeg : ∀ k,(p k).natDegree=k.val)
   (horth : ∀ j k,AronowAudit.P001.mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0),
  (∀ x∈Set.Icc (0 : ℝ) 1,(∑ k,((p k).eval x)^2) ≤ (K : ℝ)^2) ∧
   AronowAudit.P001.prob μ {ω | 1/2 < AronowAudit.P001.gramDeviation (AronowAudit.P001.sampleGram p X n ω)} ≤ 4*((K : ℝ)^3-K)/n)) := Iff.rfl

theorem T7_correspondence : SAP.P001a.T7Statement.{u1,u2} ↔
  ((∀ {Ω : Type u1} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
  (hiid : AronowAudit.P001.IID μ (fun i ω => (X i ω,Y i ω)))
  (hlaw : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
    (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1)),
  (∀ p ∈ ({(1/4 : ℝ),3/4} : Set ℝ), ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    0 ≤ AronowAudit.P001.bernoulliKL p t ∧ (AronowAudit.P001.bernoulliKL p t=0 ↔ t=p)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      (∏ i, if y i=1 then t else 1-t) ≤
        ∏ i, if y i=1 then AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.finiteSampleMean y)
          else 1-AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.finiteSampleMean y)) ∧
  (∀ n : ℕ, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i=0 ∨ y i=1) →
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      ((∏ i, if y i=1 then t else 1-t) =
        ∏ i, if y i=1 then AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.finiteSampleMean y)
          else 1-AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.finiteSampleMean y)) ↔
      t=AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.finiteSampleMean y)) ∧
  AronowAudit.P001.mean μ (Y 0)=1/2 ∧ AronowAudit.P001.var μ (Y 0)=1/4 ∧
  (∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε →
    AronowAudit.P001.prob μ {ω | ε ≤ |AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.sampleMean Y n ω)-1/2|} ≤
      1/(4*(n : ℝ)*ε^2)) ∧
  (∀ n : ℕ, 0 < n →
    1-16/(n : ℝ) ≤ AronowAudit.P001.prob μ {ω | 1/8 < |AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.sampleMean Y n ω)-1/4|} ∧
    1-16/(n : ℝ) ≤ AronowAudit.P001.prob μ {ω | 1/8 < |AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.sampleMean Y n ω)-3/4|}) ∧
  AronowAudit.P001.CP μ (fun n ω => AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.sampleMean Y n ω)) (1/2) ∧
  ¬ AronowAudit.P001.CP μ (fun n ω => AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.sampleMean Y n ω)) (1/4) ∧
  ¬ AronowAudit.P001.CP μ (fun n ω => AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.sampleMean Y n ω)) (3/4) ∧
  (∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
    (AronowAudit.P001.bernoulliKL (1/4) (1/2)+AronowAudit.P001.bernoulliKL (3/4) (1/2))/2 ≤
      (AronowAudit.P001.bernoulliKL (1/4) t+AronowAudit.P001.bernoulliKL (3/4) t)/2 ∧
    ((AronowAudit.P001.bernoulliKL (1/4) t+AronowAudit.P001.bernoulliKL (3/4) t)/2 =
      (AronowAudit.P001.bernoulliKL (1/4) (1/2)+AronowAudit.P001.bernoulliKL (3/4) (1/2))/2 ↔ t=1/2))) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X Y : ℕ → Ω → ℝ) (hiid : AronowAudit.P001.IID μ (fun i ω => (X i ω, Y i ω)))
  (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
  (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
    ENNReal.ofReal ((1-q)*3/4) • Measure.dirac (0,0) +
    ENNReal.ofReal ((1-q)/4) • Measure.dirac (0,1) +
    ENNReal.ofReal (q/4) • Measure.dirac (1,0) +
    ENNReal.ofReal (q*3/4) • Measure.dirac (1,1)),
  let T := fun n ω => AronowAudit.P001.clip (1/10) (9/10) (AronowAudit.P001.sampleMean Y n ω)
  AronowAudit.P001.CP μ T (1/4+q/2) ∧
  (∀ n, 0 < n → ∀ᵐ ω ∂μ,
    T n ω ∈ Set.Icc (1/10 : ℝ) (9/10) ∧
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      (∏ i : Fin n, if Y i ω = 1 then t else 1-t) ≤
        (∏ i : Fin n, if Y i ω = 1 then T n ω else 1-T n ω) ∧
      ((∏ i : Fin n, if Y i ω = 1 then t else 1-t) =
        (∏ i : Fin n, if Y i ω = 1 then T n ω else 1-T n ω) ↔ t = T n ω)) ∧
  (0 < q ∧ q < 1 →
    AronowAudit.P001.conditionalMeanAt μ (X 0) (Y 0) 0 = 1/4 ∧
    AronowAudit.P001.conditionalMeanAt μ (X 0) (Y 0) 1 = 3/4 ∧
    ¬ AronowAudit.P001.CP μ T (1/4) ∧ ¬ AronowAudit.P001.CP μ T (3/4)))) := Iff.rfl


end SAP.P001a.Bridge
