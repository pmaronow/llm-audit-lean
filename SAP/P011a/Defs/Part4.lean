import Mathlib
import SAP.P011a.Defs.Part3

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

def CorrectedAsymptotic : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1plus (F.model k).d B (weighted (F.model k) y)) (A k y)),
  (∀ k, operatorNorm (correctedMatrix (F.model k).d (F.model k).G) ≤ 1+2*c2) ∧
    (∀ k y, V1plus (F.model k).d (F.model k).G (weighted (F.model k) y) ≤
      V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => VYoung (F.model k).d (weighted (F.model k) y)) ∧
    Conservative F (fun k y => min
      (V1plus (F.model k).d (A k y) (weighted (F.model k) y))
      (VYoung (F.model k).d (weighted (F.model k) y))) ∧
    ((∀ k, ∃ D : ℕ, ∀ i, truncatedDegree (F.model k).d i = D) →
      Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)))

def CorrectedMatrix : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (R A : Graph n) (d : Fin n → ℕ)
    (hA : Compatible R d A) (x : Fin n → ℝ),
  PSD (correctedMatrix d A) ∧ PSD (correctedMatrix d A-oracleMatrix A) ∧
    V1plus d A x=varianceForm (correctedMatrix d A) x ∧ 0 ≤ V1plus d A x

def PositivePartFinite : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (A : Graph n),
  PSD (positivePart (oracleMatrix A)) ∧
    PSD (positivePart (oracleMatrix A) - oracleMatrix A) ∧
    operatorNorm (positivePart (oracleMatrix A)) ≤
      1 + ((Finset.univ.sup (fun i => degree A i) : ℕ) : ℝ) ∧
    (∀ x, max (V1 A x) 0 ≤ VPositive A x) ∧
    (∀ M, PSD M → frobeniusSq (positivePart (oracleMatrix A)-oracleMatrix A) ≤
      frobeniusSq (M-oracleMatrix A))

def PositivePartConservative : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4),
  Conservative F (fun k y => VPositive (F.model k).G (weighted (F.model k) y))

def PositivePartUnique : Prop :=
  ∀ {n : ℕ} (A : Graph n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : PSD M)
    (hnearest : frobeniusSq (M-oracleMatrix A) =
      frobeniusSq (positivePart (oracleMatrix A)-oracleMatrix A)),
  M = positivePart (oracleMatrix A)

def PositivePartCycle : Prop :=
  PSD (oracleMatrix cycleGraph + cycleMajorantDifference) ∧ PSD cycleMajorantDifference ∧
    quadratic (oracleMatrix cycleGraph + cycleMajorantDifference) (![0,1,-1,0] : Fin 4 → ℝ) = 3/5 ∧
    quadratic (positivePart (oracleMatrix cycleGraph)) (![0,1,-1,0] : Fin 4 → ℝ) = 1 ∧
    (∀ k, expectation ((cycleFamily (3/2)).model k)
      (fun y => ((cycleFamily (3/2)).size k : ℝ)*VPositive ((cycleFamily (3/2)).model k).G
        (weighted ((cycleFamily (3/2)).model k) y)) = 4-12/((cycleFamily (3/2)).size k : ℝ)) ∧
    InProbability (cycleFamily (3/2))
      (fun k y => ((cycleFamily (3/2)).size k : ℝ)*VPositive ((cycleFamily (3/2)).model k).G
        (weighted ((cycleFamily (3/2)).model k) y)) (fun _ => 4)

def PositivePartNonaffine : Prop :=
  ¬ ∃ c : ℝ, ∃ w : Fin 3 → Fin 3 → ℝ, ∀ A : Graph 3,
      VPositive A (![1,-2,1] : Fin 3 → ℝ) =
        c + upperSum (fun i j => w i j*adjacency A i j)

def CycleSpectrum : Prop :=
  cycleEigenvectorsᵀ*cycleEigenvectors=1 ∧
    oracleMatrix cycleGraph=cycleEigenvectors*Matrix.diagonal (![3,1,1,-1] : Fin 4 → ℝ)*cycleEigenvectorsᵀ ∧
    (∀ x, quadratic cycleClipped x=quadratic (oracleMatrix cycleGraph) x+(x 0-x 1+x 2-x 3)^2/4)

def DegreeOnlyFinite : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (D : ℕ)
    (hd : ∀ i, truncatedDegree d i ≤ D) (x : Fin n → ℝ) (A Ap : Graph n)
    (hm : Maximizes (emptyGraph n) d (fun B => V1 B x) A)
    (hp : Maximizes (emptyGraph n) d (fun B => V1plus d B x) Ap),
  (∀ (B : Graph n) (z : Fin n → ℝ), quadratic (adjacency B) z =
      (∑ i, (degree B i : ℝ)*z i^2) - upperSum (fun i j => adjacency B i j*(z i-z j)^2)) ∧
    (0 ≤ (n : ℝ)*(VYoung d x-V1 A x) ∧
      (n : ℝ)*(VYoung d x-V1 A x) ≤
        (∑ r ∈ Finset.Icc 1 D, (3*(r : ℝ)^2+2*r))*maxAbs (centered x)^2/n) ∧
    (0 ≤ (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ∧
      (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ≤
        maxAbs (centered x)^2/n*(∑ r ∈ Finset.Icc 1 D, (4*(r : ℝ)^2+r)))

def DegreeOnlyIdentity : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (A : Graph n) (x : Fin n → ℝ),
  quadratic (adjacency A) (centered x) =
      (∑ i, (degree A i : ℝ) * centered x i^2) -
        upperSum (fun i j => adjacency A i j * (centered x i-centered x j)^2)

def DegreeOnlyConservative : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F) (hr : ∀ k, (F.model k).R = emptyGraph (F.size k))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)),
  Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y))

def UnboundedDegreeGap : Prop :=
  ∀ (A : ∀ k, (Fin (k+1) → ℝ) → Graph (k+1))
    (hm : ∀ k y, Maximizes (emptyGraph (k+1)) (fun _ => k)
      (fun B => V1 B y) (A k y)),
  (∀ k y, (∀ i, y i = 1 ∨ y i = -1) →
      V1 (A k y) y = (1-average y^2)^2/2 ∧
      VYoung (fun _ => k) y = 1-average y^2) ∧
    InProbability signFamily (fun k y => V1 (A k y) y) (fun _ => 1/2) ∧
    InProbability signFamily (fun k y => VYoung (fun _ => k) y) (fun _ => 1)

def RevisedCorollaries : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (hV : CorrectedClass F V),
  Conservative F V ∧ ConservativeCoverage F V

def ResidualRootRate : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hbound : ∃ B : ℝ, ∀ k i, l2 (D k i) ≤ B)
    (hrate : Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (γhat k y-γ)))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)),
  (∀ k i, expectation (F.model k) (fun y => trueResidual (F.model k) (D k) γ y i) = 0) ∧
    (∀ k i j, expectation (F.model k) (fun y =>
      trueResidual (F.model k) (D k) γ y i*trueResidual (F.model k) (D k) γ y j) =
      covariance (F.model k) i j) ∧
    Tight F (fun k y => Real.sqrt (F.size k : ℝ)*maxAbs
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2 (trueResidual (F.model k) (D k) γ y)/Real.sqrt (F.size k : ℝ)) ∧
    InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y)
      (fittedResidual (F.model k) (D k) (γhat k) y))

def ResidualPrediction : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γ y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)),
  InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y) (fittedResidual (F.model k) (D k) (γhat k) y))

def ResidualMisspecification : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γstar : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γstar y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γstar y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0)),
  InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)-scaledTrue F k)
      (fun k => quadratic (oracleMatrix (F.model k).G)
        (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i)
          -(F.model k).theta i*(D k *ᵥ γstar) i) / (F.size k : ℝ))

def ResidualFailure : Prop :=
  Scaling unstableFamily 2 1 2 3 ∧
    (∀ k, let D : Matrix (Fin (4*(k+1))) (Fin 2) ℝ := fun i j =>
      if j=0 then 1 else (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
      MeanModel (unstableFamily.model k) D 0 ∧
      var (unstableFamily.model k) (fun y => ols D y 0) =
        (unstableFamily.size k : ℝ)/2+1/(2*(unstableFamily.size k : ℝ)) ∧
      expectation (unstableFamily.model k) (fun y => (unstableFamily.size k : ℝ)*
        VResidual (unstableFamily.model k).G
          (fittedResidual (unstableFamily.model k) D (ols D) y)) =
        (unstableFamily.size k : ℝ)+2-7/(unstableFamily.size k : ℝ)) ∧
    ¬ InProbability unstableFamily
      (fun k y => let D : Matrix (Fin (4*(k+1))) (Fin 2) ℝ := fun i j =>
        if j=0 then 1 else (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
        (unstableFamily.size k : ℝ)*VResidual (unstableFamily.model k).G
          (fittedResidual (unstableFamily.model k) D (ols D) y)) (fun _ => 2)

def ResidualPerturbation : Prop :=
  ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = M j i) (r z : Fin n → ℝ),
  |quadratic M r-quadratic M z| ≤ operatorNorm M*l2 (r-z)*(2*l2 z+l2 (r-z))

def UniversalImpossibility : Prop :=
  ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
  (∀ s : ℕ → Bool, Scaling (fixedMeanFamily a b s) (2*a+b) 1 (b^2) 2) ∧
    Scaling (mixtureFamily a b) (a+b) 1 (a^2+b^2) 2 ∧
    (∀ n, (mixtureModel a b n).law =
      ∑ s : (Fin n → Bool), ((2 : ℝ≥0∞)^n)⁻¹ •
        (fixedMeanModel a b (fun i => if hi : i < n then s ⟨i,hi⟩ else false) n).law) ∧
    ¬ (∃ T : ∀ n, (Fin (n+1) → ℝ) → ℝ,
      (∀ n, Measurable (T n)) ∧
      (∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2)) ∧
      InProbability (mixtureFamily a b) T (fun _ => a^2+b^2)) ∧
    (∀ T : ∀ n, (Fin (n+1) → ℝ) → ℝ, (∀ n, Measurable (T n)) →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun k => probability (mixtureModel a b (k+1))
        {y | a^2+b^2-T k y > ε}) atTop (𝓝 0)) →
      ¬ (∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2)))

def MixtureMoments : Prop :=
  ∀ (a b : ℝ) (s : ℕ → Bool) (n : ℕ) (hn : 0 < n),
  (∀ i, expectation (fixedMeanModel a b s n) (fun y => y i)=a*sign (s i.val) ∧
      covariance (fixedMeanModel a b s n) i i=b^2) ∧
    beta (fixedMeanModel a b s n)=average (fun i : Fin n => a*sign (s i.val)) ∧
    (n : ℝ)*var (fixedMeanModel a b s n) (betaHat (fixedMeanModel a b s n))=b^2 ∧
    (∀ i, expectation (mixtureModel a b n) (fun y => y i)=0 ∧
      covariance (mixtureModel a b n) i i=a^2+b^2) ∧
    beta (mixtureModel a b n)=0 ∧
    (n : ℝ)*var (mixtureModel a b n) (betaHat (mixtureModel a b n))=a^2+b^2

def AlternatingCounterexample : Prop :=
  Scaling alternatingFamily 2 1 1 2 ∧ Valid alternatingFamily ∧
    (∀ k, Homoskedastic (alternatingFamily.model k) ∧ beta (alternatingFamily.model k) = 1 ∧
      scaledTrue alternatingFamily k = alternatingWeight (k+1)^2) ∧
    InProbability alternatingFamily
      (fun k y => (k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k) (fun _ => 1) ∧
    Tendsto (fun k => probability (alternatingFamily.model k)
      {y | |(k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k| > 1/2}) atTop (𝓝 1) ∧
    Tendsto (fun k => probability (alternatingFamily.model k)
      {y | |(k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k| < 3/2}) atTop (𝓝 1) ∧
    Conservative alternatingFamily
      (fun k y => V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y))

end
end SAP.P011a
