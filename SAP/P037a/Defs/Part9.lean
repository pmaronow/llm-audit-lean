import SAP.P037a.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

def contrastFinite : Prop :=
  ∀ {B : ℕ} (r : RetainedRow B) (hSize : 0 < populationSize r)
      (s : PairedExposure r) (m : ℕ) (eta K : ℝ)
      (heta : 0 < eta) (hK : 0 ≤ K) (hn : ∀ b, r.students b ≤ m)
      (hb : ∀ b i, eta ≤ r.pi b i ∧ |r.y b i| ≤ K ∧ |r.g b i| ≤ K)
      (h2 : ∀ b i, eta ≤ s.pi b i ∧ |s.y b i| ≤ K ∧ |s.g b i| ≤ K),
    mean (independentDesign r.law) (oracleContrast r s)=populationContrast r s ∧
      variance (independentDesign r.law) (oracleContrast r s)=
        (∑ b, variance (r.law b) (contrastBlockTotal r s b))/(populationSize r:ℝ)^2 ∧
      (∀ b z, |contrastBlockTotal r s b z| ≤ 2*m*(K+2*K/eta)) ∧
      (∀ b, variance (r.law b) (contrastBlockTotal r s b) ≤
        (2*m*(K+2*K/eta))^2)

def contrastLimits : Prop :=
  ∀ (r : ∀ B, RetainedRow (B+1))
      (s : ∀ B, PairedExposure (r B)) (m : ℕ) (c eta K : ℝ)
      (h : BlockBounds r m c eta K)
      (h2 : ∀ B b i, eta ≤ (s B).pi b i ∧ |(s B).y b i| ≤ K ∧ |(s B).g b i| ≤ K),
    (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => rowProbability (r B)
        (fun w => eps < |oracleContrast (r B) (s B) w-populationContrast (r B) (s B)|))
        Filter.atTop (nhds 0)) ∧
      (∀ v : ℝ, 0 < v →
        (∀ B, v*(B+1) ≤ ∑ b, variance ((r B).law b) (contrastBlockTotal (r B) (s B) b)) →
        ∀ x : ℝ, Filter.Tendsto (fun B => rowProbability (r B) (fun w =>
          (populationSize (r B):ℝ)*(oracleContrast (r B) (s B) w-populationContrast (r B) (s B)) /
            Real.sqrt (∑ b, variance ((r B).law b) (contrastBlockTotal (r B) (s B) b)) ≤ x))
          Filter.atTop (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal)))

def fittedSubtractions : Prop :=
  ∀ {B q : ℕ} (r : RetainedRow B) (hSize : 0 < populationSize r)
      (x : Covariates r q) (betaHat betaStar : Fin q → ℝ)
      (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : RowAssignment r)
      (hp : ∀ b i, 0 < p b i),
    fittedMean r x betaHat r.pi w-fittedMean r x betaStar r.pi w =
        (∑ k, ((∑ b, ∑ i,
          (1-(if r.exposed b (w b) i then 1 else 0)/r.pi b i)*x b i k) / populationSize r)*
          (betaHat k-betaStar k)) ∧
      fittedMean r x betaHat p w-fittedMean r x betaHat r.pi w =
        (∑ b, ∑ i, (if r.exposed b (w b) i then 1 else 0)*
          (r.y b i-(∑ k, x b i k*betaHat k)) * ((p b i)⁻¹-(r.pi b i)⁻¹)) / populationSize r

def fittedLimits : Prop :=
  ∀ {q : ℕ} (r : ∀ B, RetainedRow (B+1))
      (x : ∀ B, Covariates (r B) q)
      (pHat : ∀ B, RowAssignment (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
      (m : ℕ) (c eta K L : ℝ) (Q : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ)
      (hbounds : BlockBounds r m c eta K)
      (hx : ∀ B b i k, |x B b i k| ≤ L)
      (hQ : ∀ k l, Filter.Tendsto (fun B => covariateGram (r B) (x B) k l)
        Filter.atTop (nhds (Q k l)))
      (hv : ∀ k, Filter.Tendsto (fun B => covariateRhs (r B) (x B) k)
        Filter.atTop (nhds (v k)))
      (hposQ : ∀ a : Fin q → ℝ, a ≠ 0 → 0 < ∑ k, a k*(Q.mulVec a) k)
      (hp : ∀ B w b i, 0 < pHat B w b i)
      (hSim : ∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => rowProbability (r B)
        (fun w => ∃ b i, eps < Real.sqrt (B+1)*|pHat B w b i-(r B).pi b i|))
        Filter.atTop (nhds 0))
      (hg : ∀ B b i, (r B).g b i = ∑ k, x B b i k*(Q⁻¹.mulVec v) k),
    let betaStar := Q⁻¹.mulVec v
      let betaHat := fun B w => fittedCoefficient (r B) (x B) (pHat B w) w
      let muHat := fun B w => fittedMean (r B) (x B) (betaHat B w) (pHat B w) w
      (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => rowProbability (r B)
        (fun w => ∃ k, eps < |betaHat B w k-betaStar k|)) Filter.atTop (nhds 0)) ∧
      (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => rowProbability (r B)
        (fun w => eps < Real.sqrt (B+1)*|muHat B w-oracleMean (r B) w|))
        Filter.atTop (nhds 0)) ∧
      (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => rowProbability (r B)
        (fun w => eps < |muHat B w-potentialMean (r B)|)) Filter.atTop (nhds 0)) ∧
      (∀ sigmaSquared : ℝ, 0 < sigmaSquared →
        (∀ B, sigmaSquared*(B+1) ≤ totalBlockVariance (r B)) →
        ∀ z : ℝ, Filter.Tendsto (fun B => rowProbability (r B) (fun w =>
          (populationSize (r B):ℝ)*(muHat B w-potentialMean (r B)) /
            Real.sqrt (totalBlockVariance (r B)) ≤ z)) Filter.atTop
          (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic z)).toReal)))

def contrastRate : Prop :=
  ∀ (r : ∀ B, RetainedRow (B+1)) (s : ∀ B, PairedExposure (r B))
    (m : ℕ) (c eta K : ℝ), BlockBounds r m c eta K →
    (∀ B b i, eta ≤ (s B).pi b i ∧ |(s B).y b i| ≤ K ∧ |(s B).g b i| ≤ K) →
    ∀ (B : ℕ) (eps : ℝ), 0 < eps →
    variance (independentDesign (r B).law) (oracleContrast (r B) (s B)) ≤
      (2*m*(K+2*K/eta))^2/(c^2*(B+1)) ∧
    rowProbability (r B)
      (fun w => eps < |oracleContrast (r B) (s B) w-populationContrast (r B) (s B)|) ≤
      (2*m*(K+2*K/eta))^2/(c^2*(B+1)*eps^2)

def contrastLindeberg : Prop :=
  ∀ (r : ∀ B, RetainedRow (B+1)) (s : ∀ B, PairedExposure (r B))
    (m : ℕ) (c eta K v : ℝ), BlockBounds r m c eta K →
    (∀ B b i, eta ≤ (s B).pi b i ∧ |(s B).y b i| ≤ K ∧ |(s B).g b i| ≤ K) →
    0 < v → (∀ B, v*(B+1) ≤ ∑ b, variance ((r B).law b) (contrastBlockTotal (r B) (s B) b)) →
    ∀ (B : ℕ) (eps : ℝ), 0 < eps →
    4*m*(K+2*K/eta) < eps*Real.sqrt (v*(B+1)) →
    (∑ b, mean ((r B).law b) (fun z =>
      let U := contrastBlockTotal (r B) (s B) b z -
        mean ((r B).law b) (contrastBlockTotal (r B) (s B) b)
      U^2 * if eps*Real.sqrt (∑ b, variance ((r B).law b)
        (contrastBlockTotal (r B) (s B) b)) < |U| then 1 else 0)) = 0

def T11Statement : Prop :=
  individualUnbiased ∧ individualBound ∧ blockUnbiased ∧ oracleUnbiasedVariance ∧
  blockIndependence ∧ oracleFiniteBounds ∧ oracleConsistency ∧ oracleNormality ∧
  centeredBlockBound ∧ centeredTotalIdentity ∧ contrastFinite ∧ contrastLimits ∧
  contrastRate ∧ contrastLindeberg ∧ fittedSubtractions ∧ fittedLimits

end SAP.P037a
