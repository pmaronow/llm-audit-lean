import Mathlib
import SAP.P026a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a

open Finset
open scoped BigOperators
noncomputable section

/-- The ninety equiprobable allocations of the printed numerical example. -/
abbrev W2Allocation := Fin 6 × Fin 15

/-- Fitted values, over the sixteen original units, with rational input data. -/
def w2Predict {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℚ)
    (c : Fin k → ℚ) (i : Fin 16) : ℚ := ∑ j, A i j * c j

/-- The weighted Gram matrix; its determinant is certified nonzero below. -/
def w2Gram {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℚ)
    (q : Fin 16 → ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  fun j l => ∑ i, q i * A i j * A i l

/-- Actual real weighted sum of squared residuals, allowing real competitors. -/
def w2Loss {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℚ)
    (q y : Fin 16 → ℚ) (c : Fin k → ℝ) : ℝ :=
  ∑ i, (q i : ℝ) * ((y i : ℝ) - ∑ j, (A i j : ℝ) * c j)^2

/-- The specified coefficient vector uniquely minimizes the real least-squares
objective. Zero weights omit units, as in a fit on just one block. -/
def w2UniqueFit {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℚ)
    (q y : Fin 16 → ℚ) (c : Fin k → ℚ) : Prop :=
  (∀ d : Fin k → ℝ, w2Loss A q y (fun j => (c j : ℝ)) ≤ w2Loss A q y d) ∧
  (∀ d : Fin k → ℝ,
    w2Loss A q y d = w2Loss A q y (fun j => (c j : ℝ)) →
    d = fun j => (c j : ℝ))

/-- Algebraic certificate sufficient for a unique weighted least-squares fit. -/
def w2ValidFit {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℚ)
    (q y : Fin 16 → ℚ) (c : Fin k → ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (w2Gram A q).det ≠ 0 ∧
    ∀ j, (∑ i, q i * A i j * (y i - w2Predict A c i)) = 0

def w2LinearDesign : Matrix (Fin 16) (Fin 2) ℚ := fun i => ![1, paperTableX i]

/-- `false` selects the first block; `true` selects the second block. -/
def w2BlockWeight (b : Bool) (i : Fin 16) : ℚ :=
  if (if b then 6 ≤ i.val else i.val < 6) then 1 else 0

/-- Coefficients fitted on the selected block, hence used on the other block. -/
def w2LinearBeta (b : Bool) : Fin 2 → ℚ :=
  if b then ![1/4, 1/8] else ![70/93, 1/31]

def w2Treatment (w : W2Allocation) (i : Fin 16) : ℚ :=
  armIndicator paperTableUnitDesign true w i

def w2FeCovDesign (w : W2Allocation) : Matrix (Fin 16) (Fin 4) ℚ :=
  fun i => ![1, w2Treatment w i, if 6 ≤ i.val then 1 else 0, paperTableX i]

/-- Full coefficient vector of FE (Cov.), with columns (1,T,block2,X). -/
def w2FeCovBeta (w : W2Allocation) : Fin 4 → ℚ :=
  let a := 5/6 - paperFeEstimate w * paperTableTreatmentMean w false -
    paperFeXCoefficient w * (5/2)
  ![a, paperFeEstimate w,
    3/5 - paperFeEstimate w * paperTableTreatmentMean w true -
      paperFeXCoefficient w * (14/5) - a,
    paperFeXCoefficient w]

/-- Inverse inclusion weights 1/pi_(observed arm,i), using the printed
block probabilities. Equality to the actual design marginals is asserted. -/
def w2IPWWeight (w : W2Allocation) (i : Fin 16) : ℚ :=
  if i.val < 6 then 2 else if paperTableUnitDesign.treatment w i then 3 else 3/2

def w2IPWDesign (w : W2Allocation) : Matrix (Fin 16) (Fin 2) ℚ :=
  fun i => ![1, w2Treatment w i]

def w2IPWArmWeight (w : W2Allocation) (a : Bool) : ℚ :=
  ∑ i, if paperTableUnitDesign.treatment w i = a then w2IPWWeight w i else 0

def w2IPWArmMean (w : W2Allocation) (a : Bool) : ℚ :=
  (∑ i, if paperTableUnitDesign.treatment w i = a then
    w2IPWWeight w i * paperTableY i else 0) / w2IPWArmWeight w a

/-- IPW is the difference of the inverse-probability weighted arm means,
equivalently the treatment coefficient in WLS on (1,T). -/
def w2IPWBeta (w : W2Allocation) : Fin 2 → ℚ :=
  ![w2IPWArmMean w false, w2IPWArmMean w true - w2IPWArmMean w false]

def w2IPWEstimate (w : W2Allocation) : ℚ := w2IPWBeta w 1

def w2FeDesign (w : W2Allocation) : Matrix (Fin 16) (Fin 3) ℚ :=
  fun i => ![1, w2Treatment w i, if 6 ≤ i.val then 1 else 0]

/-- FE without X: the within-block treatment slope. Its denominator is
proved strictly positive on every allocation. -/
def w2FeEstimate (w : W2Allocation) : ℚ :=
  (∑ i, paperTableCenteredT w i * paperTableCenteredY i) /
    (∑ i, (paperTableCenteredT w i)^2)

def w2FeBeta (w : W2Allocation) : Fin 3 → ℚ :=
  let a := 5/6 - w2FeEstimate w * paperTableTreatmentMean w false
  ![a, w2FeEstimate w, 3/5 - w2FeEstimate w * paperTableTreatmentMean w true - a]

/-- Treatment-coordinate clustered HC1 sandwich. For G=10 clusters, N=16
units and k regressors (including the intercept), the factor is
(10/9)*15/(16-k). The squared inverse-Gram row times each cluster score
is the corresponding diagonal of B⁻¹(sum score*scoreᵀ)B⁻¹.
Only k=2,3 is used, with nonzero Gram determinants and positive 16-k.
This fixes the small-sample convention left implicit in the paper. -/
def w2ClusterHC1 {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℚ)
    (q y : Fin 16 → ℚ) (c : Fin k → ℚ) (t : Fin k) : ℚ :=
  (10/9) * (15 / (16 - (k : ℚ))) *
    ∑ g : Fin 10, (∑ j, (w2Gram A q)⁻¹ t j *
      ∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => paperTableCluster i = g),
        q i * A i j * (y i - w2Predict A c i))^2

def w2IPWVariance (w : W2Allocation) : ℚ :=
  w2ClusterHC1 (w2IPWDesign w) (w2IPWWeight w) paperTableY (w2IPWBeta w) 1

def w2FeVariance (w : W2Allocation) : ℚ :=
  w2ClusterHC1 (w2FeDesign w) (fun _ => 1) paperTableY (w2FeBeta w) 1

def w2LinearEstimate : W2Allocation → ℚ :=
  htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual

def w2LinearVariance : W2Allocation → ℚ :=
  printedVarianceEstimate paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual

def w2HTEstimate : W2Allocation → ℚ :=
  htContrast paperTableDesign 16 paperTableClusterY paperTableClusterY

def w2HTVariance : W2Allocation → ℚ :=
  printedVarianceEstimate paperTableDesign 16 paperTableClusterY paperTableClusterY

def w2PriorEstimate : W2Allocation → ℚ :=
  htContrast paperTableDesign 16 paperTablePriorResidual paperTablePriorResidual

def w2PriorVariance : W2Allocation → ℚ :=
  printedVarianceEstimate paperTableDesign 16 paperTablePriorResidual paperTablePriorResidual

/-- Three-decimal rounding with the lower endpoint included. -/
def w2RealRounds (x : ℝ) (r : ℚ) : Prop :=
  (r : ℝ) - 1/2000 ≤ x ∧ x < (r : ℝ) + 1/2000

/-- All ten Table 2 rows, using actual real square roots, population moments
(division by 90), and the true ATE zero. Biases and RMSEs refer respectively
to the ATE and the true design variance of the ATE estimator. -/
def w2TableColumn (e v : W2Allocation → ℚ) : Fin 10 → ℝ :=
  let m := mean paperTableDesign e
  let s := designVariance paperTableDesign e
  let a := mean paperTableDesign v
  let z := designVariance paperTableDesign v
  ![0, (m : ℝ), (m : ℝ), Real.sqrt (s : ℝ), Real.sqrt ((s + m^2 : ℚ) : ℝ),
    (s : ℝ), (a : ℝ), ((a-s : ℚ) : ℝ), Real.sqrt (z : ℝ),
    Real.sqrt ((z + (a-s)^2 : ℚ) : ℝ)]

def w2PrintedColumn (m s rm v ev bv sv rv : ℚ) : Fin 10 → ℚ :=
  ![0, m, m, s, rm, v, ev, bv, sv, rv]

def w2ColumnRounds (e v : W2Allocation → ℚ) (r : Fin 10 → ℚ) : Prop :=
  ∀ j, w2RealRounds (w2TableColumn e v j) (r j)

/-- Rational certificates for the four nonconstant ATE rows. Square-root
certificates are used only with positive lower endpoints in the assembly. -/
def w2ATECertificate (e : W2Allocation → ℚ) (m s rm v : ℚ) : Prop :=
  roundsToThree (mean paperTableDesign e) m ∧
  sdRoundsToThree (designVariance paperTableDesign e) s ∧
  sdRoundsToThree (designVariance paperTableDesign e + (mean paperTableDesign e)^2) rm ∧
  roundsToThree (designVariance paperTableDesign e) v

/-- Rational certificates for the four variance-estimator rows. -/
def w2VarianceCertificate (e v : W2Allocation → ℚ) (ev bv sv rv : ℚ) : Prop :=
  roundsToThree (mean paperTableDesign v) ev ∧
  roundsToThree (mean paperTableDesign v - designVariance paperTableDesign e) bv ∧
  sdRoundsToThree (designVariance paperTableDesign v) sv ∧
  sdRoundsToThree (designVariance paperTableDesign v +
    (mean paperTableDesign v - designVariance paperTableDesign e)^2) rv

/-- P026-T7; Table 2, p. 149 (PDF p. 15); Table 1, p. 147 (PDF p. 13);
Section 7.1, p. 148 (PDF p. 14).
For the printed population and ninety equiprobable assignments, the opposite-block
lines are the unique OLS fits, and FE (Cov.) is the unique OLS regression on
(1,T,block2,X). G (Linear) has mean zero, variance and expected equation [35]
variance estimate 38307/634880, and variance-estimator variance
2400328658503/15687787688755200. Its complete corrected column is
(0,0,0,.246,.246,.060,.060,0,.012,.012). FE (Cov.) has corrected ATE mean and
bias -.014, SE and RMSE .279, and variance .078, with the stated strict mean
and variance intervals; G (Linear) has the smaller RMSE.
All columns without X are unchanged: HT
(0,0,0,.429,.429,.184,.184,0,.037,.037), G (Prior)
(0,0,0,.302,.302,.091,.091,0,.020,.020), IPW
(0,-.014,-.014,.276,.277,.076,.071,-.005,.017,.018), and FE
(0,-.016,-.016,.283,.283,.080,.074,-.006,.019,.020).
HT and prior are unbiased, with variance equal to expected equation [35]
variance estimate 353/1920 and 233/2560, respectively. Their variance-estimator
variances are 10147/7372800 and 20083/52428800. IPW is WLS with inverse
observed-arm inclusion weights, and FE is OLS on (1,T,block2); both fits are
unique. Their clustered variance estimates use the explicit HC1 convention
(10/9)*15/(16-k), k=2,3. All inverses and arm denominators exist on every
assignment. The usual measure-theoretic conditions are assumed; here every
quantity is a moment of a function on a fixed finite probability space. -/
def T7WholeStatement : Prop :=
  T7Statement ∧
  averageEffect 16 paperTableY paperTableY = 0 ∧
  (∀ b, w2UniqueFit w2LinearDesign (w2BlockWeight b) paperTableY (w2LinearBeta b)) ∧
  (∀ w, w2UniqueFit (w2FeCovDesign w) (fun _ => 1) paperTableY (w2FeCovBeta w)) ∧
  (∀ w, (∀ i, 0 < w2IPWWeight w i ∧
      w2IPWWeight w i = 1 / inclusion paperTableUnitDesign
        (paperTableUnitDesign.treatment w i) i) ∧
    0 < w2IPWArmWeight w true ∧ 0 < w2IPWArmWeight w false ∧
    (w2Gram (w2IPWDesign w) (w2IPWWeight w)).det ≠ 0 ∧
    w2UniqueFit (w2IPWDesign w) (w2IPWWeight w) paperTableY (w2IPWBeta w)) ∧
  (∀ w, 0 < (∑ i, (paperTableCenteredT w i)^2) ∧
    (w2Gram (w2FeDesign w) (fun _ => 1)).det ≠ 0 ∧
    w2UniqueFit (w2FeDesign w) (fun _ => 1) paperTableY (w2FeBeta w)) ∧
  (∀ w, adjustedContrast paperTableUnitDesign 16 paperTableY paperTableY
      (fun _ i => paperTableLinearPrediction i) w = w2LinearEstimate w ∧
    adjustedContrast paperTableUnitDesign 16 paperTableY paperTableY
      (fun _ _ => 0) w = w2HTEstimate w ∧
    adjustedContrast paperTableUnitDesign 16 paperTableY paperTableY
      (fun _ _ => 1/2) w = w2PriorEstimate w) ∧
  designVariance paperTableDesign w2HTVariance = 10147/7372800 ∧
  designVariance paperTableDesign w2PriorVariance = 20083/52428800 ∧
  w2ColumnRounds w2LinearEstimate w2LinearVariance
    (w2PrintedColumn 0 (246/1000) (246/1000) (60/1000) (60/1000) 0 (12/1000) (12/1000)) ∧
  w2ColumnRounds w2HTEstimate w2HTVariance
    (w2PrintedColumn 0 (429/1000) (429/1000) (184/1000) (184/1000) 0 (37/1000) (37/1000)) ∧
  w2ColumnRounds w2PriorEstimate w2PriorVariance
    (w2PrintedColumn 0 (302/1000) (302/1000) (91/1000) (91/1000) 0 (20/1000) (20/1000)) ∧
  w2ColumnRounds w2IPWEstimate w2IPWVariance
    (w2PrintedColumn (-14/1000) (276/1000) (277/1000) (76/1000) (71/1000) (-5/1000) (17/1000) (18/1000)) ∧
  w2ColumnRounds w2FeEstimate w2FeVariance
    (w2PrintedColumn (-16/1000) (283/1000) (283/1000) (80/1000) (74/1000) (-6/1000) (19/1000) (20/1000)) ∧
  w2RealRounds (Real.sqrt ((designVariance paperTableDesign paperFeEstimate : ℚ) : ℝ)) (279/1000) ∧
  w2RealRounds (Real.sqrt ((designVariance paperTableDesign paperFeEstimate +
    (mean paperTableDesign paperFeEstimate)^2 : ℚ) : ℝ)) (279/1000) ∧
  Real.sqrt ((38307/634880 : ℚ) : ℝ) <
    Real.sqrt ((designVariance paperTableDesign paperFeEstimate +
      (mean paperTableDesign paperFeEstimate)^2 : ℚ) : ℝ)

end
end SAP.P026a
