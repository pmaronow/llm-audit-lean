import Mathlib
import SAP.P041.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- A genuine positive normal critical point, including uniqueness on the
nonnegative half-line. Only levels strictly between zero and one are used. -/
def NormalCriticalW1 (α c : ℝ) : Prop :=
  0 < c ∧ normalTwoSided c = α ∧
    ∀ d : ℝ, 0 ≤ d → normalTwoSided d = α → d = c

/-- Student's reference density with 197 degrees of freedom. -/
def Student197DensityW1 (t : ℝ) : ℝ :=
  Real.Gamma (99 : ℝ) / (Real.sqrt (197 * Real.pi) * Real.Gamma (197/2)) *
    (1 + t^2/197) ^ (-(99 : ℝ))

/-- Two-sided Student reference probability, as a function of the statistic.
The density is continuous, so this finite interval integral always exists. -/
def Student197TailW1 (x : ℝ) : ℝ :=
  1 - 2 * ∫ t in (0 : ℝ)..|x|, Student197DensityW1 t

def Student197ConstantW1 : ℝ :=
  (4 : ℝ)^98 / ((Nat.choose 196 98 : ℝ) * Real.pi * Real.sqrt 197)

def Student197TaylorW1 (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-1 : ℝ)^j * (Nat.choose (98+j) j : ℝ) * u^j

def Student197IntegratedW1 (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1),
    (-1 : ℝ)^j * (Nat.choose (98+j) j : ℝ) * x^(2*j+1) /
      ((197 : ℝ)^j * (2*j+1 : ℕ))

def CitationRowsW1 {n : ℕ} (cell : Fin n → Fin 4) : Matrix (Fin n) (Fin 3) ℝ :=
  fun i j => citationCellDesign (cell i) j

def BinaryResponseW1 {n : ℕ} (y : Fin n → Bool) : Fin n → ℝ :=
  fun i => if y i then 1 else 0

/-- Exactly the four cells and binary survivor counts in the claim. -/
def CitationInputsW1 (n : ℕ) (cell : Fin n → Fin 4) (y : Fin n → Bool) : Prop :=
  n = 200 ∧
  (∀ c : Fin 4, (Finset.univ.filter (fun i => cell i = c)).card = 50) ∧
  (∀ c : Fin 4, (Finset.univ.filter (fun i => cell i = c ∧ y i = true)).card =
    (![12,25,23,42] : Fin 4 → ℕ) c)

def CitationFitW1 {n : ℕ} (cell : Fin n → Fin 4) (y : Fin n → Bool) : Prop :=
  let X := CitationRowsW1 cell
  let Y := BinaryResponseW1 y
  X.transpose * X = citationGram ∧ X.transpose *ᵥ Y = ![102,67,65] ∧
  IsUnit (X.transpose * X).det ∧ (X.transpose * X)⁻¹ = citationGramInverse ∧
  olsCoefficients X Y = citationBeta ∧
  X *ᵥ olsCoefficients X Y = fun i =>
    (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) (cell i)

def CitationResidualFactsW1 {n : ℕ} (cell : Fin n → Fin 4) (y : Fin n → Bool) : Prop :=
  let X := CitationRowsW1 cell
  let Y := BinaryResponseW1 y
  (∀ c : Fin 4, (∑ i ∈ Finset.univ.filter (fun i => cell i = c),
    (olsResidual X Y i)^2) =
      (![1833/200,2509/200,2493/200,1353/200] : Fin 4 → ℝ) c) ∧
  (∑ i : Fin n, (olsResidual X Y i)^2) = 2047/50 ∧
  (∀ i : Fin n, citationGramInverse 1 ⬝ᵥ X i =
    (![-1/100,1/100,-1/100,1/100] : Fin 4 → ℝ) (cell i)) ∧
  hc1Covariance X Y 1 1 = 2047/492500

def Student197EndpointsW1 : Prop :=
  0.615 < Student197TailW1 (64/129) ∧ Student197TailW1 (64/129) < 0.625 ∧
  0.10 < Student197TailW1 1 ∧
  0.01 < Student197TailW1 2.6005 ∧ Student197TailW1 2.6015 < 0.01

def CitationNormalFactsW1 : Prop :=
  0.615 < normalTwoSided (64/129) ∧ normalTwoSided (64/129) < 0.625 ∧
  (∀ x : ℝ, |x| < 1 → 0.10 < normalTwoSided x) ∧
  ∃ c : ℝ, NormalCriticalW1 0.01 c ∧ 2.5755 < c ∧ c < 2.5765

/-- P041-T7; S11 File, Table A (rendered p. 1); main text p. 4/8 (PDF p. 4).
The four binary-outcome cells give the stated OLS fit and HC1 variance. The
standard error is 0.06446... and rounds to 0.064. The erroneous printed
statistic has a two-sided p value rounding to 0.62 and is not significant at
10%, under either the normal or Student t(197) reference. The corrected
statistic exceeds both genuine 1% critical points, retaining three stars.
The usual measure-theoretic conditions are assumed. These are reference
calculations, not an assertion of an exact sampling law for robust OLS. -/
def T7WholeStatement : Prop :=
  T7Statement ∧
  (∀ (n : ℕ) (cell : Fin n → Fin 4) (y : Fin n → Bool),
    CitationInputsW1 n cell y → CitationFitW1 cell y ∧ CitationResidualFactsW1 cell y) ∧
  0.06446 < Real.sqrt (2047/492500 : ℝ) ∧ Real.sqrt (2047/492500 : ℝ) < 0.06447 ∧
  CitationNormalFactsW1 ∧ Student197EndpointsW1 ∧
  (∀ x : ℝ, |x| < 1 → 0.10 < Student197TailW1 x) ∧
  ∃ cN cT : ℝ,
    NormalCriticalW1 0.01 cN ∧ 2.5755 < cN ∧ cN < 2.5765 ∧
    0 < cT ∧ Student197TailW1 cT = 0.01 ∧
    (∀ d : ℝ, 0 ≤ d → Student197TailW1 d = 0.01 → d = cT) ∧
    2.6005 < cT ∧ cT < 2.6015 ∧ cN < 2.61 ∧ cT < 2.61 ∧
    (let t : ℝ := (8/25) / Real.sqrt (2047/492500)
     t^2 = 50432/2047 ∧ 4.89 < |t| ∧ cN < |t| ∧ cT < |t| ∧
       normalTwoSided t < 0.01 ∧ Student197TailW1 t < 0.01)

/-- Fine uniform certificates, including the domain conditions implied by
each printed rectangle. -/
def CoxRectangleW1 (h₀ s₀ zlo zhi plo phi : ℝ) : Prop :=
  ∀ h s : ℝ, printedInterval h₀ h → printedInterval s₀ s →
    0 < h ∧ h < 1 ∧ 0 < s ∧ zlo ≤ |hazardWald h s| ∧
      |hazardWald h s| ≤ zhi ∧ plo ≤ normalTwoSided (hazardWald h s) ∧
      normalTwoSided (hazardWald h s) ≤ phi

def CoxCentreW1 (h s z p : ℝ) : Prop :=
  hazardWald h s < 0 ∧ |hazardWald h s - z| < 0.00001 ∧
    |normalTwoSided (hazardWald h s) - p| < 0.0000001

def NormalTierEquivalencesW1 (c₁ c₅ c₁₀ : ℝ) : Prop :=
  ∀ z : ℝ,
    (significanceTier z = 3 ↔ c₁ < |z|) ∧
    (significanceTier z = 2 ↔ c₅ < |z| ∧ |z| ≤ c₁) ∧
    (significanceTier z = 1 ↔ c₁₀ < |z| ∧ |z| ≤ c₅) ∧
    (significanceTier z = 0 ↔ |z| ≤ c₁₀)

/-- P041-T8; S6 File, Tables B and E (rendered pp. 2–3), and S9 File,
Table A (rendered p. 1); main text p. 4/8 (PDF p. 4).
All four rounding rectangles have the stated Wald and Gaussian p enclosures,
central approximations, and strongest tiers 3, 2, 2, 2. The genuine normal
critical points have the stated approximations and give exactly the same
tier rule. Under nested cutoffs the first three printed weaker levels hold;
the fourth printed 1% assertion fails. The usual measure-theoretic conditions
are assumed. Decimal ellipses are approximations with explicit errors. -/
def T8WholeStatement : Prop :=
  T8Statement ∧
  CoxRectangleW1 0.670 0.095 2.8064 2.8426 0.004416378 0.005073862 ∧
  CoxRectangleW1 0.480 0.174 2.0181 2.0314 0.041792640 0.044011941 ∧
  CoxRectangleW1 0.274 0.162 2.1820 2.1974 0.027554610 0.029563591 ∧
  CoxRectangleW1 0.316 0.149 2.4345 2.4520 0.013945057 0.015189259 ∧
  (∀ h s : ℝ, printedInterval 0.670 h → printedInterval 0.095 s →
    0.0044 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.0051) ∧
  (∀ h s : ℝ, printedInterval 0.480 h → printedInterval 0.174 s →
    0.041 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.045) ∧
  (∀ h s : ℝ, printedInterval 0.274 h → printedInterval 0.162 s →
    0.027 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.030) ∧
  (∀ h s : ℝ, printedInterval 0.316 h → printedInterval 0.149 s →
    0.0139 < normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.0152) ∧
  CoxCentreW1 0.670 0.095 (-2.82442) 0.0047366 ∧
  CoxCentreW1 0.480 0.174 (-2.02474) 0.0428938 ∧
  CoxCentreW1 0.274 0.162 (-2.18967) 0.0285475 ∧
  CoxCentreW1 0.316 0.149 (-2.44319) 0.0145578 ∧
  ∃ c₁ c₅ c₁₀ : ℝ,
    NormalCriticalW1 0.01 c₁ ∧ |c₁ - 2.5758293| < 0.0000001 ∧
    NormalCriticalW1 0.05 c₅ ∧ |c₅ - 1.9599640| < 0.0000001 ∧
    NormalCriticalW1 0.10 c₁₀ ∧ |c₁₀ - 1.6448536| < 0.0000001 ∧
    NormalTierEquivalencesW1 c₁ c₅ c₁₀ ∧
    c₁ < 2.80 ∧ c₅ < 2.01 ∧ 2.04 < c₁ ∧
    c₅ < 2.18 ∧ 2.20 < c₁ ∧ c₅ < 2.43 ∧ 2.46 < c₁

def BalancedCellsW1 {n r : ℕ} (study : Fin n → Fin r) (treated : Fin n → Bool) : Prop :=
  ∀ (w : Fin r) (b : Bool),
    (Finset.univ.filter (fun i => study i = w ∧ treated i = b)).card = 50

def PositiveRowsW1 {n : ℕ} (study : Fin n → Fin 3) (treated : Fin n → Bool) :
    Matrix (Fin n) (Fin 4) ℝ := fun i =>
  ![1, if treated i then 1 else 0, if study i = 1 then 1 else 0,
    if study i = 2 then 1 else 0]

def CitedRowsW1 {n : ℕ} (study : Fin n → Fin 2) (treated : Fin n → Bool) :
    Matrix (Fin n) (Fin 3) ℝ := fun i =>
  ![1, if treated i then 1 else 0, if study i = 1 then 1 else 0]

def FormerRowsW1 {n : ℕ} (treated : Fin n → Bool) : Matrix (Fin n) (Fin 2) ℝ :=
  fun i => ![1, if treated i then 1 else 0]

def ArmTotalW1 {n : ℕ} (treated : Fin n → Bool) (b : Bool) (Y : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => treated i = b), Y i

def StudyTotalW1 {n r : ℕ} (study : Fin n → Fin r) (w : Fin r) (Y : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => study i = w), Y i

def PositiveDesignFactsW1 : Prop :=
  ∀ (n : ℕ) (study : Fin n → Fin 3) (treated : Fin n → Bool) (Y : Fin n → ℝ),
    BalancedCellsW1 study treated →
    n = 300 ∧
    (PositiveRowsW1 study treated).transpose * PositiveRowsW1 study treated = positiveStudyGram ∧
    IsUnit ((PositiveRowsW1 study treated).transpose * PositiveRowsW1 study treated).det ∧
    (PositiveRowsW1 study treated).transpose *ᵥ Y =
      ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y,
        ArmTotalW1 treated true Y, StudyTotalW1 study 1 Y, StudyTotalW1 study 2 Y] ∧
    olsCoefficients (PositiveRowsW1 study treated) Y 1 =
      ArmTotalW1 treated true Y / 150 - ArmTotalW1 treated false Y / 150

def CitedDesignFactsW1 : Prop :=
  ∀ (n : ℕ) (study : Fin n → Fin 2) (treated : Fin n → Bool) (Y : Fin n → ℝ),
    BalancedCellsW1 study treated →
    n = 200 ∧
    (CitedRowsW1 study treated).transpose * CitedRowsW1 study treated = citationGram ∧
    IsUnit ((CitedRowsW1 study treated).transpose * CitedRowsW1 study treated).det ∧
    (CitedRowsW1 study treated).transpose *ᵥ Y =
      ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y,
        ArmTotalW1 treated true Y, StudyTotalW1 study 1 Y] ∧
    olsCoefficients (CitedRowsW1 study treated) Y 1 =
      ArmTotalW1 treated true Y / 100 - ArmTotalW1 treated false Y / 100

def FormerDesignFactsW1 : Prop :=
  ∀ (n : ℕ) (treated : Fin n → Bool) (Y : Fin n → ℝ),
    (Finset.univ.filter (fun i => treated i = true)).card = 75 →
    (Finset.univ.filter (fun i => treated i = false)).card = 76 →
    n = 151 ∧
    (FormerRowsW1 treated).transpose * FormerRowsW1 treated = !![151,75;75,75] ∧
    IsUnit ((FormerRowsW1 treated).transpose * FormerRowsW1 treated).det ∧
    (FormerRowsW1 treated).transpose *ᵥ Y =
      ![ArmTotalW1 treated true Y + ArmTotalW1 treated false Y, ArmTotalW1 treated true Y] ∧
    olsCoefficients (FormerRowsW1 treated) Y 1 =
      ArmTotalW1 treated true Y / 75 - ArmTotalW1 treated false Y / 76

/-- Columns are 6, 12, 24 and 168 hours throughout the S11 tables below. -/
def S11HorizonsW1 : Fin 4 → ℝ := ![6,12,24,168]

/-- Rows are the positive, cited and former-senator regressions. -/
def S11SurvivalTableW1 : Fin 3 → Fin 4 → ℝ :=
  ![![17/150,23/150,11/75,19/150], ![8/25,37/100,39/100,23/100],
    ![-51/1900,-51/1900,-51/1900,-307/5700]]

def S11PrintedTableW1 : Fin 3 → Fin 4 → ℝ :=
  ![![0.113,0.153,0.147,0.127], ![0.320,0.370,0.390,0.230],
    ![-0.027,-0.027,-0.027,-0.054]]

def S11TreatedSurvivorsW1 : Fin 3 → Fin 4 → ℝ :=
  ![![105,98,90,68], ![67,63,58,34], ![72,72,72,68]]

def S11ControlSurvivorsW1 : Fin 3 → Fin 4 → ℝ :=
  ![![88,75,68,49], ![35,26,19,11], ![75,75,75,73]]

def SurvivalAndRemovalSlopeW1 {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ)
    (Y : Fin n → ℝ) (j : Fin k) (b v : ℝ) : Prop :=
  olsCoefficients X Y j = b ∧ olsCoefficients X (1-Y) j = -b ∧ b ≠ 0 ∧
    withinPrintedPrecision b v ∧ ¬ withinPrintedPrecision (-b) v

/-- The supplied survivor counts give actual regression coefficients, and
complementing these outcomes gives their negative coefficients. The arbitrary
real Y includes Y_i=survivalIndicator r_i (S11HorizonsW1 h). -/
def S11RegressionFactsW1 : Prop :=
  (∀ (n : ℕ) (study : Fin n → Fin 3) (treated : Fin n → Bool) (Y : Fin n → ℝ) (h : Fin 4),
    BalancedCellsW1 study treated →
    ArmTotalW1 treated true Y = S11TreatedSurvivorsW1 0 h →
    ArmTotalW1 treated false Y = S11ControlSurvivorsW1 0 h →
    SurvivalAndRemovalSlopeW1 (PositiveRowsW1 study treated) Y 1
      (S11SurvivalTableW1 0 h) (S11PrintedTableW1 0 h)) ∧
  (∀ (n : ℕ) (study : Fin n → Fin 2) (treated : Fin n → Bool) (Y : Fin n → ℝ) (h : Fin 4),
    BalancedCellsW1 study treated →
    ArmTotalW1 treated true Y = S11TreatedSurvivorsW1 1 h →
    ArmTotalW1 treated false Y = S11ControlSurvivorsW1 1 h →
    SurvivalAndRemovalSlopeW1 (CitedRowsW1 study treated) Y 1
      (S11SurvivalTableW1 1 h) (S11PrintedTableW1 1 h)) ∧
  (∀ (n : ℕ) (treated : Fin n → Bool) (Y : Fin n → ℝ) (h : Fin 4),
    (Finset.univ.filter (fun i => treated i = true)).card = 75 →
    (Finset.univ.filter (fun i => treated i = false)).card = 76 →
    ArmTotalW1 treated true Y = S11TreatedSurvivorsW1 2 h →
    ArmTotalW1 treated false Y = S11ControlSurvivorsW1 2 h →
    SurvivalAndRemovalSlopeW1 (FormerRowsW1 treated) Y 1
      (S11SurvivalTableW1 2 h) (S11PrintedTableW1 2 h))

/-- P041-T9; S11 File, first paragraph and Tables A and B (rendered p. 1);
main text p. 4/8 (PDF p. 4).
Complementing an outcome reverses all slopes and residuals and preserves the
robust meat. HC1 covariances and standard errors agree whenever their divisor
exists. The stated balanced designs imply full rank and the difference-of-arm
survival slopes, reproducing all twelve entries and excluding their removal
interpretation. The six-hour full vectors and the initialization/replacement
rules give the stated coding correction. The usual measure-theoretic
conditions are assumed; the sample-size guard applies only to HC1. -/
def T9WholeStatement : Prop :=
  (∀ (n k : ℕ) (j₀ : Fin k) (X : Matrix (Fin n) (Fin k) ℝ) (S : Fin n → ℝ),
    IsUnit (X.transpose * X).det → (∀ i, X i j₀ = 1) →
    olsCoefficients X (1-S) = Pi.single j₀ 1 - olsCoefficients X S ∧
    olsResidual X (1-S) = -olsResidual X S ∧
    robustMeat X (olsResidual X (1-S)) = robustMeat X (olsResidual X S) ∧
    (k < n → hc1Covariance X (1-S) = hc1Covariance X S ∧
      ∀ j, Real.sqrt (hc1Covariance X (1-S) j j) = Real.sqrt (hc1Covariance X S j j))) ∧
  PositiveDesignFactsW1 ∧ CitedDesignFactsW1 ∧ FormerDesignFactsW1 ∧ S11RegressionFactsW1 ∧
  (∀ (m : Fin 3) (h : Fin 4),
    armSurvivalDifference ((![150,100,75] : Fin 3 → ℝ) m)
      ((![150,100,76] : Fin 3 → ℝ) m)
      (S11TreatedSurvivorsW1 m h) (S11ControlSurvivorsW1 m h) = S11SurvivalTableW1 m h ∧
    S11SurvivalTableW1 m h ≠ 0 ∧
    withinPrintedPrecision (S11SurvivalTableW1 m h) (S11PrintedTableW1 m h) ∧
    ¬ withinPrintedPrecision (-S11SurvivalTableW1 m h) (S11PrintedTableW1 m h)) ∧
  (∀ (n : ℕ) (study : Fin n → Fin 3) (treated : Fin n → Bool) (Y : Fin n → ℝ),
    BalancedCellsW1 study treated → ArmTotalW1 treated true Y = 105 →
    ArmTotalW1 treated false Y = 88 → StudyTotalW1 study 1 Y = 91 → StudyTotalW1 study 2 Y = 65 →
    (PositiveRowsW1 study treated).transpose *ᵥ Y = ![193,105,91,65] ∧
    (PositiveRowsW1 study treated).transpose *ᵥ (1-Y) = ![107,45,9,35] ∧
    olsCoefficients (PositiveRowsW1 study treated) Y = ![47/150,17/150,27/50,7/25] ∧
    olsCoefficients (PositiveRowsW1 study treated) (1-Y) = ![103/150,-17/150,-27/50,-7/25]) ∧
  (∀ (r : Option ℝ) (h : ℝ),
    (if (∃ t : ℝ, r = some t ∧ t ≤ h) then (0 : ℝ) else 1) = survivalIndicator r h ∧
    (if (∃ t : ℝ, r = some t ∧ t ≤ h) then (1 : ℝ) else 0) = removalIndicator r h)

/-- Product likelihood of the four supplied 12-hour counts under independent
fact lifetimes with the indicated exponential laws. -/
def ModelCountLikelihoodW1 (qA qF : ℝ) : ℝ :=
  binomialCountProbability 150 75 (1-exponentialSurvival (negativeHazard qA) 12) *
  binomialCountProbability 150 52 (1-exponentialSurvival (positiveHazard qA) 12) *
  binomialCountProbability 76 1 (1-exponentialSurvival (negativeHazard qF) 12) *
  binomialCountProbability 75 3 (1-exponentialSurvival (positiveHazard qF) 12)

/-- The stipulated evidence-to-population implication of canonical P2.
The test summaries are supplied observations; compatibility means strictly
positive probability of the supplied counts, not refitting Cox from counts. -/
def SuppliedEvidenceImpliesNullW1 : Prop :=
  ∀ qA qF : ℝ, 0 < qA → qA < 1 → 0 < qF → qF < 1 →
    normalTwoSided (hazardWald 0.629 0.091) < 0.01 →
    0.10 < normalTwoSided (hazardWald 0.691 0.318) →
    |observedSurvivalContrast 75 76 3 1| < |observedSurvivalContrast 150 150 52 75| →
    0 < twelveHourContrast qF → twelveHourContrast qF < twelveHourContrast qA →
    0 < ModelCountLikelihoodW1 qA qF → positiveHazard qF / negativeHazard qF = 1

/-- P041-T11; p. 5/8 (PDF p. 5); Abstract p. 1/8 (PDF p. 1).
The printed claim is false: the stipulated implication from active rejection,
former nondetection and smaller absolute contrasts to absence of former
relative bias has an independent-exponential countermodel with common ratio
2/3, exact contrasts and strictly positive count likelihood. The valid three
former p-value calculations, rounding compatibility and relative-effect
imprecision are retained. The usual measure-theoretic conditions are assumed.
This refutes the stated evidence-sufficiency implication, not an assertion
about the actual presence of a cultural or policy mechanism on Wikipedia. -/
def T11WholeStatement : Prop :=
  ¬ SuppliedEvidenceImpliesNullW1 ∧ T11Statement ∧ T2Statement ∧
  (∀ h s : ℝ, printedInterval 0.629 h → printedInterval 0.091 s →
    normalTwoSided (hazardWald h s) < 0.01) ∧
  (∀ h s : ℝ, printedInterval 0.691 h → printedInterval 0.318 s →
    0.415 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.425) ∧
  (∀ h s : ℝ, printedInterval 0.627 h → printedInterval 0.406 s →
    0.465 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.475) ∧
  (∃ h s : ℝ, 0.7745 < h ∧ h < 0.7755 ∧ 0.5025 < s ∧ s < 0.5035 ∧
    0.695 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) < 0.705) ∧
  |observedSurvivalContrast 75 76 3 1| < |observedSurvivalContrast 150 150 52 75| ∧
  |observedSurvivalContrast 75 76 7 3| < |observedSurvivalContrast 150 150 82 101| ∧
  0 < positiveHazard (4/5) ∧ 0 < negativeHazard (4/5) ∧
  0 < positiveHazard (99/100) ∧ 0 < negativeHazard (99/100) ∧
  positiveHazard (4/5) / negativeHazard (4/5) = 2/3 ∧
  positiveHazard (99/100) / negativeHazard (99/100) = 2/3 ∧ (2/3 : ℝ) ≠ 1 ∧
  twelveHourContrast (4/5) = 16/125 ∧ twelveHourContrast (99/100) = 9801/1000000 ∧
  0 < twelveHourContrast (99/100) ∧
  13 * twelveHourContrast (99/100) < twelveHourContrast (4/5) ∧
  1-exponentialSurvival (negativeHazard (4/5)) 12 = 61/125 ∧
  1-exponentialSurvival (positiveHazard (4/5)) 12 = 9/25 ∧
  1-exponentialSurvival (negativeHazard (99/100)) 12 = 29701/1000000 ∧
  1-exponentialSurvival (positiveHazard (99/100)) 12 = 199/10000 ∧
  0 < binomialCountProbability 150 75 (61/125) ∧
  0 < binomialCountProbability 150 52 (9/25) ∧
  0 < binomialCountProbability 76 1 (29701/1000000) ∧
  0 < binomialCountProbability 75 3 (199/10000) ∧
  0 < ModelCountLikelihoodW1 (4/5) (99/100)

/-- P041-T12; Abstract p. 1/8 (PDF p. 1); Effects of Citations on Survival,
pp. 4/8–5/8 (PDF pp. 4–5).
The printed claim is false: under the stated directional reading of “more
likely than”, each of 36%, 29% and 64% fails separately. The exact directional
increases are 575/13, 100/3 and 375/4, rounding to 44%, 33% and 94%. The
symmetric percentages do round to the printed numbers and all three removal
comparisons have the stated direction. The usual measure-theoretic conditions
are assumed. This refutation concerns the three directional percentages. -/
def T12WholeStatement : Prop :=
  T12Statement ∧
  relativeIncrease (75/150) (52/150) = 575/13 ∧
  relativeIncrease (92/150) (69/150) = 100/3 ∧
  relativeIncrease (62/100) (32/100) = 375/4 ∧
  ¬ roundsWhole (relativeIncrease (75/150) (52/150)) 36 ∧
  ¬ roundsWhole (relativeIncrease (92/150) (69/150)) 29 ∧
  ¬ roundsWhole (relativeIncrease (62/100) (32/100)) 64 ∧
  roundsWhole (relativeIncrease (75/150) (52/150)) 44 ∧
  roundsWhole (relativeIncrease (92/150) (69/150)) 33 ∧
  roundsWhole (relativeIncrease (62/100) (32/100)) 94

end SAP.P041
