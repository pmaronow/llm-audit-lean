import SAP.P039.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/- Ordinary least squares uses an injective design map, the inverse Gram matrix,
Euclidean squared residuals, and conventional residual degrees of freedom.
The tail formulas are the nominal analytic p-values specified by target T3.
The Student and chi-square laws are explicit product-Gaussian pushforwards. -/

noncomputable def squaredLength {n : ℕ} (v : Fin n → ℝ) : ℝ := dotProduct v v

noncomputable def FullColumnRank {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  Function.Injective A.mulVec

noncomputable def ols {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (c : Fin n → ℝ) : Fin p → ℝ :=
  (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ c)

noncomputable def olsResidual {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (c : Fin n → ℝ) : Fin n → ℝ :=
  c - A *ᵥ ols A c

noncomputable def olsSSE {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (c : Fin n → ℝ) : ℝ :=
  squaredLength (olsResidual A c)

noncomputable def olsSESquared {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin n → ℝ) (j : Fin p) : ℝ :=
  olsSSE A c / ((n : ℝ) - p) * (Aᵀ * A)⁻¹ j j

noncomputable def olsResidualStandardError {n p : ℕ}
    (A : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.sqrt (olsSSE A y / ((n : ℝ)-p))

noncomputable def olsT {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin n → ℝ) (j : Fin p) : ℝ :=
  ols A c j / Real.sqrt (olsSESquared A c j)

noncomputable def olsTSquared {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin n → ℝ) (j : Fin p) : ℝ :=
  (ols A c j) ^ 2 / olsSESquared A c j

noncomputable def IsLeastSquares {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (β : Fin p → ℝ) : Prop :=
  ∀ b, squaredLength (y - A *ᵥ β) ≤ squaredLength (y - A *ᵥ b)

noncomputable def witnessU : Fin 6 → ℝ := ![1, -1, 0, 0, 0, 0]

noncomputable def witnessV : Fin 6 → ℝ := ![0, 0, 1, -1, 0, 0]

noncomputable def witnessW : Fin 6 → ℝ := ![0, 0, 0, 0, 1, -1]

noncomputable def witnessY : Fin 6 → ℝ := ![1, -1, 3/2, -3/2, 1, -1]

noncomputable def witnessZ : Matrix (Fin 6) (Fin 2) ℝ := fun i j => ![1, witnessU i] j

noncomputable def residualLine {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℝ :=
  fun i j => ![1, x i] j

noncomputable def fullDesign {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin (k+1)) ℝ :=
  fun i j => if hj : j.val < k then Z i ⟨j.val, hj⟩ else x i

noncomputable def controlProjection {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Z * (Zᵀ * Z)⁻¹ * Zᵀ

noncomputable def residualMaker {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := 1 - controlProjection Z

noncomputable def studentFourTail (t : ℝ) : ℝ :=
  let z := t / Real.sqrt (4 + t^2)
  1 - (3/2 : ℝ)*z + (1/2 : ℝ)*z^3

noncomputable def studentThreeTail (t : ℝ) : ℝ :=
  let q := t / Real.sqrt 3
  1 - (2 / Real.pi) * (Real.arctan q + q / (1+q^2))

noncomputable def studentLaw (ν : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)).map
    (fun z => z 0 / Real.sqrt ((∑ i ∈ Finset.univ.erase (0 : Fin (ν+1)), (z i)^2) / ν))

noncomputable def chiSquaredLaw (ν : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin ν => gaussianReal 0 1)).map (fun z => ∑ i, (z i)^2)

noncomputable def vectorCovariance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ε : Ω → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ ω, (ε ω i - ∫ η, ε η i ∂μ) * (ε ω j - ∫ η, ε η j ∂μ) ∂μ

/-- Exact decimal regression inputs, ordered by election year 1948, 1952, ..., 2012.
Columns: outcome margin, income growth, incumbent tenure, war fatalities, extremism. -/
noncomputable def tableTwoInputs : Matrix (Fin 17) (Fin 5) ℝ :=
  !![(112/25 : ℝ), (1934828833/500000000 : ℝ), (16/1 : ℝ), (0/1 : ℝ), (119984289/500000000 : ℝ);
    (-217/20 : ℝ), (2417476109/1000000000 : ℝ), (20/1 : ℝ), (1904152679/10000000 : ℝ), (1374649/15625000 : ℝ);
    (77/5 : ℝ), (72046309/125000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-51046667/1000000000 : ℝ);
    (-17/100 : ℝ), (336587/20000000 : ℝ), (8/1 : ℝ), (0/1 : ℝ), (-53180451/1000000000 : ℝ);
    (1129/50 : ℝ), (3258883307/1000000000 : ℝ), (4/1 : ℝ), (474421501/500000000 : ℝ), (-318262019/1000000000 : ℝ);
    (-7/10 : ℝ), (1398802867/1000000000 : ℝ), (8/1 : ℝ), (91018219/625000 : ℝ), (54862857/250000000 : ℝ);
    (463/20 : ℝ), (303629933/125000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-455834851/1000000000 : ℝ);
    (-103/50 : ℝ), (628281/800000 : ℝ), (8/1 : ℝ), (2086606979/1000000000 : ℝ), (25423097/500000000 : ℝ);
    (-487/50 : ℝ), (-207120123/250000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-19407/31250 : ℝ);
    (1821/100 : ℝ), (1283325533/500000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (273800291/1000000000 : ℝ);
    (193/25 : ℝ), (189045253/125000000 : ℝ), (8/1 : ℝ), (0/1 : ℝ), (173195729/1000000000 : ℝ);
    (-139/25 : ℝ), (77430623/100000000 : ℝ), (12/1 : ℝ), (0/1 : ℝ), (192515613/1000000000 : ℝ);
    (851/100 : ℝ), (283826897/250000000 : ℝ), (4/1 : ℝ), (0/1 : ℝ), (-146050087/1000000000 : ℝ);
    (51/100 : ℝ), (837710937/500000000 : ℝ), (8/1 : ℝ), (0/1 : ℝ), (-42411239/250000000 : ℝ);
    (123/50 : ℝ), (32470207/31250000 : ℝ), (4/1 : ℝ), (3860627651/1000000000 : ℝ), (62372671/250000000 : ℝ);
    (-727/100 : ℝ), (-349851591/500000000 : ℝ), (8/1 : ℝ), (1398476601/100000000 : ℝ), (-119001519/1000000000 : ℝ);
    (96/25 : ℝ), (86756221/250000000 : ℝ), (4/1 : ℝ), (24/5 : ℝ), (40330327/1000000000 : ℝ)]

noncomputable def tableTwoOutcome : Fin 17 → ℝ := fun i => tableTwoInputs i 0

noncomputable def tableA1 : Matrix (Fin 17) (Fin 3) ℝ := fun i j => ![(1 : ℝ), tableTwoInputs i 1, tableTwoInputs i 2] j

noncomputable def tableA2 : Matrix (Fin 17) (Fin 4) ℝ := fun i j => ![(1 : ℝ), tableTwoInputs i 1, tableTwoInputs i 2, tableTwoInputs i 3] j

noncomputable def tableA3 : Matrix (Fin 17) (Fin 5) ℝ := fun i j => ![(1 : ℝ), tableTwoInputs i 1, tableTwoInputs i 2, tableTwoInputs i 3, tableTwoInputs i 4] j
end SAP.P039
