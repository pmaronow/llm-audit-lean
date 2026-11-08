import SAP.P019a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a
open scoped BigOperators
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

/-- Ordered independent samples, without discarding empty cells. -/
def FiniteLaw.iid (P : FiniteLaw Ω) (n : ℕ) : FiniteLaw (Fin n → Ω) where
  mass := fun s => ∏ i, P.mass (s i)
  nonneg := by intro s; exact Finset.prod_nonneg (fun i _ => P.nonneg (s i))
  total := by rw [← Fintype.prod_sum]; simp [P.total]

/-- The empty sample has mean zero by convention. -/
def Study.ybar (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (∑ i, bitVal (S.Y (s i))) / (n : ℝ)

def Study.cellCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℕ :=
  ∑ i, if S.cell z y (s i) then 1 else 0

/-- Printed subgroup ratio on occupied cells, with fixed value c on an empty cell. -/
def Study.cellMean (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) (c : ℝ) : ℝ :=
  if S.cellCount s z y = 0 then c else
    (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ) else 0) / (S.cellCount s z y : ℝ)

def Study.occupied (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : Prop :=
  0 < S.cellCount s true false ∧ 0 < S.cellCount s false false

def Study.muHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.ybar s + (1 - S.ybar s) * (S.cellMean s true false c1 - S.cellMean s false false c0)

def Study.armCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) : ℕ :=
  ∑ i, if S.Z (s i) = z then 1 else 0

/-- Treatment fraction, with value zero on the empty sample. -/
def Study.gammaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (S.armCount s true : ℝ) / (n : ℝ)

/-- Sample variance with divisor N-1, explicitly set to zero when N<2. -/
def Study.cellVariance (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℝ :=
  if S.cellCount s z y < 2 then 0 else
    (∑ i, if S.cell z y (s i) then
      ((S.V (s i) : ℝ) - S.cellMean s z y 0)^2 else 0) / ((S.cellCount s z y : ℝ) - 1)

/-- Whole variance estimate is cV whenever the printed formula is undefined. -/
def Study.muVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true false ∧ 2 ≤ S.cellCount s false false ∧
      S.ybar s < 1 ∧ 0 < S.gammaHat s ∧ S.gammaHat s < 1 then
    (((1 - S.muHat s c1 c0)^2 / (1 - S.ybar s)) * S.ybar s +
      (1 - S.ybar s) * (S.cellVariance s true false / S.gammaHat s +
        S.cellVariance s false false / (1 - S.gammaHat s))) / (n : ℝ)
  else cV

def Study.patternFibre (S : Study Ω) {n : ℕ} (s t : Fin n → Ω) : Prop :=
  ∀ i, S.Y (t i) = S.Y (s i) ∧ S.Z (t i) = S.Z (s i)

def Study.sampleA (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ := 1 - S.ybar s

def Study.sampleB (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true false c1 - S.cellMean s false false c0 - 1

/-- Used only inside expectations conditional on occupied cells. -/
def Study.sampleH (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / (S.cellCount s true false : ℝ) +
    S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (S.cellCount s false false : ℝ)

def Study.negativeCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℕ :=
  S.cellCount s true false + S.cellCount s false false

def Study.betaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true true c1 - S.cellMean s false true c0

/-- Whole placebo variance estimate is cV when either cell has fewer than two observations. -/
def Study.betaVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true true ∧ 2 ≤ S.cellCount s false true then
    S.cellVariance s true true / (S.cellCount s true true : ℝ) +
      S.cellVariance s false true / (S.cellCount s false true : ℝ)
  else cV

end
end SAP.P019a
