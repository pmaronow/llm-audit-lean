import SAP.P019b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b

open scoped BigOperators
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

/-- The unconditioned law of an ordered IID sample. -/
def FiniteLaw.iid (P : FiniteLaw Ω) (n : ℕ) : FiniteLaw (Fin n → Ω) where
  mass := fun s => ∏ i, P.mass (s i)
  nonneg := by intro s; exact Finset.prod_nonneg (fun i _ => P.nonneg (s i))
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]

/-- Sample means at n = 0 receive value zero; all sample conclusions are limits. -/
def Study.ybar (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (∑ i, bitVal (S.Y (s i))) / (n : ℝ)

def Study.cellCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℕ :=
  ∑ i, if S.cell z y (s i) then 1 else 0

/-- A fixed constant c completes a mean on an empty cell. -/
def Study.cellMean (S : Study Ω) {n : ℕ} (s : Fin n → Ω)
    (z y : Bool) (c : ℝ) : ℝ :=
  if S.cellCount s z y = 0 then c else
    (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ) else 0) /
      (S.cellCount s z y : ℝ)

def Study.muHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.ybar s + (1 - S.ybar s) * (S.cellMean s true false c1 - S.cellMean s false false c0)

def Study.armCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) : ℕ :=
  ∑ i, if S.Z (s i) = z then 1 else 0

def Study.armMean (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) (c : ℝ) : ℝ :=
  if S.armCount s z = 0 then c else
    (∑ i, if S.Z (s i) = z then (S.V (s i) : ℝ) else 0) / (S.armCount s z : ℝ)

def Study.standardHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.armMean s true c1 - S.armMean s false c0

def Study.gammaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (S.armCount s true : ℝ) / (n : ℝ)

/-- Cell sample variance with divisor N - 1, completed by zero for N < 2. -/
def Study.cellVariance (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℝ :=
  if S.cellCount s z y < 2 then 0 else
    (∑ i, if S.cell z y (s i) then
      ((S.V (s i) : ℝ) - S.cellMean s z y 0)^2 else 0) / ((S.cellCount s z y : ℝ) - 1)

/-- The printed plug-in variance, with a fixed whole-estimate completion cV. -/
def Study.muVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true false ∧ 2 ≤ S.cellCount s false false ∧
      S.ybar s < 1 ∧ 0 < S.gammaHat s ∧ S.gammaHat s < 1 then
    (((1 - S.muHat s c1 c0)^2 / (1 - S.ybar s)) * S.ybar s +
      (1 - S.ybar s) * (S.cellVariance s true false / S.gammaHat s +
        S.cellVariance s false false / (1 - S.gammaHat s))) / (n : ℝ)
  else cV

/-- Equation (3), including its population conditional variances. -/
def Study.sigmaSq (S : Study Ω) : ℝ :=
  ((1 - S.mu)^2 / (1 - S.mu * S.truthRate)) * (S.mu * S.truthRate) +
    (1 - S.mu * S.truthRate) *
      (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / S.gamma +
        S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (1 - S.gamma))

def Study.standardSigmaSq (S : Study Ω) : ℝ :=
  S.law.cv (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) / S.gamma +
    S.law.cv (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false) / (1 - S.gamma)

def Study.betaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true true c1 - S.cellMean s false true c0

def Study.betaVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true true ∧ 2 ≤ S.cellCount s false true then
    S.cellVariance s true true / (S.cellCount s true true : ℝ) +
      S.cellVariance s false true / (S.cellCount s false true : ℝ)
  else cV

def Study.directArmMean (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) (c : ℝ) : ℝ :=
  if S.armCount s z = 0 then c else
    (∑ i, if S.Z (s i) = z then bitVal (S.Y (s i)) else 0) / (S.armCount s z : ℝ)

def Study.deltaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.directArmMean s true c1 - S.directArmMean s false c0

def Study.directArmVariance (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) : ℝ :=
  if S.armCount s z < 2 then 0 else
    (∑ i, if S.Z (s i) = z then
      (bitVal (S.Y (s i)) - S.directArmMean s z 0)^2 else 0) / ((S.armCount s z : ℝ) - 1)

def Study.deltaVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) : ℝ :=
  if 2 ≤ S.armCount s true ∧ 2 ≤ S.armCount s false then
    S.directArmVariance s true / (S.armCount s true : ℝ) +
      S.directArmVariance s false / (S.armCount s false : ℝ)
  else cV

end
end SAP.P019b
