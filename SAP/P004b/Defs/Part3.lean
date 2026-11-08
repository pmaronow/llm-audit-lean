import SAP.P004b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

def InProb (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => prob (p N) (fun z => ε < |U N z|)) atTop (nhds 0)

def BigOp (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N in atTop, prob (p N) (fun z => C * |r N| < |U N z|) < ε

def LittleOp (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) (r : ℕ → ℝ) : Prop :=
  InProb p (fun N z => U N z / r N)

def normalCDF (x : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

def normalQuantile (a : ℝ) : ℝ := sInf {x : ℝ | a ≤ normalCDF x}

def NormalLimit (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun N => prob (p N) (fun z => U N z ≤ x)) atTop (nhds (normalCDF x))

def Nondegenerate (V : ℕ → ℝ) : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop, v ≤ (N : ℝ) * V N

def LiminfAtLeast (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, a-ε ≤ u N

def Conservative (coverage : ℕ → ℝ) (α : ℝ) : Prop :=
  LiminfAtLeast coverage (1-α)

def PrintedCoverage (coverage : ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto coverage atTop (nhds L) ∧ 1 - α ≤ L

def residualContrast {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  bit (z i) * (R i z - g i true) / p i -
  (1-bit (z i)) * (R i z - g i false) / (1-p i)

def residualEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) : ℝ :=
  nodeEffect p R i - (g i true - g i false)

def armSign (a : Bool) : ℝ := if a then 1 else -1

def secondMomentBound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z - g i true)^2) i true / p i +
    marginal p (fun i z => (R i z - g i false)^2) i false / (1-p i))) +
    ∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      armSign a * armSign b * pairMarginal p
        (fun z => (R i z - g i a)*(R j z - g j b)) i j a b) / (N : ℝ)^2

def homophilyQ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualEffect p R g i * residualEffect p R g j) / N

def oracleHAC {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualContrast p R g i z * residualContrast p R g j z) / (N : ℝ)^2

def weightedEpsilon {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (z : Assignment N) (i : Fin N) : ℝ :=
  armCount z true / N * bit (z i) / phat i * (R i z-g i true) +
  armCount z false / N * (1-bit (z i)) / (1-phat i) * (R i z-g i false)

def sahLimit {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, (B i).card * (marginal p (fun i z => (R i z-g i true)^2) i true / p i +
    marginal p (fun i z => (R i z-g i false)^2) i false / (1-p i))) / (N : ℝ)^2

def designMatrix {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin 2) ℝ :=
  fun i a => if a = 0 then 1 else bit (z i)

def lambda {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ :=
  bit (z i) / armCount z true - (1-bit (z i)) / armCount z false

def residualMaker {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin N) ℝ :=
  let X := designMatrix z
  1 - X * (X.transpose * X)⁻¹ * X.transpose

def sandwich {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let X := designMatrix z
  let A := (X.transpose * X)⁻¹
  A * (X.transpose * Matrix.of (fun i j => e i * e j * Q i j) * X) * A

def kernelVariance {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, lambda z i * lambda z j * e i * e j * Q i j

def centeredSummand {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (μ1 μ0 : ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  (μ1-μ0 + residualContrast p R (fun _ a => if a then μ1 else μ0) i z - nodeEffect p R i) / N

def DependencyGraph {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (V : Fin N → Ω → ℝ) (B : Fin N → Finset (Fin N)) : Prop :=
  (∀ i, i ∈ B i) ∧ (∀ i j, j ∈ B i ↔ i ∈ B j) ∧
  ∀ I J : Finset (Fin N), (∀ i ∈ I, ∀ j ∈ J, j ∉ B i) →
    ProbabilityTheory.IndepFun (fun ω (i : I) => V i ω) (fun ω (j : J) => V j ω) μ

def loneRademacher (N : ℕ) (i : Fin N) (z : Assignment N) : ℝ :=
  if i.val = 0 then 2*bit (z i)-1 else 0

def FiniteDependencyGraph {N : ℕ} (p : Fin N → ℝ) (V : CircleTable N)
    (B : Fin N → Finset (Fin N)) : Prop :=
  (∀ i, i ∈ B i) ∧ (∀ i j, j ∈ B i ↔ i ∈ B j) ∧
  ∀ I J : Finset (Fin N), (∀ i ∈ I, ∀ j ∈ J, j ∉ B i) →
    ∀ A : (I → ℝ) → Prop, ∀ C : (J → ℝ) → Prop,
      prob p (fun z => A (fun i => V i z) ∧ C (fun j => V j z)) =
        prob p (fun z => A (fun i => V i z)) * prob p (fun z => C (fun j => V j z))

end
end SAP.P004b
