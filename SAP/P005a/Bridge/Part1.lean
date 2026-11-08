import SAP.P005a.Defs
import AronowAudit.P005.Wave1.Gap.GP005B1b
import AronowAudit.P005.Wave1.Gap.GP005B4c
import AronowAudit.P005.Wave1.Gap.GP005B4b
import AronowAudit.P005.Wave1.Gap.GLP005B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.Bridge
open SAP.P005a Finset Filter
open scoped BigOperators Matrix Topology
noncomputable section

/-- The adapter preserves exactly the three fixed arrays. -/
def toPopulation {n d : ℕ} (P : Population n d) : AronowAudit.P005.Population n d :=
  ⟨P.x, P.yT, P.yC⟩

def fromPopulation {n d : ℕ} (P : AronowAudit.P005.Population n d) : Population n d :=
  ⟨P.x, P.yT, P.yC⟩

theorem from_to {n d : ℕ} (P : Population n d) :
    fromPopulation (toPopulation P) = P := rfl

theorem to_from {n d : ℕ} (P : AronowAudit.P005.Population n d) :
    toPopulation (fromPopulation P) = P := rfl

def toArm : Arm → AronowAudit.P005.Arm
  | .treated => .treated
  | .control => .control

theorem armSet_eq {n : ℕ} (t : Arm) (S : Finset (Fin n)) :
    AronowAudit.P005.armSet (toArm t) S = armSet t S := by cases t <;> rfl

theorem armSize_eq (n m : ℕ) (t : Arm) :
    AronowAudit.P005.armSize n m (toArm t) = armSize n m t := by cases t <;> rfl

theorem sampleCov_eq {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ) :
    AronowAudit.P005.sampleCov S a b = sampleCov S a b := rfl

theorem standardized_eq {n d : ℕ} (P : Population n d) :
    AronowAudit.P005.standardized (toPopulation P) = standardized P := rfl

theorem leverage_eq {n d : ℕ} (P : Population n d) :
    AronowAudit.P005.leverage (toPopulation P) = leverage P := rfl

theorem kappa_eq {n d : ℕ} (P : Population n d) :
    AronowAudit.P005.kappa (toPopulation P) = kappa P := rfl

theorem armL_eq {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) :
    AronowAudit.P005.armL (toPopulation P) S = armL P S := rfl

theorem armN_eq {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    AronowAudit.P005.armN (toPopulation P) S y = armN P S y := rfl

theorem Lhat_eq {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) :
    AronowAudit.P005.Lhat (toPopulation P) m S = Lhat P m S := rfl

theorem standingAssumptions_eq (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)) :
    AronowAudit.P005.standingAssumptions d m (fun n => toPopulation (P n)) =
      standingAssumptions d m P := rfl

theorem signPopulation_eq : AronowAudit.P005.signPopulation = toPopulation signPopulation := rfl

theorem weightPopulation_eq : AronowAudit.P005.weightPopulation = toPopulation weightPopulation := rfl

theorem leveragePopulation_eq :
    AronowAudit.P005.leveragePopulation = toPopulation leveragePopulation := rfl

theorem spikePopulation_eq (n : ℕ) :
    AronowAudit.P005.spikePopulation n = toPopulation (spikePopulation n) := rfl

/-- Complementing a uniform treated subset gives the uniform control subset. -/
theorem expectation_control {n m : ℕ} (hm : m ≤ n) (f : Finset (Fin n) → ℝ) :
    expectation m (fun S => f (control S)) = expectation (n-m) f :=
  AronowAudit.P005.Wave1.control_arm_transport hm f

/-- Existing sign and linearity facts, in the shared SAP vocabulary. -/
theorem nu3_sign {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    dot (xMean P S) (armNu3 P S y) =
      -(dot (xMean P S) (xMean P S) * mean S (centered y)) :=
  AronowAudit.P005.Wave1.t6_nu3_sign (toPopulation P) S y

theorem expectation_neg {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) :
    expectation m (fun S => -(f S)) = -expectation m f := by
  change AronowAudit.P005.expectation m (fun S => -(f S)) =
    -AronowAudit.P005.expectation m f
  simpa only [neg_one_mul] using AronowAudit.P005.expectation_mul m f (-1)

end
end SAP.P005a.Bridge
