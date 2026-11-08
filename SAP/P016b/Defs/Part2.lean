import SAP.P016b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators
open MeasureTheory
noncomputable section

/-- A normalized finite probability law, permitting zero-weight points. -/
structure FiniteLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

def mass {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (E : Ω → Prop) : ℝ :=
  by classical exact ∑ ω, if E ω then P.weight ω else 0

def upperP {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) : ℝ :=
  mass P (fun w => s z ≤ s w)

def lowerP {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) : ℝ :=
  mass P (fun w => s w ≤ s z)

def doubledP (L U : ℝ) : ℝ := min 1 (2 * min L U)

def uniformLaw (Ω : Type) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight := fun _ => 1 / Fintype.card Ω
  nonneg := fun _ => by positivity
  total := by simp [div_eq_mul_inv, Fintype.card_ne_zero]

def uniformMass (Ω : Type) [Fintype Ω] (E : Ω → Prop) : ℝ := by
  classical
  exact (∑ ω, if E ω then (1 : ℝ) else 0) / Fintype.card Ω

def uniformExpectation (Ω : Type) [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def lowerCount {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℕ :=
  ∑ b, if ref b ≤ obs then 1 else 0

def upperCount {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℕ :=
  ∑ b, if obs ≤ ref b then 1 else 0

/-- Inclusive empirical tails without adding the observed statistic; claims require B > 0. -/
def rawP {B : ℕ} (ref : Fin B → ℝ) (obs : ℝ) : ℝ :=
  doubledP ((lowerCount ref obs : ℝ)/B) ((upperCount ref obs : ℝ)/B)

abbrev ReferenceVector (B : ℕ) := Fin (B+1) → ℝ

def Exchangeable {B : ℕ} (μ : Measure (ReferenceVector B)) : Prop :=
  ∀ π : Equiv.Perm (Fin (B+1)), Measure.map (fun t i => t (π i)) μ = μ

def correctedLower {B : ℕ} (t : ReferenceVector B) : ℝ :=
  (1+(lowerCount (fun b => t b.succ) (t 0) : ℝ))/(B+1)

def correctedUpper {B : ℕ} (t : ReferenceVector B) : ℝ :=
  (1+(upperCount (fun b => t b.succ) (t 0) : ℝ))/(B+1)

def iidWeight {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (m : ℕ)
    (draw : Fin m → Ω) : ℝ := ∏ i, P.weight (draw i)

def iidMass {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (m : ℕ)
    (E : (Fin m → Ω) → Prop) : ℝ := by
  classical
  exact ∑ draw, if E draw then iidWeight P m draw else 0

def binomialMixture (M B c : ℕ) : ℝ :=
  2/(M : ℝ) * ∑ r : Fin M, ∑ k ∈ Finset.range (c+1),
    (Nat.choose B k : ℝ) * (((r.val+1 : ℕ) : ℝ)/M)^k *
      (((M : ℝ)-(r.val+1))/M)^(B-k)

end
end SAP.P016b
