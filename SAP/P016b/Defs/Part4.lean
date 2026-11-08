import SAP.P016b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators Classical
open MeasureTheory
noncomputable section

def T14Statement : Prop :=
  (∀ (B : ℕ), 0 < B → ∀ (μ : Measure (ReferenceVector B)) [IsProbabilityMeasure μ],
    Exchangeable μ →
    (∀ (c : ℕ), c ≤ B →
      μ.real {t | lowerCount (fun b => t b.succ) (t 0) ≤ c} ≤ (c+1 : ℝ)/(B+1) ∧
      μ.real {t | upperCount (fun b => t b.succ) (t 0) ≤ c} ≤ (c+1 : ℝ)/(B+1)) ∧
    (∀ (α : ℝ), 0 < α → α < 1 →
      μ.real {t | rawP (fun b => t b.succ) (t 0) < α} ≤
        2*(Nat.ceil (α*B/2) : ℝ)/(B+1)) ∧
    (∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
      μ.real {t | correctedLower t ≤ α} ≤ (Nat.floor (α*(B+1)) : ℝ)/(B+1) ∧
      μ.real {t | correctedUpper t ≤ α} ≤ (Nat.floor (α*(B+1)) : ℝ)/(B+1) ∧
      (Nat.floor (α*(B+1)) : ℝ)/(B+1) ≤ α ∧
      μ.real {t | doubledP (correctedLower t) (correctedUpper t) ≤ α} ≤ α)) ∧
  (∀ (μ : Measure (ReferenceVector 1000)) [IsProbabilityMeasure μ], Exchangeable μ →
    μ.real {t | rawP (fun b => t b.succ) (t 0) < 1/20} ≤ 50/1001) ∧
  (∀ (μ : Measure (ReferenceVector 10000)) [IsProbabilityMeasure μ], Exchangeable μ →
    μ.real {t | rawP (fun b => t b.succ) (t 0) < 1/20} ≤ 500/10001) ∧
  (50/1001 : ℝ) < 1/20 ∧ (500/10001 : ℝ) < 1/20 ∧
  (∀ (Ω : Type) [Fintype Ω] (P : FiniteLaw Ω) (B : ℕ) (s : Ω → ℝ)
    (π : Equiv.Perm (Fin (B+1))) (E : ReferenceVector B → Prop),
    iidMass P (B+1) (fun draw => E (fun i => s (draw (π i)))) =
      iidMass P (B+1) (fun draw => E (fun i => s (draw i)))) ∧
  ExactValidity

def T15Statement : Prop :=
  (let Y : Outcome 4 := ![9,11,10,12]
   let z := complete4 5
   additiveAdjust Y z (1/2) = ![9,11,19/2,23/2] ∧
   multiplicativeAdjust Y z 2 = ![9,11,5,6] ∧
   ecdf (additiveAdjust Y z (1/2)) z true 6 = 0 ∧
   ecdf (multiplicativeAdjust Y z 2) z true 6 = 1) ∧
  (sampleECDF (![1,3] : Outcome 2) 2 = 1/2 ∧
   sampleECDF (![1,3] : Outcome 2) 3 = 1) ∧
  (∀ t b : ℝ, (∃ t0 : ℝ, t=t0 ∧ b=t0) ↔ b=t) ∧
  ¬ (∃ t0 : ℝ, (1/2 : ℝ)=t0 ∧ (2 : ℝ)=t0)

def T16Statement : Prop :=
  (∀ (n : ℕ) (Y : Outcome n) (z : Assignment n) (i : Fin n)
    (t t' a a' : ℝ), a ≠ 0 → a' ≠ 0 →
    (z i = false → additiveAdjust Y z t i = Y i ∧ multiplicativeAdjust Y z a i = Y i) ∧
    (z i = true → additiveAdjust Y z t i = Y i-t ∧ multiplicativeAdjust Y z a i = Y i/a ∧
      (t ≠ t' → additiveAdjust Y z t i ≠ additiveAdjust Y z t' i) ∧
      (a ≠ a' → Y i ≠ 0 → multiplicativeAdjust Y z a i ≠ multiplicativeAdjust Y z a' i))) ∧
  (∀ (n : ℕ) (Y : Outcome n) (z : Assignment n) (t a x : ℝ),
    0 < groupSize z false → a ≠ 0 →
    ecdf (additiveAdjust Y z t) z false x = ecdf Y z false x ∧
    ecdf (multiplicativeAdjust Y z a) z false x = ecdf Y z false x) ∧
  (∀ (n : ℕ), 0 < n → ∀ (u : Outcome n) (x : ℝ),
    sampleECDF u x = ((Finset.univ.filter (fun i => u i ≤ x)).card : ℝ)/n) ∧
  (∃ t0 b0 : ℝ, (1/2 : ℝ)=t0 ∧ (2 : ℝ)=b0) ∧
  ¬ (∃ t0 : ℝ, (1/2 : ℝ)=t0 ∧ (2 : ℝ)=t0)

def T17Statement : Prop :=
  (∀ (n : ℕ) (Y : Outcome n) (z : Assignment n),
    0 < groupSize z false → 0 < groupSize z true → ∀ t : ℝ,
    let u := additiveAdjust Y z t
    (∀ i, z i = true → u i+t = Y i) ∧
    groupMean (fun i => u i+t) z true - groupMean u z false = meanDifference u z+t ∧
    groupMean (fun i => u i+t) z true - groupMean u z false = meanDifference Y z) ∧
  meanDifference u4 (complete4 5) = 2 ∧
  groupMean (fun i => u4 i+10) (complete4 5) true - groupMean u4 (complete4 5) false = 12

end
end SAP.P016b
