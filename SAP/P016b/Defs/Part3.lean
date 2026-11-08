import SAP.P016b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators Classical
open MeasureTheory
noncomputable section

/-- Exact-tail validity at both weak and strict cutoffs for a positive finite law. -/
def ExactValidity : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (P : FiniteLaw Ω), (∀ z, 0 < P.weight z) →
    ∀ (s : Ω → ℝ) (α : ℝ), 0 ≤ α → α ≤ 1 →
      mass P (fun z => upperP P s z ≤ α) ≤ α ∧
      mass P (fun z => lowerP P s z ≤ α) ≤ α ∧
      mass P (fun z => doubledP (lowerP P s z) (upperP P s z) ≤ α) ≤ α ∧
      mass P (fun z => upperP P s z < α) ≤ α ∧
      mass P (fun z => lowerP P s z < α) ≤ α ∧
      mass P (fun z => doubledP (lowerP P s z) (upperP P s z) < α) ≤ α

def T12Statement : Prop :=
  (∀ n : ℕ, EffectIncreasingOnGroups (meanDifference (n := n))) ∧
  (¬ EffectIncreasingOnGroups (ks (n := 4)) ∧
   ¬ EffectIncreasingOnGroups (signedKS (n := 4))) ∧
  ExactValidity ∧
  (∀ k : Fin 6,
    upperP (uniformLaw (Fin 6)) (fun j => ks u4 (complete4 j)) k =
      (![1/3,1,1,1,1,1/3] : Fin 6 → ℝ) k) ∧
  (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    mass (uniformLaw (Fin 6)) (fun k => upperP (uniformLaw (Fin 6))
      (fun j => ks u4 (complete4 j)) k ≤ α) =
      if α < 1/3 then 0 else if α < 1 then 1/3 else 1)

/-- The tie-free rank and raw weak-cutoff size law, restricted to levels below one. -/
def NoTiesRawLaw : Prop :=
  ∀ (B : ℕ), 0 < B → ∀ (μ : Measure (ReferenceVector B)) [IsProbabilityMeasure μ],
    Exchangeable μ → (∀ᵐ t ∂μ, Function.Injective t) →
    ∀ (α : ℝ), 0 ≤ α → α < 1 → ∀ (c : ℕ), c = Nat.floor (α*B/2) → 2*c < B →
      (∀ k : Fin (B+1), μ.real {t | (∑ b : Fin B,
        if t b.succ < t 0 then (1 : ℕ) else 0) = k.val} = 1/(B+1)) ∧
      (∀ᵐ t ∂μ, lowerCount (fun b => t b.succ) (t 0) =
        (∑ b : Fin B, if t b.succ < t 0 then (1 : ℕ) else 0) ∧
        upperCount (fun b => t b.succ) (t 0) = B-lowerCount (fun b => t b.succ) (t 0)) ∧
      μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ α} = 2*(c+1)/(B+1)

/-- The exact finite population and the complement characterization of its RSS fibers. -/
def PowerTwoDesign : Prop :=
  let y : Outcome 16 := fun i => (2 : ℝ)^i.val
  Fintype.card (Balanced 16 8) = 12870 ∧
  (∑ i, y i) = 65535 ∧ (∑ i, (y i)^2) = 1431655765 ∧
  (∀ z : Balanced 16 8, rss y z.val = 1431655765 -
    ((groupSum y z.val true)^2 + (65535-groupSum y z.val true)^2)/8) ∧
  (Finset.univ.image (fun z : Balanced 16 8 => rss y z.val)).card = 6435 ∧
  (∀ z w : Balanced 16 8, rss y z.val = rss y w.val ↔
    z.val = w.val ∨ z.val = fun i => !(w.val i))

/-- Exact iid rejection probabilities, their comparison bounds, and positive zero-p mass. -/
def PowerTwoSampled : Prop :=
  let y : Outcome 16 := fun i => (2 : ℝ)^i.val
  (∀ B : ℕ, 0 < B → ∀ c : ℕ, 2*c < B →
    uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
      lowerCount (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) ≤ c ∨
      upperCount (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) ≤ c) =
        binomialMixture 6435 B c) ∧
  (∀ B c : ℕ, 0 < B → c < B →
    2*(c+1)/(B+1)-2/(6435 : ℝ) ≤ binomialMixture 6435 B c ∧
    binomialMixture 6435 B c ≤ 2*(c+1)/(B+1)) ∧
  (∀ B ∈ ({1000,10000} : Finset ℕ),
    uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
      rawP (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) ≤ 1/20) =
      binomialMixture 6435 B (B/40)) ∧
  (∀ B ∈ ({1000,10000} : Finset ℕ),
    uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
      rawP (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) < 1/20) =
      binomialMixture 6435 B (B/40-1)) ∧
  1/20 < binomialMixture 6435 1000 25 ∧ 1/20 < binomialMixture 6435 10000 250 ∧
  binomialMixture 6435 1000 24 < 1/20 ∧ binomialMixture 6435 10000 249 < 1/20 ∧
  (∀ B : ℕ, 0 < B → uniformMass (Fin (B+1) → Balanced 16 8) (fun draw =>
    rawP (fun b => rss y (draw b.succ).val) (rss y (draw 0).val) = 0) =
    binomialMixture 6435 B 0 ∧ binomialMixture 6435 B 0 =
      2*(∑ r ∈ Finset.range 6434, (6434-r : ℝ)^B)/(6435 : ℝ)^(B+1) ∧
    0 < binomialMixture 6435 B 0)

def T13Statement : Prop :=
  NoTiesRawLaw ∧
  (∀ (μ : Measure (ReferenceVector 1000)) [IsProbabilityMeasure μ],
    Exchangeable μ → (∀ᵐ t ∂μ, Function.Injective t) →
      μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20} = 4/77 ∧
      1/20 < μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20}) ∧
  (∀ (μ : Measure (ReferenceVector 10000)) [IsProbabilityMeasure μ],
    Exchangeable μ → (∀ᵐ t ∂μ, Function.Injective t) →
      μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20} = 502/10001 ∧
      1/20 < μ.real {t | rawP (fun b => t b.succ) (t 0) ≤ 1/20}) ∧
  PowerTwoDesign ∧ PowerTwoSampled ∧
  (4/77 : ℝ)-2/6435 = 2326/45045 ∧ (1/20 : ℝ) < 2326/45045

end
end SAP.P016b
