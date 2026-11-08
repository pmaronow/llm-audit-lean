import Mathlib
import SAP.P029b.Defs.Part1
import SAP.P029b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b

universe u v

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def T14Statement : Prop :=
  
  (∀ (n1 n0 : ℕ) (hn1 : 0 < n1) (hn0 : 0 < n0)
    (p1 p0 : ℝ) (hp0 : 0 ≤ p0) (horder : p0 ≤ p1) (hp1 : p1 ≤ 1),
    fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0) =
      fE (binomialArmLaw n1 n0 p1 p0)
        (fun k => positiveScore ((k.2.val : ℝ)/n0) ((k.1.val : ℝ)/n1)) ∧
    0 ≤ fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0) ∧
    (0 < p0 → p1 < 1 → 0 < fE (binomialArmLaw n1 n0 p1 p0) (armRateScore n1 n0) - (p1-p0)) ∧
    (∀ δ : ℝ, 0 < δ →
      fP (binomialArmLaw n1 n0 p1 p0) (fun k => δ < |armRateScore n1 n0 k - (p1-p0)|) ≤
        (p1*(1-p1)/n1 + p0*(1-p0)/n0) / δ^2)) ∧
  (∀ (n1 n0 : ℕ) (_ : 0 < n1) (_ : 0 < n0) (p1 p0 : ℝ)
      (_ : 0 ≤ p0) (horder : p0 ≤ p1) (_ : p1 ≤ 1)
      (k : Fin (n1+1) × Fin (n0+1)),
    |armRateScore n1 n0 k - (p1-p0)| ≤
      |((k.1.val : ℝ)/n1 - (k.2.val : ℝ)/n0) - (p1-p0)|) ∧
  (∀ (n1 n0 : ℕ → ℕ)
    (hn1 : ∀ n, 0 < n1 n) (hn0 : ∀ n, 0 < n0 n)
    (ht1 : Tendsto n1 atTop atTop) (ht0 : Tendsto n0 atTop atTop)
    (p1 p0 : ℝ) (hp0 : 0 ≤ p0) (horder : p0 ≤ p1) (hp1 : p1 ≤ 1),
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      fP (binomialArmLaw (n1 n) (n0 n) p1 p0)
        (fun k => δ < |armRateScore (n1 n) (n0 n) k - (p1-p0)|)) atTop (𝓝 0)) ∧
  (∀ (n1 n0 : ℕ) (hn1 : 0 < n1) (hn0 : 0 < n0)
    (p1 : ℝ) (hp1 : p1 ∈ Icc (0 : ℝ) 1),
    fP (binomialArmLaw n1 n0 p1 0) (fun k => k.2.val = 0) = 1 ∧
    (∀ k : Fin (n1+1) × Fin (n0+1), k.2.val = 0 →
      armRateScore n1 n0 k = (k.1.val : ℝ)/n1) ∧
    fE (binomialArmLaw n1 n0 p1 0) (armRateScore n1 n0) = p1)


def T15Statement : Prop :=
  
  (FIV sixMass (liftUnit constantUnit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit constantUnit) ∧
    fScore sixMass (liftUnit constantUnit) () = 1/2 ∧
    (1/4 : ℝ) < fScore sixMass (liftUnit constantUnit) () ∧
    fE sixMass (fun i => (constantUnit i.1).tau) = 1 ∧
    fWald sixMass (liftUnit constantUnit) Prod.snd (fun _ => 2) = 1) ∧
  (Tendsto (fun _ : ℕ => |(1/2 : ℝ)-fScore sixMass (liftUnit constantUnit) ()|)
      atTop (𝓝 0) ∧ ¬ Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0)) ∧
  (∀ n (level : ℝ), level ∈ Icc (0 : ℝ) 1 →
    Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level (1/2) ∧
    (∀ c, Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level c → c = 1/2)) ∧
  ((∀ n, belowCount (fun _ : Fin (n+1) => (1/2 : ℝ)) (1/2) = 0) ∧
    (1/(1/2 : ℝ) = 2))


def T16Statement : Prop :=
  
  (∀ {n : ℕ} (s : Fin (n+1) → ℝ) (level c b : ℝ)
    (hlevel : level ∈ Ioo (0 : ℝ) 1) (hq : Type7Quantile s level c) (hb : ∀ i, b ≤ s i),
    (belowCount s c : ℝ) ≤ 1 + n*level ∧
    (belowCount s c : ℝ)/(n+1) ≤ level + 1/(n+1) ∧ b ≤ c) ∧
  (∀ (s : (n : ℕ) → Fin (n+1) → ℝ)
    (c : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (hq : ∀ n, Type7Quantile (s n) (((n+1 : ℕ) : ℝ)^(-α)) (c n)),
    Tendsto (fun n => (belowCount (s n) (c n) : ℝ)/(n+1)) atTop (𝓝 0)) ∧
  (∀ {n : ℕ} (s V : Fin (n+1) → ℝ) (level c b K : ℝ),
    level ∈ Ioo (0 : ℝ) 1 → Type7Quantile s level c →
    0 < b → (∀ i, b ≤ s i ∧ s i ≤ 1) → 0 ≤ K → (∀ i, |V i| ≤ K) →
    (∀ i, 0 ≤ weightChange (s i) c ∧
      weightChange (s i) c ≤ (1/b) * (if s i < c then 1 else 0)) ∧
    |(∑ i, weightChange (s i) c * V i)/(n+1)| ≤ (K/b) * (level + 1/(n+1))) ∧
  ((∀ n (level c : ℝ), level ∈ Icc (0 : ℝ) 1 →
    Type7Quantile (fun _ : Fin (n+1) => (1/2 : ℝ)) level c → c = 1/2) ∧
    ¬ Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 0)) ∧
  (∀ {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (cutoff : ℕ → Ω → ℝ) (h : ICSWConditions μ U Z c m s) (α : ℝ) (hα : 0 < α)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < mP μ {ω | (U 0 ω).x = x} →
      ε < scoreAt μ (U 0) x ∧ scoreAt μ (U 0) x ≤ 1)
    (hcmeas : ∀ n, Measurable (cutoff n))
    (hquantile : ∀ n, ∀ᵐ ω ∂μ,
      Type7Quantile (fun i : Fin (n+1) => s n i.val ω)
        (((n+1 : ℕ) : ℝ)^(-α)) (cutoff n ω))  (_ : RatiosEventuallyDefined μ U Z (fun n i ω => 1/s n i ω)) (_ : RatiosEventuallyDefined μ U Z (fun n i ω => 1/max (s n i ω) (cutoff n ω))),
    TendstoInMeasure μ (fun n ω => winsorizedSequence U Z s cutoff n ω -
      icswSequence U Z s n ω) atTop (fun _ => 0) ∧
    TendstoInMeasure μ (icswSequence U Z s) atTop
      (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
    TendstoInMeasure μ (winsorizedSequence U Z s cutoff) atTop
      (fun _ => ∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) ∧
    ((∀ x, 0 < mP μ {ω | (U 0 ω).x = x} → latentAt μ (U 0) x) →
      (∑ x, mP μ {ω | (U 0 ω).x = x} * complierAt μ (U 0) x) = ∫ ω, (U 0 ω).tau ∂μ))


def T17Statement : Prop :=
  
  (∀ (π : ℝ) (z d : Bool), π ∈ Ioo (0 : ℝ) 1 →
    bernoulliFactor (nestedReceipt π 0 z) d = bernoulliFactor (π * bit z) d) ∧
  (∀ {I Θ : Type*} [Fintype I] (π : Θ → I → ℝ) (Z D : I → Bool),
    (∀ θ i, π θ i ∈ Ioo (0 : ℝ) 1) →
    (∀ i, Z i = false → D i = false) →
    (∀ θ, (∏ i, bernoulliFactor (π θ i * bit (Z i)) (D i)) =
      ∏ i ∈ Finset.univ.filter (fun i => Z i = true), bernoulliFactor (π θ i) (D i)) ∧
    (∀ θ, (∀ t, (∏ i, bernoulliFactor (π t i * bit (Z i)) (D i)) ≤
          ∏ i, bernoulliFactor (π θ i * bit (Z i)) (D i)) ↔
      (∀ t, (∏ i ∈ Finset.univ.filter (fun i => Z i = true), bernoulliFactor (π t i) (D i)) ≤
          ∏ i ∈ Finset.univ.filter (fun i => Z i = true), bernoulliFactor (π θ i) (D i)))) ∧
  (((3/4 : ℝ)^1 + (1-3/4)^0 = 7/4) ∧
    ((3/4 : ℝ)^0 + (1-3/4)^1 = 5/4) ∧
    bernoulliFactor (3/4) true = 3/4 ∧ bernoulliFactor (3/4) false = 1/4)


def T18Statement : Prop :=
  
  (∀ {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hxmeas : Measurable (fun ω => (U ω).x))
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (hz : Measurable Z)
    (hmon : μ {ω | (U ω).defier} = 0)
    (hi : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ)
    (hz0 : 0 < mP μ {ω | Z ω = true}) (hz1 : mP μ {ω | Z ω = true} < 1)
    (x : X) (hx : 0 < mP μ {ω | (U ω).x = x})
    (hAC : 0 < mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}),
    let a := mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}
    let b := alwaysAmongAC μ U x
    a*b = mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} ∧
    a*(1-b) = scoreAt μ U x ∧
    (∀ z, mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x ∧ Z ω = z} =
      scoreAt μ U x * bit z + mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} ∧
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x ∧ Z ω = z} =
        nestedReceipt a b z)) ∧
  (∀ {X : Type*} (u : PotentialUnit X) (h : ¬ u.defier),
    ¬ (u.complier ∧ u.d0 = true) ∧
    (u.complier ∨ u.d0 = true ↔ u.d1 = true)) ∧
  (∀ (a b : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (z : Bool),
    nestedReceipt a b z ∈ Ioo (0 : ℝ) 1 ∧
      nestedReceipt a b z = if z then a else a*b) ∧
  (∀ (p μ : ℝ) (hp : 0 < p),
    (p*μ)/p = μ) ∧
  (let U : Bool × Bool → PotentialUnit Unit := fun i => ⟨(),false,i.1,0,1⟩
    let p := randomized (fun _ : Bool => (1/2 : ℝ)) (1/2)
    fP p (fun i => (U i).receipt i.2 = true) = 1/4 ∧
    fScore p U () = 1/2 ∧
    ((1/2 : ℝ)*bit false = 0) ∧ ((1/2 : ℝ)*bit true = 1/2))


def T19Statement : Prop :=
  
  (∀ (iAC iA : ℝ) (z : Bool),
    (latentAC iAC = 0 ∨ latentAC iAC = 1) ∧
    (latentA iAC iA = 0 ∨ latentA iAC iA = 1) ∧
    (latentC iAC iA = 0 ∨ latentC iAC iA = 1) ∧
    latentA iAC iA ≤ latentAC iAC ∧ latentA iAC iA * latentC iAC iA = 0 ∧
    (latentD iAC iA z = 0 ∨ latentD iAC iA z = 1) ∧
    latentD iAC iA true - latentD iAC iA false = latentC iAC iA ∧
    0 ≤ latentC iAC iA ∧
    (latentD iAC iA false = 1 ↔ latentA iAC iA = 1) ∧
    (latentD iAC iA false = 0 ∧ latentD iAC iA true = 1 ↔ latentC iAC iA = 1) ∧
    (latentD iAC iA false = 0 ∧ latentD iAC iA true = 0 ↔ latentAC iAC = 0)) ∧
  ((¬ ∃ D : ℝ, D = D*1 + 1) ∧
    ((0 : ℝ) = 0*1+0 ∧ (1 : ℝ) = 1*1+0) ∧
    (∀ D A : ℝ, D = D*0+A ↔ D = A)) ∧
  (∀ (Y0 τ D : ℝ),
    Y0 + τ*D = Y0 + D*((Y0+τ)-Y0))


def T20Statement : Prop :=
  
  (¬ (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z → ∀ (x : X), 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
        typicalAt μ U Z x → latentAt μ U x)) ∧
  (FIV sixMass (liftUnit case2Unit) Prod.snd ∧
    fLatentIgnorability sixMass (liftUnit case2Unit) ∧
    fCE sixMass (fun i => (case2Unit i.1).y0)
      (fun i => (case2Unit i.1).receipt i.2 = true) = 1/2 ∧
    fCE sixMass (fun i => (case2Unit i.1).y0)
      (fun i => (case2Unit i.1).receipt i.2 = false) = 0 ∧
    fCE sixMass (fun i => (case2Unit i.1).y1)
      (fun i => (case2Unit i.1).receipt i.2 = true) = 3/2 ∧
    fCE sixMass (fun i => (case2Unit i.1).y1)
      (fun i => (case2Unit i.1).receipt i.2 = false) = 1)


def T21Statement : Prop :=
  
  (∀ {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (hiv : IVAssumptions μ U Z)
    (c m : X → ℝ) (hv : ScoreVersions μ U c m)
    (ε : ℝ) (he : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1)
    (τ : ℝ) (hτ : ∀ ω, (U ω).tau = τ),
    (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
      mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} = τ ∧ complierAt μ U x = τ) ∧
    A1Versions μ U m ∧ mWald μ U Z (fun _ => 1) = τ ∧
      mWald μ U Z (fun ω => 1/c (U ω).x) = τ) ∧
  (¬ (∀ {Ω X : Type} [MeasurableSpace Ω]
      [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) →
      IndepFun (fun ω => (U ω).tau) (fun ω => decide (U ω).complier) μ →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ))) ∧
  (¬ (∀ {Ω X : Type} [MeasurableSpace Ω]
      [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} →
        IndepFun (fun ω => (U ω).tau) (fun ω => ((U ω).d0, (U ω).d1))
          (ENNReal.ofReal ((mP μ {ω | (U ω).x = x})⁻¹) • μ.restrict {ω | (U ω).x = x})) →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ)))


def T23Statement : Prop :=
  ∃ q : ReceiptParameters,
      q.val = packageCells ∧
      IsMinimizer
        (fun t : ReceiptParameters =>
          packageObjective
            (receiptLikelihood t)
            observationWeight) q ∧
      ¬ IsMinimizer
        (fun t : ReceiptParameters =>
          weightedObjective
            (receiptLikelihood t)
            observationWeight) q

end
end SAP.P029b
