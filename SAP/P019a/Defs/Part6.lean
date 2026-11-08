import SAP.P019a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical
universe u

def T4Statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (S : Study Ω), S.standing →
  (∀ (n : ℕ) (z : Bool), (S.law.iid n).prob (fun s => S.cellCount s z false = 0) =
    (1 - S.law.prob (S.cell z false))^n ∧
    0 < (S.law.iid n).prob (fun s => S.cellCount s z false = 0)) ∧
  (∀ (n : ℕ), 2 ≤ n → ∀ c1 c0 : ℝ,
    let P := S.law.iid n
    let A := @Study.sampleA Ω _ S n
    let B := fun s : Fin n → Ω => S.sampleB s c1 c0
    let h := @Study.sampleH Ω _ S n
    let b := S.listMean true false - S.listMean false false - 1
    0 < P.prob S.occupied ∧
    (∀ k : ℕ, k ≤ n → P.prob (fun s => S.negativeCount s = k) ≠ 0 →
      (∀ i : ℕ, i ≤ k →
        P.ce (fun s => if S.cellCount s true false = i then 1 else 0)
          (fun s => S.negativeCount s = k) =
            (Nat.choose k i : ℝ) * S.gamma^i * (1-S.gamma)^(k-i)) ∧
      P.ce (fun s => if 0 < S.cellCount s true false then 1 else 0)
        (fun s => S.negativeCount s = k) = 1-(1-S.gamma)^k ∧
      P.ce (fun s => if 0 < S.cellCount s false false then 1 else 0)
        (fun s => S.negativeCount s = k) = 1-S.gamma^k) ∧
    (∀ s : Fin n → Ω, S.occupied s → P.prob (S.patternFibre s) ≠ 0 →
      (∀ z : Bool,
        P.ce (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.listMean z false ∧
        P.cv (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z false) / (S.cellCount s z false : ℝ)) ∧
      P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
        (S.patternFibre s) = 0 ∧
      P.ce B (S.patternFibre s) = b ∧ P.cv B (S.patternFibre s) = h s) ∧
    (∀ a : ℝ, P.prob (fun s => S.occupied s ∧ A s = a) ≠ 0 → ∀ z : Bool,
      P.ce (fun s => S.cellMean s z false (if z then c1 else c0))
        (fun s => S.occupied s ∧ A s = a) = S.listMean z false) ∧
    (∀ z : Bool,
      P.ccov (fun t => S.cellMean t z false (if z then c1 else c0)) A S.occupied = 0) ∧
    P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
      S.occupied = 0 ∧
    P.cv (fun s => S.muHat s c1 c0) S.occupied =
      b^2 * P.cv A S.occupied + P.ce (fun s => A s ^ 2 * h s) S.occupied ∧
    P.cv (fun s => A s * B s) S.occupied =
      b^2 * P.cv A S.occupied + P.ce (fun s => A s ^ 2 * h s) S.occupied ∧
    (P.ce A S.occupied)^2 * P.cv B S.occupied +
      P.cv A S.occupied * (P.ce B S.occupied)^2 +
      P.cv A S.occupied * P.cv B S.occupied =
        b^2 * P.cv A S.occupied +
          P.ce (fun s => A s ^ 2) S.occupied * P.ce h S.occupied ∧
    P.cv (fun s => A s * B s) S.occupied -
      ((P.ce A S.occupied)^2 * P.cv B S.occupied +
        P.cv A S.occupied * (P.ce B S.occupied)^2 +
        P.cv A S.occupied * P.cv B S.occupied) =
      P.ccov (fun s => A s^2) h S.occupied) ∧
  (let R := fun n : ℕ => (S.law.iid (n+2)).ccov
      (fun s => (S.sampleA s)^2) (fun s => S.sampleH s) (fun s => S.occupied s);
    Asymptotics.IsBigO atTop R (fun n : ℕ => (1/((n+2 : ℕ) : ℝ))^2) ∧
    Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)^2 * R n) atTop
      (nhds (-2 * (S.mu * S.truthRate) *
        (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / S.gamma +
         S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (1-S.gamma))))) ∧
  (∀ n : ℕ, 0 < n →
    (S.law.iid n).mean (fun s => (S.armCount s true : ℝ)) = (n : ℝ)*S.gamma ∧
    ∀ s : Fin n → Ω, (S.armCount s true : ℝ) = (n : ℝ)*S.gammaHat s)

def T9Statement : Prop :=
  (∀ j : Fin 5, (sequentialStudy j).standing ∧ (sequentialStudy j).beta = 1) ∧
  (∀ a : Fin 5 → Bool, (uniformFin 128 (by norm_num)).prob
    (fun ω => ∀ j, (sequentialStudy j).Z ω = a j) = 1/32) ∧
  (∀ j ω, (sequentialStudy j).betaPsi ω = sequentialPsi j ω) ∧
  (∀ j, (uniformFin 128 (by norm_num)).mean (sequentialPsi j) = 0) ∧
  (∀ j k, (uniformFin 128 (by norm_num)).mean
    (fun ω => sequentialPsi j ω * sequentialPsi k ω) =
      if j = k then (if j.val < 4 then 4 else 2) else 2) ∧
  WeakLimit (uniformFin 128 (by norm_num))
    (fun _ s j => studentized ((sequentialStudy j).betaHat s 0 0) 1
      ((sequentialStudy j).betaVarianceHat s 0))
    ((Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)).map correlatedNormals) ∧
  WeakLimit (uniformFin 128 (by norm_num)) (fun _ s => fisherStatistic
    (fun j => normalPValue ((sequentialStudy j).betaHat s 0 0) 1
      ((sequentialStudy j).betaVarianceHat s 0))) sequentialFisherLimit ∧
  Integrable (fun x : ℝ => x) sequentialFisherLimit ∧
  Integrable (fun x : ℝ => x^2) sequentialFisherLimit ∧
  20 < continuousVariance sequentialFisherLimit ∧ sequentialFisherLimit ≠ chiSquareTen

def T10Statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (P : FiniteLaw Ω) (S : Fin 5 → Study Ω),
    (∀ j, (S j).law = P) → (∀ j, (S j).standing) → jointAssignmentStable P S →
    (∀ j, (S j).beta = 1) ∧
    (∀ j k : Fin 5, j ≠ k → ∀ ω, P.prob (latentVectorFibre S ω) ≠ 0 →
      P.ce (fun t => (S j).betaPsi t * (S k).betaPsi t) (latentVectorFibre S ω) = 0) ∧
    (∀ j k : Fin 5, j ≠ k → P.mean (fun ω => (S j).betaPsi ω * (S k).betaPsi ω) = 0) ∧
    WeakLimit P (fun _ s j => studentized ((S j).betaHat s 0 0) 1
      ((S j).betaVarianceHat s 0)) (Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)) ∧
    WeakLimit P (fun _ s j => normalPValue ((S j).betaHat s 0 0) 1
      ((S j).betaVarianceHat s 0))
      (Measure.pi (fun _ : Fin 5 => volume.restrict (Set.Icc (0 : ℝ) 1))) ∧
    WeakLimit P (fun _ s => fisherStatistic (fun j =>
      normalPValue ((S j).betaHat s 0 0) 1 ((S j).betaVarianceHat s 0))) chiSquareTen

def T11Statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (S : Study Ω),
    (S.noLiarsDesign → S.treatmentIndependent →
      0 < S.law.prob (fun ω => S.Z ω = false) →
      0 < S.law.prob (fun ω => S.Z ω = true) →
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) =
        S.law.mean (fun ω => (S.W ω : ℝ)) + S.mu ∧
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false) =
        S.law.mean (fun ω => (S.W ω : ℝ)) ∧
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) -
        S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false) = S.mu) ∧
    (S.monotone → 0 < S.law.prob (fun ω => S.Y ω = true) →
      S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = true) = 1) ∧
    (S.standing → ∀ α : ℝ, 0 < α → α < 1 →
      {x : ℝ | 1-α/2 ≤ normalCDF x}.Nonempty →
      BddBelow {x : ℝ | 1-α/2 ≤ normalCDF x} →
      Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
        |S.muHat s 0 0-S.mu| ≤ normalQuantile (1-α/2) *
          Real.sqrt (S.muVarianceHat s 0 0 0))) atTop (nhds (1-α))) ∧
    (S.monotone → S.noLiarsDesign → S.treatmentIndependent →
      0 < S.law.prob (S.cell false true) → 0 < S.law.prob (S.cell true true) →
      S.listMean true true = S.listMean false true + 1)

end
end SAP.P019a
