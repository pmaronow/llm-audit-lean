import SAP.P016b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b
open scoped BigOperators Classical
noncomputable section

/-- All specified numerical and coordinate facts of the 256-unit calibration witness. -/
def CalibrationWitness : Prop :=
  let y := calibrationY
  let z := calibrationZ
  let t : ℝ := 34/99
  let a : ℝ := 413/396
  let d := discrepancy y z t a
  groupSize z false = 128 ∧ groupSize z true = 128 ∧
  groupMean y z false = 10 ∧ groupMean y z true = 10 ∧ tss y/256 = 131/128 ∧
  a = 1+t/8 ∧
  (∀ i, d i = if i.val < 129 then 0 else if i.val < 192 then t/8
    else if i.val < 255 then 3*t/8 else t/2) ∧
  (Finset.univ.filter (fun i => z i = true ∧ d i ≠ 0)).card = 127 ∧
  evenMedian (m := 128) d = 0 ∧
  groupMean (multiplicativeGenerate y z a) z true - 10 = 85/198 ∧
  groupMean (additiveGenerate y z t) z true - 10 = t ∧
  (85/198 : ℝ) = (5/4)*t ∧
  10-groupMean (multiplicativeAdjust y z a) z true = 170/413 ∧
  10-groupMean (additiveAdjust y z t) z true = t ∧
  (170/413 : ℝ)/t = 495/413 ∧ (1 : ℝ) < 495/413

def T18Statement : Prop :=
  CalibrationWitness ∧
  ∀ a : ℝ, 0 ≤ evenMedian (m := 128) (discrepancy calibrationY calibrationZ (34/99) a)

def T19Statement : Prop :=
  (∀ (m : ℕ), 0 < m → ∀ (y : Outcome (2*m)) (z : Assignment (2*m)),
    groupSize z true = m → ∀ (t a : ℝ) (i : Fin (2*m)),
      discrepancy y z t a i = if z i then |(a-1)*y i-t| else 0) ∧
  (∀ (m : ℕ), 0 < m → ∀ (y : Outcome (2*m)) (z : Assignment (2*m)),
    groupSize z true = m → ∀ t a : ℝ,
      evenMedian (discrepancy y z t a) = (1/2) *
        sInf {v : ℝ | ∃ i, z i = true ∧ v = |(a-1)*y i-t|}) ∧
  (∀ (m : ℕ), 0 < m → ∀ (y : Outcome (2*m)) (z : Assignment (2*m)),
    groupSize z true = m → ∀ (t : ℝ) (j : Fin (2*m)), z j = true → y j ≠ 0 →
      discrepancy y z t (1+t/y j) j = 0 ∧
      evenMedian (discrepancy y z t (1+t/y j)) = 0 ∧
      (∀ a, 0 ≤ evenMedian (discrepancy y z t a)) ∧
      (∀ i, z i = true → discrepancy y z t (1+t/y j) i = |t| * |y i/y j-1| ∧
        (t ≠ 0 → y i ≠ y j → discrepancy y z t (1+t/y j) i ≠ 0))) ∧
  (∀ (n : ℕ) (Y : Outcome n) (z : Assignment n), 0 < groupSize z true →
    ∀ t a : ℝ, a ≠ 0 →
      groupMean Y z true - groupMean (additiveAdjust Y z t) z true = t ∧
      groupMean Y z true - groupMean (multiplicativeAdjust Y z a) z true =
        (1-1/a)*groupMean Y z true) ∧
  (∀ (m : ℕ), 0 < m → ∀ (y : Outcome (2*m)) (t a : ℝ), a ≠ 0 →
    uniformExpectation (Balanced (2*m) m) (fun z => groupMean y z.val true) = pooledMean y ∧
    uniformExpectation (Balanced (2*m) m) (fun z =>
      groupMean y z.val true - groupMean (additiveAdjust y z.val t) z.val true) = t ∧
    uniformExpectation (Balanced (2*m) m) (fun z =>
      groupMean y z.val true - groupMean (multiplicativeAdjust y z.val a) z.val true) =
      (1-1/a)*pooledMean y) ∧
  (∀ μ t a : ℝ, μ ≠ 0 → μ ≠ t → a ≠ 0 →
    ((1-1/a)*μ = t ↔ a = μ/(μ-t))) ∧
  CalibrationWitness ∧
  (10 : ℝ)/(10-34/99) = 495/478 ∧ (413/396 : ℝ) ≠ 495/478 ∧
  (10 : ℝ)*(1-1/(413/396)) = 170/413 ∧ (170/413 : ℝ) ≠ 34/99

end
end SAP.P016b
