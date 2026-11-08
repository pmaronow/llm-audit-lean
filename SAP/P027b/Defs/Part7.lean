import SAP.P027b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

variable {U Ω : Type} [Fintype U] [Fintype Ω]

def liftDesign {G : Type} [Fintype G] (D : Design G Ω) (n : G → ℕ) :
    Design (Σ g, Fin (n g)) Ω where
  weight := D.weight
  nonneg := D.nonneg
  total := D.total
  selected ω k := D.selected ω k.1

def groupTotal {G : Type} (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (g : G) : ℝ :=
  ∑ j, y ⟨g,j⟩

def groupSquares {G : Type} (n : G → ℕ) (y : (Σ g, Fin (n g)) → ℝ) (g : G) : ℝ :=
  ∑ j, y ⟨g,j⟩ ^ 2

def oneDraw {G : Type} [Fintype G] (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (hs : ∑ g, p g = 1) : Design G G where
  weight := p
  nonneg := hp
  total := hs
  selected g k := decide (g = k)

def phaseProb (r : ℕ) (g : Fin r × Fin 2) : ℝ :=
  if g.2 = 0 then 1/(6*r) else 5/(6*r)

def phaseGrouped (r : ℕ) (hr : 0 < r) : Design (Fin r × Fin 2) (Fin r × Fin 2) :=
  oneDraw (phaseProb r) (fun g => by unfold phaseProb; split <;> positivity)
    ((by
      have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      simp only [Fintype.sum_prod_type, phaseProb, Fin.sum_univ_two]
      norm_num only [Fin.reduceEq, ite_true, ite_false]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      <;> ring))

def phaseOriginal (r m : ℕ) (hr : 0 < r) := liftDesign (phaseGrouped r hr) (fun _ => m)

def phaseSize {r m : ℕ} (k : Σ _ : Fin r × Fin 2, Fin m) : ℝ :=
  if k.1.2 = 0 then 2 else 10

def periodicMeanV {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  variance (phaseOriginal r m hr) (htMean (phaseOriginal r m hr) z)

def periodicMeanH {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  expect (phaseOriginal r m hr) (fun ω => htVarianceEstimator (phaseOriginal r m hr) z ω /
    ((m:ℝ)*(2*r))^2)

def periodicMeanC {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  expect (phaseOriginal r m hr) (fun ω => c2Estimator (phaseOriginal r m hr) z ω /
    ((m:ℝ)*(2*r))^2)

def periodicMeanW {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  expect (phaseOriginal r m hr) (wrEstimator (phaseOriginal r m hr) z m)

def contrastR (q : ℝ) : ℝ := 5*(q-1)/(9*q-5)

def contrastCoefficient (q : ℝ) : ℝ := 6*q/(9*q-5)

def periodicContrast {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  periodicMeanC hr z-(1+contrastR (2*r))*periodicMeanH hr z

def populationSquareNorm {K : Type} [Fintype K] (z : K → ℝ) : ℝ := ∑ k, z k^2

structure PhaseDecomposition (r m : ℕ)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  within : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  signal : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  low : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  high : (Σ _ : Fin r × Fin 2, Fin m) → ℝ
  within_zero : ∀ g, groupTotal (fun _ : Fin r × Fin 2 => m) within g = 0
  signal_multiple : ∃ b : ℝ, ∀ k, signal k = b*(phaseSize k-6)
  low_constant : ∃ v : (Fin r × Fin 2) → ℝ, (∑ g, v g) = 0 ∧
    (∀ g, g.2 ≠ 0 → v g = 0) ∧ ∀ k, low k = v k.1
  high_constant : ∃ v : (Fin r × Fin 2) → ℝ, (∑ g, v g) = 0 ∧
    (∀ g, g.2 = 0 → v g = 0) ∧ ∀ k, high k = v k.1
  reconstruct : ∀ k, z k = within k+signal k+low k+high k

def phaseCenteredSpace (r m : ℕ) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  carrier := {v | ∑ k, v k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change (∑ k, v k) = 0 at hv
    change (∑ k, w k) = 0 at hw
    simpa [Finset.sum_add_distrib, hv, hw]
  smul_mem' := by
    intro c v hv
    change (∑ k, v k) = 0 at hv
    simpa [← Finset.mul_sum, hv]

def phaseWithinSpace (r m : ℕ) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  carrier := {v | ∀ g, ∑ j : Fin m, v ⟨g,j⟩ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw g
    simpa [Finset.sum_add_distrib, hv g, hw g]
  smul_mem' := by intro c v hv g; simpa [← Finset.mul_sum, hv g]

def phaseSignalSpace (r m : ℕ) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) :=
  Submodule.span ℝ {fun k => phaseSize k - 6}

def phaseParitySpace (r m : ℕ) (high : Bool) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) where
  carrier := {v | (∀ (g : Fin r × Fin 2) (i j : Fin m), v ⟨g,i⟩ = v ⟨g,j⟩) ∧
    (∀ k, (if high then k.1.2 = 0 else k.1.2 ≠ 0) → v k = 0) ∧
    ∑ k, v k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    refine ⟨?_, ?_, ?_⟩
    · intro g i j; change v ⟨g,i⟩ + w ⟨g,i⟩ = v ⟨g,j⟩ + w ⟨g,j⟩
      rw [hv.1 g i j, hw.1 g i j]
    · intro k hk; change v k + w k = 0; rw [hv.2.1 k hk, hw.2.1 k hk]; ring
    · simpa [Finset.sum_add_distrib, hv.2.2, hw.2.2]
  smul_mem' := by
    intro c v hv
    refine ⟨?_, ?_, ?_⟩
    · intro g i j; change c * v ⟨g,i⟩ = c * v ⟨g,j⟩; rw [hv.1 g i j]
    · intro k hk; change c * v k = 0; rw [hv.2.1 k hk]; ring
    · simpa [← Finset.mul_sum, hv.2.2]

def phaseComponentSpace (r m : ℕ) (i : Fin 4) :
    Submodule ℝ ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) :=
  if i = 0 then phaseWithinSpace r m else if i = 1 then phaseSignalSpace r m
  else if i = 2 then phaseParitySpace r m false else phaseParitySpace r m true

def GaussianNoise {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ε : K → Ξ → ℝ) (σ2 : ℝ) : Prop :=
  (∀ k, AEMeasurable (ε k) μ ∧ μ.map (ε k) = gaussianReal 0 σ2.toNNReal) ∧
    iIndepFun ε μ

def chiSquaredLaw (d : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
    (fun v : Fin d → ℝ => ∑ j, v j^2)

def a3HighH : Fin 4 → ℝ := ![1412.15,1564.34,1430.59,1562.38]

def a3HighC : Fin 4 → ℝ := ![2029.28,2396.58,2032.07,2395.86]

def a3HighR : Fin 4 → ℕ := ![2,10,2,10]

def a3HighM : Fin 4 → ℕ := ![30,30,60,60]

def a3HighContrast : Fin 4 → ℝ := ![-102561/1550,-29703/1750,-281297/3100,-25671/1750]

def a3HighExponent : Fin 4 → ℕ := ![189,213,522,371]

def rawOutcomes {Ξ K : Type} (x : K → ℝ) (β : ℝ) (ε : K → Ξ → ℝ)
    (ξ : Ξ) (k : K) : ℝ := β*x k+ε k ξ

def centeredOutcomes {Ξ K : Type} [Fintype K] (x : K → ℝ) (β : ℝ)
    (ε : K → Ξ → ℝ) (ξ : Ξ) (k : K) : ℝ :=
  rawOutcomes x β ε ξ k - (∑ l, rawOutcomes x β ε ξ l)/(Fintype.card K : ℝ)

def periodicModelPredictions (N m ρ : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  let q := N/m
  let σ2 := 900*(1-ρ^2)
  let β2 := 900*ρ^2*(N-1)/(16*N)
  let B := 16*β2/q+σ2*(N-m)/N^2
  let V := (9*q/5)*B
  let H := V-B
  let C := H+(N-m)/N^2*(16*N*β2+(N-1)*σ2)
  let W := (9/5)*σ2/m
  (V,H,C,W)

end
end SAP.P027b
