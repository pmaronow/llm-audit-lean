import SAP.P032.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

/-! Bounded counterexample data; country and record labels start at zero. -/

def pairDyads : Fin 2 → DyadData (Fin 4) := fun r =>
  ⟨![({0,1} : Finset (Fin 4)), {2,3}] r, by fin_cases r <;> decide⟩

def pairErrorValues : Fin 4 → Fin 2 → ℝ := ![![-1,-1], ![-1,1], ![1,-1], ![1,1]]

def negativePairDistribution : FiniteDistribution (Fin 4) where
  weight := ![1/8,3/8,3/8,1/8]
  nonneg := by intro s; fin_cases s <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def positivePairDistribution : FiniteDistribution (Fin 4) where
  weight := ![3/8,1/8,1/8,3/8]
  nonneg := by intro s; fin_cases s <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def pairCovariance (sign : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,sign/2; sign/2,1]

def pairIntercept : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => 1

def pairSlope : Matrix (Fin 2) (Fin 1) ℝ := fun r _ => ![-1,1] r

def fourDyadData : Fin 4 → DyadData (Fin 6) := fun r =>
  ⟨![({0,1} : Finset (Fin 6)), {0,2}, {3,4}, {3,5}] r, by fin_cases r <;> decide⟩

def fourDistribution : FiniteDistribution (Fin 16) where
  weight := fun ω => 3/64 + if ω = 3 ∨ ω = 12 then 1/8 else 0
  nonneg := by intro ω; split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def fourErrorValues : Fin 16 → Fin 4 → ℝ :=
  ![![-1,-1,-1,-1], ![-1,-1,-1,1], ![-1,-1,1,-1], ![-1,-1,1,1],
    ![-1,1,-1,-1], ![-1,1,-1,1], ![-1,1,1,-1], ![-1,1,1,1],
    ![1,-1,-1,-1], ![1,-1,-1,1], ![1,-1,1,-1], ![1,-1,1,1],
    ![1,1,-1,-1], ![1,1,-1,1], ![1,1,1,-1], ![1,1,1,1]]

def fourCovariance : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1/4,-1/4,-1/4; 1/4,1,-1/4,-1/4;
    -1/4,-1/4,1,1/4; -1/4,-1/4,1/4,1]

def sixDyadData : Fin 6 → DyadData (Fin 4) := fun r =>
  ⟨![({0,1} : Finset (Fin 4)), {0,2}, {0,3}, {1,2}, {1,3}, {2,3}] r,
    by fin_cases r <;> decide⟩

def sixCovariance : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,1/8,1/8,1/8,1/8,-1/2;
    1/8,1,1/8,1/8,-1/2,1/8;
    1/8,1/8,1,-1/2,1/8,1/8;
    1/8,1/8,-1/2,1,1/8,1/8;
    1/8,-1/2,1/8,1/8,1,1/8;
    -1/2,1/8,1/8,1/8,1/8,1]

def recordMean (u : R → ℝ) : ℝ := (Fintype.card R : ℝ)⁻¹ * ∑ r, u r

def residualInterceptVariance (d : R → DyadData M) (u : R → ℝ) : ℝ :=
  (Fintype.card R : ℝ)^(-2 : ℤ) * quadForm (fun r s => dyadicMask d r s)
    (fun r => u r-recordMean u)

def blockDyad {k : ℕ} (b : Fin k) (d : DyadData M) : DyadData (Fin k × M) where
  members := d.members.map ⟨fun i => (b,i), by intro i j h; exact (Prod.mk.inj h).2⟩
  two := by simp [d.two]

def fourReplicatedDyads (m : ℕ) (r : Fin m × Fin 4) : DyadData (Fin m × Fin 6) :=
  blockDyad r.1 (fourDyadData r.2)

def sixReplicatedDyads (m : ℕ) (r : Fin m × Fin 6) : DyadData (Fin m × Fin 4) :=
  blockDyad r.1 (sixDyadData r.2)

def fourReplicatedErrors {Ω : Type*} (block : ℕ → Ω → Fin 16)
    (m : ℕ) (ω : Ω) (r : Fin m × Fin 4) : ℝ := fourErrorValues (block r.1.val ω) r.2

def fourIncidentPairTotal {Ω : Type*} (block : ℕ → Ω → Fin 16) (b : ℕ) (ω : Ω) (pair : Fin 2) : ℝ :=
  if pair = 0 then fourErrorValues (block b ω) 0 + fourErrorValues (block b ω) 1
    else fourErrorValues (block b ω) 2 + fourErrorValues (block b ω) 3

def fairSignValue (a : Fin 2) : ℝ := if a = 0 then -1 else 1

def sixErrorValues (a : Fin 13 → Fin 2) (r : Fin 6) : ℝ :=
  (Real.sqrt 2/4) * (∑ i : Fin 4,
    if i ∈ (sixDyadData r).members then fairSignValue (a ⟨i.val, by omega⟩) else 0) +
  (if r.val < 3 then 1 else -1) * (Real.sqrt 2/2) *
    fairSignValue (a ⟨4+(![0,1,2,2,1,0] r : Fin 3).val, by omega⟩) +
  (1/2 : ℝ) * fairSignValue (a ⟨7+r.val, by omega⟩)

def sixReplicatedErrors {Ω : Type*} (block : ℕ → Ω → (Fin 13 → Fin 2))
    (m : ℕ) (ω : Ω) (r : Fin m × Fin 6) : ℝ := sixErrorValues (block r.1.val ω) r.2

def sixIncidentQuadratic (a : Fin 13 → Fin 2) : ℝ :=
  quadForm (fun r s => dyadicMask sixDyadData r s) (sixErrorValues a)

def onesDesign : Matrix R (Fin 1) ℝ := fun _ _ => 1

def fourSpectralBasis : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,0,1; 1,-1,0,1; -1,0,1,1; -1,0,-1,1]

def fourSpectralInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/4,1/4,-1/4,-1/4; 1/2,-1/2,0,0; 0,0,1/2,-1/2; 1/4,1/4,1/4,1/4]

def sixSpectralBasis : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,1,1,1,0,0; -1,0,1,0,1,0; 0,-1,1,0,0,1;
    0,-1,1,0,0,-1; -1,0,1,0,-1,0; 1,1,1,-1,0,0]

def sixSpectralInverse : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/6,-2/6,1/6,1/6,-2/6,1/6; 1/6,1/6,-2/6,-2/6,1/6,1/6;
    1/6,1/6,1/6,1/6,1/6,1/6; 1/2,0,0,0,0,-1/2;
    0,1/2,0,0,-1/2,0; 0,0,1/2,-1/2,0,0]

def fourBlockTotal (a : Fin 16) : ℝ := ∑ r, fourErrorValues a r

def fourIncidentSquares (a : Fin 16) : ℝ :=
  (fourErrorValues a 0+fourErrorValues a 1)^2 +
  (fourErrorValues a 2+fourErrorValues a 3)^2

def fairSignDistribution : FiniteDistribution (Fin 2) where
  weight := fun _ => 1/2
  nonneg := by intro a; norm_num
  total := by norm_num [Fin.sum_univ_succ]

def sixSignDistribution : FiniteDistribution (Fin 13 → Fin 2) where
  weight := fun _ => 1/8192
  nonneg := by intro a; norm_num
  total := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,Fintype.card_fin]
    norm_num

def sixProductMeasure : Measure (Fin 13 → Fin 2) :=
  Measure.pi (fun _ : Fin 13 => distributionMeasure fairSignDistribution)

def sixLoadings : Matrix (Fin 6) (Fin 13) ℝ :=
  let t := Real.sqrt 2
  ![![t/4,t/4,0,0,t/2,0,0,1/2,0,0,0,0,0],
    ![t/4,0,t/4,0,0,t/2,0,0,1/2,0,0,0,0],
    ![t/4,0,0,t/4,0,0,t/2,0,0,1/2,0,0,0],
    ![0,t/4,t/4,0,0,0,-t/2,0,0,0,1/2,0,0],
    ![0,t/4,0,t/4,0,-t/2,0,0,0,0,0,1/2,0],
    ![0,0,t/4,t/4,-t/2,0,0,0,0,0,0,0,1/2]]

def sixBlockTotal (a : Fin 13 → Fin 2) : ℝ := ∑ r : Fin 6, sixErrorValues a r

def replicatedMatrix (m : ℕ) (A : Matrix R R ℝ) : Matrix (Fin m × R) (Fin m × R) ℝ :=
  Matrix.of (fun r s => if r.1 = s.1 then A r.2 s.2 else 0)

def diagonalRestriction (A : Matrix R R ℝ) : Matrix R R ℝ :=
  Matrix.of (fun r s => recordMask r s * A r s)

end
end SAP.P032
