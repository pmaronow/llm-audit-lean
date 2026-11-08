import SAP.P053.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Counterexamples include both the labelled statistic and the covariate-weighted difference,
at four units and at every positive repeated block size. Upper-tail p-values include ties.
The inference comparison retains the complete six-unit and four-unit examples.
-/

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

def FourCounterexample : Prop :=
    (support (ι := Fin 4) 2).card = 6 ∧
    fourA ∈ support 2 ∧ fourB ∈ support 2 ∧
    binaryTau 2 2 fourY fourA = 0 ∧ binaryTau 2 2 fourY fourB = 0 ∧
    countTable 2 2 (totalSuccesses fourY) (successes fourY fourA) = (1,1,1,1) ∧
    countTable 2 2 (totalSuccesses fourY) (successes fourY fourB) = (1,1,1,1) ∧
    labelStatistic fourA = 1 ∧ labelStatistic fourB = 0 ∧
    binaryTau 2 2 (fun i => fourX i && fourY i) fourA = 1/2 ∧
    binaryTau 2 2 (fun i => fourX i && fourY i) fourB = -1/2

def FourNonfactorization : Prop :=
    (¬ ∃ g : ℝ → ℝ, ∀ s ∈ support (ι := Fin 4) 2,
      labelStatistic s = g (binaryTau 2 2 fourY s)) ∧
    (¬ ∃ g : ℝ → ℝ, ∀ s ∈ support (ι := Fin 4) 2,
      binaryTau 2 2 (fun i => fourX i && fourY i) s = g (binaryTau 2 2 fourY s))

def RepeatedCounterexample (m : ℕ) (hm : 0 < m) : Prop :=
    repeatA m ∈ support (2*m) ∧ repeatB m ∈ support (2*m) ∧
    binaryTau (2*m) (2*m) (repeatY m) (repeatA m)=0 ∧
    binaryTau (2*m) (2*m) (repeatY m) (repeatB m)=0 ∧
    countTable (2*m) (2*m) (totalSuccesses (repeatY m))
      (successes (repeatY m) (repeatA m))=((m : ℤ),(m : ℤ),(m : ℤ),(m : ℤ)) ∧
    countTable (2*m) (2*m) (totalSuccesses (repeatY m))
      (successes (repeatY m) (repeatB m))=((m : ℤ),(m : ℤ),(m : ℤ),(m : ℤ)) ∧
    repeatLabel m hm (repeatA m)=1 ∧ repeatLabel m hm (repeatB m)=0 ∧
    binaryTau (2*m) (2*m) (fun i => repeatX m i && repeatY m i) (repeatA m)=1/2 ∧
    binaryTau (2*m) (2*m) (fun i => repeatX m i && repeatY m i) (repeatB m)=-1/2 ∧
    ((2*m : ℕ) : ℝ)/(4*m : ℕ)=1/2 ∧
    (totalSuccesses (repeatY m) : ℝ)/(4*m : ℕ)=1/2

def RepeatedNonfactorization (m : ℕ) (hm : 0 < m) : Prop :=
    (¬ ∃ g : ℝ → ℝ, ∀ z ∈ support (ι := Fin m × Fin 4) (2*m),
      repeatLabel m hm z = g (binaryTau (2*m) (2*m) (repeatY m) z)) ∧
    (¬ ∃ g : ℝ → ℝ, ∀ z ∈ support (ι := Fin m × Fin 4) (2*m),
      binaryTau (2*m) (2*m) (fun i => repeatX m i && repeatY m i) z =
        g (binaryTau (2*m) (2*m) (repeatY m) z))

def RepeatedScaling : Prop :=
    Tendsto (fun k : ℕ => 4*(k+1)) atTop atTop ∧
    Tendsto (fun k : ℕ => ((2*(k+1) : ℕ) : ℝ)/(4*(k+1) : ℕ)) atTop (nhds (1/2)) ∧
    Tendsto (fun k : ℕ => (totalSuccesses (repeatY (k+1)) : ℝ)/(4*(k+1) : ℕ))
      atTop (nhds (1/2)) ∧
    (∀ k : ℕ, (∑ i : Fin (k+1) × Fin 4,
      ((binaryReal (repeatY (k+1) i))^4+(binaryReal (repeatY (k+1) i))^4)) /
      (4*(k+1) : ℕ) ≤ 2)

def SixDistribution : Prop :=
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=0)).card=1 ∧
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=1)).card=9 ∧
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=2)).card=9 ∧
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=3)).card=1 ∧
    (∀ z ∈ support 3, binaryTau 3 3 sixY z=(2*(successes sixY z : ℝ)-3)/3)

def SixInference : Prop :=
    (support (ι := Fin 6) 3).card=20 ∧ sixTop ∈ support 3 ∧
    binaryTau 3 3 sixY sixTop=1 ∧
    upperP 3 (binaryTau 3 3 sixY) sixTop=1/20 ∧
    upperP 3 (fun w => |binaryTau 3 3 sixY w|) sixTop=1/10 ∧
    upperP 3 (binaryTau 3 3 sixY) sixTop ≤ 1/20 ∧
    ¬ upperP 3 (fun w => |binaryTau 3 3 sixY w|) sixTop ≤ 1/20

def FourInference : Prop :=
    fourTop ∈ support 2 ∧ fourBottom ∈ support 2 ∧
    binaryTau 2 2 fourY fourTop=1 ∧ binaryTau 2 2 fourY fourBottom=-1 ∧
    upperP 2 (binaryTau 2 2 fourY) fourTop=1/6 ∧
    upperP 2 (fun w => |binaryTau 2 2 fourY w|) fourTop=1/3 ∧
    upperP 2 (binaryTau 2 2 fourY) fourBottom=1 ∧
    upperP 2 (fun w => |binaryTau 2 2 fourY w|) fourBottom=1/3 ∧
    (∀ z ∈ support 2, z ≠ fourTop → z ≠ fourBottom →
      binaryTau 2 2 fourY z=0 ∧ upperP 2 (binaryTau 2 2 fourY) z=5/6 ∧
        upperP 2 (fun w => |binaryTau 2 2 fourY w|) z=1)

/-- Both finite statistics and all repeated-block witnesses refute the unrestricted reading. -/
def T2Statement : Prop :=
  FourCounterexample ∧ FourNonfactorization ∧
  (∀ (m : ℕ) (hm : 0 < m), RepeatedCounterexample m hm ∧ RepeatedNonfactorization m hm) ∧
  RepeatedScaling

/-- Exact inclusive upper-tail inferences on six and four units, and monotone invariance. -/
def T3Statement : Prop :=
  SixDistribution ∧ SixInference ∧ (support (ι := Fin 4) 2).card = 6 ∧ FourInference ∧
  (∀ (n1 n0 : ℕ), 0 < n1 → 0 < n0 → ∀ (y : Fin (n1+n0) → ℝ) (g : ℝ → ℝ),
    let T := fun z => sampleMean z y - sampleMean zᶜ y
    StrictMonoOn g (T '' {z | z ∈ support n1}) →
      ∀ z ∈ support n1, upperP n1 (g ∘ T) z = upperP n1 T z)

def T4Statement : Prop :=
  ∀ (p S1 S0 : ℝ), 0 < p → p < 1 → 0 ≤ S1 → 0 ≤ S0 →
    ((S0^2/p+S1^2/(1-p))-(S1^2/p+S0^2/(1-p)) =
      ((S1^2-S0^2)*(2*p-1))/(p*(1-p))) ∧
    ((S1^2/p+S0^2/(1-p) < S0^2/p+S1^2/(1-p)) ↔
      ((1/2 < p ∧ S0 < S1) ∨ (p < 1/2 ∧ S1 < S0)))

end
end SAP.P053
