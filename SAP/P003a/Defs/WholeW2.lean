import Mathlib
import SAP.P003a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-! Search traces contain the brackets immediately before evaluations. The final
bracket is recorded separately. A chronological reply function allows arbitrary
replies, including a sequence produced by a randomized or adaptive oracle. -/

def w2Mid (p : ℤ × ℤ) : ℤ := (p.1+p.2)/2

def w2Search (fuel : ℕ) (reply : ℕ → ℤ → Bool) (t : ℕ) (a b : ℤ) :
    (ℤ × ℤ) × List (ℤ × ℤ) :=
  match fuel with
  | 0 => ((a,b), [])
  | s+1 =>
    if b ≤ a+1 then ((a,b), []) else
      let c := (a+b)/2
      let next := if reply t c then w2Search s reply (t+1) a c
                  else w2Search s reply (t+1) c b
      (next.1, (a,b)::next.2)

def w2Run (k₁ k₂ : ℤ) (reply : ℕ → ℤ → Bool) :=
  w2Search ((k₂-k₁+1).toNat+1) reply 0 (k₁-1) (k₂+1)

def w2Queries (k₁ k₂ : ℤ) (reply : ℕ → ℤ → Bool) : List ℤ :=
  (w2Run k₁ k₂ reply).2.map w2Mid

def W2SearchGeometry (k₁ k₂ : ℤ) (reply : ℕ → ℤ → Bool) : Prop :=
  let s := w2Run k₁ k₂ reply
  s.1.2 = s.1.1+1 ∧ s.2.length < (k₂-k₁+1).toNat+1 ∧
  k₁-1 ≤ s.1.1 ∧ s.1.2 ≤ k₂+1 ∧
  (∀ p ∈ s.2, k₁-1 ≤ p.1 ∧ p.2 ≤ k₂+1 ∧ p.1 < w2Mid p ∧ w2Mid p < p.2) ∧
  (w2Queries k₁ k₂ reply).Nodup ∧
  (∀ c ∈ w2Queries k₁ k₂ reply, k₁ ≤ c ∧ c ≤ k₂)

def W2SearchLogBound (k₁ k₂ : ℤ) (reply : ℕ → ℤ → Bool) : Prop :=
  let d := (k₂-k₁+1).toNat
  (w2Queries k₁ k₂ reply).length ≤ Nat.log 2 d+1 ∧
  ((w2Queries k₁ k₂ reply).length : ℝ) ≤ (⌊logTwo d⌋ : ℤ)+1 ∧
  ((⌊logTwo d⌋ : ℤ) : ℝ)+1 ≤ (⌊logTwo d+2⌋ : ℤ)

def W2ThresholdBrackets (k₁ k₂ r : ℤ) (f : ℤ → Bool) : Prop :=
  let s := w2Run k₁ k₂ (fun _ c => f c)
  s.1.1 = r ∧ k₁-1 ≤ s.1.1 ∧ s.1.1 ≤ r ∧ r < s.1.2 ∧ s.1.2 ≤ k₂+1 ∧
  (∀ p ∈ s.2, k₁-1 ≤ p.1 ∧ p.1 ≤ r ∧ r < p.2 ∧ p.2 ≤ k₂+1) ∧
  sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1) =
    (s.1.1, w2Queries k₁ k₂ (fun _ c => f c))

def W2BalancedDomains (o : Counts) (m : ℕ) : Prop :=
  let n := 2*m
  let Δ : ℤ := (o.a : ℤ)-o.c
  o.total = n ∧ -(m : ℤ) ≤ Δ ∧ Δ ≤ m ∧
  (n : ℝ)*estimate o = (2*Δ : ℤ) ∧
  (candidateNumerators o).toFinset = Finset.Icc (Δ-m) (Δ+m) ∧
  (Finset.Icc (2*Δ) (Δ+m)).card = ((m : ℤ)-Δ).toNat+1 ∧
  (Finset.Icc (Δ-m) (2*Δ)).card = ((m : ℤ)+Δ).toNat+1 ∧
  (Finset.Icc (2*Δ) (Δ+m)).card ≤ n+1 ∧
  (Finset.Icc (Δ-m) (2*Δ)).card ≤ n+1

def w2Cost (cost : ℤ → ℕ) (qs : List ℤ) : ℕ := (qs.map cost).sum

def W2EndpointCosts (o : Counts) (m : ℕ) : Prop :=
  let n := 2*m
  let Δ : ℤ := (o.a : ℤ)-o.c
  ∀ (ru rl : ℕ → ℤ → Bool) (cu cl : ℤ → ℕ),
    (∀ x ∈ w2Queries (2*Δ) (Δ+m) ru, cu x ≤ if x = 0 then 2*(n+1) else n+1) →
    (∀ x ∈ w2Queries (Δ-m) (2*Δ) rl, cl x ≤ if x = 0 then 2*(n+1) else n+1) →
    let U := w2Cost cu (w2Queries (2*Δ) (Δ+m) ru)
    let L := w2Cost cl (w2Queries (Δ-m) (2*Δ) rl)
    U ≤ (n+1)*(Nat.log 2 (n+1)+2) ∧
    L ≤ (n+1)*(Nat.log 2 (n+1)+2) ∧
    (((n+1)*(Nat.log 2 (n+1)+2) : ℕ) : ℝ) ≤
      ((n+1 : ℕ) : ℝ)*((⌊logTwo (n+1 : ℕ)+3⌋ : ℤ) : ℝ) ∧
    (15 ≤ n → ((U+L : ℕ) : ℝ) ≤ 4*n*logTwo n)

/-- P003-T5; p. 20 (PDF p. 20); used on p. 8 (PDF p. 8) and p. 21 (PDF p. 21).
The corrected sentinel search has interior, valid, distinct queries, preserves the
threshold brackets and returns the threshold. For arbitrary chronological replies
it reaches adjacency before exhausting fuel and uses at most floor(log2 d)+1
queries, hence satisfies the printed weaker bound. In a positive balanced design
the upper and lower domains have at most n+1 points. Under the stated per-query
permutation-test costs each endpoint uses at most (n+1)(floor(log2(n+1))+2)
tests, at most the printed relaxed budget, and both use at most 4 n log2 n for n≥15. -/
def T5WholeStatement : Prop :=
  (∀ k₁ k₂ : ℤ, k₁ ≤ k₂ → ∀ reply : ℕ → ℤ → Bool,
    W2SearchGeometry k₁ k₂ reply ∧ W2SearchLogBound k₁ k₂ reply) ∧
  (∀ (k₁ k₂ r : ℤ) (f : ℤ → Bool), k₁ ≤ k₂ → k₁-1 ≤ r → r ≤ k₂ →
    (∀ x, k₁ ≤ x → x ≤ k₂ → (f x = false ↔ x ≤ r)) →
    W2ThresholdBrackets k₁ k₂ r f) ∧
  (∀ (o : Counts) (m : ℕ), 0 < m → o.a+o.b = m → o.c+o.d = m →
    W2BalancedDomains o m ∧ W2EndpointCosts o m) ∧
  (∀ n : ℕ, 15 ≤ n →
    2*((n+1 : ℕ) : ℝ)*((⌊logTwo (n+1 : ℕ)+3⌋ : ℤ) : ℝ) ≤ 4*n*logTwo n)

/-! Actual labeled experiments use the existing uniform assignment law. No
nonemptiness assumption is imposed: it follows from 0<m<n. -/

noncomputable def w2Deviation {n m : ℕ} (y : PotentialTable n) (z : Assignment n m) : ℝ :=
  |tableEstimator y z.val-tableTau y|

noncomputable def w2Tail {n : ℕ} (m : ℕ) (y : PotentialTable n) (x : ℝ) : ℝ :=
  uniformProb (fun z : Assignment n m => x ≤ w2Deviation y z)

noncomputable def w2Support {n : ℕ} (m : ℕ) (y : PotentialTable n) : Finset ℝ :=
  Finset.univ.image (w2Deviation (m := m) y)

def W2RejectingHalfLine {n : ℕ} (m : ℕ) (y : PotentialTable n) (α : ℝ) : Prop :=
  (w2Support m y).Nonempty ∧
  ∃ d ∈ w2Support m y, α ≤ w2Tail m y d ∧
    (∀ e ∈ w2Support m y, α ≤ w2Tail m y e → e ≤ d) ∧
    {x | w2Tail m y x < α} = Set.Ioi d ∧
    (∃ x, w2Tail m y x < α) ∧
    ¬ ∃ x, w2Tail m y x < α ∧ ∀ u, w2Tail m y u < α → x ≤ u

/-- P003-T11; p. 19 (PDF p. 19).
The printed claim is false: in every legal experiment and at every interior level,
the rejecting real thresholds form the open half-line above the largest support
point with tail at least alpha, and have no smallest element. For n=2, m=1 and
the all-zero table the effect and both estimates are zero, and the tail is one
on x≤0 and zero on x>0, giving the explicit rejecting half-line (0,infinity). -/
def T11WholeStatement : Prop :=
  (∀ (n m : ℕ) (y : PotentialTable n) (α : ℝ), 0 < m → m < n →
    0 < α → α < 1 → W2RejectingHalfLine m y α) ∧
  (let y : PotentialTable 2 := fun _ => (false,false)
   tableTau y = 0 ∧ (∀ z : Assignment 2 1, tableEstimator y z.val = 0) ∧
   (∀ x : ℝ, w2Tail 1 y x = if x ≤ 0 then 1 else 0) ∧
   {x | w2Tail 1 y x < 1/2} = Set.Ioi 0) ∧
  T11Statement

def W2SupportRepair {n : ℕ} (m : ℕ) (y : PotentialTable n) (α : ℝ) : Prop :=
  let R := (w2Support m y).filter (fun d => w2Tail m y d < α)
  ((R = ∅ ∧ ∀ z : Assignment n m, ¬ w2Tail m y (w2Deviation y z) < α) ∨
    ∃ x ∈ R, (∀ d ∈ R, x ≤ d) ∧
      (∀ z : Assignment n m, w2Tail m y (w2Deviation y z) < α ↔ x ≤ w2Deviation y z) ∧
      uniformProb (fun z : Assignment n m => w2Tail m y (w2Deviation y z) < α) =
        w2Tail m y x ∧ w2Tail m y x < α) ∧
  uniformProb (fun z : Assignment n m => w2Tail m y (w2Deviation y z) < α) < α

def W2Inversion {n : ℕ} (m : ℕ) (y : PotentialTable n) (α : ℝ) : Prop :=
  (∀ z : Assignment n m,
    let o := unitObserved (unitOutcomes y z.val) z.val
    PossibleTable (unitOutcomes y z.val) z.val y ∧ Possible o (tableCounts y) ∧
    (w2Tail m y (w2Deviation y z) ≥ α →
      α ≤ (pValue (tableCounts y) o : ℝ) ∧
      tableTau y ∈ accepted α o ∧ tableTau y ∈ exactInterval α o)) ∧
  uniformProb (fun z : Assignment n m => tableTau y ∈
    exactInterval α (unitObserved (unitOutcomes y z.val) z.val)) ≥ 1-α

/-- P003-T12; p. 19 (PDF p. 19).
For every finitely supported real probability law the probability of a tail
p-value strictly below an interior alpha is strictly below alpha. In a legal
experiment the rejecting attained deviations are either absent or have a least
point x; rejection is exactly D≥x and has probability q(x)<alpha. The true
table is possible at every observation and is accepted on nonrejection, putting
its effect in the accepted set and its interval hull. Consequently exact
randomization inversion covers with probability at least one minus alpha. -/
def T12WholeStatement : Prop :=
  T12Statement.{0} ∧
  (∀ (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (s : Finset ℝ), μ (s : Set ℝ) = 1 → ∀ α : ℝ, 0 < α → α < 1 →
    (μ {d | (μ (Set.Ici d)).toReal < α}).toReal < α) ∧
  (∀ (n m : ℕ) (y : PotentialTable n) (α : ℝ), 0 < m → m < n →
    0 < α → α < 1 → W2SupportRepair m y α ∧ W2Inversion m y α)

/-! A lattice is a subtype of the real numbers, rather than an integer law
assumed in advance. All theorems below guard its denominator by 0<k. -/

def W2Lattice (k : ℕ) := {x : ℝ // ∃ j : ℤ, x = (j : ℝ)/(k : ℝ)}

noncomputable def w2Point (k : ℕ) (j : ℤ) : W2Lattice k := ⟨(j : ℝ)/(k : ℝ), j, rfl⟩

def W2LatticePMF {k : ℕ} (f : W2Lattice k → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ Summable f ∧ (∑' x, f x) = 1

noncomputable def w2Rescale {k : ℕ} (f : W2Lattice k → ℝ) (j : ℤ) : ℝ :=
  f (w2Point k j)

noncomputable def w2ImageMass {k : ℕ} (f : W2Lattice k → ℝ) (j : ℤ) : ℝ :=
  ∑' x : W2Lattice k, if (k : ℝ)*x.val = (j : ℝ) then f x else 0

noncomputable def w2SourceMean {k : ℕ} (f : W2Lattice k → ℝ) : ℝ :=
  ∑' x : W2Lattice k, x.val*f x

def W2LatticeMoment {k : ℕ} (f : W2Lattice k → ℝ) : Prop :=
  Summable (fun x : W2Lattice k => x.val*f x)

def W2LatticeSymmetric {k : ℕ} (f : W2Lattice k → ℝ) (c₂ : ℤ) : Prop :=
  ∀ j, w2Rescale f (c₂-j) = w2Rescale f j

def W2LatticeSD {k : ℕ} (f : W2Lattice k → ℝ) : Prop := IsSD (w2Rescale f)

noncomputable def w2HalfPointMass (x : W2Lattice 2) : ℝ :=
  if x.val = 1/2 then 1 else 0

noncomputable def w2PrintedRescale (j : ℤ) : ℝ := w2HalfPointMass (w2Point 2 (4*j))

/-- P003-T14; p. 18 (PDF p. 18).
Unrestricted printed decrease excludes every integer pmf; corrected SD includes
the point mass at zero and the fair zero-one law of mean one half. For a positive
lattice denominator k, the source law f on k⁻¹Z gives the pmf g(j)=f(j/k) of kX,
without a moment assumption. Absolute first moments exist simultaneously; when
they exist, the source mean is the integer mean divided by k, with the equivalent
half-integer center assertion. At physical center c₂/(2k), lattice symmetry
is the reflection identity for g, and lattice SD is exactly IsSD g.
For the point mass at one half with k=2 the correct image is unit mass at one,
whereas the printed f(2j) is identically zero and is not a pmf. -/
def T14WholeStatement : Prop :=
  ((∀ f, IsPMF f → ¬ PrintedDecrease f) ∧ IsSD zeroMass ∧ IsSD fairMass ∧
    ¬ PrintedDecrease zeroMass) ∧
  (∑' j : ℤ, (j : ℝ)*fairMass j) = 1/2 ∧
  (∀ (k : ℕ), 0 < k → ∀ f : W2Lattice k → ℝ, W2LatticePMF f →
    IsPMF (w2Rescale f) ∧ (∀ j, w2ImageMass f j = w2Rescale f j) ∧
    (∀ (x : W2Lattice k) (j : ℤ), (k : ℝ)*x.val = j ↔ x = w2Point k j) ∧
    (∀ c₂ : ℤ, W2LatticeSymmetric f c₂ ↔
      ∀ j : ℤ, f (w2Point k (c₂-j)) = f (w2Point k j)) ∧
    (W2LatticeSD f ↔ IsSD (w2Rescale f)) ∧
    (W2LatticeMoment f ↔ Summable (fun j : ℤ => (j : ℝ)*w2Rescale f j)) ∧
    (W2LatticeMoment f →
      w2SourceMean f = (∑' j : ℤ, (j : ℝ)*w2Rescale f j)/(k : ℝ) ∧
      ∀ c₂ : ℤ, w2SourceMean f = (c₂ : ℝ)/(2*k) ↔
        (∑' j : ℤ, (j : ℝ)*w2Rescale f j) = (c₂ : ℝ)/2)) ∧
  (W2LatticePMF w2HalfPointMass ∧
    (∀ j, w2Rescale w2HalfPointMass j = if j = 1 then 1 else 0) ∧
    (∀ j, (w2Point 2 (4*j)).val = 2*(j : ℝ)) ∧
    (∀ j, w2PrintedRescale j = 0) ∧ ¬ IsPMF w2PrintedRescale)

/-! The second dependent joint law is specified on four actual weighted atoms. -/

def w2BX : Fin 4 → ℤ := ![-1,0,0,1]
def w2BY : Fin 4 → ℤ := ![0,0,1,1]
noncomputable def w2BW : Fin 4 → ℝ := ![1/3,1/6,1/6,1/3]

noncomputable def w2ThreeMass (j : ℤ) : ℝ :=
  (if j = -1 then 1/3 else 0)+(if j = 0 then 1/3 else 0)+(if j = 1 then 1/3 else 0)

noncomputable def w2BSumMass (j : ℤ) : ℝ :=
  (if j = -1 then 1/3 else 0)+(if j = 0 then 1/6 else 0)+
  (if j = 1 then 1/6 else 0)+(if j = 2 then 1/3 else 0)

/-- P003-T9; p. 23 (PDF p. 23).
The printed claim is false: with corrected SD and lattice denominator one,
dependent variables can have an SD first marginal and a fair zero-one second
marginal while their sum fails SD. The identical fair pair gives masses one half
at zero and two and mean one. The four atoms (-1,0),(0,0),(0,1),(1,1) with weights
one third, one sixth, one sixth, one third give a uniform first marginal on
{-1,0,1} of mean zero and a fair second marginal. Their sum has those four masses
at -1,0,1,2, is symmetric about its mean one half, and fails decrease and SD. -/
def T9WholeStatement : Prop :=
  T9Statement ∧
  (∀ i : Fin 4, 0 < w2BW i) ∧ (∑ i, w2BW i) = 1 ∧
  (∀ j : ℤ,
    (∑ i : Fin 4, if w2BX i = j then w2BW i else 0) = w2ThreeMass j ∧
    (∑ i : Fin 4, if w2BY i = j then w2BW i else 0) = fairMass j ∧
    (∑ i : Fin 4, if w2BX i+w2BY i = j then w2BW i else 0) = w2BSumMass j) ∧
  IsSD w2ThreeMass ∧ (∑' j : ℤ, (j : ℝ)*w2ThreeMass j) = 0 ∧
  IsMass w2BSumMass ∧ (∑' j : ℤ, (j : ℝ)*w2BSumMass j) = 1/2 ∧
  (∀ j, w2BSumMass (1-j) = w2BSumMass j) ∧
  w2BSumMass 1 < w2BSumMass 2 ∧ ¬ IsSD w2BSumMass

end SAP.P003a
