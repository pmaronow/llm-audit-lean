import Mathlib
import SAP.P044.Defs
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
namespace SAP.P044
open Finset
open scoped BigOperators
noncomputable section
/-- Uniform rational mass on a finite type. Normalization requires a nonempty type. -/
def w1Uniform {Ω : Type*} [Fintype Ω] : Ω → ℚ :=
  fun _ => 1 / (Fintype.card Ω : ℚ)
/-- The matching witness has `n+2` ordinary pairs and one distinguished pair. -/
def w1MatchingN (n : ℕ) : ℕ := 2 * (n + 3)
/-- Its exhaustive bank has two choices for the distinguished pair and `n+2`
choices for the ordinary treated pair. In particular `n=4998` gives 10000 rows. -/
def w1MatchingR (n : ℕ) : ℕ := 2 * (n + 2)
def w1MatchingAdj (n : ℕ) : Adjacency (w1MatchingN n) :=
  fun i j => decide (i ≠ j ∧ i.val / 2 = j.val / 2)
def w1MatchingAssignments (n : ℕ) (s : Fin (w1MatchingR n)) :
    Assignment (w1MatchingN n) :=
  let br : Fin 2 × Fin (n + 2) := finProdFinEquiv.symm s
  fun i => decide (if i.val / 2 = 0 then br.1 = 1 else i.val / 2 = br.2.val + 1)
def w1MatchingF (n : ℕ) : Fin (w1MatchingR n) → Fin (w1MatchingN n) → Exposure :=
  fun s => exposure (w1MatchingAdj n) (w1MatchingAssignments n s)
/-- Only the two distinguished vertices have nonzero outcomes; their outcomes
are one at every exposure. Thus the target contrast is zero. -/
def w1MatchingY (n : ℕ) : Fin (w1MatchingN n) → Exposure → ℚ :=
  fun i _ => if i.val < 2 then 1 else 0
def w1MatchingBankF (n : ℕ) (e : Equiv.Perm (Fin (w1MatchingR n))) :=
  fun s => w1MatchingF n (e s)
def w1MatchingW (n : ℕ) (e : Equiv.Perm (Fin (w1MatchingR n))) :
    Fin (w1MatchingN n) → Exposure → ℚ := smoothedWeight (w1MatchingBankF n e)
def w1MatchingQ (n : ℕ) (e : Equiv.Perm (Fin (w1MatchingR n))) :
    Fin (w1MatchingN n) → Fin (w1MatchingN n) → Exposure → Exposure → ℚ :=
  smoothedJoint (w1MatchingBankF n e)
def w1MatchingT (n : ℕ) (e : Equiv.Perm (Fin (w1MatchingR n))) :
    Fin (w1MatchingR n) → ℚ :=
  htContrast (w1MatchingF n) (w1MatchingY n) (w1MatchingW n e) .d11 .d00
def w1MatchingV (n : ℕ) (e : Equiv.Perm (Fin (w1MatchingR n))) :
    Fin (w1MatchingR n) → ℚ :=
  varianceEstimate (w1MatchingF n) (w1MatchingY n)
    (w1MatchingW n e) (w1MatchingQ n e) .d11 .d00
def w1MatchingFirst (n : ℕ) : Fin (w1MatchingR n) := ⟨0, by unfold w1MatchingR; omega⟩
def w1MatchingWeight (n : ℕ) : ℚ := ((n : ℚ) + 3) / (2 * n + 5)
def w1MatchingJoint (n : ℕ) : ℚ := ((n : ℚ) + 2) / (2 * n + 5)
def w1MatchingIndependentMass (n : ℕ) :
    (Equiv.Perm (Fin (w1MatchingR n)) × Fin (w1MatchingR n)) → ℚ :=
  fun x => w1Uniform x.1 * w1Uniform x.2
/-- Geometry and interpretation of the finite design, including exposure
sufficiency on all profiles by composition with the four-condition mapping. -/
def W1MatchingGeometry (n : ℕ) : Prop :=
  (∀ i j, w1MatchingAdj n i j = w1MatchingAdj n j i) ∧
  (∀ i, w1MatchingAdj n i i = false ∧ ∃ j, w1MatchingAdj n i j = true) ∧
  Function.Injective (w1MatchingAssignments n) ∧
  (∀ s i, w1MatchingF n s i =
    if w1MatchingAssignments n s i then Exposure.d11 else Exposure.d00) ∧
  tau (w1MatchingY n) .d11 .d00 = 0
/-- The uniform design's exact marginal probabilities and their positive support. -/
def W1MatchingMarginals (n : ℕ) : Prop :=
  (∀ i a, marginal w1Uniform (w1MatchingF n) i a =
    match a with
    | .d11 => if i.val < 2 then (1/2 : ℚ) else 1 / ((n : ℚ) + 2)
    | .d00 => if i.val < 2 then (1/2 : ℚ) else ((n : ℚ) + 1) / ((n : ℚ) + 2)
    | _ => 0) ∧
  (∀ i, 0 < marginal w1Uniform (w1MatchingF n) i .d11 ∧
    0 < marginal w1Uniform (w1MatchingF n) i .d00)
/-- The exhaustive permuted bank's inputs needed by the S7 functional.
The positivity involving an ordinary vertex prevents a zero adjustment from
importing a nonzero distinguished squared outcome into a mixed pair. -/
def W1MatchingInputs (n : ℕ) : Prop :=
  (∀ e i a, 0 < w1MatchingW n e i a) ∧
  (∀ e i j a b, 0 ≤ w1MatchingQ n e i j a b) ∧
  (∀ e i a, w1MatchingQ n e i i a a = w1MatchingW n e i a) ∧
  (∀ e i a, i.val < 2 → (a = Exposure.d11 ∨ a = .d00) →
    w1MatchingW n e i a = w1MatchingWeight n) ∧
  (∀ e i j a b, i.val < 2 → j.val < 2 →
    (a = Exposure.d11 ∨ a = .d00) → (b = Exposure.d11 ∨ b = .d00) →
    w1MatchingQ n e i j a b =
      if a = b then (if i = j then w1MatchingWeight n else w1MatchingJoint n) else 0) ∧
  (∀ e i j a b, (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2) →
    (a = Exposure.d11 ∨ a = .d00) → (b = Exposure.d11 ∨ b = .d00) →
    0 < w1MatchingQ n e i j a b)
def W1MatchingPointwise (n : ℕ) : Prop :=
  ∀ e s, w1MatchingT n e s =
    if w1MatchingAssignments n s ⟨0, by unfold w1MatchingN; omega⟩ then
      2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n)
    else -(2 / ((w1MatchingN n : ℚ) * w1MatchingWeight n))
def W1MatchingWithin (n : ℕ) : Prop :=
  ∀ e s,
    totalVarianceEstimate (w1MatchingF n) (w1MatchingY n)
      (w1MatchingW n e) (w1MatchingQ n e) .d11 s +
    totalVarianceEstimate (w1MatchingF n) (w1MatchingY n)
      (w1MatchingW n e) (w1MatchingQ n e) .d00 s =
    4 / w1MatchingWeight n ^ 2 - 2 / w1MatchingWeight n - 2 / w1MatchingJoint n
def W1MatchingCross (n : ℕ) : Prop :=
  ∀ e s,
    totalCovarianceEstimate (w1MatchingF n) (w1MatchingY n)
      (w1MatchingW n e) (w1MatchingQ n e) .d11 .d00 s = -2 / w1MatchingWeight n
/-- Evaluation at any fixed position of a uniformly chosen permutation has
the original uniform law, expressed for all rational statistics. -/
def W1UniformFirstLaw : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (a : α) (g : α → ℚ),
    expect w1Uniform (fun e : Equiv.Perm α => g (e a)) = expect w1Uniform g
/-- These are genuine finite probability laws. Every bank is an exhaustive
list of distinct profiles; both observation marginals are the original design.
The second observation is specifically the first row of the random bank. -/
def W1MatchingSampling (n : ℕ) : Prop :=
  (∀ e : Equiv.Perm (Fin (w1MatchingR n)),
    Function.Injective (fun r => w1MatchingAssignments n (e r))) ∧
  (∀ (e : Equiv.Perm (Fin (w1MatchingR n))) s, ∃ r, e r = s) ∧
  (∀ s : Fin (w1MatchingR n), 0 < w1Uniform s) ∧
  (∑ s : Fin (w1MatchingR n), w1Uniform s) = 1 ∧
  (∀ e : Equiv.Perm (Fin (w1MatchingR n)), 0 < w1Uniform e) ∧
  (∑ e : Equiv.Perm (Fin (w1MatchingR n)), w1Uniform e) = 1 ∧
  (∀ x, 0 < w1MatchingIndependentMass n x) ∧
  (∑ x, w1MatchingIndependentMass n x) = 1 ∧
  (∀ s, (∑ e, w1MatchingIndependentMass n (e, s)) = w1Uniform s) ∧
  (∀ s, (∑ e : Equiv.Perm (Fin (w1MatchingR n)),
    if e (w1MatchingFirst n) = s then w1Uniform e else 0) = w1Uniform s)
/-- Moments under the product law of a uniform exhaustive bank order and an
independent uniform observation, and under observation equal to its first row. -/
def W1MatchingMoments (n : ℕ) : Prop :=
  let R := w1MatchingR n
  let N : ℚ := w1MatchingN n
  let w := w1MatchingWeight n
  let q := w1MatchingJoint n
  let t := fun x : Equiv.Perm (Fin R) × Fin R => w1MatchingT n x.1 x.2
  let v := fun x : Equiv.Perm (Fin R) × Fin R => w1MatchingV n x.1 x.2
  let t₁ := fun e : Equiv.Perm (Fin R) => w1MatchingT n e (e (w1MatchingFirst n))
  let v₁ := fun e : Equiv.Perm (Fin R) => w1MatchingV n e (e (w1MatchingFirst n))
  expect (w1MatchingIndependentMass n) t = 0 ∧
  designVariance (w1MatchingIndependentMass n) t = 4 / (N ^ 2 * w ^ 2) ∧
  expect (w1MatchingIndependentMass n) v = (4 / w ^ 2 + 2 / w - 2 / q) / N ^ 2 ∧
  expect w1Uniform t₁ = 0 ∧
  designVariance w1Uniform t₁ = 4 / (N ^ 2 * w ^ 2) ∧
  expect w1Uniform v₁ = (4 / w ^ 2 + 2 / w - 2 / q) / N ^ 2 ∧
  expect (w1MatchingIndependentMass n) v -
      designVariance (w1MatchingIndependentMass n) t =
    -2 * (2 * n + 5) / (((n : ℚ) + 2) * (n + 3) * N ^ 2) ∧
  expect w1Uniform v₁ - designVariance w1Uniform t₁ =
    -2 * (2 * n + 5) / (((n : ℚ) + 2) * (n + 3) * N ^ 2) ∧
  expect (w1MatchingIndependentMass n) v < designVariance (w1MatchingIndependentMass n) t ∧
  expect w1Uniform v₁ < designVariance w1Uniform t₁
/-- Error transfer under a finite joint law. The observation marginal is the
specified design; bank and observation may be dependent. The input guards are
exactly the positivity and nonnegativity presupposed by S7. -/
def W1ErrorTransfer : Prop :=
  ∀ {Ω B D : Type} {N : ℕ} [Fintype Ω] [Fintype B] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (J : FiniteDesign (B × Ω))
    (hm : ∀ ω, ∑ t, J.mass (t, ω) = P.mass ω)
    (f : Ω → Fin N → D) (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b)
    (w : B → Fin N → D → ℝ) (q : B → Fin N → Fin N → D → D → ℝ)
    (hw : ∀ t i d, 0 < w t i d) (hq : ∀ t i j d e, 0 ≤ q t i j d e)
    (hd : ∀ t i d, q t i i d d = w t i d),
    let V₀ := varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b
    let T₀ := htContrast f y (marginal P.mass f) a b
    let Vw := fun x : B × Ω => varianceEstimate f y (w x.1) (q x.1) a b x.2
    let Tw := fun x : B × Ω => htContrast f y (w x.1) a b x.2
    let S := zeroSurplus y (joint P.mass f) a b
    (expect J.mass Vw - designVariance J.mass Tw = S +
      expect J.mass (fun x => Vw x - V₀ x.2) -
      (designVariance J.mass Tw - designVariance P.mass T₀)) ∧
    (∀ εV εT : ℝ, 0 ≤ εV → 0 ≤ εT →
      |expect J.mass (fun x => Vw x - V₀ x.2)| ≤ εV →
      |designVariance J.mass Tw - designVariance P.mass T₀| ≤ εT →
      designVariance J.mass Tw ≤ expect J.mass Vw + εV + εT)
/-- P044-T2; p. 217 (PDF p. 9), with p. 213 (PDF p. 5).
Exact supported design inputs give precisely the structural-zero surplus and
conservative HT variance. Finite simulated inputs can fail under independent
and included observations, including 10000 distinct draws and first-draw reuse:
the exhaustive matching family supplies both joint laws. An exact transfer
identity gives a corrected inequality under bounds on the expected
variance-estimate error and the contrast-variance error. The usual
measure-theoretic conditions are assumed (all laws here are finite).
The Hajek sentence is a scope qualification: its linearized approximation and
reported numerical robustness supply no general finite-sample guarantee. -/
def T2WholeStatement : Prop :=
  T2Statement.{0,0} ∧
  (∀ n : ℕ, W1MatchingGeometry n ∧ W1MatchingMarginals n ∧
    W1MatchingInputs n ∧ W1MatchingSampling n ∧ W1MatchingMoments n) ∧
  w1MatchingR 4998 = 10000 ∧ w1MatchingN 4998 = 10002 ∧
  W1ErrorTransfer
/-- P044-T3; p. 212 (PDF p. 4), related p. 216 and Note 1, p. 221.
The nonisolated four-unit star under uniform complete assignment of two
treatments has the six stated exposure vectors and exact exposure probabilities.
The two schedules give identical observed data and effects zero and minus one,
so no statistic is unbiased under both. Every observed inverse-probability
term has a positive denominator; the means, contrast, and biases hold without
an extra positivity assumption. Usual measure-theoretic conditions are assumed. -/
def T3WholeStatement : Prop :=
  T3Statement ∧
  (fun r => exposure starAdj (starAssignments r)) =
    ![![.d01,.d00,.d10,.d10], ![.d01,.d10,.d00,.d10],
      ![.d01,.d10,.d10,.d00], ![.d11,.d01,.d01,.d11],
      ![.d11,.d01,.d11,.d01], ![.d11,.d11,.d01,.d01]] ∧
  (let f := fun r => exposure starAdj (starAssignments r)
    let p := marginal (fun _ : Fin 6 => (1/6 : ℚ)) f
    (∀ r i a, f r i = a → 0 < p i a) ∧
    (∀ flag : Bool, let y := if flag then starA else starB
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htMean f y p .d11) = 1 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htMean f y p .d00) = 3/4 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htContrast f y p .d11 .d00) = 1/4 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htContrast f y p .d11 .d00) - tau y .d11 .d00 =
        if flag then 1/4 else 5/4)) ∧
  (fun i => degree starAdj i) = ![3,1,1,1] ∧
  (∀ a, ∃ i, 0 < marginal (fun _ : Fin 6 => (1/6 : ℚ))
    (fun r => exposure starAdj (starAssignments r)) i a)
/-- P044-T7; p. 216, with pp. 212, 214 (PDF pp. 8, 4, 6).
The exhaustive eight-cycle bank has the stated base exposure vector, counts,
positive exact probabilities, smoothed weights, means, constant contrasts and
biases. Its four joint counts give returned entries 1/9 and 1/8 with row sum
17/72, inconsistent with the returned marginal 1/3; the exact joint row sums
to 1/4. Usual measure-theoretic conditions are assumed (finite laws). -/
def T7WholeStatement : Prop :=
  T7Statement ∧
  exposure cycle8Adj (cycle8Assignments 0) =
    ![.d11,.d11,.d01,.d10,.d01,.d00,.d00,.d01] ∧
  (let f := fun r => exposure cycle8Adj (cycle8Assignments r);
    (∀ b, jointCount f 0 1 .d11 b =
      (match b with | .d11 => 1 | .d10 => 0 | .d01 => 1 | .d00 => 0)) ∧
    (∀ b, (smoothedJoint f 0 1 .d11 b : ℚ) =
      (match b with | .d11 => 1/9 | .d10 => 0 | .d01 => 1/8 | .d00 => 0)) ∧
    (∀ b, joint (fun _ : Fin 8 => (1/8 : ℚ)) f 0 1 .d11 b =
      (match b with | .d11 => 1/8 | .d10 => 0 | .d01 => 1/8 | .d00 => 0)) ∧
    (∑ b, joint (fun _ : Fin 8 => (1/8 : ℚ)) f 0 1 .d11 b) = 1/4 ∧
    (1/8 + 1/8 : ℚ) = 1/4) ∧
  (∀ a, (∑ i : Fin 8, cycle8Y i a) / 8 = cycle8Y 0 a)
/-- Ordered deletion and insertion. The order isomorphism puts the other
coordinates in their original order, including the empty vector when `n=0`. -/
def w1DeleteOwn {n : ℕ} (i : Fin (n + 1)) (z : Assignment (n + 1)) : Fin n → Bool :=
  fun j => z (finSuccAboveOrderIso i j).val
def w1InsertOwn {n : ℕ} (i : Fin (n + 1)) (a : Bool) (u : Fin n → Bool) :
    Assignment (n + 1) :=
  insertOwn i a (fun j => u ((finSuccAboveOrderIso i).symm j))
def w1OrderedNoInterference {n : ℕ} (y : Fin (n + 1) → Assignment (n + 1) → ℝ) : Prop :=
  ∀ i a u v, y i (w1InsertOwn i a u) = y i (w1InsertOwn i a v)
def w1OrderedInterference {n : ℕ} (y : Fin (n + 1) → Assignment (n + 1) → ℝ) : Prop :=
  ∃ i a u v, y i (w1InsertOwn i a u) ≠ y i (w1InsertOwn i a v)
/-- Dimension composability of an `r×c` and an `s×t` matrix, without assigning
a junk value to the syntactically ill-typed row-times-row product. -/
def w1MatrixComposable (_r c s _t : ℕ) : Prop := c = s
def w1Bit (b : Bool) : ℕ := if b then 1 else 0
def w1AdjRow {N : ℕ} (A : Adjacency N) (i : Fin N) : Matrix (Fin 1) (Fin N) ℕ :=
  fun _ j => w1Bit (A i j)
def w1TreatmentColumn {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin 1) ℕ :=
  fun j _ => w1Bit (z j)
/-- The four printed product predicates, with natural subtraction only on the
Boolean value zero or one, so subtraction does not truncate a negative value. -/
def w1ExposurePredicate {N : ℕ} (A : Adjacency N) (z : Assignment N)
    (i : Fin N) (d : Exposure) : Prop :=
  match d with
  | .d11 => w1Bit (z i) * (if 0 < peerCount A z i then 1 else 0) = 1
  | .d10 => w1Bit (z i) * (if peerCount A z i = 0 then 1 else 0) = 1
  | .d01 => (1 - w1Bit (z i)) * (if 0 < peerCount A z i then 1 else 0) = 1
  | .d00 => (1 - w1Bit (z i)) * (if peerCount A z i = 0 then 1 else 0) = 1
/-- P044-T9; pp. 210-211 (PDF pp. 2-3), corrected interference notation.
Ordered deletion and insertion reconstruct every treatment profile.
The corrected interference definition is the negation of no interference.
No interference is equivalent to invariance at fixed own treatment.
Row times column equals the treated-peer count, independent of own treatment
on a zero-diagonal network.
The printed pair of rows has incompatible dimensions when N exceeds one.
Exactly one printed product condition holds, selecting the label whose bits
are own treatment and the presence of a treated peer. No symmetry or absence
of isolates is required. Usual measure-theoretic conditions are assumed. -/
def T9WholeStatement : Prop :=
  T9Statement ∧
  (∀ {n : ℕ} (i : Fin (n + 1)) (z : Assignment (n + 1)),
    w1InsertOwn i (z i) (w1DeleteOwn i z) = z) ∧
  (∀ {n : ℕ} (y : Fin (n + 1) → Assignment (n + 1) → ℝ),
    (w1OrderedNoInterference y ↔ NoInterference y) ∧
    (w1OrderedInterference y ↔ Interference y) ∧
    (w1OrderedInterference y ↔ ¬ w1OrderedNoInterference y) ∧
    (w1OrderedNoInterference y ↔ ∀ i z z', z i = z' i → y i z = y i z')) ∧
  (∀ N : ℕ, w1MatrixComposable 1 N N 1 ∧
    (w1MatrixComposable 1 N 1 N ↔ N = 1) ∧
    (1 < N → ¬ w1MatrixComposable 1 N 1 N)) ∧
  (∀ {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N),
    ((w1AdjRow A i) * (w1TreatmentColumn z)) 0 0 =
      (∑ j, w1Bit (A i j) * w1Bit (z j)) ∧
    (∑ j, w1Bit (A i j) * w1Bit (z j)) = peerCount A z i) ∧
  (∀ {N : ℕ} (A : Adjacency N) (z : Assignment N) (i : Fin N),
    (∀ d, w1ExposurePredicate A z i d ↔ exposure A z i = d) ∧
    (∃! d, w1ExposurePredicate A z i d) ∧
    exposure A z i =
      if z i then (if 0 < peerCount A z i then .d11 else .d10)
      else (if 0 < peerCount A z i then .d01 else .d00))
end
end SAP.P044
