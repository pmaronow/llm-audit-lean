import Mathlib
import SAP.P002b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The arm-specific potential-response expression in the oracle expansion. -/
def oraclePotentialContrast {n k : ℕ} (P : CovPopulation n k) (β : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  groupMean S (fun i => w P.pop true β i - slopeDot (P.x i) (psi P true β)) -
    groupMean Sᶜ (fun i => w P.pop false β i - slopeDot (P.x i) (psi P false β))

/-- The same expression with the two population intercepts subtracted. -/
def oracleCenteredContrast {n k : ℕ} (P : CovPopulation n k) (β : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  groupMean S (fun i => w P.pop true β i - psi P true β none -
    slopeDot (P.x i) (psi P true β)) -
  groupMean Sᶜ (fun i => w P.pop false β i - psi P false β none -
    slopeDot (P.x i) (psi P false β))

/-- P002-T20; Supplement p. 37 (Supplement PDF p. 17).
The corrected control remainder tends to zero in design probability along every
admissible fixed-dimension model sequence. At the LATE, the oracle contrast equals
the arm-specific potential-response contrast, its intercept-centered version, and
the difference of arm residual means. Population intercepts are population means,
and the mean response contrast is the complier fraction times LATE minus beta.
The remainder uses the existing totalized inverse and zero-division convention;
on the domain of the displayed ordinary inverse and normalization it is (E.29). -/
def T20WholeStatement : Prop :=
  (∀ {n k : ℕ} (P : CovPopulation n k), ValidDesign P.pop →
    MonotoneReceipt P.pop → (compliers P.pop).Nonempty →
    (∀ s, ∑ i, P.x i s = 0) → (gram P.x Finset.univ).det ≠ 0 →
    (∀ (a : Bool) (β : ℝ), psi P a β none = mean (w P.pop a β)) ∧
    (∀ β : ℝ, mean (w P.pop true β) - mean (w P.pop false β) =
      ((compliers P.pop).card : ℝ) / (n : ℝ) * (late P.pop - β)) ∧
    mean (w P.pop true (late P.pop)) - mean (w P.pop false (late P.pop)) = 0 ∧
    psi P true (late P.pop) none - psi P false (late P.pop) none = 0 ∧
    (∀ S : Finset (Fin n), S ∈ assignments P.pop →
      oracleTau P (late P.pop) S = oraclePotentialContrast P (late P.pop) S ∧
      oraclePotentialContrast P (late P.pop) S =
        oracleCenteredContrast P (late P.pop) S ∧
      oracleCenteredContrast P (late P.pop) S =
        groupMean S (residual P true (late P.pop)) -
          groupMean Sᶜ (residual P false (late P.pop)))) ∧
  (∀ (sizes : ℕ → ℕ), StrictMono sizes → ∀ (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (∀ j, Xi (P j) δ e A B r) →
    ∀ κ : ℝ, 0 < κ → Tendsto (fun j => probability (P j).pop
      (fun S => κ ≤ |controlRemainder (P j) S|)) atTop (nhds 0))

/-- A four-cell population, repeated j+1 times: x and the response are independent
balanced signs, all units comply, and both potential outcomes equal the response.
The order of the four cells is (-1,-1), (-1,1), (1,-1), (1,1). -/
def tailBlockPopulation (j : ℕ) : CovPopulation (4 * (j + 1)) 1 where
  pop := {
    y := fun i _ => if i.val % 2 = 0 then -1 else 1
    d := fun _ a => a
    n1 := 2 * (j + 1) }
  x := fun i _ => if i.val % 4 < 2 then -1 else 1

/-- The next prescribed sample after a finite selected-curve crossing. The
crossing list is sorted; the first remaining element is its least element. -/
def nextAlgorithm2Sample (J : List ℝ) (e : EReal) : ℝ :=
  let E : List ℝ := J.filter fun β => e < (β : EReal)
  if E = [] then (e.toReal : ℝ) + 1 else ((e.toReal : ℝ) + (E.head! : ℝ)) / (2 : ℝ)

/-- A choice policy may depend on the complete list of previously recorded
interval-index pairs and the sample currently queried by the algorithm. -/
def AdmissibleIndexPolicy {M : ℕ} (g : Fin M → ℝ → ℝ) (α : ℝ)
    (choose : List (RecordedPiece M) → ℝ → Fin M) : Prop :=
  ∀ history β, choose history β ∈ mcIndices g α β

/-- A completed run follows the specified policy at every query. Its initial
query is min(J)-1; subsequent queries use the current left endpoint. -/
def PolicyAlgorithm2Run {M : ℕ} (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ)
    (choose : List (RecordedPiece M) → ℝ → Fin M)
    (pieces : List (RecordedPiece M)) : Prop :=
  Algorithm2Run g α J pieces ∧
  ∀ i : Fin pieces.length, (pieces.get i).index = choose (pieces.take i.val)
    (if i.val = 0 then J.head! - 1 else nextAlgorithm2Sample J (pieces.get i).left)

/-- The complete interval and returned-set contract of a finished corrected run. -/
def Algorithm2WholeContract {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ)
    (α : ℝ) (J : List ℝ) (pieces : List (RecordedPiece M)) : Prop :=
  pieces.length ≤ J.length + 1 ∧
  (pieces.map (fun p => p.right)).Pairwise (· < ·) ∧
  (∀ p ∈ pieces, p.right = ⊤ ∨ ∃ e : ℝ, p.right = (e : EReal) ∧ e ∈ J) ∧
  (∀ β : ℝ, ∃ p ∈ pieces, β ∈ closedInterval p.left p.right) ∧
  (∀ p ∈ pieces, ∀ β ∈ closedInterval p.left p.right, p.index ∈ mcIndices g α β) ∧
  (∀ p ∈ pieces, pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right) ∧
  returnedSet f g pieces = mcSet f g α

/-- P002-T22; Main p. 16 (PDF p. 16), Algorithm 2; Supplement pp. 44-45
(Supplement PDF pp. 24-25), Algorithm 4 and Section H.2.
Every admissible history-dependent choice policy terminates in at most |J|+1
iterations when J is nonempty. Every completed corrected run has ordered crossing
endpoints, covers the real line, selects a quantile curve throughout each closed
interval, and returns exactly the empirical confidence set. This holds for every
regular nonnegative quadratic-ratio family, hence for both paper data settings
where the displayed ordinary regression inverses exist. -/
def T22WholeStatement : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ J : List ℝ, IntersectionList (fun m => arFunction (Qg m)) J → J ≠ [] →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∀ choose, AdmissibleIndexPolicy g α choose →
      ∃ pieces, PolicyAlgorithm2Run g α J choose pieces ∧
        Algorithm2WholeContract f g α J pieces) ∧
    (∀ pieces, Algorithm2Run g α J pieces → Algorithm2WholeContract f g α J pieces)

/-- A finite union of real intervals. Order-connected subsets include every
endpoint convention, singletons, unbounded intervals, and the empty set. -/
def FiniteIntervalUnion (s : Set ℝ) : Prop :=
  ∃ (m : ℕ) (I : Fin m → Set ℝ), (∀ i, Set.OrdConnected (I i)) ∧
    ∀ x, x ∈ s ↔ ∃ i, x ∈ I i

/-- Two points lie in the same complementary open cell of a finite cut set. -/
def SameOpenCell (cuts : Finset ℝ) (x y : ℝ) : Prop :=
  x ∉ cuts ∧ y ∉ cuts ∧ ∀ c ∈ cuts, (x < c ↔ y < c)

/-- The full-randomization confidence set for fixed real response and receipt
vectors. This also permits algebraic statements before specializing to observations. -/
def fixedAdjustedConfidenceSet {n k : ℕ} (P : CovPopulation n k)
    (Y D : Fin n → ℝ) (S : Finset (Fin n)) (α : ℝ) : Set ℝ :=
  {β | adjustedAR P (fun i => Y i - β * D i) S ≤
    quantile P.pop (adjustedAR P (fun i => Y i - β * D i)) α}

/-- The coefficient on Z in the interacted regression, obtained by the invertible
change from arm intercepts (phi_0,phi_1) to (alpha_0,alpha_1)=(phi_0,phi_1-phi_0).
The two arm slope vectors are unchanged by this change of coordinates. -/
def interactedTreatmentCoefficient {n k : ℕ} (P : CovPopulation n k)
    (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  fitted P q S true none - fitted P q S false none

/-- Exact rational witness for the noninterval possibility in Remark 4.
Unit 1 is a complier, the other observed recipients are always-takers, and all
potential outcomes are constant in receipt. All eight covariates are distinct. -/
def intervalWitnessPopulation : CovPopulation 8 1 where
  pop := {
    y := fun i _ => (![(-4 : ℝ), 0, 2, -2, 2, -6, -4, 6]) i
    d := fun i a => if i = 1 then a else decide (i = 5 ∨ i = 6 ∨ i = 7)
    n1 := 4 }
  x := fun i _ => 2 * (i.val : ℝ) - 7

def intervalWitnessAssignment : Finset (Fin 8) := {0, 1, 2, 3}

def intervalWitnessSet : Set ℝ :=
  fixedAdjustedConfidenceSet intervalWitnessPopulation
    (observedY intervalWitnessPopulation.pop intervalWitnessAssignment)
    (fun i => binary (observedD intervalWitnessPopulation.pop intervalWitnessAssignment i))
    intervalWitnessAssignment (1/2)

/-- P002-T26; Main p. 10 (PDF p. 10), Remark 4 and (12); Supplement
Section I, pp. 45-47 (Supplement PDF pp. 25-27).
The adjusted full-randomization confidence set is a finite union of intervals
where its ordinary regression inverses exist; it can be nonempty without being
a single interval. The adjusted contrast is affine, and its outcome and receipt
contrasts are the treatment coefficients of the corresponding interacted fits.
The well-defined adjusted Wald ratio has zero contrast and statistic and belongs
to the confidence set at every interior level. Under the stated IV invertibility
conditions, the IV product identity holds, and a nonzero receipt contrast gives
equality of the IV coefficient and the Wald ratio. No positive-variance condition
is imposed: zero-over-zero is zero and absolute nonzero-over-zero is infinity. -/
def T26WholeStatement : Prop :=
  (∀ {n k : ℕ} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)), ValidDesign P.pop → S ∈ assignments P.pop →
    (∀ s, ∑ i, P.x i s = 0) →
    (gram P.x S).det ≠ 0 → (gram P.x Sᶜ).det ≠ 0 →
    (∀ β, adjustedTau P (fun i => Y i - β * D i) S =
      adjustedTau P Y S - β * adjustedTau P D S) ∧
    interactedTreatmentCoefficient P Y S = adjustedTau P Y S ∧
    interactedTreatmentCoefficient P D S = adjustedTau P D S ∧
    (∀ α : ℝ, (0 < α ∧ α < 1) →
      (∀ R ∈ assignments P.pop, (gram P.x R).det ≠ 0 ∧ (gram P.x Rᶜ).det ≠ 0) →
      FiniteIntervalUnion (fixedAdjustedConfidenceSet P Y D S α)) ∧
    (adjustedTau P D S ≠ 0 → ∀ α : ℝ, (0 < α ∧ α < 1) →
      adjustedTau P (fun i => Y i - adjustedWald P Y D S * D i) S = 0 ∧
      adjustedAR P (fun i => Y i - adjustedWald P Y D S * D i) S = 0 ∧
      adjustedWald P Y D S ∈ fixedAdjustedConfidenceSet P Y D S α) ∧
    ((ivCross P D S).det ≠ 0 → (instrumentGram P S).det ≠ 0 →
      adjustedTau P D S * ivCoefficients P Y D S (.inl 0) = adjustedTau P Y S ∧
      (adjustedTau P D S ≠ 0 → ivCoefficients P Y D S (.inl 0) = adjustedWald P Y D S))) ∧
  ((-12 : ℝ) ∈ intervalWitnessSet ∧ (10 : ℝ) ∈ intervalWitnessSet ∧
    (-7 : ℝ) ∉ intervalWitnessSet)

/-- Corrected counterpart of P002-T28; Main p. 17 (PDF p. 17), Theorem 3; Algorithms 1-2,
main pp. 15-16; Algorithms 3-4, Supplement p. 44; Section H.2, p. 45.
Complete crossing lists have at most 4*M^2 elements. Every Algorithm 1/3 run
uses |J|+1 gaps and returns the empirical confidence set, as does every corrected
Algorithm 2/4 run. Every admissible adaptive
Algorithm 2/4 choice policy terminates within |J|+1 iterations. If no curves cross,
any quantile selection at any real sample returns the same confidence set.
The theorem holds for all regular nonnegative quadratic-ratio families, including
the two paper settings on the domain of their ordinary regression inverses. -/
def T28CorrectedStatement : Prop :=
  T22WholeStatement ∧
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∃ J, IntersectionList g J ∧ J.length ≤ 4*M^2) ∧
    (∀ J, IntersectionList g J → ∃ pieces, Algorithm1Run g α J pieces) ∧
    (∀ J pieces, Algorithm1Run g α J pieces →
      pieces.length = J.length+1 ∧ returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J ≠ [] → ∃ pieces, Algorithm2Run g α J pieces) ∧
    (∀ J pieces, Algorithm2Run g α J pieces → returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J = [] →
      (∀ β, (mcIndices g α β).Nonempty) ∧
      ∀ β m, m ∈ mcIndices g α β → {x | f x ≤ g m x} = mcSet f g α)

/-- Four all-complier units with both potential outcomes (0,1,2,4), two treated
units, and no covariates. This is an unadjusted instance of the printed theorem. -/
def printedIndexPopulation : CovPopulation 4 0 where
  pop := {
    y := fun i _ => if i=0 then 0 else if i=1 then 1 else if i=2 then 2 else 4
    d := fun _ a => a
    n1 := 2 }
  x := fun _ j => Fin.elim0 j

def printedIndexObserved : Finset (Fin 4) := {0,1}

def printedIndexSimulated (m : Fin 2) : Finset (Fin 4) :=
  if m=0 then printedIndexObserved else {0,2}

def printedIndexQ0 : QuadraticAR := ⟨1/16, 5/16, 25/64, 0, 0, 5/128⟩

def printedIndexQ1 : QuadraticAR := ⟨0, 0, 9/64, 1/64, 5/64, 13/128⟩

def printedIndexFamily (m : Fin 2) : QuadraticAR :=
  if m=0 then printedIndexQ0 else printedIndexQ1

/-- The records made by printed Step 4. Their indices are 1,0,1 on the
successive intervals ending at -4,-1,+infinity. -/
def printedIndexPieces : List (RecordedPiece 2) :=
  [⟨⊥, (-4 : ℝ), 1⟩, ⟨(-4 : ℝ), (-1 : ℝ), 0⟩, ⟨(-1 : ℝ), ⊤, 1⟩]

/-- The defined terms of printed Step 5: for adjacent Step-4 records p_k,p_(k+1),
apply p_k's index to p_(k+1)'s interval [e_k,e_(k+1)]. This includes every printed
term whose endpoints were defined by Step 4. It does not assign a junk value to
the undefined endpoint e_(n_I+1) in the last printed term. Any completion of that
last term by a set and any union containing the defined terms retain these points. -/
def printedStep5DefinedSet {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ)
    (pieces : List (RecordedPiece M)) : Set ℝ :=
  {β | ∃ p q, (p,q) ∈ pieces.zip pieces.tail ∧
    β ∈ closedInterval q.left q.right ∧ f β ≤ g p.index β}

/-- The printed claim is false: the shifted interval-index comparisons in
Algorithm 2, Step 5 can accept a point rejected by the empirical confidence set.
P002-T28; Main p. 17 (PDF p. 17), Theorem 3; Algorithm 2, main p. 16.
Four all-complier units with equal potential outcomes (0,1,2,4), observed treated
set {0,1}, simulations {0,1},{0,2}, and alpha=1/2 satisfy Assumption 6. The complete
crossing list is [-4,-1], and Step 4 records indices 1,0,1. At beta=0 the empirical
set rejects, while the defined shifted middle comparison accepts. Every returned
union containing the defined printed terms therefore differs from the empirical
set, regardless of how the last undefined endpoint is completed. The corrected
pair-preserving theorem is stated separately as T28CorrectedStatement. -/
def T28WholeStatement : Prop :=
  let P := printedIndexPopulation
  let O := printedIndexObserved
  let f := arFunction printedIndexQ0
  let g := fun m => arFunction (printedIndexFamily m)
  ValidDesign P.pop ∧ MonotoneReceipt P.pop ∧ (compliers P.pop).Nonempty ∧
  O ∈ assignments P.pop ∧ (∀ m, printedIndexSimulated m ∈ assignments P.pop) ∧
  printedIndexQ0 = dataCoefficients P false O O ∧
  (∀ m, printedIndexFamily m = dataCoefficients P false O (printedIndexSimulated m)) ∧
  DataGeneratedCoefficients printedIndexQ0 printedIndexFamily ∧
  ARRegular printedIndexQ0 ∧ (∀ m, ARRegular (printedIndexFamily m)) ∧
  IntersectionList g [-4,-1] ∧ Algorithm2Run g (1/2) [-4,-1] printedIndexPieces ∧
  f 0 = 10 ∧ g 1 0 = 18/13 ∧
  (0 : ℝ) ∈ printedStep5DefinedSet f g printedIndexPieces ∧
  (0 : ℝ) ∉ mcSet f g (1/2) ∧
  (∀ returned : Set ℝ, printedStep5DefinedSet f g printedIndexPieces ⊆ returned →
    returned ≠ mcSet f g (1/2))

end
end SAP.P002b
