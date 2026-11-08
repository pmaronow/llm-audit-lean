import SAP.P002b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

structure QuadraticAR where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ

def arFunction (Q : QuadraticAR) (β : ℝ) : ℝ :=
  (Q.a*β^2+Q.b*β+Q.c)/(Q.d*β^2+Q.e*β+Q.f)

/-- Everywhere-positive variance denominators and nonnegative squared-statistic numerators. -/
def ARRegular (Q : QuadraticAR) : Prop :=
  (∀ β, 0 < Q.d*β^2+Q.e*β+Q.f) ∧ (∀ β, 0 ≤ Q.a*β^2+Q.b*β+Q.c)

/-- The empirical critical value for squared AR curves. M > 0, an interior
significance level, and nonnegative curves exclude the empty-candidate fallback. -/
def mcCritical {M} (g : Fin M → ℝ → ℝ) (α β : ℝ) : ℝ :=
  let C := (Finset.univ.image (fun m => Real.sqrt (g m β))).filter fun q =>
    (1-α)*(M : ℝ) ≤ ((Finset.univ.filter (fun m => Real.sqrt (g m β) ≤ q)).card : ℝ)
  if h : C.Nonempty then C.min' h else 0

def mcIndices {M} (g : Fin M → ℝ → ℝ) (α β : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun m => Real.sqrt (g m β) = mcCritical g α β

def mcSet {M} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ) : Set ℝ :=
  {β | Real.sqrt (f β) ≤ mcCritical g α β}

def closedInterval (l u : EReal) : Set ℝ := {β | l ≤ (β : EReal) ∧ (β : EReal) ≤ u}

def openInterval (l u : EReal) : Set ℝ := {β | l < (β : EReal) ∧ (β : EReal) < u}

def crossing {M} (g : Fin M → ℝ → ℝ) (β : ℝ) : Prop :=
  ∃ s t, g s ≠ g t ∧ g s β = g t β

structure RecordedPiece (M : ℕ) where
  left : EReal
  right : EReal
  index : Fin M

def pieceSet {M} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (p : RecordedPiece M) : Set ℝ :=
  {β | β ∈ closedInterval p.left p.right ∧ f β ≤ g p.index β}

def returnedSet {M} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (pieces : List (RecordedPiece M)) : Set ℝ :=
  {β | ∃ p ∈ pieces, β ∈ pieceSet f g p}

def IntersectionList {M} (g : Fin M → ℝ → ℝ) (J : List ℝ) : Prop :=
  J.Pairwise (· < ·) ∧ ∀ β, β ∈ J ↔ crossing g β

def gapSample (l u : EReal) : ℝ :=
  if l=⊥ then (if u=⊤ then 0 else u.toReal-1)
  else if u=⊤ then l.toReal+1 else (l.toReal+u.toReal)/2

def gapEndpoints (J : List ℝ) : List (EReal × EReal) :=
  (⊥ :: J.map (fun x => (x : EReal))).zip (J.map (fun x => (x : EReal)) ++ [⊤])

/-- Algorithm 1/3 samples each gap in the complete sorted intersection list.
Its predicate imposes quantile-index validity only at the prescribed sample point. -/
def Algorithm1Run {M} (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ)
    (pieces : List (RecordedPiece M)) : Prop :=
  IntersectionList g J ∧ pieces.map (fun p => (p.left,p.right)) = gapEndpoints J ∧
  ∀ p ∈ pieces, p.index ∈ mcIndices g α (gapSample p.left p.right)

def Algorithm2Step {M} (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ)
    (p : RecordedPiece M) (next : Option (RecordedPiece M)) : Prop :=
  let C : Set ℝ := {β | p.left < (β : EReal) ∧ ∃ m, g m ≠ g p.index ∧ g m β=g p.index β}
  (if C.Nonempty then ∃ e : ℝ, IsLeast C e ∧ p.right=(e : EReal)
    else p.right=⊤) ∧
  (match next with
   | none => p.right=⊤
   | some q => p.right ≠ ⊤ ∧ q.left=p.right ∧
       let E : List ℝ := J.filter fun β => p.right < (β : EReal)
       q.index ∈ mcIndices g α
         (if E=[] then (p.right.toReal : ℝ)+1
           else ((p.right.toReal : ℝ)+(E.head! : ℝ))/(2 : ℝ)))

/-- A completed finite execution of corrected Algorithm 2/4: the first
left endpoint is negative infinity and the final step ends at positive infinity.
This predicate does not express termination for an arbitrary prescribed policy. -/
def Algorithm2Run {M} (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ)
    (pieces : List (RecordedPiece M)) : Prop :=
  IntersectionList g J ∧ J ≠ [] ∧ pieces ≠ [] ∧
  (∀ p, pieces.head?=some p → p.left=⊥ ∧
    p.index ∈ mcIndices g α (J.head!-1)) ∧
  (∀ i : Fin pieces.length,
    Algorithm2Step g α J (pieces.get i) (pieces[i.val+1]?))

def rawVarianceCross {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (fraction P)^2*(1-fraction P)^2 *
    ((∑ i ∈ S, (Y i-armMean Y S true)*(D i-armMean D S true))/(P.n1 : ℝ)^2 +
     (∑ i ∈ Sᶜ, (Y i-armMean Y S false)*(D i-armMean D S false))/(controlSize P)^2)

def rawCoefficients {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : QuadraticAR where
  a := (rawTau P D S)^2
  b := -2*rawTau P Y S*rawTau P D S
  c := (rawTau P Y S)^2
  d := rawSigma2 P D S
  e := -2*rawVarianceCross P Y D S
  f := rawSigma2 P Y S

def adjustedVarianceCross {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, (Y i-dotProduct (augmented P.x i) (fitted P Y S true))*
      (D i-dotProduct (augmented P.x i) (fitted P D S true)))/(P.pop.n1 : ℝ)^2 +
  (∑ i ∈ Sᶜ, (Y i-dotProduct (augmented P.x i) (fitted P Y S false))*
      (D i-dotProduct (augmented P.x i) (fitted P D S false)))/(controlSize P.pop)^2

def adjustedCoefficients {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : QuadraticAR where
  a := (adjustedTau P D S)^2
  b := -2*adjustedTau P Y S*adjustedTau P D S
  c := (adjustedTau P Y S)^2
  d := adjustedSigma2 P D S
  e := -2*adjustedVarianceCross P Y D S
  f := adjustedSigma2 P Y S

def dataCoefficients {n k} (P : CovPopulation n k) (adjusted : Bool)
    (O T : Finset (Fin n)) : QuadraticAR :=
  let Y := observedY P.pop O
  let D := fun i => binary (observedD P.pop O i)
  if adjusted then adjustedCoefficients P Y D T else rawCoefficients P.pop Y D T

/-- One common observed dataset generates all observed and simulated curves.
The adjusted branch requires centered covariates and full-rank observed and simulated
arm designs, the domain of the paper's ordinary inverse formulas. -/
def DataGeneratedCoefficients {M} (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) : Prop :=
  ∃ (n k : ℕ) (P : CovPopulation n k) (adjusted : Bool)
    (O : Finset (Fin n)) (T : Fin M → Finset (Fin n)),
    ValidDesign P.pop ∧ MonotoneReceipt P.pop ∧ (compliers P.pop).Nonempty ∧
    O ∈ assignments P.pop ∧ (∀ m, T m ∈ assignments P.pop) ∧
    (adjusted=true → 0 < k ∧ (∀ s, ∑ i, P.x i s=0) ∧
      ∀ R, (R=O ∨ ∃ m, R=T m) → (gram P.x R).det ≠ 0 ∧ (gram P.x Rᶜ).det ≠ 0) ∧
    Qf=dataCoefficients P adjusted O O ∧ ∀ m, Qg m=dataCoefficients P adjusted O (T m)

end
end SAP.P002b
