import SAP.P044.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

noncomputable section

def T2Statement : Prop :=
  (∀ {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b),
    (expect P.mass (varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b) -
      designVariance P.mass (htContrast f y (marginal P.mass f) a b) =
      zeroSurplus y (joint P.mass f) a b) ∧
    (designVariance P.mass (htContrast f y (marginal P.mass f) a b) ≤
      expect P.mass (varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b))) ∧
  (∀ included : Bool,
    expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) <
      designVariance (cliqueJointMass included) (fun x => cliqueT x.1 x.2))

def T3Statement : Prop :=
  ((∀ i, ∃ j, starAdj i j = true) ∧
    (∀ r, (Finset.univ.filter (fun i => starAssignments r i)).card = 2) ∧
    (∀ i a, marginal (fun _ : Fin 6 => (1/6 : ℚ))
      (fun r => exposure starAdj (starAssignments r)) i a =
      if i = 0 then (match a with | .d11 => 1/2 | .d10 => 0 | .d01 => 1/2 | .d00 => 0)
      else (match a with | .d11 => 1/6 | .d10 => 1/3 | .d01 => 1/3 | .d00 => 1/6)) ∧
    (∀ r i, starA i (exposure starAdj (starAssignments r) i) = 1 ∧
      starB i (exposure starAdj (starAssignments r) i) = 1) ∧
    tau starA .d11 .d00 = 0 ∧ tau starB .d11 .d00 = -1) ∧
  ((∀ i j, starAdj i j = starAdj j i) ∧
    (∀ i, starAdj i i = false) ∧
    Function.Injective starAssignments ∧
    (∀ z : Assignment 4, (Finset.univ.filter (fun i => z i)).card = 2 ↔
      ∃ r : Fin 6, starAssignments r = z)) ∧
  (∀ (T : Assignment 4 → (Fin 4 → Exposure) → (Fin 4 → ℝ) → ℝ),
    let f := fun r => exposure starAdj (starAssignments r)
    let TA := fun r => T (starAssignments r) (f r) (fun i => (starA i (f r i) : ℝ))
    let TB := fun r => T (starAssignments r) (f r) (fun i => (starB i (f r i) : ℝ))
    expect (fun _ : Fin 6 => (1/6 : ℝ)) TA = expect (fun _ : Fin 6 => (1/6 : ℝ)) TB ∧
    ¬(expect (fun _ : Fin 6 => (1/6 : ℝ)) TA = 0 ∧
      expect (fun _ : Fin 6 => (1/6 : ℝ)) TB = -1)) ∧
  (let f := fun r => exposure starAdj (starAssignments r);
    let p := marginal (fun _ : Fin 6 => (1/6 : ℚ)) f;
    ∀ (_hpos : ∀ r i a, f r i = a → 0 < p i a) (flag : Bool),
      let y := if flag then starA else starB;
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htMean f y p .d11) = 1 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htMean f y p .d00) = 3/4 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htContrast f y p .d11 .d00) = 1/4 ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ)) (htContrast f y p .d11 .d00) - tau y .d11 .d00 =
        if flag then 1/4 else 5/4)

def T4Statement : Prop :=
  (∀ {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (ha : ∀ i, 0 < marginal P.mass f i a) (hb : ∀ i, 0 < marginal P.mass f i b),
    (∀ i, expect P.mass (fun ω => htTerm f y (marginal P.mass f) a ω i) = y i a) ∧
    expect P.mass (htMean f y (marginal P.mass f) a) = (∑ i, y i a) / N ∧
    expect P.mass (htMean f y (marginal P.mass f) b) = (∑ i, y i b) / N ∧
    expect P.mass (htContrast f y (marginal P.mass f) a b) = tau y a b ∧
    (∀ i, expect P.mass (fun ω => htTerm f y (marginal P.mass f) b ω i) = y i b)) ∧
  (∀ {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (hN : 0 < N) (P : FiniteDesign Ω) (z : Ω → Assignment N)
    (f : Ω → Fin N → D) (y : Fin N → D → ℝ) (a b : D) (hab : a ≠ b)
    (j : Fin N) (hzero : marginal P.mass f j a = 0) (δ : ℝ) (hδ : δ ≠ 0)
    (T : Assignment N → (Fin N → D) → (Fin N → ℝ) → ℝ),
    let y' := fun i e => if i = j ∧ e = a then y i e + δ else y i e
    let TA := fun ω => T (z ω) (f ω) (fun i => y i (f ω i))
    let TB := fun ω => T (z ω) (f ω) (fun i => y' i (f ω i))
    (∀ ω, 0 < P.mass ω → ∀ i, y i (f ω i) = y' i (f ω i)) ∧
    expect P.mass TA = expect P.mass TB ∧
    tau y' a b - tau y a b = δ / N ∧
    ¬(expect P.mass TA = tau y a b ∧ expect P.mass TB = tau y' a b)) ∧
  (∀ {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D]
    (P : FiniteDesign Ω) (f : Ω → Fin N → D) (y : Fin N → D → ℝ)
    (a b : D) (hab : a ≠ b) (hS : (commonSupport P.mass f a b).Nonempty),
    expect P.mass (fun ω =>
      ((commonSupport P.mass f a b).sum (fun i : Fin N =>
        htTerm f y (marginal P.mass f) a ω i -
        htTerm f y (marginal P.mass f) b ω i)) /
        (commonSupport P.mass f a b).card) =
      ((commonSupport P.mass f a b).sum (fun i : Fin N => y i a - y i b)) /
        (commonSupport P.mass f a b).card) ∧
  (let f := fun r => exposure starAdj (starAssignments r)
    let p := marginal (fun _ : Fin 6 => (1/6 : ℚ)) f
    let S := Finset.univ.filter (fun i => 0 < p i .d11 ∧ 0 < p i .d00)
    S = {1,2,3} ∧
    (∀ flag : Bool, let y := if flag then starB else starA
      ((∑ i ∈ S, (y i .d11 - y i .d00)) / S.card = 0) ∧
      expect (fun _ : Fin 6 => (1/6 : ℚ))
        (fun r => (∑ i ∈ S, (htTerm f y p .d11 r i - htTerm f y p .d00 r i)) / S.card) = 0)) ∧
  (∀ (N M : ℕ) (hN : 0 < N)
    (hM : 1 ≤ M) (hMN : M ≤ N - 1) (A : Adjacency N)
    (hsym : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = false) (i : Fin N),
    let k := (Finset.univ.filter (fun j => A i j)).card
    completeProbability N M A i .d10 = ((N - 1 - k).choose (M - 1) : ℚ) / (N.choose M) ∧
    completeProbability N M A i .d00 = ((N - 1 - k).choose M : ℚ) / (N.choose M) ∧
    completeProbability N M A i .d11 = (M : ℚ) / N - completeProbability N M A i .d10 ∧
    completeProbability N M A i .d01 = ((N - M : ℕ) : ℚ) / N - completeProbability N M A i .d00 ∧
    ((∀ a, 0 < completeProbability N M A i a) ↔ 2 ≤ M ∧ 1 ≤ k ∧ k ≤ N - M - 1)) ∧
  (∀ (A : Adjacency 1000) (_hsym : ∀ i j, A i j = A j i)
      (_hdiag : ∀ i, A i i = false) (i : Fin 1000),
    let k := (Finset.univ.filter (fun j => A i j)).card
    (∀ a, 0 < completeProbability 1000 100 A i a) ↔ 1 ≤ k ∧ k ≤ 899) ∧
  (marginal (fun _ : Fin 6 => (1/6 : ℚ))
    (fun r => exposure starAdj (starAssignments r)) 0 .d00 = 0 ∧
  marginal (fun _ : Fin 6 => (1/6 : ℚ))
    (fun r => exposure starAdj (starAssignments r)) 0 .d10 = 0 ∧
  (∀ i, ∃ j, starAdj i j = true) ∧ degree starAdj 0 = 3)

end
end SAP.P044
