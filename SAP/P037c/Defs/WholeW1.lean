import Mathlib
import SAP.P037c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-! Finite laws below make the usual measure-theoretic conditions automatic. -/

/-- Four disjoint ten-pupil blocks; the second coordinate is (pair, side). -/
abbrev Whole35Student := Fin 4 × (Fin 5 × Bool)

def whole35Side (s : Bool) : Finset Whole35Student :=
  Finset.univ ×ˢ (Finset.univ ×ˢ {s})

def whole35Support : Finset (Finset Whole35Student) :=
  Finset.univ.powerset.filter (fun z => ∀ h, (z.filter (fun i => i.1 = h)).card = 5)

def whole35Partner (i : Whole35Student) : Whole35Student := (i.1, partner i.2)

noncomputable def whole35Outcome (z : Finset Whole35Student) (i : Whole35Student) : ℝ :=
  if i ∈ z then 1 else 0

noncomputable def whole35Statistic (z : Finset Whole35Student)
    (Y : Whole35Student → ℝ) : ℝ :=
  (∑ i ∈ z, Y (whole35Partner i)) / 20 -
    (∑ i ∈ Finset.univ \ z, Y (whole35Partner i)) / 20

noncomputable def whole35Mass (_z : Finset Whole35Student) : ℝ :=
  1 / (whole35Support.card : ℝ)

/-- P037-T35; SI Appendix pp. 29 and 32, Fig. S5 (pp. 30–32).
Own-seed outcomes alone give the stated one-block distribution, p-values and rejection
probability 8/63. With four disjoint copies the uniform support has size 252^4,
the copied observation has statistic -1, exactly two assignments have absolute statistic
1, and its exact two-sided p-value is 2/252^4. The usual measure-theoretic conditions
are assumed (all spaces and sums here are finite). -/
def T35WholeStatement : Prop :=
  T35Statement ∧
  whole35Support.card = 252^4 ∧
  (∑ z ∈ whole35Support, whole35Mass z) = 1 ∧
  (∀ z ∈ whole35Support, 0 < whole35Mass z ∧ z.card = 20) ∧
  whole35Side false ∈ whole35Support ∧
  (∀ (z z' : Finset Whole35Student) i,
    (i ∈ z ↔ i ∈ z') → whole35Outcome z i = whole35Outcome z' i) ∧
  (∀ z ∈ whole35Support, ∀ Y,
    nominationStatistic Finset.univ
      (fun i j => if j = whole35Partner i then 1 else 0) (fun _ => 1)
      (whole35Outcome z) Y = whole35Statistic z Y) ∧
  whole35Statistic (whole35Side false) (whole35Outcome (whole35Side false)) = -1 ∧
  (∀ z ∈ whole35Support,
    |whole35Statistic z (whole35Outcome (whole35Side false))| ≤ 1) ∧
  (whole35Support.filter (fun z =>
    |whole35Statistic z (whole35Outcome (whole35Side false))| = 1)).card = 2 ∧
  (∑ z ∈ whole35Support, whole35Mass z *
    (if |whole35Statistic z (whole35Outcome (whole35Side false))| ≥
      |whole35Statistic (whole35Side false) (whole35Outcome (whole35Side false))|
      then 1 else 0)) = 2 / (252:ℝ)^4

abbrev Whole27Assignment := (Fin 4 × Fin 3) → Fin 4

/-- The explicit E1 law, not the school-and-seed law E2. -/
noncomputable def whole27Mass (_d : Whole27Assignment) : ℝ := (1/4:ℝ)^12

/-- P037-T27; SI Appendix pp. 18–19; main p. 568 (PDF p. 3).
The specified twelve-unit potential outcomes give different separate and pooled WLS
means and contrasts under both weight vectors. E1 consists of independent uniform
four-category exposures, with every joint cylinder probability (1/4)^its size,
marginals 1/4, weights 4 and observed realization probability (1/4)^12 > 0.
E2 is the six-school seed design with focal probabilities (1/2,1/8,1/8,1/4),
realization probability 1/640 and weights (2,8,8,4). All stated coefficients,
residuals, means and contrast differences hold. The usual measure-theoretic
conditions are assumed (all spaces and sums here are finite). -/
def T27WholeStatement : Prop :=
  T27Statement ∧
  (∑ d : Whole27Assignment, whole27Mass d) = 1 ∧
  (∀ d, 0 < whole27Mass d) ∧
  (∀ (s : Finset (Fin 4 × Fin 3)) (a : Whole27Assignment),
    (∑ d : Whole27Assignment, whole27Mass d *
      (if ∀ i ∈ s, d i = a i then 1 else 0)) = (1/4:ℝ)^s.card) ∧
  (∀ i k, (∑ d : Whole27Assignment, whole27Mass d *
    (if d i = k then 1 else 0)) = 1/4 ∧
    1 / (∑ d : Whole27Assignment, whole27Mass d *
      (if d i = k then 1 else 0)) = 4) ∧
  (∑ d : Whole27Assignment, whole27Mass d *
    (if ∀ i, d i = i.1 then 1 else 0)) = (1/4:ℝ)^12 ∧
  0 < (1/4:ℝ)^12 ∧
  (∀ i : Fin 4 × Fin 3, regression12Potential i i.1 = regression12Y i) ∧
  ((Finset.univ : Finset (Fin 6)).powersetCard 3).card = 20 ∧
  (∑ _schools ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
    ∑ _seeds : Fin 6 → Bool × Bool, (1/(20*4^6):ℝ)) = 1 ∧
  0 < (1/(20*4^6):ℝ)

noncomputable def whole33Mean (z : Fin 6 × (Fin 4 → Bool))
    (Y : (Fin 4 × Fin 2) → ℝ) (k : Fin 4) : ℝ :=
  let b := (regressionMap (controlWeight (controlExposure z))
    (controlFullRow (controlExposure z))).mulVec Y
  b k.castSucc + b 4 / 4

noncomputable def whole33Imputed (z : Fin 6 × (Fin 4 → Bool)) (i : Fin 4 × Fin 2) : ℝ :=
  controlY i + controlPointMean (controlExposure z i) - controlPointMean (controlObserved i)

/-- P037-T33; SI Appendix pp. 19–20, also pp. 14–15.
The specified normalized 96-state abstract exposure design has the stated marginals,
ranks, point coefficients, standardized means and eight residuals. At every assignment
and every exposure the full-control imputed refit mean is the residual refit mean plus
the fixed point mean. The two full-control contrast variances equal Vfull; the collapsed
residual contrast variance equals Vcol, with 2 < Vcol < 5/2 < 9 < Vfull < 37/4.
Their standard deviations round to 1.53 and 3.03. The usual measure-theoretic
conditions are assumed (all spaces and sums here are finite). -/
def T33WholeStatement : Prop :=
  T33Statement ∧
  (∑ i : Fin 4 × Fin 2, controlPiI i) / 8 = 1/4 ∧
  (∀ z k, whole33Mean z (whole33Imputed z) k =
    whole33Mean z controlResidual k + controlPointMean k) ∧
  (305/200:ℝ) < Real.sqrt controlCollapsedVarianceCertificate ∧
  Real.sqrt controlCollapsedVarianceCertificate < 307/200 ∧
  (605/200:ℝ) < Real.sqrt controlFullVarianceCertificate ∧
  Real.sqrt controlFullVarianceCertificate < 607/200

/-- Column space of a real matrix, including a matrix with no columns. -/
noncomputable def wholeColumnSpace {I J : Type*} [Fintype J]
    (H : Matrix I J ℝ) : Submodule ℝ (I → ℝ) := LinearMap.range H.mulVecLin

/-- A coefficient functional is estimable exactly when it kills the design kernel. -/
def wholeEstimable {I J : Type*} [Fintype J] (H : Matrix I J ℝ)
    (ell : (J → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ v, H.mulVec v = 0 → ell v = 0

/-- Finite population variance under a specified normalized law. -/
noncomputable def wholeVariance {Ω : Type*} [Fintype Ω]
    (prob f : Ω → ℝ) : ℝ :=
  (∑ z, prob z * (f z)^2) - (∑ z, prob z * f z)^2

/-- Reduced-control refits retain the projected, rather than the whole, omitted shift. -/
def Whole34Reduced : Prop :=
  ∀ (n p q : ℕ) (D : Fin n → Fin 4)
    (C : Matrix (Fin n) (Fin p) ℝ) (Cc : Matrix (Fin n) (Fin q) ℝ)
    (w : Fin n → ℝ), (∀ i, 0 < w i) →
    Function.Injective (pooledExposureRow D Cc).mulVec →
    ∀ (tau : Fin 4 → ℝ) (gamma : Fin p → ℝ) (r : Fin n → ℝ),
    let Hc := pooledExposureRow D Cc
    let Lc := regressionMap w Hc
    let theta := fun j : Fin (4+q) => if h : j.val < 4 then tau ⟨j.val,h⟩ else 0
    let omitted := C.mulVec gamma
    Lc.mulVec (fun i => r i + tau (D i) + omitted i) =
      Lc.mulVec r + theta + Lc.mulVec omitted ∧
    (Hc.mulVec (Lc.mulVec omitted) = omitted ↔ omitted ∈ wholeColumnSpace Hc)

/-- The original two probability controls and the collapsed sum control. -/
noncomputable def whole34TwoControls : Matrix (Fin 4 × Fin 2) (Fin 2) ℝ :=
  fun i => ![controlPiI i, controlPi i 2]

noncomputable def whole34SumControl : Matrix (Fin 4 × Fin 2) (Fin 1) ℝ :=
  fun i => ![controlPiI i + controlPi i 2]

noncomputable def whole34Indicators (D : (Fin 4 × Fin 2) → Fin 4) :
    Matrix (Fin 4 × Fin 2) (Fin 4) ℝ := fun i k => if D i = k then 1 else 0

/-- A concrete strict loss of control space, together with an actual variance discrepancy. -/
def Whole34LostControl : Prop :=
  wholeColumnSpace whole34SumControl < wholeColumnSpace whole34TwoControls ∧
  (∀ D, wholeColumnSpace (pooledExposureRow D whole34SumControl) =
    wholeColumnSpace (whole34Indicators D)) ∧
  (∀ D, wholeColumnSpace (pooledExposureRow D whole34TwoControls) =
    wholeColumnSpace (controlFullRow D)) ∧
  (fun i => controlPiI i * controlPoint 4) ∉
    wholeColumnSpace (whole34Indicators controlObserved) ∧
  controlVariance (fun z => controlContrast z false controlResidual) ≠
    controlVariance (fun z => controlContrast z true (whole33Imputed z))

/-- Full-rank basis representation and unique fitted WLS values for every presentation. -/
def Whole34Basis : Prop :=
  ∀ (n p : ℕ) (H : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ),
    (∀ i, 0 < w i) →
    (∃ (q : ℕ) (B : Matrix (Fin n) (Fin q) ℝ),
      Function.Injective B.mulVec ∧ wholeColumnSpace B = wholeColumnSpace H) ∧
    ∀ (q : ℕ) (B : Matrix (Fin n) (Fin q) ℝ),
      Function.Injective B.mulVec → wholeColumnSpace B = wholeColumnSpace H →
      ∀ y : Fin n → ℝ,
        regressionMinimum w B y ((regressionMap w B).mulVec y) ∧
        (∃ a, regressionMinimum w H y a) ∧
        (∀ a, regressionMinimum w H y a ↔
          H.mulVec a = B.mulVec ((regressionMap w B).mulVec y))

/-- Aliased coefficient presentations preserve fitted shifts and all estimable functionals. -/
def Whole34Aliased : Prop :=
  (∀ (n p : ℕ) (H : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ),
    (∀ i, 0 < w i) → ∀ (y : Fin n → ℝ) (theta a b : Fin p → ℝ),
    regressionMinimum w H y a →
    regressionMinimum w H (y + H.mulVec theta) b →
    H.mulVec b = H.mulVec a + H.mulVec theta ∧
      ∀ ell, wholeEstimable H ell → ell b = ell a + ell theta) ∧
  (∀ (Ω : Type) [Fintype Ω] (n p : ℕ)
    (H : Ω → Matrix (Fin n) (Fin p) ℝ) (w r : Ω → Fin n → ℝ)
    (theta : Fin p → ℝ) (a b : Ω → Fin p → ℝ)
    (ell : (Fin p → ℝ) →ₗ[ℝ] ℝ) (prob : Ω → ℝ),
    (∀ z i, 0 < w z i) → (∀ z, wholeEstimable (H z) ell) →
    (∀ z, regressionMinimum (w z) (H z) (r z) (a z)) →
    (∀ z, regressionMinimum (w z) (H z) (r z + (H z).mulVec theta) (b z)) →
    (∀ z, 0 ≤ prob z) → (∑ z, prob z) = 1 →
    (∀ z, ell (b z) = ell (a z) + ell theta) ∧
      wholeVariance prob (fun z => ell (b z)) = wholeVariance prob (fun z => ell (a z)))

/-- P037-T34; SI Appendix pp. 19–20, also pp. 14–15.
For fixed units and controls, positive weights and full column rank, the printed
constant-effect imputation equals r + H_z theta, its WLS coefficients shift by theta,
and every standardized mean and contrast shifts by its fixed point value and has the
same variance as the residual refit. Fewer controls retain only the projection of the
omitted control contribution; this equals that contribution exactly when it belongs
to the reduced design space. The T33 design has a strictly smaller collapsed control
space, an omitted contribution outside the reduced design, and unequal variances.
Aliased presentations have the same unique fitted values after passing to a full-rank
basis, and the shift and variance identities hold for estimable means and contrasts.
The usual measure-theoretic conditions are assumed; finite normalized laws describe
distributions on the finitely many exposure assignments. -/
def T34WholeStatement : Prop :=
  (∀ (Ω : Type) [Fintype Ω], T34Statement Ω) ∧
  Whole34Reduced ∧ Whole34LostControl ∧ Whole34Basis ∧ Whole34Aliased

/-- Expected-projection orthogonality derived from the canonical raw first moments. -/
def Whole43Orthogonality : Prop :=
  ∀ (Ω K : Type) [Fintype Ω] [Fintype K] (B : ℕ)
    (d : FiniteDesign Ω) (T C : Ω → (Fin B × Fin 4) → ℝ)
    (X : K → (Fin B × Fin 4) → ℝ) (mu : (Fin B × Fin 4) → ℝ)
    (lam : K → ℝ) (p : ℝ),
    (∀ i, designMean d (fun w => T w i) = p) →
    (∀ i, designMean d (fun w => T w i * C w i) = p * mu i) →
    (∀ i, blockDemean mu i = ∑ k, lam k * blockDemean (X k) i) →
    cross d (fun w => blockDemean (T w)) (fun w => blockDemean (T w)) ≠ 0 →
    let r := blockResidual d T C X lam p
    (∀ i, designMean d (fun w => r w i) = 0) ∧
    cross d r (fun w => blockDemean (T w)) = 0 ∧
    (∀ k, cross d r (fun _ => blockDemean (X k)) = 0) ∧
    cross d r (fun w => blockDemean (fun i => T w i * C w i)) = cross d r r

noncomputable def whole43Design : FiniteDesign (Fin 4) where
  weight := fun _ => 1/4
  nonneg := by intro w; norm_num
  total := by norm_num [Fin.sum_univ_four]

noncomputable def whole43Treatment (w : Fin 4) (i : Fin 1 × Fin 4) : ℝ :=
  if (w.val < 2) = (i.2.val < 2) then 1 else 0

noncomputable def whole43Composition (w : Fin 4) (_i : Fin 1 × Fin 4) : ℝ :=
  if w.val = 0 ∨ w.val = 2 then 1/4 else 3/4

noncomputable def whole43Outcome (w : Fin 4) (i : Fin 1 × Fin 4) : ℝ :=
  (i.2.val:ℝ)/10 + whole43Treatment w i * (3/10 + (2/5)*whole43Composition w i)

/-- Four-state certificate, including actual normal equations and positive denominators. -/
def Whole43Certificate : Prop :=
  (∀ i, designMean whole43Design (fun w => whole43Treatment w i) = 1/2) ∧
  (∀ i, designMean whole43Design
    (fun w => whole43Treatment w i * whole43Composition w i) = (1/2:ℝ)*(1/2)) ∧
  (∀ i : Fin 1 × Fin 4, blockDemean (fun _ => (1/2:ℝ)) i =
    ∑ k : Fin 0, (Fin.elim0 k : ℝ) * blockDemean (Fin.elim0 k) i) ∧
  cross whole43Design (fun w => blockDemean (whole43Treatment w))
    (fun w => blockDemean (whole43Treatment w)) = 1 ∧
  cross whole43Design
    (blockResidual whole43Design whole43Treatment whole43Composition
      (fun k : Fin 0 => Fin.elim0 k) (fun k => Fin.elim0 k) (1/2))
    (blockResidual whole43Design whole43Treatment whole43Composition
      (fun k : Fin 0 => Fin.elim0 k) (fun k => Fin.elim0 k) (1/2)) = 1/16 ∧
  NormalEquations whole43Design (fun w => blockDemean (whole43Treatment w))
    (fun w => blockDemean (fun i => whole43Treatment w i * whole43Composition w i))
    (fun k : Fin 0 => Fin.elim0 k) (fun w => blockDemean (whole43Outcome w))
    (3/10) (fun k => Fin.elim0 k) (2/5) ∧
  (∀ w i, whole43Treatment w i = 0 ∨ whole43Treatment w i = 1) ∧
  (∀ w, (∑ i : Fin 1 × Fin 4, whole43Treatment w i) = 2) ∧
  (∀ i, whole43Treatment 0 i + whole43Treatment 2 i = 1 ∧
    whole43Treatment 1 i + whole43Treatment 3 i = 1) ∧
  (∀ w i, whole43Composition w i = 1/4 ∨ whole43Composition w i = 3/4) ∧
  (∃ i j : Fin 1 × Fin 4, (i.2.val:ℝ)/10 ≠ (j.2.val:ℝ)/10)

/-- P037-T43; accepted 19 October review of E001; SI Eq. (2), p. 13,
repeated pp. 15–16; main p. 568 (PDF p. 3).
On any finite normalized design and complete four-school blocks, the stated raw first
moments and mean-spanning controls imply E[r]=0, E[r't]=0, E[r'V]=0 and E[r'z]=E[r'r].
If E[t't] is nonzero and K=E[r'r]>0, every actual expected-normal-equation solution
obeys b-beta=E[sum r_i T_i eta_i]/K; eta=0 implies b=beta for arbitrary fixed untreated
levels. A four-state binary complementary two-of-four certificate has compositions
1/4 or 3/4, nonconstant untreated levels, E[t't]=1, K=1/16 and an actual solution.
The usual measure-theoretic conditions are assumed (all spaces and sums here are finite). -/
def T43WholeStatement : Prop :=
  (∀ (Ω K : Type) [Fintype Ω] [Fintype K], T43Statement Ω K) ∧
  Whole43Orthogonality ∧ Whole43Certificate

end SAP.P037c
