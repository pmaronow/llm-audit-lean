import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

noncomputable section
namespace AronowAudit.P041

/-- "lengthofincumbency: Year Senator was first elected" (deposited codebook
p. 1), in contrast to the S9/S10 tenure labels. The conversion "L=C-Y",
with C=2014, is used in P041-T10 and P041-E004. -/
def tenureFromYear (C Y : ℝ) : ℝ := C - Y

/-- "h₀(t) exp(bY+aT+gTY+w)", P041-T10: the Cox hazard expressed using
first-election year, the fitted S9 covariate. The paper prints hazard ratios,
not this parameterization (P041-E004). -/
def yearHazard (h₀ b a g Y T w : ℝ) : ℝ :=
  h₀ * Real.exp (b*Y + a*T + g*T*Y + w)

/-- The same Cox hazard in tenure coordinates: bL=-b, aL=a+Cg, gL=-g,
h₀L=h₀ exp(Cb), P041-E004 / P041-T10(i). -/
def tenureHazard (h₀ b a g C L T w : ℝ) : ℝ :=
  (h₀ * Real.exp (C*b)) * Real.exp ((-b)*L + (a+C*g)*T + (-g)*T*L + w)

/-- P041-T10(i): complete affine reparameterization of the linear predictor
and equality of fitted hazards; no baseline or treatment-main-effect term
is omitted when year is replaced by tenure. -/
theorem year_tenure_reparameterization (h₀ a b g C L T w : ℝ) :
    b*(C-L)+a*T+g*T*(C-L)+w =
      C*b+(-b)*L+(a+C*g)*T+(-g)*T*L+w ∧
    tenureHazard h₀ b a g C L T w = yearHazard h₀ b a g (C-L) T w := by
  constructor
  · ring
  · unfold tenureHazard yearHazard
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- P041-T10(ii): the hazard-ratio multiplier for one more year of tenure
is exp(-g)=1/exp(g); the same identity applies to the S10 main coefficient b.
The treatment hazard ratio at tenure L changes by this reciprocal factor. -/
theorem tenure_multiplier_is_reciprocal (a g C L : ℝ) :
    Real.exp (-g) = 1 / Real.exp g ∧
    Real.exp ((a+C*g)+(-g)*(L+1)) =
      Real.exp ((a+C*g)+(-g)*L) * (1/Real.exp g) ∧
    (∀ r : ℝ, 0 < r →
      ((r < 1 ↔ 1 < 1/r) ∧ (1 < r ↔ 1/r < 1))) := by
  refine ⟨by rw [Real.exp_neg, one_div], ?_, ?_⟩
  · have he : (a+C*g)+(-g)*(L+1) = ((a+C*g)+(-g)*L) + (-g) := by ring
    rw [he, Real.exp_add, Real.exp_neg, one_div]
  · intro r hr
    constructor
    · rw [lt_div_iff₀ hr]
      simpa using (Iff.rfl : r < 1 ↔ r < 1)
    · rw [div_lt_iff₀ hr]
      simp

/-- P041-T10(iii): reciprocals of every possible unrounded S9/S10 entry.
Only the 1.056 interaction rows determine the reciprocal at three decimals:
it lies in [0.9465,0.9475), so rounds to 0.947. -/
theorem printed_tenure_reciprocal_enclosures :
    (∀ r : ℝ, 0.989-0.0005 ≤ r → r ≤ 0.989+0.0005 →
      1.0106 < 1/r ∧ 1/r < 1.0117 ∧ 1 < 1/r) ∧
    (∀ r : ℝ, 0.981-0.0005 ≤ r → r ≤ 0.981+0.0005 →
      1.0188 < 1/r ∧ 1/r < 1.0199 ∧ 1 < 1/r) ∧
    (∀ r : ℝ, 1.056-0.0005 ≤ r → r ≤ 1.056+0.0005 →
      0.9465 < 1/r ∧ 1/r < 0.9475 ∧ 1/r < 1) ∧
    (∀ r : ℝ, 1.004-0.0005 ≤ r → r ≤ 1.004+0.0005 →
      0.9955 < 1/r ∧ 1/r < 0.9966 ∧ 1/r < 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro r hl hu
  all_goals
    have hr : 0 < r := by linarith
    constructor
    · apply (lt_div_iff₀ hr).2; nlinarith
    · constructor
      · apply (div_lt_iff₀ hr).2; nlinarith
      · first
        | apply (lt_div_iff₀ hr).2; nlinarith
        | apply (div_lt_iff₀ hr).2; nlinarith

/-- P041-T10(iv): delta-method SE of the reciprocal ratio is s/r²;
negating the log interaction coefficient leaves the squared Wald statistic
unchanged. The algebra applies also to S10's year main effect. -/
theorem reciprocal_standard_error_and_wald (g V s : ℝ) (_hV : 0 ≤ V)
    (hs : s = Real.exp g * Real.sqrt V) :
    (1/Real.exp g) * Real.sqrt V = s/(Real.exp g)^2 ∧ (-g)^2/V = g^2/V := by
  constructor
  · rw [hs]
    field_simp
  · rw [neg_sq]

/-- "(132/125)^[T(Y-2009)]", P041-E004 / P041-T10(v),
represented equivalently by exp(log(132/125) T (Y-2009)). -/
def illustrativeYearRelativeHazard (T Y : ℝ) : ℝ :=
  Real.exp (Real.log (132/125) * T * (Y-2009))

/-- P041-T10(v): explicit first-election years 2009 and 2008 correspond
to tenures 5 and 6; the treatment hazard ratio goes from 1 to 125/132,
while the year multiplier 132/125 is greater than 1. The multipliers
multiply to 1. This is an illustrative exact law, not an unrounded refit. -/
theorem year_tenure_exact_instance :
    tenureFromYear 2014 2009 = 5 ∧ tenureFromYear 2014 2008 = 6 ∧
    illustrativeYearRelativeHazard 0 2009 = 1 ∧
    illustrativeYearRelativeHazard 0 2008 = 1 ∧
    illustrativeYearRelativeHazard 1 2009 = 1 ∧
    illustrativeYearRelativeHazard 1 2008 = 125/132 ∧
    (1:ℝ) < 132/125 ∧ (125/132:ℝ) < 1 ∧
    (132/125:ℝ)*(125/132) = 1 := by
  have he : illustrativeYearRelativeHazard 1 2008 = (125/132:ℝ) := by
    unfold illustrativeYearRelativeHazard
    norm_num only [mul_one]
    rw [mul_neg_one, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  simp only [he]
  norm_num [tenureFromYear, illustrativeYearRelativeHazard]

end AronowAudit.P041

