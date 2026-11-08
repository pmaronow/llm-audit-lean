import Mathlib
import SAP.P009b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The first `b` assignment coordinates; `hb` expresses that this vector exists. -/
def wholePrefix {n b : ℕ} (hb : b ≤ n) (z : Assignment n) : Assignment b :=
  fun i => z ⟨i.val, lt_of_lt_of_le i.isLt hb⟩

/-- A map with values in the three-point support used in Proposition 11. -/
def wholeThreeValued {Ω : Type*} (f : Ω → ℝ) : Prop :=
  ∀ ω, f ω = -1 ∨ f ω = 0 ∨ f ω = 1

/-- The finite objective defining the prefix minimizer; every competing
three-valued map is included, so ties impose no extra assumption. -/
def wholePrefixMinimizer {n b : ℕ} (E : Experiment n) (α : ℝ) (hb : b ≤ n)
    (f : Assignment b → ℝ) : Prop :=
  wholeThreeValued f ∧ ∀ g : Assignment b → ℝ, wholeThreeValued g →
    approximationError E.design α (fun z => f (wholePrefix hb z)) ≤
      approximationError E.design α (fun z => g (wholePrefix hb z))

/-- The heavy-atom example in the corrected Proposition 11 step. The
all-control point is distinguished; all other points have mass `4^(-b)`. -/
def wholeHeavyMass (b : ℕ) (z : Assignment b) : ℝ :=
  if z = (fun _ => false) then 1 - ((2 : ℝ)^b - 1) * ((4 : ℝ)^b)⁻¹
  else ((4 : ℝ)^b)⁻¹

/-- P009-T27; Supplement A, p. 37, proof of Proposition 11, first paragraph;
f_n^* is defined on p. 36.
Bernoulli prefixes have full support of size 2^b and both atom bounds. Finite
small-atom laws have disjoint three-point approximations. Minimizing maps and
minimizing sequences exist; every choice of minimizers has error at most twice
the geometric atom bound, that bound tends to zero, and both endpoint masses
tend to alpha/2. The explicit heavy-atom laws satisfy the printed lower bound
but cannot have both positive endpoint limits, showing why that lower bound
alone does not justify the limits. -/
def T27WholeStatement : Prop :=
  (∀ {n : ℕ} (E : Experiment n) (k : ℝ) (_hk : 0 < k)
    (_hBER : Bernoulli E)
    (_hMarg : ∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹)
    (b : ℕ) (hb : b ≤ n),
    (∀ a : Assignment b,
      k⁻¹^b ≤ prob E.design (fun z => wholePrefix hb z = a) ∧
      prob E.design (fun z => wholePrefix hb z = a) ≤ (1-k⁻¹)^b) ∧
    {a : Assignment b | 0 < prob E.design (fun z => wholePrefix hb z = a)} = Set.univ ∧
    {a : Assignment b | 0 < prob E.design (fun z => wholePrefix hb z = a)}.ncard = 2^b) ∧
  T27ApproximationStatement.{u} ∧
  (∀ {n b : ℕ} (E : Experiment n) (α : ℝ) (hb : b ≤ n),
    ∃ f : Assignment b → ℝ, wholePrefixMinimizer E α hb f) ∧
  (∀ (S : Study) (k q s α : ℝ) (_hReg : RegularSequence S k q s)
    (_hBER : ∀ t, Bernoulli (S.experiment t)) (_hα : 0 < α ∧ α < 1)
    (b : ℕ → ℕ) (hb : ∀ t, b t ≤ S.N t) (_hbInfinity : Tendsto b atTop atTop),
    (∃ f : (t : ℕ) → Assignment (b t) → ℝ,
      ∀ t, wholePrefixMinimizer (S.experiment t) α (hb t) (f t)) ∧
    Tendsto (fun t => (1-k⁻¹)^b t) atTop (nhds 0) ∧
    (∀ f : (t : ℕ) → Assignment (b t) → ℝ,
      (∀ t, wholePrefixMinimizer (S.experiment t) α (hb t) (f t)) →
      (∀ t, approximationError (S.experiment t).design α
        (fun z => f t (wholePrefix (hb t) z)) ≤ 2*(1-k⁻¹)^b t) ∧
      (∀ a : Bool, Tendsto (fun t => prob (S.experiment t).design
        (fun z => f t (wholePrefix (hb t) z) = if a then 1 else -1))
        atTop (nhds (α/2))))) ∧
  (∃ P : (b : ℕ) → Law (Assignment b),
    (∀ b z, (P b).mass z = wholeHeavyMass b z) ∧
    (∀ b z, ((4 : ℝ)^b)⁻¹ ≤ (P b).mass z) ∧
    Tendsto (fun b => (P b).mass (fun _ => false)) atTop (nhds 1) ∧
    (∀ (α : ℝ), 0 < α ∧ α < 1 →
      ∀ f : (b : ℕ) → Assignment b → ℝ, (∀ b, wholeThreeValued (f b)) →
      ¬ ((Tendsto (fun b => prob (P b) (fun z => f b z = 1)) atTop (nhds (α/2))) ∧
         (Tendsto (fun b => prob (P b) (fun z => f b z = -1)) atTop (nhds (α/2))))))

/-- Positive outcomes in this experiment make reciprocal powers ordinary real
powers, without a convention for fractional powers of negative bases. -/
def wholeReciprocalExperiment : Experiment 1 := fairExperiment 1 (fun _ _ => 1/4)

/-- The printed claim is false: P009-T29; Supplement A, p. 3, Lemma A3 and its
first proof display.
With the stated condition q >= 2a and no lower
bound on a, the fair one-unit constant-outcome experiment satisfies all of
Assumption 1 with k=q=2 and s=1. At a=-1 the corrected same-unit arm covariance
is 4, whereas k^(2a)=1/4. Every outcome is strictly positive, so all the powers
and finite moments exist. This refutes the unrestricted-order assertion; it
does not refute its natural-power or nonnegative-order specialization. -/
def T29WholeStatement : Prop :=
  let E := wholeReciprocalExperiment
  let X := fun z : Assignment 1 =>
    if z 0 = true then Real.rpow (E.outcome 0 z) (-1) else 0
  Bernoulli E ∧ Regular E 2 2 1 ∧
  (∀ i z, 0 < E.outcome i z) ∧
  2*(-1 : ℝ) ≤ 2 ∧ cov E.design X X = 4 ∧
  Real.rpow 2 (2*(-1 : ℝ)) = 1/4 ∧
  ¬ cov E.design X X ≤ Real.rpow 2 (2*(-1 : ℝ))

/-- A concrete two-unit pairing used to check the included independence
sentence in the proof of Lemma A17. -/
def wholeTwoPairing : Pairing 2 where
  partner := Equiv.swap 0 1
  involution := by intro i; simp
  no_fixed := by intro i; fin_cases i <;> decide

/-- Independent choice of orientation for a single pair: masses one half at
10 and 01, and zero at 00 and 11. -/
def wholeTwoPairedLaw : Law (Assignment 2) where
  mass := fun z => (if z = ![true, false] then (1/2 : ℝ) else 0) +
    (if z = ![false, true] then (1/2 : ℝ) else 0)
  nonneg := by intro z; split_ifs <;> norm_num
  total := by norm_num [Finset.sum_add_distrib]

def wholeTwoPairedExperiment : Experiment 2 := ⟨wholeTwoPairedLaw, fun _ _ => 0⟩

/-- The printed claim is false: P009-T34; Supplement A, p. 17, proof of Lemma A17;
Lemma A17 on p. 16
and Lemma A4 on p. 3.
The included background assertion that Z_i is
independent of Z_j whenever i differs from rho(j) fails for i=j. The explicit
two-unit paired design with zero outcomes satisfies Assumption 1 with k=q=2
and s=1, yet i=j=1 differs from its partner, and its fair treatment event has
self-intersection probability 1/2 rather than the product 1/4. This refutes
that background sentence, not the corrected moment bounds or Lemma A17. -/
def T34WholeStatement : Prop :=
  let E := wholeTwoPairedExperiment
  Paired E wholeTwoPairing ∧ Regular E 2 2 1 ∧
  (0 : Fin 2) ≠ wholeTwoPairing.partner 0 ∧
  marginal E 0 true = 1/2 ∧
  prob E.design (fun z => z 0 = true ∧ z 0 = true) = 1/2 ∧
  marginal E 0 true * marginal E 0 true = 1/4 ∧
  prob E.design (fun z => z 0 = true ∧ z 0 = true) ≠
    marginal E 0 true * marginal E 0 true

/-- The vector likelihood ratio and the treated-incoming-count likelihood
ratio, on the actual vector support. The count probability is positive too. -/
def wholeVectorCountRatio : Prop :=
  ∀ {n : ℕ} (E : Experiment n) (m : ℕ) (_hCR : Complete E m)
    (i : Fin n) (_hc : incoming E i ≤ min m (n-m)) (w : Assignment n) (b : Bool),
    0 < prob E.design (fun z => maskedOthers E i z = w) →
    0 < prob E.design (fun z => treatedIncoming E i z = treatedIncoming E i w) ∧
    cmean E.design (fun z => z i = b)
      (fun z => if maskedOthers E i z = w then 1 else 0) /
        prob E.design (fun z => maskedOthers E i z = w) =
    cmean E.design (fun z => z i = b)
      (fun z => if treatedIncoming E i z = treatedIncoming E i w then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = treatedIncoming E i w)

/-- P009-T18; Supplement A, pp. 9–10, Lemma A12 and its proof.
Complete randomization gives both incoming-count hypergeometric laws, the
zero-count case, the scalar likelihood-ratio identity with its strict bracket
bounds and every link of the scalar bound, and the supported-vector bound
(equivalently the finite-support maximum bound). Each supported-vector
likelihood ratio equals its treated-incoming-count likelihood ratio. -/
def T18WholeStatement : Prop :=
  T18CoreStatement ∧ T18ZeroStatement ∧ wholeVectorCountRatio

/-- Interference dependence for a supplied binary indicator array. -/
def wholeArrayD {n : ℕ} (J : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  if ∃ ℓ, J ℓ i = 1 ∧ J ℓ j = 1 then 1 else 0

/-- Pair-induced dependence for a supplied array and a supplied pairing map. -/
def wholeArrayE {n : ℕ} (J : Fin n → Fin n → ℝ) (ρ : Fin n → Fin n)
    (i j : Fin n) : ℝ :=
  if wholeArrayD J i j = 0 ∧ ∃ ℓ, J ℓ i = 1 ∧ J (ρ ℓ) j = 1 then 1 else 0

def wholeArrayC {n : ℕ} (J : Fin n → Fin n → ℝ) (ℓ : Fin n) : ℝ := ∑ j, J ℓ j

def wholeArrayEAvg {n : ℕ} (J : Fin n → Fin n → ℝ) (ρ : Fin n → Fin n) : ℝ :=
  (∑ i, ∑ j, wholeArrayE J ρ i j) / n

def wholeArrayC2 {n : ℕ} (J : Fin n → Fin n → ℝ) : ℝ :=
  Real.sqrt ((∑ ℓ, wholeArrayC J ℓ ^ 2) / n)

/-- P009-T20; Supplement A, pp. 5–6, Lemma A7 and its proof; Definition 7,
p. 685 (PDF p. 13).
For every reflexive binary interference array and every involutive pairing
map, the pair-dependence indicator is bounded by both witness counts. The
complete normalized proof chain bounds average pair dependence by the triple
sum, factors it into outgoing-count products, bounds those by paired squares,
splits the two sums, reindexes by the pairing permutation, and identifies the
result with C_2 squared. The real inequality 2xy <= x^2+y^2 holds universally.
Only the positive sample size presupposed by the averages is required. -/
def T20WholeStatement : Prop :=
  (∀ x y : ℝ, 2*x*y ≤ x^2+y^2) ∧
  ∀ {n : ℕ} (_hn : 0 < n) (J : Fin n → Fin n → ℝ)
    (_hJ : ∀ i j, J i j = 0 ∨ J i j = 1) (_hdiag : ∀ i, J i i = 1)
    (ρ : Fin n → Fin n) (_hρ : Function.Involutive ρ),
    let c := wholeArrayC J
    let A := ∑ i : Fin n, ∑ j : Fin n, ∑ ℓ : Fin n, J ℓ i * J (ρ ℓ) j
    let B := ∑ ℓ : Fin n, c ℓ * c (ρ ℓ)
    let Q := ∑ ℓ : Fin n, c ℓ ^ 2
    let Qρ := ∑ ℓ : Fin n, c (ρ ℓ) ^ 2
    (∀ i j, wholeArrayE J ρ i j ≤
      ∑ ℓ, (1-wholeArrayD J i j)*J ℓ i*J (ρ ℓ) j) ∧
    (∀ i j, (∑ ℓ, (1-wholeArrayD J i j)*J ℓ i*J (ρ ℓ) j) ≤
      ∑ ℓ, J ℓ i*J (ρ ℓ) j) ∧
    wholeArrayEAvg J ρ = (∑ i, ∑ j, wholeArrayE J ρ i j)/(n : ℝ) ∧
    wholeArrayEAvg J ρ ≤ A/(n : ℝ) ∧
    A/(n : ℝ) = B/(n : ℝ) ∧
    B/(n : ℝ) ≤ (∑ ℓ : Fin n, (c ℓ ^ 2 + c (ρ ℓ) ^ 2))/(2*(n : ℝ)) ∧
    (∑ ℓ : Fin n, (c ℓ ^ 2 + c (ρ ℓ) ^ 2))/(2*(n : ℝ)) = Q/(2*(n : ℝ))+Qρ/(2*(n : ℝ)) ∧
    Qρ = Q ∧
    Q/(2*(n : ℝ))+Qρ/(2*(n : ℝ)) = Q/(n : ℝ) ∧
    Q/(n : ℝ) = wholeArrayC2 J ^ 2 ∧
    wholeArrayEAvg J ρ ≤ wholeArrayC2 J ^ 2

end
end SAP.P009b
