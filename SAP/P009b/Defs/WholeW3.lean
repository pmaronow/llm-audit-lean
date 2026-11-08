import Mathlib
import SAP.P009b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009b
noncomputable section

/-- The graph of the ordinary real power on the corrected claim's nonnegative
exponent domain. Every base, including zero, has zeroth power one. At positive
orders, nonnegative bases use `Real.rpow`; a negative base requires a reduced
nonnegative rational exponent with a positive odd denominator and has sign
`(-1)^p`. In particular this does not use Mathlib's negative-base real power. -/
def OrdinaryPowerW3 (x t v : ℝ) : Prop :=
  (t = 0 ∧ v = 1) ∨
  (0 < t ∧ 0 ≤ x ∧ v = Real.rpow x t) ∨
  (0 < t ∧ x < 0 ∧ ∃ p d : ℕ,
    0 < d ∧ Odd d ∧ Nat.Coprime p d ∧ t = (p : ℝ) / (d : ℝ) ∧
      v = (-1 : ℝ) ^ p * Real.rpow |x| t)

/-- The ordinary powered outcome, masked by unit `i`'s assignment to arm `b`.
The supplied values `u` are constrained by `OrdinaryPowerW3` on design support;
values on assignments of mass zero never affect a moment or covariance. -/
def powerArmW3 {n : ℕ} (u : Assignment n → ℝ) (i : Fin n) (b : Bool)
    (z : Assignment n) : ℝ := if z i = b then u z else 0

/-- The absolute outcome moment of real order `t` under the finite design.
At order zero this is one, including when every outcome is zero. -/
def outcomeMomentW3 {n : ℕ} (E : Experiment n) (i : Fin n) (t : ℝ) : ℝ :=
  mean E.design (fun z => Real.rpow |E.outcome i z| t)

/-- Every numerical link of Lemma A3's corrected moment chain, with signed and
absolute covariance versions of its first inequality and endpoint. The two
arm variables retain their respective outcome indices. All square roots denote
the nonnegative root, equivalently the displayed power one half. -/
def CovarianceMomentChainW3 {n : ℕ} (E : Experiment n) (k q a : ℝ)
    (i j : Fin n) (b : Bool) (u v : Assignment n → ℝ) : Prop :=
  let X := powerArmW3 u i b
  let Y := powerArmW3 v j b
  let M := fun r => outcomeMomentW3 E r (2*a)
  let Q := fun r => Real.rpow (outcomeMomentW3 E r q) (2*a/q)
  let K := Real.rpow (Real.rpow k q) (2*a/q)
  cov E.design X Y ≤ Real.sqrt (var E.design X * var E.design Y) ∧
  |cov E.design X Y| ≤ Real.sqrt (var E.design X * var E.design Y) ∧
  Real.sqrt (var E.design X * var E.design Y) ≤ Real.sqrt (M i * M j) ∧
  Real.sqrt (M i * M j) ≤ Real.sqrt (Q i * Q j) ∧
  Real.sqrt (Q i * Q j) ≤ Real.sqrt (K * K) ∧
  Real.sqrt (K * K) = Real.sqrt (Real.rpow k (4*a)) ∧
  Real.sqrt (Real.rpow k (4*a)) = Real.rpow k (2*a) ∧
  cov E.design X Y ≤ Real.rpow k (2*a) ∧
  |cov E.design X Y| ≤ Real.rpow k (2*a)

/-- P009-T29; Supplement A, p. 3, Lemma A3 and the first display of its proof.
For any positive finite population and any assignment design, Assumption 1B
with k > 0 and finite real q >= 2 implies the entire corrected covariance
moment chain for every real a in [0,q/2] whose ordinary outcome powers exist
on positive-probability assignments. The j arm uses Y_j. The chain includes
Cauchy--Schwarz, the second-moment bound, real-order Jensen interpolation,
Assumption 1B's moment bound, both square-root equalities, and the endpoint
Cov <= k^(2a); the same chain bounds absolute covariance. The printed first
line, using Y_i in both arm variables, is also a true Cauchy--Schwarz bound.
Ordinary powers follow `OrdinaryPowerW3`, preserving signed integer powers
and odd-denominator fractional powers; every zeroth power, including 0^0,
is one. Both a = 0 and 2a = q are included. Only the two outcomes entering
a covariance need powers on the design support. The usual measure-theoretic
conditions are assumed and hold automatically on this finite assignment space. -/
def T29WholeStatement_W3 : Prop :=
  (∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (u : Assignment n → ℝ)
    (i j : Fin n) (b : Bool),
    cov E.design (powerArmW3 u i b) (powerArmW3 u j b) ≤
      Real.sqrt (var E.design (powerArmW3 u i b) *
        var E.design (powerArmW3 u j b))) ∧
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (k q a : ℝ)
    (_hk : 0 < k) (_hq : 2 ≤ q) (_ha : 0 ≤ a) (_hqa : 2*a ≤ q)
    (_hMoment : ∀ r, outcomeMomentW3 E r q ≤ Real.rpow k q)
    (i j : Fin n) (b : Bool) (u v : Assignment n → ℝ)
    (_hu : ∀ z, 0 < E.design.mass z → OrdinaryPowerW3 (E.outcome i z) a (u z))
    (_hv : ∀ z, 0 < E.design.mass z → OrdinaryPowerW3 (E.outcome j z) a (v z)),
    CovarianceMomentChainW3 E k q a i j b u v

end
end SAP.P009b
