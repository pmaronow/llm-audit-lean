import Mathlib
import SAP.P016b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b.WH.W1
open scoped BigOperators

/-- Natural endpoints represent the nonnegative interval [lo/scale, hi/scale].
The enclosure predicates below are only used at positive scales. -/
structure NatBounds where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq, Repr

def boundsZero : NatBounds := ⟨0, 0⟩
def boundsOne (scale : ℕ) : NatBounds := ⟨scale, scale⟩

def boundsRatio (scale num den : ℕ) : NatBounds :=
  ⟨num*scale/den, (num*scale+den-1)/den⟩

def boundsAdd (a b : NatBounds) : NatBounds := ⟨a.lo+b.lo, a.hi+b.hi⟩

def boundsMul (scale : ℕ) (a b : NatBounds) : NatBounds :=
  ⟨a.lo*b.lo/scale, (a.hi*b.hi+scale-1)/scale⟩

def boundsNatMul (n : ℕ) (a : NatBounds) : NatBounds := ⟨n*a.lo, n*a.hi⟩

def boundsSum (as : List NatBounds) : NatBounds := as.foldl boundsAdd boundsZero

def boundsRescale (scale outScale : ℕ) (a : NatBounds) : NatBounds :=
  ⟨a.lo*outScale/scale, (a.hi*outScale+scale-1)/scale⟩

/-- The cross-multiplied form avoids divisions in soundness proofs. -/
def Encloses (scale : ℕ) (a : NatBounds) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (scale : ℝ)*x ∧ (scale : ℝ)*x ≤ a.hi

/-- All basic operations used by the numerical evaluator preserve enclosures.
The nonnegative domain follows from natural lower endpoints and positive scale. -/
def IntervalArithmeticSound : Prop :=
  (∀ scale num den : ℕ, 0 < scale → 0 < den →
    Encloses scale (boundsRatio scale num den) ((num : ℝ)/den)) ∧
  (∀ (scale : ℕ) (a b : NatBounds) (x y : ℝ), 0 < scale →
    Encloses scale a x → Encloses scale b y →
    Encloses scale (boundsMul scale a b) (x*y)) ∧
  (∀ (scale n : ℕ) (a : NatBounds) (x : ℝ), 0 < scale →
    Encloses scale a x → Encloses scale (boundsNatMul n a) ((n : ℝ)*x)) ∧
  (∀ (scale : ℕ) (as : List NatBounds) (xs : List ℝ), 0 < scale →
    List.Forall₂ (Encloses scale) as xs → Encloses scale (boundsSum as) xs.sum) ∧
  (∀ (scale outScale : ℕ) (a : NatBounds) (x : ℝ), 0 < scale → 0 < outScale →
    Encloses scale a x → Encloses outScale (boundsRescale scale outScale a) x)

/-- Binary exponentiation with outward rounding at each multiplication. -/
def boundsPow (scale : ℕ) (a : NatBounds) (n : ℕ) : NatBounds :=
  if hn : n = 0 then boundsOne scale else
    let half := boundsPow scale a (n/2)
    let square := boundsMul scale half half
    if n % 2 = 0 then square else boundsMul scale square a
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

/-- A table [seed, seed*a, ..., seed*a^(count-1)] with rounded products.
The evaluator zips tables of the same length, with no default entries. -/
def boundsPowersFrom (scale : ℕ) (a seed : NatBounds) : ℕ → List NatBounds
  | 0 => []
  | count+1 => seed :: boundsPowersFrom scale a (boundsMul scale seed a) count

/-- Soundness of the binary power and the forward table at all in-range indices. -/
def IntervalPowersSound : Prop :=
  (∀ (scale : ℕ) (a : NatBounds) (x : ℝ) (n : ℕ), 0 < scale →
    Encloses scale a x → Encloses scale (boundsPow scale a n) (x^n)) ∧
  (∀ (scale : ℕ) (a seed : NatBounds) (x y : ℝ) (count : ℕ), 0 < scale →
    Encloses scale a x → Encloses scale seed y →
    List.Forall₂ (Encloses scale) (boundsPowersFrom scale a seed count)
      ((List.range count).map fun j => y*x^j))

/-- One binomial CDF row. The q table starts at q^(B-c), so only O(c+log B)
rounded multiplications are needed. Soundness requires c ≤ B and r ≤ M. -/
def mixtureRowBounds (scale M B c r : ℕ) (coeff : List ℕ) : NatBounds :=
  let p := boundsRatio scale r M
  let q := boundsRatio scale (M-r) M
  let ps := boundsPowersFrom scale p (boundsOne scale) (c+1)
  let qs := boundsPowersFrom scale q (boundsPow scale q (B-c)) (c+1)
  boundsSum (List.zipWith boundsNatMul coeff (List.zipWith (boundsMul scale) ps qs.reverse))

/-- Sum the M CDF rows, multiply by 2/M, then round to the output scale. -/
def mixtureBounds (scale outScale M B c : ℕ) : NatBounds :=
  let coeff := (List.range (c+1)).map (Nat.fast_choose B)
  boundsRescale scale outScale
    (boundsMul scale (boundsRatio scale 2 M)
      (boundsSum ((List.range M).map fun r => mixtureRowBounds scale M B c (r+1) coeff)))

/-- General enclosure of the same real finite sum used in the claim.
Positive M and scales exclude zero denominators; c ≤ B justifies B-c and c-k. -/
def MixtureEnclosureSound : Prop :=
  ∀ scale outScale M B c : ℕ, 0 < scale → 0 < outScale → 0 < M → c ≤ B →
    Encloses outScale (mixtureBounds scale outScale M B c) (binomialMixture M B c)

/-- A finite integer certificate for a displayed decimal prefix. The evaluator
uses 600 internal digits and 20 output digits; all tests are strict integer
inequalities and can be checked by kernel reduction in independently proved blocks. -/
def PrefixCertificate (B c lower upper digits : ℕ) : Prop :=
  let a := mixtureBounds (10^600) (10^20) 6435 B c
  lower*10^20 < a.lo*10^digits ∧ a.hi*10^digits < upper*10^20

end SAP.P016b.WH.W1
