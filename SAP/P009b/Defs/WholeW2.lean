import Mathlib
import SAP.P009b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
noncomputable section

/-- The corrected deterministic centre in Supplement B, Section 1.4.
All subtraction in the formula is real subtraction, including when b = 1. -/
def w2CorrectedCenter (N : ℝ) (b : ℕ) : ℝ :=
  (N - ((b : ℝ) - 1) ^ 2) / (N + (b : ℝ) * ((b : ℝ) - 1))

/-- The centre printed in Supplement B, Section 1.4. -/
def w2PrintedCenter (N : ℝ) (b : ℕ) : ℝ :=
  (N - ((b : ℝ) - 1) - (b : ℝ) * ((b : ℝ) - 1)) /
    (N + (b : ℝ) * ((b : ℝ) - 1))

/-- The limiting centre as a function of a_n / sqrt(n). -/
def w2RatioCenter (r : ℝ) : ℝ := (1 - r ^ 2) / (1 + r ^ 2)

/-- The random normalized variance gap in the corrected convergence display. -/
def w2NormalizedGap (S : Study) (t : ℕ) (z : Assignment (S.N t)) : ℝ :=
  size S t / dAvg (S.experiment t) *
    (vBER (S.experiment t) z - var (S.experiment t).design (ht (S.experiment t)))

/-- The fair one-source model, with b_n = floor(a_n) and the stipulated source baseline.
The bounds on floor(a_n) ensure that the source exists and every denominator is positive. -/
def W2OneSourceModel (S : Study) (a : ℕ → ℝ)
    (c : (t : ℕ) → Fin (S.N t) → ℝ) : Prop :=
  (∀ t, 1 ≤ ⌊a t⌋₊ ∧ ⌊a t⌋₊ ≤ S.N t) ∧
  (∀ t, c t ⟨0, S.positive t⟩ = -1 / 4) ∧
  (∀ t, (S.experiment t).design = fairLaw (S.N t)) ∧
  (∀ t, (S.experiment t).outcome = oneSourceOutcome ⌊a t⌋₊ (c t))

/-- P009-T22; Supplement B, p. 8, Section 1.4: the B₂ display and the display after
"Taken together, we can conclude that".
The fair one-source model has all corrected finite aggregate formulas and every individual
pair/arm conditional covariance identity. Under the standing regularity assumptions, its
normalized variance gap converges in probability about both the corrected and printed centres.
If a_n / sqrt(n) tends to zero its limit is one; if n / a_n² tends to zero its limit is minus one.
For comparable order the gap is asymptotic in probability to (1-a_n²/n)/(1+a_n²/n);
a ratio limit lambda > 0 gives (1-lambda²)/(1+lambda²), whose positive, zero and negative
possibilities are all realized by regular one-source studies. Comparability alone does not
assert existence of a limit. -/
def T22WholeStatement : Prop :=
  T22FiniteStatement ∧ T22CorrectionStatement ∧
  (∀ {n : ℕ} (hn : 0 < n) (b : ℕ) (_hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ),
    let E := fairExperiment n (oneSourceOutcome b c)
    (∀ (i j : Fin n), i ≠ j → ∀ u v : Bool,
      prob E.design (fun z => z i = u ∧ z j = v) = 1 / 4 ∧
      ccov E.design (fun z => z i = u ∧ z j = v) (E.outcome i) (E.outcome j) =
        (if 0 < i.val ∧ i.val < b then (1 : ℝ) else 0) *
        (if 0 < j.val ∧ j.val < b then (1 : ℝ) else 0) * bit u * bit v) ∧
    (c ⟨0, hn⟩ = -1 / 4 →
      B1 E = ((b : ℝ) - 1) / ((n : ℝ) + (b : ℝ) * ((b : ℝ) - 1)))) ∧
  (∀ (S : Study) (k q s : ℝ), RegularSequence S k q s →
    ∀ (a : ℕ → ℝ) (c : (t : ℕ) → Fin (S.N t) → ℝ), W2OneSourceModel S a c →
    let C := fun t => w2CorrectedCenter (size S t) ⌊a t⌋₊
    let P := fun t => w2PrintedCenter (size S t) ⌊a t⌋₊
    InProbability S (fun t z => w2NormalizedGap S t z - C t) ∧
    InProbability S (fun t z => w2NormalizedGap S t z - P t) ∧
    (Tendsto (fun t => a t / Real.sqrt (size S t)) atTop (nhds 0) →
      Tendsto C atTop (nhds 1) ∧ Tendsto P atTop (nhds 1) ∧
      InProbability S (fun t z => w2NormalizedGap S t z - 1)) ∧
    (Tendsto (fun t => size S t / (a t) ^ 2) atTop (nhds 0) →
      Tendsto C atTop (nhds (-1)) ∧ Tendsto P atTop (nhds (-1)) ∧
      InProbability S (fun t z => w2NormalizedGap S t z - (-1))) ∧
    (∀ ell : ℝ, 0 < ell →
      Tendsto (fun t => a t / Real.sqrt (size S t)) atTop (nhds ell) →
      Tendsto C atTop (nhds (w2RatioCenter ell)) ∧
      Tendsto P atTop (nhds (w2RatioCenter ell)) ∧
      InProbability S (fun t z => w2NormalizedGap S t z - w2RatioCenter ell)) ∧
    ((∃ L U : ℝ, 0 < L ∧ 0 < U ∧
        ∀ᶠ t in atTop, L ≤ a t / Real.sqrt (size S t) ∧
          a t / Real.sqrt (size S t) ≤ U) →
      InProbability S (fun t z => w2NormalizedGap S t z -
        w2RatioCenter (a t / Real.sqrt (size S t))))) ∧
  (∀ ell : ℝ, 0 < ell → ∃ (S : Study) (a : ℕ → ℝ)
      (c : (t : ℕ) → Fin (S.N t) → ℝ),
    W2OneSourceModel S a c ∧ RegularSequence S 2 4 1 ∧
    Tendsto (fun t => a t / Real.sqrt (size S t)) atTop (nhds ell)) ∧
  (∀ ell : ℝ, 0 < ell →
    (0 < w2RatioCenter ell ↔ ell < 1) ∧
    (w2RatioCenter ell = 0 ↔ ell = 1) ∧
    (w2RatioCenter ell < 0 ↔ 1 < ell))

/-- Definition 9's internal average mixing coefficient, with the existing zero-power convention.
Zeroing the own coordinate represents deletion by an injective padding of the remaining vector. -/
def w2AlphaInt {n : ℕ} (E : Experiment n) (θ : ℝ) : ℝ :=
  ∑ i, mixPower (alpha E.design (fun z => z i) (maskedOthers E i)) θ

/-- Definition 9's extended moment order, including infinity for uniformly bounded variables. -/
abbrev W2MomentIndex := WithTop ℝ

/-- A finite moment bound, or essential boundedness at order infinity. -/
def W2MomentBound {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ)
    (k : ℝ) (r : W2MomentIndex) : Prop :=
  if r = ⊤ then ∀ z, 0 < P.mass z → |X z| ≤ k
  else mean P (fun z => Real.rpow |X z| (r.untopD 0)) ≤ Real.rpow k (r.untopD 0)

/-- An observed moment order with a uniform bound along the study. -/
def W2AdmissibleObserved (S : Study) (r : W2MomentIndex) : Prop :=
  2 ≤ r ∧ ∃ k > 0, ∀ t i, W2MomentBound (S.experiment t).design
    ((S.experiment t).outcome i) k r

/-- A potential moment order with a uniform bound along the study. -/
def W2AdmissiblePotential (S : Study) (r : W2MomentIndex) : Prop :=
  1 ≤ r ∧ ∃ k > 0, ∀ t i b, W2MomentBound (S.experiment t).design
    (potential (S.experiment t) i b) k r

/-- Attained maximal observed and potential moment orders, as in Definition 9. -/
def W2MaximalMoments (S : Study) (q s : W2MomentIndex) : Prop :=
  W2AdmissibleObserved S q ∧ (∀ r, W2AdmissibleObserved S r → r ≤ q) ∧
  W2AdmissiblePotential S s ∧ (∀ r, W2AdmissiblePotential S r → r ≤ s)

/-- The external exponent (q-2)/q, equal to one at the bounded-outcome order infinity. -/
def w2ExtExponent (q : W2MomentIndex) : ℝ :=
  if q = ⊤ then 1 else (q.untopD 0 - 2) / q.untopD 0

/-- All treatments equal a single Bernoulli(p) variable. Positive n distinguishes its two atoms. -/
def W2CommonAssignment {n : ℕ} (E : Experiment n) (p : ℝ) : Prop :=
  ∀ z, E.design.mass z =
    if z = (fun _ => true) then p else if z = (fun _ => false) then 1 - p else 0

/-- P009-T26; p. 688 (PDF p. 16), Remark 2, fourth sentence; Definition 9, p. 687.
No interference makes I and d diagonal, the masked other-treatment vector zero and the internal
mixing coefficient zero, so Assumption 6 holds. Standing regularity bounds every potential
outcome by k^(1+1/q) <= k^(3/2), supplies every finite moment order and attained infinite
maximal orders, and selects external exponent one. Under common Bernoulli(p) assignment,
the masked pair coefficient is alpha(T,T)=p(1-p), and the external coefficient at any specified
exponent theta is (n-1)[p(1-p)]^theta. For every exponent theta in [0,1] (the range of
(q-2)/q), its ratio to n tends to [p(1-p)]^theta > 0, it lies eventually between positive
multiples of n, and Assumption 5 fails. At exponent one p=1/2 gives (n-1)/4 and ratio to n/4
tending to one; p=1/3 gives 2(n-1)/9 and ratio tending to 8/9, hence no asymptotic
equivalence to n/4. -/
def T26WholeStatement : Prop :=
  (∀ {n : ℕ} (E : Experiment n), NoInterference E →
    (∀ i j, I E i j = (if i = j then 1 else 0) ∧
      d E i j = (if i = j then 1 else 0)) ∧
    (∀ i z, maskedOthers E i z = fun _ => false) ∧
    (∀ θ : ℝ, w2AlphaInt E θ = 0)) ∧
  (∀ (S : Study), (∀ t, NoInterference (S.experiment t)) →
    ∀ θ : ℝ, LittleO (fun t => w2AlphaInt (S.experiment t) θ) (size S)) ∧
  (∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (k q s : ℝ),
    Regular E k q s → NoInterference E →
    (∀ i z, |E.outcome i z| ≤ Real.rpow k (1 + 1 / q)) ∧
    Real.rpow k (1 + 1 / q) ≤ Real.rpow k (3 / 2) ∧
    (∀ i b z, |potential E i b z| ≤ Real.rpow k (3 / 2))) ∧
  (∀ (S : Study) (k q s : ℝ), RegularSequence S k q s →
    (∀ t, NoInterference (S.experiment t)) →
    (∀ r u : ℝ, 2 ≤ r → 1 ≤ u → RegularSequence S (Real.rpow k (3 / 2)) r u) ∧
    W2MaximalMoments S ⊤ ⊤ ∧ w2ExtExponent ⊤ = 1) ∧
  (∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (p : ℝ), 0 < p ∧ p < 1 →
    NoInterference E → W2CommonAssignment E p →
    (∀ i : Fin n, alpha E.design (fun z => z i) (fun z => z i) = p * (1 - p)) ∧
    (∀ i j : Fin n, i ≠ j → alpha E.design (masked E i) (masked E j) =
      alpha E.design (fun z => z i) (fun z => z i)) ∧
    (∀ θ : ℝ, alphaExt E θ = ((n : ℝ) - 1) * Real.rpow (p * (1 - p)) θ) ∧
    alphaExt E (w2ExtExponent ⊤) = ((n : ℝ) - 1) * p * (1 - p) ∧
    (p = 1 / 2 → alphaExt E 1 = ((n : ℝ) - 1) / 4) ∧
    (p = 1 / 3 → alphaExt E 1 = 2 * ((n : ℝ) - 1) / 9)) ∧
  (∀ (S : Study) (p : ℝ), 0 < p ∧ p < 1 →
    (∀ t, NoInterference (S.experiment t)) →
    (∀ t, W2CommonAssignment (S.experiment t) p) →
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      Tendsto (fun t => alphaExt (S.experiment t) θ / size S t)
        atTop (nhds (Real.rpow (p * (1 - p)) θ)) ∧
      0 < Real.rpow (p * (1 - p)) θ ∧
      (∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ᶠ t in atTop,
        l * size S t ≤ alphaExt (S.experiment t) θ ∧
          alphaExt (S.experiment t) θ ≤ u * size S t) ∧
      ¬ LittleO (fun t => alphaExt (S.experiment t) θ) (size S)) ∧
    (p = 1 / 2 → Tendsto (fun t => alphaExt (S.experiment t) 1 / (size S t / 4))
      atTop (nhds 1)) ∧
    (p = 1 / 3 →
      Tendsto (fun t => alphaExt (S.experiment t) 1 / (size S t / 4))
        atTop (nhds (8 / 9)) ∧
      ¬ Tendsto (fun t => alphaExt (S.experiment t) 1 / (size S t / 4))
        atTop (nhds 1))) ∧
  (∃ S : Study, RegularSequence S 3 2 1 ∧
    (∀ t, NoInterference (S.experiment t)) ∧
    (∀ t, W2CommonAssignment (S.experiment t) (1 / 3)) ∧
    LittleO (fun t => w2AlphaInt (S.experiment t) 1) (size S) ∧
    ¬ LittleO (fun t => alphaExt (S.experiment t) 1) (size S))

end
end SAP.P009b
