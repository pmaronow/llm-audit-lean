import Mathlib
import SAP.P009b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P009b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A real statistic depends only on the coordinates in S. -/
def DependsOnW4 {n : ℕ} (f : Assignment n → ℝ) (S : Set (Fin n)) : Prop :=
  ∀ z z', (∀ i ∈ S, z i = z' i) → f z = f z'

/-- Independence of a collection of whole pairs from its joint complement,
expressed by factorization of arbitrary real statistics on the finite cube. -/
def PairBlockFactorizationW4 {n : ℕ} (E : Experiment n) (ρ : Pairing n) : Prop :=
  ∀ (S : Set (Fin n)), (∀ i, ρ.partner i ∈ S ↔ i ∈ S) →
    ∀ f g : Assignment n → ℝ, DependsOnW4 f S → DependsOnW4 g Sᶜ →
      mean E.design (fun z => f z * g z) = mean E.design f * mean E.design g

/-- Mutual independence of any finite family of disjoint collections of whole
pairs. Factorization for all real statistics includes joint event probabilities.
The empty family is included, with both sides equal to one. -/
def PairBlocksMutuallyIndependentW4 {n : ℕ} (E : Experiment n)
    (ρ : Pairing n) : Prop :=
  ∀ (m : ℕ) (S : Fin m → Set (Fin n)),
    (∀ a i, ρ.partner i ∈ S a ↔ i ∈ S a) →
    (∀ a b, a ≠ b → Disjoint (S a) (S b)) →
    ∀ f : Fin m → Assignment n → ℝ, (∀ a, DependsOnW4 (f a) (S a)) →
      mean E.design (fun z => ∏ a, f a z) = ∏ a, mean E.design (f a)

/-- The conditional minus unconditional mean of y_i(b; Z_{-i}).
The own coordinate is overwritten, so this is a function of the other assignments. -/
def potentialMeanShiftW4 {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) : ℝ :=
  cmean E.design (fun z => z i = b) (potential E i b) -
    mean E.design (potential E i b)

/-- The sum over the two treatment arms of absolute potential-mean shifts. -/
def twoArmShiftW4 {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ :=
  ∑ b : Bool, |potentialMeanShiftW4 E i b|

/-- The complete displayed proof chain of Lemma A17, with the stronger 2k
bound included before weakening to 2k². The full and masked potential outcomes
agree in T34WholeStatement_W4, so either gives exactly these summands. -/
def PairedBiasChainW4 {n : ℕ} (E : Experiment n) (ρ : Pairing n) (k : ℝ) : Prop :=
  let W := fun i => I E (ρ.partner i) i
  let B := twoArmShiftW4 E
  adse E - eate E =
      (∑ i, (potentialMeanShiftW4 E i true - potentialMeanShiftW4 E i false)) /
        (n : ℝ) ∧
  |adse E - eate E| ≤ (∑ i, (W i + (1 - W i)) * B i) / (n : ℝ) ∧
  (∑ i, (W i + (1 - W i)) * B i) / (n : ℝ) =
      (∑ i, W i * B i) / (n : ℝ) ∧
  (∑ i, W i * B i) / (n : ℝ) ≤ 2 * k * (∑ i, W i) / (n : ℝ) ∧
  2 * k * (∑ i, W i) / (n : ℝ) ≤ 2 * k ^ 2 * (∑ i, W i) / (n : ℝ) ∧
  2 * k ^ 2 * (∑ i, W i) / (n : ℝ) = 2 * k ^ 2 * (n : ℝ)⁻¹ * rSum E ρ ∧
  |adse E - eate E| ≤ 2 * k ^ 2 * (n : ℝ)⁻¹ * rSum E ρ

/-- P009-T34; Supplement A, p. 17, proof of Lemma A17, last display and the
sentence after it. Lemma A17: p. 16. Lemma A4: p. 3.
Under paired randomization and Assumption 1, full and masked outcomes agree.
Both treatment probabilities are one half; treatments in distinct pairs are
independent, whole pairs are mutually independent, and each own treatment is
independent of the joint vector outside its pair. Each absolute conditional
potential-mean shift equals half the difference between the two conditional
means, is at most its unconditional absolute first moment, and that moment is
at most k. Noninterfering-partner terms vanish. Moreover k ≥ 2 and the two-arm
sum is at most 2k ≤ 2k². The complete weighted proof chain gives the unchanged
Lemma A17 bound |ADSE − EATE| ≤ 2k² n⁻¹ R_SUM. The usual measure-theoretic
conditions are assumed and hold automatically on this finite assignment space.
The corrected independence assertion requires distinct units in different pairs;
the factorization assertions state the stronger joint independence actually used. -/
def T34WholeStatement_W4 : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (ρ : Pairing n), Paired E ρ →
    ∀ k q s : ℝ, Regular E k q s →
    (∀ i z, E.outcome i z = E.outcome i (masked E i z) ∧
      ∀ b, potential E i b z = potential E i b (maskedOthers E i z)) ∧
    (∀ i b, marginal E i b = 1 / 2) ∧
    (∀ z, 0 < E.design.mass z → ∀ i, z i = !(z (ρ.partner i))) ∧
    PairBlockFactorizationW4 E ρ ∧
    PairBlocksMutuallyIndependentW4 E ρ ∧
    (∀ i j : Fin n, i ≠ j → i ≠ ρ.partner j → ∀ a b : Bool,
      prob E.design (fun z => z i = a ∧ z j = b) =
        marginal E i a * marginal E j b) ∧
    (∀ (i : Fin n) (f : Assignment n → ℝ),
      DependsOnW4 f ({i, ρ.partner i} : Set (Fin n))ᶜ → ∀ b : Bool,
        mean E.design (fun z => (if z i = b then (1 : ℝ) else 0) * f z) =
          marginal E i b * mean E.design f) ∧
    (∀ (i : Fin n) (b : Bool),
      |potentialMeanShiftW4 E i b| =
        (1 / 2) * |cmean E.design (fun z => z i = b) (potential E i b) -
          cmean E.design (fun z => z i = !b) (potential E i b)| ∧
      |potentialMeanShiftW4 E i b| ≤ mean E.design (fun z => |potential E i b z|) ∧
      mean E.design (fun z => |potential E i b z|) ≤ k ∧
      (1 - I E (ρ.partner i) i) *
          cmean E.design (fun z => z i = b) (potential E i b) =
        (1 - I E (ρ.partner i) i) * mean E.design (potential E i b)) ∧
    2 ≤ k ∧ (∀ i, twoArmShiftW4 E i ≤ 2 * k) ∧ 2 * k ≤ 2 * k ^ 2 ∧
    PairedBiasChainW4 E ρ k

end
end SAP.P009b
