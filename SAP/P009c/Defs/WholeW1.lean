import Mathlib
import SAP.P009c.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c
open Filter
open scoped Topology
noncomputable section

/-- A real extension of Definition 6: on its nonzero-denominator domain it is
exactly the printed Hájek contrast. Values elsewhere are unrestricted. -/
def HajekExtension (S : Study)
    (H : (t : ℕ) → Assignment (S.N t) → ℝ) : Prop :=
  ∀ t z, ArmsNonempty (S.experiment t) z →
    H t z = size S t * muHat (S.experiment t) true z / nHat (S.experiment t) true z -
      size S t * muHat (S.experiment t) false z / nHat (S.experiment t) false z

/-- The printed ratios define random variables on the design support for all
sufficiently large populations. This is a denominator guard, not a consequence
of interior individual treatment probabilities for arbitrary designs. -/
def EventuallySupportedArms (S : Study) : Prop :=
  ∀ᶠ t in atTop, ∀ z, 0 < (S.experiment t).design.mass z →
    ArmsNonempty (S.experiment t) z

/-- Both consistency conclusions and both stochastic orders, using the specified
extension of the printed Hájek contrast. -/
def WholeEstimatorClaims (S : Study)
    (H : (t : ℕ) → Assignment (S.N t) → ℝ) (θ a : ℕ → ℝ) : Prop :=
  HTClaims S θ a ∧
    InProbability S (fun t z => H t z - θ t) ∧
    Op S (fun t z => H t z - θ t) a

/-- P009-T40; p. 683 (PDF p. 11); proof in Supplement A, Section 4, pp. 6–7.
For every growing study with uniformly interior treatment marginals and failure
of restricted interference, replacement potential outcomes satisfy Assumption 1,
preserve the same positive interference-density limsup, and make HT inconsistent
for EATE, with designs and population sizes unchanged. Whenever the printed Hájek
ratios exist on the support eventually, the same replacement makes every real
extension of that contrast inconsistent for EATE as well.
-/
def T40WholeStatement : Prop :=
  ∀ (S : Study) (k : ℝ), 0 < k →
    (∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
      marginal (S.experiment t) i true ≤ 1 - k⁻¹) →
    ¬ Restricted S →
    ∃ y : (t : ℕ) → Fin (S.N t) → Assignment (S.N t) → ℝ,
      let S' : Study := {S with experiment := fun t => {S.experiment t with outcome := y t}}
      (∃ K q s, RegularSequence S' K q s) ∧
      (∃ L > 0,
        HasLimsup (fun t => dAvg (S.experiment t) / size S t) L ∧
        HasLimsup (fun t => dAvg (S'.experiment t) / size S' t) L) ∧
      (¬ InProbability S' (fun t z => ht (S'.experiment t) z - eate (S'.experiment t))) ∧
      (EventuallySupportedArms S →
        ∀ H : (t : ℕ) → Assignment (S'.N t) → ℝ, HajekExtension S' H →
          ¬ InProbability S' (fun t z => H t z - eate (S'.experiment t)))

/-- P009-T41; p. 684 (PDF p. 12); proof in Supplement A, Section 5, pp. 7–9.
Under Assumption 1, Bernoulli randomization and restricted interference, HT and
every real extension of the printed Hájek contrast are consistent for EATE and
both have stochastic order sqrt(d_AVG)/sqrt(n). Thus the conclusions do not
depend on values assigned when a treatment arm is empty.
-/
def T41WholeStatement : Prop :=
  ∀ (S : Study) (k q s : ℝ), RegularSequence S k q s →
    (∀ t, Bernoulli (S.experiment t)) → Restricted S →
    ∀ H : (t : ℕ) → Assignment (S.N t) → ℝ, HajekExtension S H →
      WholeEstimatorClaims S H (fun t => eate (S.experiment t)) (bernoulliRate S)

/-- P009-T43; p. 685 (PDF p. 13); proof in Supplement A, Section 7, p. 16.
Under Assumption 1, Bernoulli or complete randomization and bounded average
interference dependence, HT and every real extension of the printed Hájek
contrast are consistent for EATE and both have stochastic order 1/sqrt(n).
-/
def T43WholeStatement : Prop :=
  ∀ (S : Study) (k q s : ℝ), RegularSequence S k q s →
    ((∀ t, Bernoulli (S.experiment t)) ∨ CompleteSequence S) →
    BigO (fun t => dAvg (S.experiment t)) (fun _ => 1) →
    ∀ H : (t : ℕ) → Assignment (S.N t) → ℝ, HajekExtension S H →
      WholeEstimatorClaims S H (fun t => eate (S.experiment t))
        (fun t => 1 / Real.sqrt (size S t))

/-- P009-T45; p. 688 (PDF p. 16); proof in Supplement A, Section 9, pp. 18–22.
Under Assumption 1, restricted interference, design mixing and design separation,
HT and every real extension of the printed Hájek contrast are consistent for EATE
and both have stochastic order sqrt(d_AVG)/sqrt(n) + sqrt(alpha_EXT)/sqrt(n) +
alpha_INT/n. The result holds for every admissible observed and potential moment
index, including infinity, and hence for the maximal indices of Definition 9
whenever those maxima exist. No attainment assumption is needed.
-/
def T45WholeStatement : Prop :=
  ∀ (S : Study) (k : ℝ) (q s : MomentIndex), RegularMix S k q s → Restricted S →
    LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S) →
    LittleO (fun t => alphaInt (S.experiment t) (intExponent s)) (size S) →
    ∀ H : (t : ℕ) → Assignment (S.N t) → ℝ, HajekExtension S H →
      WholeEstimatorClaims S H (fun t => eate (S.experiment t))
        (fun t => bernoulliRate S t +
          Real.sqrt (alphaExt (S.experiment t) (extExponent q)) / Real.sqrt (size S t) +
          alphaInt (S.experiment t) (intExponent s) / size S t)

/-- P009-T46; p. 689 (PDF p. 17); proof in Supplement A, Section 10, pp. 22–24.
Under Assumption 1, restricted interference and design mixing, HT and every real
extension of the printed Hájek contrast are consistent for ADSE and both have
stochastic order sqrt(d_AVG)/sqrt(n) + sqrt(alpha_EXT)/sqrt(n). The result holds
for every admissible observed and potential moment index, including infinity,
and therefore includes every defined maximal-index choice of Definition 9.
Design separation is not assumed.
-/
def T46WholeStatement : Prop :=
  ∀ (S : Study) (k : ℝ) (q s : MomentIndex), RegularMix S k q s → Restricted S →
    LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S) →
    ∀ H : (t : ℕ) → Assignment (S.N t) → ℝ, HajekExtension S H →
      WholeEstimatorClaims S H (fun t => adse (S.experiment t))
        (fun t => bernoulliRate S t +
          Real.sqrt (alphaExt (S.experiment t) (extExponent q)) / Real.sqrt (size S t))

end
end SAP.P009c
