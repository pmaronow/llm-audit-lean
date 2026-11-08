import SAP.P009c.Defs.WholeW1
import SAP.P009c.Bridge
import AronowAudit.P009.P009_BernoulliCompletion
import AronowAudit.P009.P009_CompleteConditional
import AronowAudit.P009.Wave1.Gap.GP0091B2b
import AronowAudit.P009.Wave1.Gap.GLP0091B10
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P009c.WH.W1
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Stochastic order survives arbitrary changes on events of vanishing probability.
Proof route: for epsilon > 0, use the original stochastic-order bound at
epsilon/2 and eventual P(D) <= epsilon/2. Outside D the two tail events agree;
the finite union bound then gives the same cutoff K and the same rate a.
No bound on the new values on D, and no comparison between P(D) and a, is needed.
Expected proof size: 30–60 lines. Shared by T41, T43, T45 and T46. -/
def T41_L1 : Prop :=
  ∀ (S : Study) (X Y : (t : ℕ) → Assignment (S.N t) → ℝ)
    (a : ℕ → ℝ) (D : (t : ℕ) → Assignment (S.N t) → Prop),
    Tendsto (fun t => prob (S.experiment t).design (D t)) atTop (nhds 0) →
    (∀ t z, ¬ D t z → X t z = Y t z) →
    Op S X a → Op S Y a
/-- The probability that either of two real count functions is zero is at most
the sum of their normalized-count MSEs, for any positive real normalization.
Proof route: a zero count has normalized error from one of absolute value one.
Use probability_union_bound on the two zero-count events and apply
BernoulliCompletion.second_moment_tail at cutoff one to each error. The abstract
form needs no inverse marginal probabilities and no outcome assumptions.
Expected proof size: 25–60 lines. Shared by T41, T43, T45 and T46. -/
def T41_L2 : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (P : Law Ω) (U V : Ω → ℝ) (n : ℝ), 0 < n →
    prob P (fun z => U z = 0 ∨ V z = 0) ≤
      mean P (fun z => (U z / n - 1) ^ 2) +
      mean P (fun z => (V z / n - 1) ^ 2)
theorem extension_eq_hajek (S : Study)
    (H : (t : ℕ) → Assignment (S.N t) → ℝ) (hH : HajekExtension S H)
    (t : ℕ) (z : Assignment (S.N t)) (hz : ArmsNonempty (S.experiment t) z) :
    H t z = hajek (S.experiment t) z := by
  rw [hH t z hz]
  simp only [hajek, hz, ite_true]
  rfl
theorem inProbability_eventual_support_congr (S : Study)
    (X Y : (t : ℕ) → Assignment (S.N t) → ℝ)
    (h : ∀ᶠ t in atTop, ∀ z, 0 < (S.experiment t).design.mass z → X t z = Y t z) :
    InProbability S X ↔ InProbability S Y := by
  have heq (ε : ℝ) : ∀ᶠ t in atTop,
      prob (S.experiment t).design (fun z => ε < |X t z|) =
        prob (S.experiment t).design (fun z => ε < |Y t z|) := by
    filter_upwards [h] with t ht
    apply AronowAudit.P009.CompleteConditional.mean_support_congr
      (Bridge.toLaw (S.experiment t).design)
    intro z hz
    dsimp only
    simp only [ht z hz]
  constructor
  · intro hX ε hε
    exact (tendsto_congr' (heq ε)).mp (hX ε hε)
  · intro hY ε hε
    exact (tendsto_congr' (heq ε)).mpr (hY ε hε)

/-- The denominator guard and all arm counts survive outcome replacement
definitionally. Only eventual equality on the support is needed here. -/
theorem T40_assembly : T40WholeStatement := by
  intro S k hk hA hFail
  obtain ⟨y, hy⟩ := AronowAudit.P009.Wave1.unrestricted_inconsistency_zero_completion
    (Bridge.toStudy S) k hk hA hFail
  refine ⟨y, hy.1, hy.2.1, hy.2.2.1, ?_⟩
  let S' : Study := {S with experiment := fun t => {S.experiment t with outcome := y t}}
  intro hDomain H hH hConv
  apply hy.2.2.2
  apply (inProbability_eventual_support_congr S'
    (fun t z => hajek (S'.experiment t) z - eate (S'.experiment t))
    (fun t z => H t z - eate (S'.experiment t)) ?_).mpr hConv
  filter_upwards [hDomain] with t ht
  intro z hz
  have hArms : ArmsNonempty (S'.experiment t) z := ht z hz
  rw [extension_eq_hajek S' H hH t z hArms]

theorem mean_square_nonneg {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) :
    0 ≤ mean P (fun z => X z ^ 2) := by
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (P.nonneg z) (sq_nonneg _))

theorem empty_probability_zero_of_counts (h2 : T41_L2) (S : Study)
    (hCount : ∀ b : Bool, Tendsto (fun t => mean (S.experiment t).design
      (fun z => (nHat (S.experiment t) b z / size S t - 1) ^ 2)) atTop (nhds 0)) :
    Tendsto (fun t => prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z)) atTop (nhds 0) := by
  have hb (t : ℕ) : prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z) ≤
      mean (S.experiment t).design (fun z => (nHat (S.experiment t) true z / size S t - 1) ^ 2) +
      mean (S.experiment t).design (fun z => (nHat (S.experiment t) false z / size S t - 1) ^ 2) := by
    have hn : 0 < size S t := by
      dsimp only [size]
      exact_mod_cast S.positive t
    simpa only [ArmsNonempty, not_and_or, not_not] using
      h2 (Assignment (S.N t)) (S.experiment t).design
        (nHat (S.experiment t) true) (nHat (S.experiment t) false) (size S t) hn
  apply squeeze_zero
    (fun t => AronowAudit.P009.probability_nonnegative
      (Bridge.toLaw (S.experiment t).design) _)
    hb
  simpa only [add_zero, size] using (hCount true).add (hCount false)

/-- Rewrite the normalized count MSE as its variance using its exact mean one,
then apply the already proved Bernoulli count-variance bound. -/
theorem bernoulli_count_mse {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (b : Bool) :
    mean E.design (fun z => (nHat E b z / (n : ℝ) - 1) ^ 2) ≤ k / (n : ℝ) := by
  let A := Bridge.toExperiment E
  have hp (i : Fin n) : 0 < AronowAudit.P009.marginal A i b :=
    (AronowAudit.P009.BernoulliCompletion.regular_marginal_bounds A k q s hReg i b).2.2.1
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm : AronowAudit.P009.mean A.design
      (fun z => AronowAudit.P009.nHat A b z / (n : ℝ)) = 1 := by
    rw [AronowAudit.P009.mean_div, AronowAudit.P009.expected_arm_count A b hp,
      div_self hnR]
  change AronowAudit.P009.mean A.design
    (fun z => (AronowAudit.P009.nHat A b z / (n : ℝ) - 1) ^ 2) ≤ _
  calc
    _ = AronowAudit.P009.var A.design
        (fun z => AronowAudit.P009.nHat A b z / (n : ℝ)) := by
      simpa only [hm] using AronowAudit.P009.BernoulliCompletion.centered_square_mean
        A.design (fun z => AronowAudit.P009.nHat A b z / (n : ℝ))
    _ ≤ _ := AronowAudit.P009.BernoulliCompletion.count_variance_bound
      hn A k q s hReg hBER b

theorem bernoulli_empty_probability_zero (h2 : T41_L2) (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t)) :
    Tendsto (fun t => prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z)) atTop (nhds 0) := by
  have hN : Tendsto (size S) atTop atTop := tendsto_natCast_atTop_iff.mpr S.grows
  have hlim : Tendsto (fun t => k / size S t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hN
  apply empty_probability_zero_of_counts h2 S
  intro b
  exact squeeze_zero
    (fun t => mean_square_nonneg _ _)
    (fun t => bernoulli_count_mse (S.positive t) (S.experiment t) k q s
      (hReg t) (hBER t) b) hlim

theorem transfer_extension_claims (h1 : T41_L1) (S : Study)
    (H : (t : ℕ) → Assignment (S.N t) → ℝ) (θ a : ℕ → ℝ)
    (hH : HajekExtension S H)
    (hEmpty : Tendsto (fun t => prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z)) atTop (nhds 0))
    (ha : Tendsto a atTop (nhds 0)) (hBase : EstimatorClaims S θ a) :
    WholeEstimatorClaims S H θ a := by
  have hHJ : Op S (fun t z => H t z - θ t) a := by
    apply h1 S (fun t z => hajek (S.experiment t) z - θ t)
      (fun t z => H t z - θ t) a
      (fun t z => ¬ ArmsNonempty (S.experiment t) z) hEmpty
    · intro t z hz
      rw [extension_eq_hajek S H hH t z (not_not.mp hz)]
    · exact hBase.2.2.2
  exact ⟨⟨hBase.1, hBase.2.2.1⟩,
    AronowAudit.P009.BernoulliCompletion.probability_of_op_zero
      (Bridge.toStudy S) _ a ha hHJ, hHJ⟩

theorem T41_assembly (h1 : T41_L1) (h2 : T41_L2) : T41WholeStatement := by
  intro S k q s hReg hBER hRestricted H hH
  exact transfer_extension_claims h1 S H _ _ hH
    (bernoulli_empty_probability_zero h2 S k q s hReg hBER)
    (AronowAudit.P009.BernoulliCompletion.bernoulli_rate_zero
      (Bridge.toStudy S) hRestricted)
    (AronowAudit.P009.bernoulli_consistency (Bridge.toStudy S) k q s
      hReg hBER hRestricted)

theorem complete_empty_probability_zero (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hCR : CompleteSequence S) :
    Tendsto (fun t => prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z)) atTop (nhds 0) := by
  have hSupport := Bridge.complete_supportedArms S k q s hReg hCR
  have heq (t : ℕ) : prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z) = 0 := by
    calc
      _ = mean (S.experiment t).design (fun _ => 0) := by
        apply AronowAudit.P009.CompleteConditional.mean_support_congr
          (Bridge.toLaw (S.experiment t).design)
        intro z hz
        simp [hSupport t z hz]
      _ = 0 := AronowAudit.P009.mean_const (Bridge.toLaw (S.experiment t).design) 0
  simpa only [heq] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem T43_assembly (h1 : T41_L1) (h2 : T41_L2) : T43WholeStatement := by
  intro S k q s hReg hDesign hBound H hH
  have hEmpty : Tendsto (fun t => prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z)) atTop (nhds 0) := by
    rcases hDesign with hBER | hCR
    · exact bernoulli_empty_probability_zero h2 S k q s hReg hBER
    · exact complete_empty_probability_zero S k q s hReg hCR
  have hN : Tendsto (size S) atTop atTop := tendsto_natCast_atTop_iff.mpr S.grows
  have ha : Tendsto (fun t => 1 / Real.sqrt (size S t)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hN)
  exact transfer_extension_claims h1 S H _ _ hH hEmpty ha
    (AronowAudit.P009.Wave1.root_n_consistency_proof
      (Bridge.toStudy S) k q s hReg hDesign hBound)

/-- The existing arbitrary-design component estimates make both normalized
count MSEs vanish. The only new step here is squeezing by a constant times the
square of the already vanishing two-term rate. -/
theorem mixing_empty_probability_zero (h2 : T41_L2) (S : Study) (k : ℝ)
    (q s : MomentIndex) (hReg : RegularMix S k q s) (hRestricted : Restricted S)
    (hExt : LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S)) :
    Tendsto (fun t => prob (S.experiment t).design
      (fun z => ¬ ArmsNonempty (S.experiment t) z)) atTop (nhds 0) := by
  let A := Bridge.toStudy S
  have hlim : Tendsto (fun t => (8 * k ^ 4 + k ^ 2 + 1) *
      (AronowAudit.P009.Wave1.t45_rate A q t) ^ 2) atTop (nhds 0) := by
    simpa using ((AronowAudit.P009.Wave1.t45_rate_zero A q hRestricted hExt).pow 2).const_mul
      (8 * k ^ 4 + k ^ 2 + 1)
  apply empty_probability_zero_of_counts h2 S
  intro b
  exact squeeze_zero (fun t => mean_square_nonneg _ _)
    (fun t => (AronowAudit.P009.Wave1.t45_component_moments A k q s hReg t b).2) hlim

/-- Reassemble the existing HT and Hájek stochastic estimates and internal-bias
estimate at arbitrary admissible indices. No maximality premise is used. -/
theorem mixing_EATE_claims (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (hRestricted : Restricted S)
    (hExt : LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S))
    (hInt : LittleO (fun t => alphaInt (S.experiment t) (intExponent s)) (size S)) :
    EstimatorClaims S (fun t => eate (S.experiment t)) (fun t =>
      bernoulliRate S t +
      Real.sqrt (alphaExt (S.experiment t) (extExponent q)) / Real.sqrt (size S t) +
      alphaInt (S.experiment t) (intExponent s) / size S t) := by
  let A := Bridge.toStudy S
  let a := fun t => AronowAudit.P009.Wave1.t45_rate A q t +
    alphaInt (S.experiment t) (intExponent s) / size S t
  have hn (t : ℕ) : 0 < size S t := by
    dsimp only [size]
    exact_mod_cast S.positive t
  have hJ (t : ℕ) : 0 ≤ alphaInt (S.experiment t) (intExponent s) / size S t :=
    div_nonneg (AronowAudit.P009.Wave1.t45_alphaInt_nonneg
      (Bridge.toExperiment (S.experiment t)) _) (hn t).le
  have hRa (t : ℕ) : AronowAudit.P009.Wave1.t45_rate A q t ≤ a t :=
    le_add_of_nonneg_right (hJ t)
  have hlim : Tendsto a atTop (nhds 0) := by
    simpa only [a, add_zero] using
      (AronowAudit.P009.Wave1.t45_rate_zero A q hRestricted hExt).add hInt
  have hb (t : ℕ) : |adse (S.experiment t) - eate (S.experiment t)| ≤ 6 * k ^ 2 * a t := by
    calc
      _ ≤ 6 * k ^ 2 * alphaInt (S.experiment t) (intExponent s) / size S t :=
        AronowAudit.P009.Wave1.t45_internal_bias A k q s hReg t
      _ = 6 * k ^ 2 * (alphaInt (S.experiment t) (intExponent s) / size S t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (AronowAudit.P009.Wave1.t45_rate_pos A q t).le)
        (by positivity)
  have hRate : ∀ᶠ t in atTop, AronowAudit.P009.Wave1.t45_rate A q t ≤ 1 * a t :=
    Eventually.of_forall fun t => by simpa only [one_mul] using hRa t
  have hHTa : Op S (fun t z => ht (S.experiment t) z - adse (S.experiment t)) a :=
    AronowAudit.P009.BernoulliCompletion.op_change_rate A _ _ a 1 (by norm_num) hRate
      (AronowAudit.P009.Wave1.t45_ht_op A k q s hReg)
  have hHJa : Op S (fun t z => hajek (S.experiment t) z - adse (S.experiment t)) a :=
    AronowAudit.P009.BernoulliCompletion.op_change_rate A _ _ a 1 (by norm_num) hRate
      (AronowAudit.P009.Wave1.t45_hajek_op A k q s hReg hRestricted hExt)
  have hHT := AronowAudit.P009.Wave1.t45_op_recenter A (fun t z => ht (S.experiment t) z)
    (fun t => adse (S.experiment t)) (fun t => eate (S.experiment t)) a
    (6 * k ^ 2) (by positivity) hb hHTa
  have hHJ := AronowAudit.P009.Wave1.t45_op_recenter A (fun t z => hajek (S.experiment t) z)
    (fun t => adse (S.experiment t)) (fun t => eate (S.experiment t)) a
    (6 * k ^ 2) (by positivity) hb hHJa
  exact ⟨AronowAudit.P009.BernoulliCompletion.probability_of_op_zero A _ a hlim hHT,
    AronowAudit.P009.BernoulliCompletion.probability_of_op_zero A _ a hlim hHJ, hHT, hHJ⟩

theorem T45_assembly (h1 : T41_L1) (h2 : T41_L2) : T45WholeStatement := by
  intro S k q s hReg hRestricted hExt hInt H hH
  have ha : Tendsto (fun t => bernoulliRate S t +
      Real.sqrt (alphaExt (S.experiment t) (extExponent q)) / Real.sqrt (size S t) +
      alphaInt (S.experiment t) (intExponent s) / size S t) atTop (nhds 0) := by
    have hz : Tendsto (fun t => AronowAudit.P009.Wave1.t45_rate (Bridge.toStudy S) q t +
        alphaInt (S.experiment t) (intExponent s) / size S t) atTop (nhds 0) := by
      simpa only [add_zero] using
        (AronowAudit.P009.Wave1.t45_rate_zero (Bridge.toStudy S) q hRestricted hExt).add hInt
    exact hz
  exact transfer_extension_claims h1 S H _ _ hH
    (mixing_empty_probability_zero h2 S k q s hReg hRestricted hExt) ha
    (mixing_EATE_claims S k q s hReg hRestricted hExt hInt)

theorem T46_assembly (h1 : T41_L1) (h2 : T41_L2) : T46WholeStatement := by
  intro S k q s hReg hRestricted hExt H hH
  have ha := AronowAudit.P009.Wave1.t45_rate_zero (Bridge.toStudy S) q hRestricted hExt
  have hHT := AronowAudit.P009.Wave1.t45_ht_op (Bridge.toStudy S) k q s hReg
  have hHJ := AronowAudit.P009.Wave1.t45_hajek_op
    (Bridge.toStudy S) k q s hReg hRestricted hExt
  have hBase : EstimatorClaims S (fun t => adse (S.experiment t))
      (fun t => bernoulliRate S t +
        Real.sqrt (alphaExt (S.experiment t) (extExponent q)) / Real.sqrt (size S t)) :=
    ⟨AronowAudit.P009.BernoulliCompletion.probability_of_op_zero (Bridge.toStudy S) _ _ ha hHT,
      AronowAudit.P009.BernoulliCompletion.probability_of_op_zero (Bridge.toStudy S) _ _ ha hHJ,
      hHT, hHJ⟩
  exact transfer_extension_claims h1 S H _ _ hH
    (mixing_empty_probability_zero h2 S k q s hReg hRestricted hExt) ha hBase

end
end SAP.P009c.WH.W1
