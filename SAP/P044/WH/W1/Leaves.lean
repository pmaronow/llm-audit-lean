import SAP.P044.Defs.WholeW1
import SAP.P044.Bridge
import AronowAudit.P044.Wave1.Gap.GP044B3
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P044.WH.W1
open Finset Bridge
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000
/-- The matching graph is loopless, symmetric, and has no isolates; its 2(n+2)
profiles are distinct and each pair shares its treatment and exposure.
Prove by identifying the two vertices with each quotient `i.val / 2`, using
`finProdFinEquiv` for the two profile coordinates. The only neighbor is the
other vertex of that pair, so the exposure is d11 or d00 as asserted.
Recover the first profile coordinate from vertex 0 and the second from the
unique treated ordinary pair to prove injectivity. The contrast is zero by
identical potential outcomes. Expected size: 100-180 lines. -/
def T2_L1 : Prop := ∀ n : ℕ, W1MatchingGeometry n
/-- Exact marginals of the uniform matching design: 1/2 on the distinguished
pair and 1/(n+2) on each ordinary pair, with complementary d00 probabilities.
Both contrasted exposures have positive support, including at n=0.
Given the geometry, replace exposure events by treatment events and transport
the sum through `finProdFinEquiv`. Sum first over Fin 2, then over Fin (n+2),
using the single selected ordinary index; use n+2>0 for all divisions.
Expected size: 80-140 lines. -/
def T2_L2 : Prop :=
  ∀ n : ℕ, W1MatchingGeometry n → W1MatchingMarginals n
/-- Smoothed exhaustive-bank inputs, invariant under arbitrary bank ordering.
Distinguished marginals are (n+3)/(2n+5); their off-diagonal same-exposure
joints are (n+2)/(2n+5); their cross-exposure joints vanish. All four joints
between a distinguished and an ordinary vertex are positive: counts are 1
for ordinary d11 and n+1 for ordinary d00. Diagonal inputs equal marginals.
Use `Equiv.sum_comp` (or a filter-card equivalence) for permutation invariance,
and the two-coordinate sum from L2 for the mixed counts. General positivity
and diagonal equality follow directly from `smoothedWeight`, `smoothedJoint`.
Expected size: 150-250 lines. -/
def T2_L3 : Prop :=
  ∀ n : ℕ, W1MatchingGeometry n → W1MatchingMarginals n → W1MatchingInputs n
/-- Point-estimator reduction for the matching witness: only vertices 0 and 1
contribute. Both receive d11 together or d00 together, so the HT contrast is
plus or minus 2/(Nw), for every bank order and every observed profile.
Use `Finset.sum_subset` or two `Finset.sum_eq_single` reductions to discard
zero outcomes, and the distinguished marginal formula from L3.
Expected size: 50-100 lines. -/
def T2_L4 : Prop :=
  ∀ n : ℕ, W1MatchingGeometry n → W1MatchingInputs n → W1MatchingPointwise n
/-- Within-exposure S7 reduction. The two distinguished diagonal terms give
2(1/w²-1/w), their two off-diagonal terms give 2(1/w²-1/q), and only one of
the two exposures occurs. Mixed structural-zero adjustments vanish because
their joint inputs are strictly positive; ordinary-only terms have zero
outcomes. Split the ordered double sum by i.val<2 and j.val<2, use L3, and
sum the four remaining terms. Expected size: 120-220 lines. -/
def T2_L5 : Prop :=
  ∀ n : ℕ, W1MatchingGeometry n → W1MatchingInputs n → W1MatchingWithin n
/-- Cross-exposure S7 reduction, including the diagonal. All four ordered
distinguished pairs have zero k,l input, and each contributes -1/(2w), so
the covariance estimate is -2/w. Mixed pairs have positive joint input and
zero product; ordinary-only adjustments vanish. The same four-pair sum as
L5 proves this. Expected size: 100-180 lines. -/
def T2_L6 : Prop :=
  ∀ n : ℕ, W1MatchingGeometry n → W1MatchingInputs n → W1MatchingCross n
/-- A uniform random permutation sends a fixed element to a uniform element.
No empty-type case is hidden: `a : α` supplies nonemptiness. Prove that the
sum of g(e a) over permutations is independent of a, by reindexing with
right composition by a transposition. Sum this identity over a, interchange
the two finite sums, and use `e.sum_comp`; divide by the two positive finite
cardinalities. This avoids factorial counting. Expected size: 50-100 lines. -/
def T2_L7 : Prop := W1UniformFirstLaw
/-- Evaluate the two joint-law moments from the pointwise reductions.
L1 and L2 give a balanced sign at the distinguished pair. L4 gives mean zero
and constant square 4/(N²w²). L5-L6 give the constant variance estimate
(4/w²+2/w-2/q)/N². Use finite product-sum factorization for the independent
law and L7 for the first-row law. Subtract and simplify with `field_simp`
and `ring`; the common shortfall is
-2(2n+5)/((n+2)(n+3)N²), strictly negative for every n:ℕ.
All probability laws are normalized by the elementary assembly below;
the leaf may also prove their normalization directly from `w1Uniform`.
Expected size: 120-220 lines. -/
def T2_L8 : Prop :=
  ∀ n : ℕ, W1MatchingGeometry n → W1MatchingMarginals n →
    W1MatchingPointwise n → W1MatchingWithin n → W1MatchingCross n →
    W1UniformFirstLaw → W1MatchingMoments n
/-- Definitional transport uses the established equivalence of exposure labels. -/
macro "w1_transport " t:term : tactic =>
  `(tactic| (have transported := $t
             try simp [Bool.forall_bool] at transported ⊢
             all_goals (convert @transported using 0 <;> rfl)))
private theorem uniform_pos {α : Type} [Fintype α] [Nonempty α] (a : α) :
    0 < w1Uniform a := by
  unfold w1Uniform
  positivity
private theorem uniform_total {α : Type} [Fintype α] [Nonempty α] :
    (∑ a : α, w1Uniform a) = 1 := by
  simp [w1Uniform, Fintype.card_ne_zero]
private theorem matching_sampling (n : ℕ) (hg : W1MatchingGeometry n)
    (hf : W1UniformFirstLaw) : W1MatchingSampling n := by
  have : Nonempty (Fin (w1MatchingR n)) := ⟨w1MatchingFirst n⟩
  refine ⟨fun e => hg.2.2.1.comp e.injective, fun e => e.surjective,
    uniform_pos, uniform_total, uniform_pos, uniform_total, ?_, ?_, ?_, ?_⟩
  · intro x
    exact mul_pos (uniform_pos x.1) (uniform_pos x.2)
  · unfold w1MatchingIndependentMass
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, uniform_total, mul_one]
    exact uniform_total
  · intro s
    unfold w1MatchingIndependentMass
    change (∑ e, w1Uniform e * w1Uniform s) = w1Uniform s
    rw [← Finset.sum_mul, uniform_total, one_mul]
  · intro s
    have h := hf (w1MatchingFirst n) (fun r => if r = s then (1 : ℚ) else 0)
    simpa [expect, mul_ite] using h
private theorem error_transfer : W1ErrorTransfer := by
  intro Ω B D N _ _ _ hN P J hm f y a b hab ha hb w q hw hq hd
  dsimp only
  have h0 : expect P.mass
      (varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b) -
      designVariance P.mass (htContrast f y (marginal P.mass f) a b) =
      zeroSurplus y (joint P.mass f) a b :=
    AronowAudit.P044.exact_variance_surplus hN (toDesign P) f y a b hab ha hb
  have hn : 0 ≤ zeroSurplus y (joint P.mass f) a b :=
    AronowAudit.P044.zeroSurplus_nonneg y (joint P.mass f) a b
  have marginal_expect (g : Ω → ℝ) :
      expect J.mass (fun x => g x.2) = expect P.mass g := by
    unfold expect
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hm]
  have he := marginal_expect
    (varianceEstimate f y (marginal P.mass f) (joint P.mass f) a b)
  have hsub (u v : B × Ω → ℝ) :
      expect J.mass (fun x => u x - v x) = expect J.mass u - expect J.mass v := by
    simp only [expect, mul_sub, Finset.sum_sub_distrib]
  constructor
  · rw [hsub, he]
    linarith
  · intro εV εT hεV hεT hV hT
    rw [hsub, he] at hV
    have hVl := (abs_le.mp hV).1
    have hTu := (abs_le.mp hT).2
    linarith
/-- Assemble the exact theorem, finite-bank witnesses, and error qualification. -/
theorem T2_assembly (h1 : T2_L1) (h2 : T2_L2) (h3 : T2_L3) (h4 : T2_L4)
    (h5 : T2_L5) (h6 : T2_L6) (h7 : T2_L7) (h8 : T2_L8) : T2WholeStatement := by
  refine ⟨?_, ?_, by norm_num [w1MatchingR], by norm_num [w1MatchingN], error_transfer⟩
  · constructor
    · intro Ω D N _ _ hN P f y a b hab ha hb
      exact ⟨AronowAudit.P044.exact_variance_surplus hN (toDesign P) f y a b hab ha hb,
        AronowAudit.P044.exact_variance_conservative hN (toDesign P) f y a b hab ha hb⟩
    · intro included
      w1_transport (AronowAudit.P044.Wave1.clique_joint_moments_proof.2.2.2.2.2.2 included).1
  · intro n
    have hg := h1 n
    have hm := h2 n hg
    have hi := h3 n hg hm
    exact ⟨hg, hm, hi, matching_sampling n hg h7,
      h8 n hg hm (h4 n hg hi) (h5 n hg hi) (h6 n hg hi) h7⟩
private theorem restricted_T3 : T3Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := AronowAudit.P044.star_counterexample
    w1_transport And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1
      (And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 h.2.2.2.2.2.1))))
  · w1_transport AronowAudit.P044.star_design_verified
  · intro T
    w1_transport AronowAudit.P044.star_nonidentification
      (fun z d y => T z (fun i => labels.symm (d i)) y)
  · dsimp only
    intro hpos
    w1_transport AronowAudit.P044.star_counterexample.2.2.2.2.2.2
/-- The new finite table and observed-denominator check are kernel computations;
the already proved nonidentification and moment results supply the other clauses. -/
theorem T3_assembly : T3WholeStatement := by
  have ht : (fun r => exposure starAdj (starAssignments r)) =
      ![![.d01,.d00,.d10,.d10], ![.d01,.d10,.d00,.d10],
        ![.d01,.d10,.d10,.d00], ![.d11,.d01,.d01,.d11],
        ![.d11,.d01,.d11,.d01], ![.d11,.d11,.d01,.d01]] := by
    decide +kernel
  have hp : ∀ r i a, exposure starAdj (starAssignments r) i = a →
      0 < marginal (fun _ : Fin 6 => (1/6 : ℚ))
        (fun r => exposure starAdj (starAssignments r)) i a := by
    decide +kernel
  refine ⟨restricted_T3, ht, ⟨hp, restricted_T3.2.2.2 hp⟩, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
private theorem restricted_T7 : T7Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · w1_transport AronowAudit.P044.cycle8_smoothing_counterexample
  · w1_transport AronowAudit.P044.cycle8_profile_counts
  · w1_transport AronowAudit.P044.cycle8_contrast_biases
  · have h := AronowAudit.P044.cycle8_contrast_biases.2 (0 : Fin 8)
    have h1 : AronowAudit.P044.tau AronowAudit.P044.cycle8Y .d10 .d00 = 1/2 := by
      linarith [h.2.1, h.2.2.2.2.1]
    have h2 : AronowAudit.P044.tau AronowAudit.P044.cycle8Y .d01 .d00 = 1/4 := by
      linarith [h.2.2.1, h.2.2.2.2.2]
    w1_transport And.intro h1 h2
  · dsimp only
    have hm := AronowAudit.P044.cycle8_smoothing_counterexample.2.2.2.2.2.2.2.1
    have hp := AronowAudit.P044.cycle8_smoothing_counterexample.2.2.2.1
    have he : ∀ r,
        AronowAudit.P044.htContrast
          (fun r => AronowAudit.P044.exposure AronowAudit.P044.cycle8Adj (AronowAudit.P044.cycle8Assignments r))
          AronowAudit.P044.cycle8Y
          (AronowAudit.P044.marginal (fun _ : Fin 8 => (1/8 : ℚ))
            (fun r => AronowAudit.P044.exposure AronowAudit.P044.cycle8Adj (AronowAudit.P044.cycle8Assignments r)))
          .d11 .d00 r = 1 ∧
        AronowAudit.P044.htContrast
          (fun r => AronowAudit.P044.exposure AronowAudit.P044.cycle8Adj (AronowAudit.P044.cycle8Assignments r))
          AronowAudit.P044.cycle8Y
          (AronowAudit.P044.marginal (fun _ : Fin 8 => (1/8 : ℚ))
            (fun r => AronowAudit.P044.exposure AronowAudit.P044.cycle8Adj (AronowAudit.P044.cycle8Assignments r)))
          .d10 .d00 r = 1/2 ∧
        AronowAudit.P044.htContrast
          (fun r => AronowAudit.P044.exposure AronowAudit.P044.cycle8Adj (AronowAudit.P044.cycle8Assignments r))
          AronowAudit.P044.cycle8Y
          (AronowAudit.P044.marginal (fun _ : Fin 8 => (1/8 : ℚ))
            (fun r => AronowAudit.P044.exposure AronowAudit.P044.cycle8Adj (AronowAudit.P044.cycle8Assignments r)))
          .d01 .d00 r = 1/4 := by
      intro r
      dsimp only [AronowAudit.P044.htContrast]
      rw [hm r .d11, hm r .d10, hm r .d01, hm r .d00]
      norm_num [AronowAudit.P044.cycle8Y]
    have hs : ∀ i a, 0 < AronowAudit.P044.marginal (fun _ : Fin 8 => (1/8 : ℚ))
        (fun r => AronowAudit.P044.exposure AronowAudit.P044.cycle8Adj (AronowAudit.P044.cycle8Assignments r)) i a := by
      intro i a
      rw [hp i a]
      cases a <;> norm_num
    w1_transport And.intro he hs
/-- All missing cycle clauses are finite exact calculations. -/
theorem T7_assembly : T7WholeStatement := by
  refine ⟨restricted_T7, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro a
    simp [cycle8Y]
private theorem restricted_T9 : T9Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact @AronowAudit.P044.interference_iff_not
  · exact @AronowAudit.P044.noInterference_iff_same_own
  · exact @AronowAudit.P044.peerCount_is_count
  · exact @AronowAudit.P044.peerCount_own_independent
  · w1_transport @AronowAudit.P044.exposure_cases
  · intro N i z
    funext j
    by_cases hj : j = i <;> simp [insertOwn, hj]
private theorem ordered_noInterference {n : ℕ}
    (y : Fin (n + 1) → Assignment (n + 1) → ℝ) :
    w1OrderedNoInterference y ↔ NoInterference y := by
  constructor
  · intro h i a u v
    have ht := h i a (fun j => u (finSuccAboveOrderIso i j))
      (fun j => v (finSuccAboveOrderIso i j))
    simpa [w1InsertOwn] using ht
  · intro h i a u v
    exact h i a _ _
private theorem ordered_interference {n : ℕ}
    (y : Fin (n + 1) → Assignment (n + 1) → ℝ) :
    w1OrderedInterference y ↔ ¬ w1OrderedNoInterference y := by
  classical
  simp only [w1OrderedInterference, w1OrderedNoInterference, not_forall]
/-- Ordered coordinates are an order-isomorphic presentation of the existing
subtype coordinates. Matrix multiplication and the Boolean cases finish the
syntactic and four-condition repairs, including the singleton-population case. -/
theorem T9_assembly : T9WholeStatement := by
  refine ⟨restricted_T9, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i z
    funext j
    by_cases hj : j = i
    · subst j
      simp [w1InsertOwn, insertOwn]
    · simp [w1InsertOwn, insertOwn, hj, w1DeleteOwn]
  · intro n y
    have hn := ordered_noInterference y
    have hc := ordered_interference y
    refine ⟨hn, ?_, hc, hn.trans (restricted_T9.2.1 y)⟩
    rw [hc, hn, ← restricted_T9.1 y]
  · intro N
    simp only [w1MatrixComposable, iff_self, true_and]
    omega
  · intro N A z i
    refine ⟨rfl, ?_⟩
    apply Finset.sum_congr rfl
    intro j _
    cases A i j <;> cases z j <;> simp [w1Bit]
  · intro N A z i
    have he : ∀ d, w1ExposurePredicate A z i d ↔ exposure A z i = d := by
      intro d
      by_cases hp : 0 < peerCount A z i
      · have hz : peerCount A z i ≠ 0 := Nat.ne_of_gt hp
        cases hzi : z i <;> cases d <;>
          simp [w1ExposurePredicate, exposure, w1Bit, hzi, hp, hz]
      · have hz : peerCount A z i = 0 := Nat.eq_zero_of_not_pos hp
        cases hzi : z i <;> cases d <;>
          simp [w1ExposurePredicate, exposure, w1Bit, hzi, hz]
    refine ⟨he, ?_, rfl⟩
    exact ⟨exposure A z i, (he _).mpr rfl, fun d hd => ((he d).mp hd).symm⟩
end
end SAP.P044.WH.W1
