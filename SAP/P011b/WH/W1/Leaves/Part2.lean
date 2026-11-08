import SAP.P011b.WH.W1.Leaves.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

/-- One-block distribution: prove independence of the three actual leaf coordinates
by pushing forward independent uniform Fin 4 draws. Count the eight binary leaf
patterns, and sum over the independent Fin 48 centre draw. For each pattern its
probability is positive; divide the joint centre/leaf probability by that probability.
Use star_center_sum and star_leaves_mean. The two conditional ranges follow by
checking the eight patterns. This conditions on observed leaves, not latent draws. -/
def T15_L1 : Prop := W1StarBlockLaw

/-- Independent identically distributed blocks: rewrite the uniform source law as
a finite product using star_uniform_pi. Each extracted block depends only on its own
source coordinate. Push forward iIndepFun_pi, and use measurePreserving_eval to
identify every block marginal with the one-block law. The positive K premise and
Fin K block index exclude an empty observation case. -/
def T15_L2 : Prop := W1StarIID

/-- Transfer to the domain of the printed interval. Since n V1 tends in probability
to 3/16, the event V1<0 is contained in {|n V1-3/16|>3/32}, so its probability tends
to zero. The clipped and domain-restricted coverage events agree where V1≥0.
Bound the difference of their real probabilities by Pr(V1<0), using the measurable
polynomial estimator, then transfer star_counterexample_proof's coverage limit. -/
def T15_L3 : Prop := W1StarCoverageDomain

/-- The new one-block law, iid-block and interval-domain leaves extend the proved
star counterexample. The finite design and mean-offset calculations are already proved. -/
theorem T15_assembly (h1 : T15_L1) (h2 : T15_L2) (h3 : T15_L3) :
    T15WholeStatement := by
  refine ⟨star_existing, star_design_facts, h1, h2, star_offsets, h3, ?_⟩
  intro u A hA
  have he (k : ℕ) (y : Fin ((starFamily u).size k) → ℝ) :
      A k y = ((starFamily u).model k).G :=
    (AronowAudit.P011.Wave1.star_compatible u (k+1) (A k y)).mp (hA k y).1
  refine ⟨he, ?_⟩
  have hl : InProbability (starFamily u) (scaledOracle (starFamily u))
      (fun _ => if u then 53/192 else 3/16) := AronowAudit.P011.Wave1.star_limit u
  simp_rw [he]
  exact hl

/-- The canonical necessity clause is refuted by the unforced lower-star regression.
Only existing stochastic results and the elementary feasible-empty-graph bound are used. -/
theorem T16_assembly : T16WholeStatement := by
  classical
  have hfinite (k : ℕ) :
      MeanModel (w1UnforcedFamily.model k) (w1StarD false (k+1)) (w1StarB false) ∧
      ((w1StarD false (k+1))ᵀ * w1StarD false (k+1)).det ≠ 0 ∧
      (∀ i, (w1UnforcedFamily.model k).theta i = olsTheta (w1StarD false (k+1)) 0 i) ∧
      (∀ y, betaHat (w1UnforcedFamily.model k) y = ols (w1StarD false (k+1)) y 0) ∧
      beta (w1UnforcedFamily.model k) = 3/8 ∧
      scaledTrue w1UnforcedFamily k = 27/128 ∧
      meanBias (w1UnforcedFamily.model k) = -3/128 ∧
      meanVariance (w1UnforcedFamily.model k) = 3/16 ∧
      meanSpread (w1UnforcedFamily.model k) = 3/64 ∧
      Compatible (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
        (emptyGraph (w1UnforcedFamily.size k)) ∧
      (∀ y, (w1UnforcedFamily.size k : ℝ)*
        V1 (emptyGraph (w1UnforcedFamily.size k)) (weighted (w1UnforcedFamily.model k) y) =
          sampleVariance (weighted (w1UnforcedFamily.model k) y)) := by
    have hd := star_design_facts false (k+1) (by omega)
    refine ⟨(AronowAudit.P011.block_ols_representations.2 false (k+1) (by omega)).1,
      hd.2.2.1, (fun i => (hd.2.2.2.1 i).symm), hd.2.2.2.2,
      AronowAudit.P011.Wave1.star_beta false (k+1) (by omega),
      AronowAudit.P011.Wave1.star_scaledTrue false k,
      AronowAudit.P011.Wave1.star_meanBias false (k+1) (by omega),
      (unforced_moments (k+1) (by omega)).1,
      (unforced_moments (k+1) (by omega)).2, (unforced_empty k).1, (unforced_empty k).2⟩
  have hex : ∃ A : ∀ k, (Fin (w1UnforcedFamily.size k) → ℝ) → Graph (w1UnforcedFamily.size k),
      ∀ k y, Maximizes (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
        (fun B => V1 B (weighted (w1UnforcedFamily.model k) y)) (A k y) := by
    have hm (k : ℕ) (y : Fin (w1UnforcedFamily.size k) → ℝ) :
        ∃ A, Maximizes (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
          (fun B => V1 B (weighted (w1UnforcedFamily.model k) y)) A :=
      (AronowAudit.P011.oracle_sharp_bound _ _ _ (unforced_valid k)
        (fun B => V1 B (weighted (w1UnforcedFamily.model k) y))).1
    exact ⟨fun k y => Classical.choose (hm k y), fun k y => Classical.choose_spec (hm k y)⟩
  have hb (k : ℕ) : meanBias (w1UnforcedFamily.model k) = -3/128 :=
    AronowAudit.P011.Wave1.star_meanBias false (k+1) (by omega)
  have hlim : Filter.liminf (fun k => meanBias (w1UnforcedFamily.model k)) atTop = -3/128 := by
    simp_rw [hb]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-3/128 : ℝ)) atTop (𝓝 (-3/128))).liminf_eq
  refine ⟨unforced_scaling, unforced_valid, hfinite, unforced_sample_limit, hex,
    unforced_max_conservative, hlim, ?_⟩
  intro hnecessity
  have hh := hnecessity w1UnforcedFamily 1 3 (27/128) 2 unforced_scaling unforced_valid
    (fun k => w1StarD false (k+1)) (w1StarB false)
    (fun k => (hfinite k).2.1) (fun k => (hfinite k).1)
    (fun k => (hfinite k).2.2.1) unforced_max_conservative
  rw [hlim] at hh
  norm_num at hh

/-- Exact factor algebra, the existing auxiliary theorem, and the explicit
alternating-mean witness fill all clauses without any unproved leaf. -/
theorem T19_assembly : T19WholeStatement := by
  refine ⟨?_, AronowAudit.P011.Wave1.alternating_counterexample_proof.1,
    AronowAudit.P011.Wave1.alternating_counterexample_proof.2.1,
    alternating_details.1, alternating_details.2, ?_⟩
  · intro F c1 c2 c3 c4 h hs hp
    have ha : T19Statement F c1 c2 c3 c4 h hs hp :=
      AronowAudit.P011.auxiliary_corrected_display (Bridge.toFamily F) c1 c2 c3 c4 h hs hp
    refine ⟨ha, auxiliary_factor_facts F c1 c2 c3 c4 h hs hp, ?_⟩
    intro hmean
    apply ha.2.2
    have he (k : ℕ) : meanSpread (F.model k) = 0 := by
      simp [meanSpread, delta, hmean]
    simp_rw [he]
    exact tendsto_const_nhds
  · have hv (k : ℕ) (y : Fin (w1AlternatingFamily.size k) → ℝ) :
        V2star (w1AlternatingFamily.model k) y =
        V2 (w1AlternatingFamily.model k).G (weighted (w1AlternatingFamily.model k) y) :=
      AronowAudit.P011.auxiliary_empty_identity
        (Bridge.toModel (w1AlternatingFamily.model k)) rfl y
    simp_rw [hv]
    have hh : Tendsto (fun k => probability (w1AlternatingFamily.model k)
        {y | |((k : ℝ)+1)*V2 (w1AlternatingFamily.model k).G
          (weighted (w1AlternatingFamily.model k) y) - scaledTrue w1AlternatingFamily k| > 1/2})
        atTop (𝓝 1) := AronowAudit.P011.Wave1.alternating_counterexample_proof.2.2.2.2.1
    simpa only [w1AlternatingFamily, Nat.cast_add, Nat.cast_one] using hh


end
end SAP.P011b.WH.W1
