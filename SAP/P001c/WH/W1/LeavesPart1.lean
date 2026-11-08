import SAP.P001c.Defs.WholeW1
import SAP.P001c.Bridge
import AronowAudit.P001.Wave1.Gap.TailA.CDFDelta

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W1

universe u

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical

noncomputable section

/-- Recover the L2 objects needed for BLP orthogonality from the convention that
every candidate squared loss is integrable. Choose zero coefficients to get Y in
L2, and a single unit slope to get Y-X_k in L2 and hence X_k in L2. Each residual
is L2 directly from its integrable square. About 50–90 lines; no rank assumption. -/
def T49_L1 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ) (X : Ω → Fin K → ℝ) (Y : Ω → ℝ),
    (∀ k, Measurable (fun ω => X ω k)) → Measurable Y →
    finiteAffineLosses μ X Y →
    (∀ k, MemLp (fun ω => X ω k) 2 μ) ∧
    (∀ b : Fin (K+1) → ℝ, MemLp (affineResidual X Y b) 2 μ)

/-- Directional orthogonality at a quadratic-risk minimum. Expand the integrable
square of R-tD, obtaining E[R²]-2t E[DR]+t² E[D²]. Its derivative at its global
minimum t=0 vanishes (IsLocalMin.hasDerivAt_eq_zero). MemLp.integrable_mul justifies
each integral. Alternatively choose a small t of the sign of E[DR]. About 60–100
lines, including zero directions; independence and positive variance are unnecessary. -/
def T49_L2 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R D : Ω → ℝ), MemLp R 2 μ → MemLp D 2 μ →
    (∀ t : ℝ, expectation μ (fun ω => (R ω)^2) ≤
      expectation μ (fun ω => (R ω - t * D ω)^2)) →
    expectation μ (fun ω => D ω * R ω) = 0

theorem T49_assembly (h1 : T49_L1.{u}) (h2 : T49_L2.{u}) : T49WholeStatement.{u} := by
  constructor
  · intro K b x
    refine ⟨by simp [affinePredictor], ?_⟩
    intro k
    have hd := AronowAudit.P001.linear_predictor_partial_derivative b x k
    exact ⟨(AronowAudit.P001.linear_predictor_coordinate_increment b x k).1,
      hd.1, hd.2⟩
  · intro Ω mΩ μ pμ K X Y hX hY hfin b hmin
    obtain ⟨hX2, hR2⟩ := h1 Ω μ K X Y hX hY hfin
    have hmean : expectation μ (affineResidual X Y b) = 0 := by
      have hdir := h2 Ω μ (affineResidual X Y b) (fun _ => 1) (hR2 b)
        (memLp_const 1) (fun t => ?_)
      · simpa only [one_mul] using hdir
      · let c : Fin (K+1) → ℝ := Function.update b 0 (b 0+t)
        have heq : affineResidual X Y c =
            fun ω => affineResidual X Y b ω - t * (1 : ℝ) := by
          funext ω
          simp [c, affineResidual, affinePredictor, Fin.succ_ne_zero]
          ring
        simpa only [heq] using hmin c
    refine ⟨hmean, ?_⟩
    intro k
    have hprod : expectation μ (fun ω => X ω k * affineResidual X Y b ω) = 0 := by
      apply h2 Ω μ (affineResidual X Y b) (fun ω => X ω k) (hR2 b) (hX2 k)
      intro t
      let c : Fin (K+1) → ℝ := fun j => b j + if j = k.succ then t else 0
      have heq : affineResidual X Y c =
          fun ω => affineResidual X Y b ω - t * X ω k := by
        funext ω
        simp [c, affineResidual, affinePredictor, add_mul, Finset.sum_add_distrib,
          Fin.succ_inj, Ne.symm (Fin.succ_ne_zero k)]
        ring
      simpa only [heq] using hmin c
    refine ⟨hprod, ?_⟩
    rw [covariance_eq_sub (hX2 k) (hR2 b)]
    change expectation μ (fun ω => X ω k * affineResidual X Y b ω) -
      expectation μ (fun ω => X ω k) * expectation μ (affineResidual X Y b) = 0
    rw [hprod, hmean]
    ring

private theorem good_bad_complement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (c ε : ℝ) : probability μ {ω | ε ≤ dist (Z ω) c} =
      1 - probability μ {ω | |Z ω-c| < ε} := by
  have hs : MeasurableSet {ω | |Z ω-c| < ε} := by
    exact measurableSet_lt ((hZ.sub_const c).abs) measurable_const
  have he : {ω | ε ≤ dist (Z ω) c} = {ω | |Z ω-c| < ε}ᶜ := by
    ext ω
    simp [Real.dist_eq]
  rw [he]
  exact probReal_compl_eq_one_sub hs

theorem T51_assembly : T51WholeStatement := by
  constructor
  · intro Ω mΩ μ pμ Z hZ c
    constructor
    · constructor
      · intro h ε hε
        have ht := (h ε hε).const_sub 1
        simp_rw [good_bad_complement μ (Z _) (hZ _) c ε] at ht
        simpa only [sub_sub_cancel, sub_zero] using ht
      · intro h ε hε
        have ht := (h ε hε).const_sub 1
        simpa only [sub_self, good_bad_complement μ (Z _) (hZ _) c ε] using ht
    · exact AronowAudit.P001.probability_convergence_eventual_levels μ Z hZ c
  · have : IsProbabilityMeasure endpointLaw := by
      unfold endpointLaw
      infer_instance
    have hmeas (n : ℕ) : Measurable (endpointSequence n) := measurable_of_countable _
    have hcp : convergesInProbability endpointLaw endpointSequence 0 := by
      apply tendstoInMeasure_iff_measureReal_dist.mp
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hmeas n).aestronglyMeasurable)
      apply Eventually.of_forall
      intro k
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop k] with n hn
      simp [endpointSequence, ne_of_lt hn]
    have hprob (n : ℕ) :
        probability endpointLaw {k | |endpointSequence n k| < 1/2} =
          1 - (1/2 : ℝ)^(n+1) := by
      have hs : {k | |endpointSequence n k| < 1/2} = ({n} : Set ℕ)ᶜ := by
        ext k
        by_cases hk : k = n
        · simp [endpointSequence, hk]
          norm_num
        · simp [endpointSequence, hk]
      rw [hs]
      change endpointLaw.real {n}ᶜ = _
      rw [probReal_compl_eq_one_sub (measurableSet_singleton n)]
      congr 1
      change (geometricMeasure ⟨1/2, by norm_num, by norm_num⟩).real {n} = _
      rw [geometricMeasure_real_singleton (by
        intro h
        have hh := congrArg Subtype.val h
        norm_num at hh)]
      norm_num
      rw [pow_succ]
    have hlt (n : ℕ) : probability endpointLaw {k | |endpointSequence n k| < 1/2} < 1 := by
      rw [hprob]
      have hp : 0 < (1/2 : ℝ)^(n+1) := pow_pos (by norm_num) _
      linarith
    refine ⟨inferInstance, hmeas, hcp, fun n => ⟨hprob n, hlt n⟩, ?_⟩
    rintro ⟨N, hN⟩
    exact (not_le_of_gt (hlt N)) (hN N le_rfl)


end
end SAP.P001c.WH.W1
