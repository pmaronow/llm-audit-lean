import AronowAudit.P018.P018_Audit
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.Fin.Rev

/-! Identical repetitions, reversal, and equality of joint laws. -/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
open scoped symmDiff
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Reversal identities for repeated records. -/

def concentrated_repetitions_flip {N : ℕ} (d : Dyad N) : Dyad N :=
  ⟨(members d).image Fin.rev, by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, by
      rw [Finset.card_image_of_injective _ Fin.rev_injective, members_card]⟩⟩

@[simp] theorem concentrated_repetitions_flip_flip {N : ℕ} (d : Dyad N) :
    concentrated_repetitions_flip (concentrated_repetitions_flip d) = d := by
  apply Subtype.ext
  simp [concentrated_repetitions_flip, members, Finset.image_image, Function.comp_def]

def concentrated_repetitions_flipEquiv (N : ℕ) : Equiv.Perm (Dyad N) where
  toFun := concentrated_repetitions_flip
  invFun := concentrated_repetitions_flip
  left_inv := concentrated_repetitions_flip_flip
  right_inv := concentrated_repetitions_flip_flip

theorem concentrated_repetitions_sum_flip {N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Dyad N → A) :
    (∑ d, f (concentrated_repetitions_flip d)) = ∑ d, f d :=
  Equiv.sum_comp (concentrated_repetitions_flipEquiv N) f

theorem concentrated_repetitions_first_flip {N : ℕ} (d : Dyad N) :
    firstUnit (concentrated_repetitions_flip d) = (secondUnit d).rev := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_image.mpr ⟨secondUnit d, Finset.max'_mem _ _, rfl⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Fin.rev_le_rev.mpr (Finset.le_max' _ i hi)

theorem concentrated_repetitions_second_flip {N : ℕ} (d : Dyad N) :
    secondUnit (concentrated_repetitions_flip d) = (firstUnit d).rev := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_image.mpr ⟨firstUnit d, Finset.min'_mem _ _, rfl⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Fin.rev_le_rev.mpr (Finset.min'_le _ i hi)

theorem concentrated_repetitions_overlap_flip {N : ℕ} (d f : Dyad N) :
    overlap (concentrated_repetitions_flip d) (concentrated_repetitions_flip f) ↔
      overlap d f := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hi).1
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hi).2
    have hjk : j = k := Fin.rev_injective (hji.trans hki.symm)
    exact ⟨j, Finset.mem_inter.mpr ⟨hj, hjk.symm ▸ hk⟩⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.rev, Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨i, (Finset.mem_inter.mp hi).1, rfl⟩,
       Finset.mem_image.mpr ⟨i, (Finset.mem_inter.mp hi).2, rfl⟩⟩⟩

def concentrated_repetitions_reverse {N : ℕ} (ω : Fin N → Bool) : Fin N → Bool :=
  fun i => ω i.rev

theorem concentrated_repetitions_response_reverse {N : ℕ}
    (ω : Fin N → Bool) (d : Dyad N) :
    response signKernel (concentrated_repetitions_reverse ω) d =
      response signKernel ω (concentrated_repetitions_flip d) := by
  simp only [response, signKernel, concentrated_repetitions_reverse,
    concentrated_repetitions_first_flip, concentrated_repetitions_second_flip]
  exact add_comm _ _

def concentrated_repetitions_countWeight {N : ℕ} (d : Dyad N) : ℝ :=
  (concentratedRepeated.T N d : ℝ)

theorem concentrated_repetitions_weight_flip {N : ℕ} (d : Dyad N) :
    concentrated_repetitions_countWeight d =
      (2 : ℝ) ^ (2*N+2) * concentratedWeight (concentrated_repetitions_flip d) := by
  have hi : (firstUnit d).val < N := (firstUnit d).isLt
  have hj : (secondUnit d).val < N := (secondUnit d).isLt
  have hsum : ((firstUnit d).rev.val : ℤ) + (secondUnit d).rev.val +
      (firstUnit d).val + (secondUnit d).val + 2 = 2*(N : ℤ) := by
    simp only [Fin.val_rev]
    omega
  have hexp : ((2*N+2 : ℕ) : ℤ) -
      ((secondUnit d).rev.val + (firstUnit d).rev.val + 2 : ℤ) =
      ((firstUnit d).val + (secondUnit d).val + 2 : ℕ) := by
    push_cast
    omega
  simp only [concentrated_repetitions_countWeight, concentratedRepeated,
    Nat.cast_pow, Nat.cast_ofNat, concentratedWeight,
    concentrated_repetitions_first_flip, concentrated_repetitions_second_flip]
  calc
    (2 : ℝ) ^ ((firstUnit d).val + (secondUnit d).val + 2) =
        (2 : ℝ) ^ (((2*N+2 : ℕ) : ℤ) -
          ((secondUnit d).rev.val + (firstUnit d).rev.val + 2 : ℤ)) := by
      rw [hexp, zpow_natCast]
    _ = _ := by rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_natCast]

/-- Reduction of all repeated records, including the fitted block scores. -/
theorem concentrated_repetitions_record_reduction {N : ℕ} (ω : Fin N → Bool) :
    repeatedOLS concentratedRepeated ω =
      weightedOLS signKernel concentrated_repetitions_countWeight ω ∧
    repeatedVariance concentratedRepeated ω =
      weightedVariance signKernel concentrated_repetitions_countWeight ω := by
  have hg : repeatedGram concentratedRepeated ω =
      weightedGram signKernel concentrated_repetitions_countWeight ω := by
    ext a b
    change (∑ d : Dyad N, ∑ _ : Fin (concentratedRepeated.T N d),
      outer (![1] : Vec 1) ![1]) a b = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
    simp [weightedGram, concentrated_repetitions_countWeight, design, signKernel]
  have hn : (∑ d : Dyad N, ∑ t,
      score (repeatedX concentratedRepeated ω d t) (repeatedY concentratedRepeated ω d t)) =
      ∑ d, score (design signKernel ω d)
        (concentrated_repetitions_countWeight d * response signKernel ω d) := by
    apply Finset.sum_congr rfl
    intro d hd
    change (∑ _ : Fin (concentratedRepeated.T N d),
      score (![1] : Vec 1) (signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)))) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ext a
    simp [concentrated_repetitions_countWeight, design, response, signKernel,
      score, nsmul_eq_mul, mul_add]
  have hb : repeatedOLS concentratedRepeated ω =
      weightedOLS signKernel concentrated_repetitions_countWeight ω := by
    simp only [repeatedOLS, weightedOLS, hg, hn]
  refine ⟨hb, ?_⟩
  have hs : repeatedBlockScore concentratedRepeated (repeatedOLS concentratedRepeated ω) ω =
      fun d => score (design signKernel ω d) (concentrated_repetitions_countWeight d *
        (response signKernel ω d - dot (design signKernel ω d)
          (weightedOLS signKernel concentrated_repetitions_countWeight ω))) := by
    funext d
    change (∑ _ : Fin (concentratedRepeated.T N d),
      score (![1] : Vec 1) ((signValue (ω (firstUnit d)) + signValue (ω (secondUnit d))) -
        dot ![1] (repeatedOLS concentratedRepeated ω))) = _
    rw [hb]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ext a
    simp [concentrated_repetitions_countWeight, design, response, signKernel,
      score, nsmul_eq_mul, mul_sub, mul_add]
  simp only [repeatedVariance, weightedVariance, hg, hs]

/-- The total inverse rule gives scale invariance even at singular samples,
without a scalar-rank side condition. -/
theorem concentrated_repetitions_scale_total {N : ℕ} (w : Dyad N → ℝ)
    (ω : Fin N → Bool) (a : ℝ) (ha : a ≠ 0) :
    weightedOLS signKernel (fun d => a*w d) ω = weightedOLS signKernel w ω ∧
    weightedVariance signKernel (fun d => a*w d) ω = weightedVariance signKernel w ω := by
  have hg : weightedGram signKernel (fun d => a*w d) ω =
      a • weightedGram signKernel w ω := by
    simp [weightedGram, Finset.smul_sum, mul_smul]
  have hi : (weightedGram signKernel (fun d => a*w d) ω)⁻¹ =
      a⁻¹ • (weightedGram signKernel w ω)⁻¹ := by
    rw [hg, matrix_inverse_scale_total _ a ha]
  have hn : (∑ d, score (design signKernel ω d) (a*w d*response signKernel ω d)) =
      a • (∑ d, score (design signKernel ω d) (w d*response signKernel ω d)) := by
    ext b
    simp [score, Finset.mul_sum, mul_assoc]
  have hb : weightedOLS signKernel (fun d => a*w d) ω = weightedOLS signKernel w ω := by
    simp only [weightedOLS, hi, hn, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    rw [mul_inv_cancel₀ ha, one_smul]
  refine ⟨hb, ?_⟩
  simp only [weightedVariance, hi, hb]
  have hs : (fun d => score (design signKernel ω d)
      (a*w d*(response signKernel ω d-dot (design signKernel ω d) (weightedOLS signKernel w ω)))) =
      fun d => a • score (design signKernel ω d)
        (w d*(response signKernel ω d-dot (design signKernel ω d) (weightedOLS signKernel w ω))) := by
    ext d b
    simp [score, mul_assoc]
  rw [hs, meat_scale]
  exact sandwich_scale_invariance a ha _ _

theorem concentrated_repetitions_meat_flip {N k : ℕ} (q : Dyad N → Vec k) :
    meat members (fun d => q (concentrated_repetitions_flip d)) = meat members q := by
  let H : Dyad N → Dyad N → Mat k := fun d f =>
    if overlap d f then outer (q d) (q f) else 0
  calc
    _ = ∑ d, ∑ f, H (concentrated_repetitions_flip d)
        (concentrated_repetitions_flip f) := by
      unfold meat
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      change (if overlap d f then _ else _) = (if overlap (concentrated_repetitions_flip d) (concentrated_repetitions_flip f) then _ else _)
      simp only [concentrated_repetitions_overlap_flip]
    _ = ∑ d, ∑ f, H (concentrated_repetitions_flip d) f := by
      apply Finset.sum_congr rfl
      intro d hd
      exact concentrated_repetitions_sum_flip _
    _ = ∑ d, ∑ f, H d f := concentrated_repetitions_sum_flip (fun d => ∑ f, H d f)
    _ = meat members q := rfl

theorem concentrated_repetitions_relabel {N : ℕ} (w : Dyad N → ℝ)
    (ω : Fin N → Bool) :
    weightedOLS signKernel (fun d => w (concentrated_repetitions_flip d)) ω =
      weightedOLS signKernel w (concentrated_repetitions_reverse ω) ∧
    weightedVariance signKernel (fun d => w (concentrated_repetitions_flip d)) ω =
      weightedVariance signKernel w (concentrated_repetitions_reverse ω) := by
  let rω := concentrated_repetitions_reverse ω
  have hg : weightedGram signKernel (fun d => w (concentrated_repetitions_flip d)) ω =
      weightedGram signKernel w rω := by
    simpa only [weightedGram, design, signKernel] using
      (concentrated_repetitions_sum_flip
        (fun d : Dyad N => w d • outer (![1] : Vec 1) ![1]))
  have hn : (∑ d, score (design signKernel ω d)
      (w (concentrated_repetitions_flip d) * response signKernel ω d)) =
      ∑ d, score (design signKernel rω d) (w d * response signKernel rω d) := by
    simpa only [rω, concentrated_repetitions_response_reverse,
      concentrated_repetitions_flip_flip, response, signKernel, concentrated_repetitions_reverse,
      concentrated_repetitions_first_flip, concentrated_repetitions_second_flip, Fin.rev_rev, add_comm, design] using
      (concentrated_repetitions_sum_flip (fun d : Dyad N =>
        score (design signKernel rω d) (w d * response signKernel rω d)))
  have hb : weightedOLS signKernel (fun d => w (concentrated_repetitions_flip d)) ω =
      weightedOLS signKernel w rω := by
    simp only [weightedOLS, hg, hn]
  refine ⟨hb, ?_⟩
  let q : Dyad N → Vec 1 := fun d => score (design signKernel rω d)
    (w d * (response signKernel rω d - dot (design signKernel rω d)
      (weightedOLS signKernel w rω)))
  have hs : (fun d => score (design signKernel ω d)
      (w (concentrated_repetitions_flip d) * (response signKernel ω d -
        dot (design signKernel ω d)
          (weightedOLS signKernel (fun d => w (concentrated_repetitions_flip d)) ω)))) =
      fun d => q (concentrated_repetitions_flip d) := by
    ext d a
    dsimp only [q]
    rw [hb]
    simp only [rω, response, signKernel, concentrated_repetitions_reverse,
      concentrated_repetitions_first_flip, concentrated_repetitions_second_flip,
      Fin.rev_rev, add_comm, design]
  simp only [weightedVariance, hg, hs, concentrated_repetitions_meat_flip]
  rfl

theorem concentrated_repetitions_pair_identity {N : ℕ} (ω : Fin N → Bool) :
    (repeatedOLS concentratedRepeated ω, repeatedVariance concentratedRepeated ω) =
      (weightedOLS signKernel concentratedWeight (concentrated_repetitions_reverse ω),
       weightedVariance signKernel concentratedWeight (concentrated_repetitions_reverse ω)) := by
  have hw : (concentrated_repetitions_countWeight : Dyad N → ℝ) =
      fun d => (2 : ℝ) ^ (2*N+2) * concentratedWeight (concentrated_repetitions_flip d) := by
    funext d
    exact concentrated_repetitions_weight_flip d
  obtain ⟨hb, hv⟩ := concentrated_repetitions_record_reduction ω
  rw [hw] at hb hv
  obtain ⟨hsb, hsv⟩ := concentrated_repetitions_scale_total
    (fun d => concentratedWeight (concentrated_repetitions_flip d)) ω
    ((2 : ℝ) ^ (2*N+2)) (pow_ne_zero _ (by norm_num))
  obtain ⟨hrb, hrv⟩ := concentrated_repetitions_relabel concentratedWeight ω
  exact Prod.ext (hb.trans (hsb.trans hrb)) (hv.trans (hsv.trans hrv))

theorem concentrated_repetitions_reverse_preserving (N : ℕ) :
    MeasurePreserving (@concentrated_repetitions_reverse N)
      (unitSampleLaw signKernel N) (unitSampleLaw signKernel N) := by
  letI : IsProbabilityMeasure fairLaw := by
    unfold fairLaw
    infer_instance
  have he : (@concentrated_repetitions_reverse N) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin N => Bool) (Fin.revPerm : Equiv.Perm (Fin N)) := by
    funext ω i
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin N => Bool) (Fin.revPerm : Equiv.Perm (Fin N)) ω i.rev
    simpa only [Fin.revPerm_apply, Fin.rev_rev, concentrated_repetitions_reverse] using h.symm
  rw [he]
  simpa only [unitSampleLaw, signKernel] using
    (measurePreserving_piCongrLeft (fun _ : Fin N => fairLaw)
      (Fin.revPerm : Equiv.Perm (Fin N)))

theorem concentrated_repetitions_counterexample_proof (N : ℕ) (hN : 2 ≤ N) :
    IdentDistrib (fun ω => (weightedOLS signKernel concentratedWeight ω,
      weightedVariance signKernel concentratedWeight ω))
      (fun ω => (repeatedOLS concentratedRepeated ω, repeatedVariance concentratedRepeated ω))
      (unitSampleLaw signKernel N) (repeatedLaw concentratedRepeated N) := by
  classical
  let F : (Fin N → Bool) → Vec 1 × Mat 1 := fun ω =>
    (weightedOLS signKernel concentratedWeight ω, weightedVariance signKernel concentratedWeight ω)
  let R : (Fin N → Bool) → Vec 1 × Mat 1 := fun ω =>
    (repeatedOLS concentratedRepeated ω, repeatedVariance concentratedRepeated ω)
  have hF : Measurable F := measurable_of_finite F
  have hR : Measurable R := measurable_of_finite R
  have hpair : R = F ∘ concentrated_repetitions_reverse := by
    funext ω
    exact concentrated_repetitions_pair_identity ω
  have hlaw : repeatedLaw concentratedRepeated N = unitSampleLaw signKernel N := rfl
  rw [hlaw]
  refine ⟨hF.aemeasurable, hR.aemeasurable, ?_⟩
  change (unitSampleLaw signKernel N).map F = (unitSampleLaw signKernel N).map R
  rw [hpair, ← Measure.map_map hF (concentrated_repetitions_reverse_preserving N).measurable,
    (concentrated_repetitions_reverse_preserving N).map_eq]

end AronowAudit.P018.Wave1
