import AronowAudit.P018.P018_Audit
import Mathlib.Probability.Independence.Basic

/-!
Repeated and record-weighted finite target corrections using a common
finite projection argument.
-/

noncomputable section
namespace AronowAudit.P018.Wave1

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Common finite projection helpers, followed by the repeated theorem. -/

private theorem repeatedCorrection_endpoints_ne {N : ℕ} (d : Dyad N) :
    firstUnit d ≠ secondUnit d := by
  intro heq
  have hcard : (members d).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply le_antisymm
    · calc
        a ≤ secondUnit d := Finset.le_max' (members d) a ha
        _ = firstUnit d := heq.symm
        _ ≤ b := Finset.min'_le (members d) b hb
    · calc
        b ≤ secondUnit d := Finset.le_max' (members d) b hb
        _ = firstUnit d := heq.symm
        _ ≤ a := Finset.min'_le (members d) a ha
  rw [members_card] at hcard
  omega

/-- An ordered choice of the two endpoints still has the product unit law.
No symmetry of the record kernel is used. -/
private theorem repeatedCorrection_pair_preserving {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} (d : Dyad N) :
    MeasurePreserving (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d)))
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
  have hind : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ : Fin N => μ)) := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => id)
        (fun _ => measurable_id.aemeasurable))
  have hpair := hind.indepFun (repeatedCorrection_endpoints_ne d)
  refine ⟨(measurable_pi_apply (firstUnit d)).prodMk
    (measurable_pi_apply (secondUnit d)), ?_⟩
  rw [hpair.map_prod_eq_prod_map_map
    (measurable_pi_apply (firstUnit d)).aemeasurable
    (measurable_pi_apply (secondUnit d)).aemeasurable]
  rw [(measurePreserving_eval (fun _ : Fin N => μ) (firstUnit d)).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) (secondUnit d)).map_eq]

/-- All evaluated record coordinates are essentially bounded; the exceptional
set of the original pair bound is transported through its actual pair law. -/
private theorem repeatedCorrection_record_memLp {U : Type*} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k) (hR : RepeatedAtSize R N) :
    (∀ d t a, MemLp (fun ω : Fin N → U => repeatedX R ω d t a) ∞
      (repeatedLaw R N)) ∧
    (∀ d t, MemLp (fun ω : Fin N → U => repeatedY R ω d t) ∞
      (repeatedLaw R N)) := by
  letI : IsProbabilityMeasure R.μ := hR.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    dsimp only [repeatedLaw]
    infer_instance
  obtain ⟨C, hC, hbound⟩ := hR.2.2.2
  have hmeas (d : Dyad N) (t : Fin (R.T N d)) :
      Measurable (fun ω : Fin N → U => repeatedX R ω d t) ∧
      Measurable (fun ω : Fin N → U => repeatedY R ω d t) := by
    have hp : Measurable (fun ω : Fin N → U =>
        (ω (firstUnit d), ω (secondUnit d))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact ⟨(hR.2.2.1 d t).1.comp hp, (hR.2.2.1 d t).2.comp hp⟩
  have hbound' (d : Dyad N) (t : Fin (R.T N d)) :
      ∀ᵐ ω ∂ repeatedLaw R N,
        ‖repeatedX R ω d t‖ ≤ C ∧ |repeatedY R ω d t| ≤ C := by
    exact (repeatedCorrection_pair_preserving R.μ d).quasiMeasurePreserving.tendsto_ae
      (hbound d t)
  constructor
  · intro d t a
    apply MemLp.of_bound ((measurable_pi_apply a).comp (hmeas d t).1).aestronglyMeasurable C
    filter_upwards [hbound' d t] with ω hω
    exact (norm_le_pi_norm (repeatedX R ω d t) a).trans hω.1
  · intro d t
    apply MemLp.of_bound (hmeas d t).2.aestronglyMeasurable C
    filter_upwards [hbound' d t] with ω hω
    simpa only [Real.norm_eq_abs] using hω.2

/-- Signed deterministic record weights preserve essential boundedness of
the two finite normal-equation sums. -/
private theorem repeatedCorrection_weighted_memLp {U : Type*} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k) (hR : RepeatedAtSize R N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) :
    (∀ a b, MemLp (fun ω : Fin N → U => recordWeightedGram R w ω a b) ∞
      (repeatedLaw R N)) ∧
    (∀ a, MemLp (fun ω : Fin N → U => recordWeightedXY R w ω a) ∞
      (repeatedLaw R N)) := by
  classical
  obtain ⟨hX, hY⟩ := repeatedCorrection_record_memLp R hR
  constructor
  · intro a b
    have hterm (d : Dyad N) (t : Fin (R.T N d)) :
        MemLp (fun ω : Fin N → U =>
          w d t * (repeatedX R ω d t a * repeatedX R ω d t b)) ∞
          (repeatedLaw R N) :=
      ((hX d t a).fun_mul (hX d t b)).const_mul (w d t)
    simpa only [recordWeightedGram, Matrix.sum_apply, Matrix.smul_apply,
      outer, Matrix.of_apply, smul_eq_mul] using
      (memLp_finsetSum (univ : Finset (Dyad N)) (fun d _ =>
        memLp_finsetSum (univ : Finset (Fin (R.T N d))) (fun t _ => hterm d t)))
  · intro a
    have hterm (d : Dyad N) (t : Fin (R.T N d)) :
        MemLp (fun ω : Fin N → U =>
          (w d t * repeatedY R ω d t) * repeatedX R ω d t a) ∞
          (repeatedLaw R N) :=
      ((hY d t).const_mul (w d t)).fun_mul (hX d t a)
    simpa only [recordWeightedXY, Finset.sum_apply, score, Pi.smul_apply,
      smul_eq_mul] using
      (memLp_finsetSum (univ : Finset (Dyad N)) (fun d _ =>
        memLp_finsetSum (univ : Finset (Fin (R.T N d))) (fun t _ => hterm d t)))

private theorem repeatedCorrection_weighted_symmetric {U : Type*} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) :
    (recordWeightedGram R w ω).transpose = recordWeightedGram R w ω := by
  classical
  ext a b
  simp only [Matrix.transpose_apply, recordWeightedGram, Matrix.sum_apply,
    Matrix.smul_apply, outer, Matrix.of_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- The population residual score is centered only after summing the
records.  Individual block-score means need not be zero. -/
private theorem repeatedCorrection_score_expansion {U : Type*} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (ω : Fin N → U) :
    (∑ d : Dyad N, recordWeightedBlockScore R w β ω d) =
      recordWeightedXY R w ω - (recordWeightedGram R w ω).mulVec β := by
  classical
  have hnormal :
      (∑ d : Dyad N, ∑ t : Fin (R.T N d),
        score (repeatedX R ω d t) (w d t * dot (repeatedX R ω d t) β)) =
      (recordWeightedGram R w ω).mulVec β := by
    simp only [recordWeightedGram, Matrix.sum_mulVec]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro t ht
    ext a
    simp only [score, Pi.smul_apply, smul_eq_mul, dot,
      Matrix.mulVec, dotProduct, Matrix.smul_apply, outer, Matrix.of_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [← hnormal]
  ext a
  simp only [recordWeightedBlockScore, recordWeightedXY, score,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.sub_apply,
    mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- Entrywise expectation of a finite matrix-vector product. -/
private theorem repeatedCorrection_mean_mulVec {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (G : Ω → Mat k)
    (hG : ∀ a b, MemLp (fun ω => G ω a b) ∞ μ) (β : Vec k) :
    meanVec μ (fun ω => (G ω).mulVec β) = (meanMat μ G).mulVec β := by
  classical
  ext a
  simp only [meanVec, meanMat, Matrix.mulVec, dotProduct]
  rw [integral_finsetSum _ (fun b _ =>
    ((hG a b).integrable (by simp)).mul_const (β b))]
  simp only [integral_mul_const]

/-- Finite projection algebra with a general nonzero normalization.  The
only random inputs are the Gram and XY sums; the Gram must be symmetric.
The last conjunct is pointwise on the sample-rank event. -/
private theorem repeatedCorrection_finite_contract {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (G : Ω → Mat k) (b : Ω → Vec k)
    (hG : ∀ a b, MemLp (fun ω => G ω a b) ∞ μ)
    (hb : ∀ a, MemLp (fun ω => b ω a) ∞ μ)
    (hsym : ∀ ω, (G ω).transpose = G ω)
    (c : ℝ) (hc : c ≠ 0) (n : ℕ)
    (hH : (c⁻¹ • meanMat μ G).det ≠ 0) :
    let H := c⁻¹ • meanMat μ G
    let β := (meanMat μ G)⁻¹.mulVec (meanVec μ b)
    let S := fun ω => b ω - (G ω).mulVec β
    meanVec μ S = 0 ∧
    meanMat μ (fun ω => c⁻¹ • G ω) = H ∧
    ((n : ℝ) / c^2) • sandwich H⁻¹ (varMat μ S) =
      varMat μ (fun ω => H⁻¹.mulVec ((Real.sqrt n / c) • S ω)) ∧
    (∀ ω, (G ω).det ≠ 0 →
      Real.sqrt n • ((G ω)⁻¹.mulVec (b ω) - β) =
        (c⁻¹ • G ω)⁻¹.mulVec ((Real.sqrt n / c) • S ω)) := by
  classical
  let A : Mat k := meanMat μ G
  let H : Mat k := c⁻¹ • A
  let β : Vec k := A⁻¹.mulVec (meanVec μ b)
  let S : Ω → Vec k := fun ω => b ω - (G ω).mulVec β
  change meanVec μ S = 0 ∧
    meanMat μ (fun ω => c⁻¹ • G ω) = H ∧
    ((n : ℝ) / c^2) • sandwich H⁻¹ (varMat μ S) =
      varMat μ (fun ω => H⁻¹.mulVec ((Real.sqrt n / c) • S ω)) ∧
    (∀ ω, (G ω).det ≠ 0 →
      Real.sqrt n • ((G ω)⁻¹.mulVec (b ω) - β) =
        (c⁻¹ • G ω)⁻¹.mulVec ((Real.sqrt n / c) • S ω))
  have hA : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hH
    change (c⁻¹ • A).det = 0
    rw [Matrix.det_smul, hz, mul_zero]
  have hGβ (a : Fin k) : MemLp (fun ω => (G ω).mulVec β a) ∞ μ := by
    simpa only [Matrix.mulVec, dotProduct] using
      memLp_finsetSum (univ : Finset (Fin k))
        (fun j _ => (hG a j).mul_const (β j))
  have hS (a : Fin k) : MemLp (fun ω => S ω a) ∞ μ :=
    (hb a).sub (hGβ a)
  have hmean : meanVec μ S = meanVec μ b - A.mulVec β := by
    rw [← repeatedCorrection_mean_mulVec μ G hG β]
    ext a
    exact integral_sub ((hb a).integrable (by simp))
      ((hGβ a).integrable (by simp))
  have hzero : meanVec μ S = 0 := by
    rw [hmean]
    dsimp only [β]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, sub_self]
  have hAT : A.transpose = A := by
    ext a b
    change (∫ ω, G ω b a ∂μ) = ∫ ω, G ω a b ∂μ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => congrArg (fun M : Mat k => M a b) (hsym ω))
  have hHT : H.transpose = H := by
    dsimp only [H]
    rw [Matrix.transpose_smul, hAT]
  have hIT : (H⁻¹).transpose = H⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hHT]
  have hcov : varMat μ (fun ω => H⁻¹.mulVec ((Real.sqrt n / c) • S ω)) =
      ((n : ℝ) / c^2) • sandwich H⁻¹ (varMat μ S) := by
    have hscaled (a : Fin k) :
        MemLp (fun ω => ((Real.sqrt n / c) • S ω) a) 2 μ := by
      have hS2 : MemLp (fun ω => S ω a) 2 μ := (hS a).mono_exponent (by simp)
      exact hS2.const_mul (Real.sqrt n / c)
    rw [covariance_linear_map μ H⁻¹ _ hscaled,
      covariance_score_scale μ S (Real.sqrt n / c), hIT]
    have hsquare : (Real.sqrt n / c)^2 = (n : ℝ) / c^2 := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [hsquare]
    simp only [sandwich, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨hzero, meanMat_scale μ G c⁻¹, hcov.symm, ?_⟩
  intro ω hdet
  have hunit : IsUnit (G ω).det := isUnit_iff_ne_zero.mpr hdet
  have hscore : (G ω)⁻¹.mulVec (S ω) = (G ω)⁻¹.mulVec (b ω) - β := by
    dsimp only [S]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  rw [matrix_inverse_scale (G ω) hunit c⁻¹ (inv_ne_zero hc), inv_inv,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, hscore]
  have hscalar : c * (Real.sqrt n / c) = Real.sqrt n := by
    field_simp [hc] <;> ring
  rw [hscalar]

/-- Finite projection identities instantiated by the finite record sums.
The normalization is a parameter so that repeated and weighted targets use
their respective denominators. -/
private theorem repeatedCorrection_record_contract {U : Type*} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k) (hR : RepeatedAtSize R N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hH : (c⁻¹ • meanMat (repeatedLaw R N) (recordWeightedGram R w)).det ≠ 0) :
    let H := c⁻¹ • meanMat (repeatedLaw R N) (recordWeightedGram R w)
    let S := fun ω => ∑ d : Dyad N,
      recordWeightedBlockScore R w (recordWeightedBeta R w) ω d
    meanVec (repeatedLaw R N) S = 0 ∧
    meanMat (repeatedLaw R N) (fun ω => c⁻¹ • recordWeightedGram R w ω) = H ∧
    ((N : ℝ) / c^2) • sandwich H⁻¹ (varMat (repeatedLaw R N) S) =
      varMat (repeatedLaw R N) (fun ω => H⁻¹.mulVec ((Real.sqrt N / c) • S ω)) ∧
    (∀ᵐ ω ∂ repeatedLaw R N, (recordWeightedGram R w ω).det ≠ 0 →
      Real.sqrt N • (recordWeightedOLS R w ω - recordWeightedBeta R w) =
        (c⁻¹ • recordWeightedGram R w ω)⁻¹.mulVec ((Real.sqrt N / c) • S ω)) := by
  letI : IsProbabilityMeasure R.μ := hR.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    dsimp only [repeatedLaw]
    infer_instance
  obtain ⟨hG, hb⟩ := repeatedCorrection_weighted_memLp R hR w
  have h := repeatedCorrection_finite_contract (repeatedLaw R N)
    (recordWeightedGram R w) (recordWeightedXY R w) hG hb
    (repeatedCorrection_weighted_symmetric R w) c hc N hH
  dsimp only at h ⊢
  have hfirst : meanVec (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
      recordWeightedBlockScore R w (recordWeightedBeta R w) ω d) = 0 := by
    simpa only [repeatedCorrection_score_expansion, recordWeightedBeta] using h.1
  refine ⟨hfirst, h.2.1, ?_, ?_⟩
  · simpa only [repeatedCorrection_score_expansion, recordWeightedBeta] using h.2.2.1
  · apply Filter.Eventually.of_forall
    intro ω hdet
    simpa only [repeatedCorrection_score_expansion, recordWeightedBeta,
      recordWeightedOLS] using h.2.2.2 ω hdet

private theorem repeatedCorrection_L_pos {U : Type*} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k) (hR : RepeatedAtSize R N) (hN : 2 ≤ N) :
    0 < repeatedL R N := by
  classical
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    dsimp only [i, j] at hv
    omega
  let d : Dyad N := ⟨{i, j}, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, Finset.card_pair_eq_two_iff.mpr hij⟩⟩
  have hd : (0 : ℝ) < R.T N d := by exact_mod_cast hR.2.1 d
  have hle : (R.T N d : ℝ) ≤ repeatedL R N := by
    exact Finset.single_le_sum (fun e _ => Nat.cast_nonneg (R.T N e)) (Finset.mem_univ d)
  exact lt_of_lt_of_le hd hle

theorem repeated_target_correction_proof {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedAtSize R N) (hN : 2 ≤ N)
    (hH : (repeatedH R N).det ≠ 0) :
    let S := fun ω => ∑ d : Dyad N, repeatedBlockScore R (repeatedBeta R N) ω d
    meanVec (repeatedLaw R N) S = 0 ∧
    meanMat (repeatedLaw R N) (fun ω => (repeatedL R N)⁻¹ • repeatedGram R ω) = repeatedH R N ∧
    repeatedTarget R N = varMat (repeatedLaw R N) (fun ω =>
      (repeatedH R N)⁻¹.mulVec ((Real.sqrt N/repeatedL R N) • S ω)) ∧
    (∀ᵐ ω ∂ repeatedLaw R N, (repeatedGram R ω).det ≠ 0 →
      Real.sqrt N • (repeatedOLS R ω - repeatedBeta R N) =
        ((repeatedL R N)⁻¹ • repeatedGram R ω)⁻¹.mulVec ((Real.sqrt N/repeatedL R N) • S ω)) := by
  have hc : repeatedL R N ≠ 0 := ne_of_gt (repeatedCorrection_L_pos R hR hN)
  have hgram : (recordWeightedGram R (fun _ _ => (1:ℝ)) : (Fin N → U) → Mat k) =
      repeatedGram R := by
    funext ω
    simp only [recordWeightedGram, one_smul, repeatedGram]
  have hxy : (recordWeightedXY R (fun _ _ => (1:ℝ)) : (Fin N → U) → Vec k) =
      fun ω => ∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t) := by
    funext ω
    simp only [recordWeightedXY, one_mul]
  have hH' : ((repeatedL R N)⁻¹ • meanMat (repeatedLaw R N)
      (recordWeightedGram R (fun _ _ => 1))).det ≠ 0 := by
    rw [hgram]
    exact hH
  have h := repeatedCorrection_record_contract R hR (fun _ _ => 1)
    (repeatedL R N) hc hH'
  have hscoreF : (recordWeightedBlockScore R (fun _ _ => (1:ℝ)) :
      Vec k → (Fin N → U) → Dyad N → Vec k) = repeatedBlockScore R := by
    funext β ω d
    simp only [recordWeightedBlockScore, repeatedBlockScore, one_mul]
  have hbeta : (recordWeightedBeta (N := N) R (fun _ _ => (1:ℝ)) : Vec k) =
      repeatedBeta R N := by
    unfold recordWeightedBeta
    rw [hgram, hxy]
    rfl
  have hOLS : (recordWeightedOLS R (fun _ _ => (1:ℝ)) : (Fin N → U) → Vec k) =
      repeatedOLS R := by
    funext ω
    unfold recordWeightedOLS
    rw [hgram, hxy]
    rfl
  dsimp only at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [hbeta, hscoreF] at h1 h3 h4
  rw [hgram] at h2 h3 h4
  rw [hOLS] at h4
  intro S
  exact ⟨h1, h2, h3, h4⟩

/-! Finite projection identities with the dyad normalization. -/

private theorem weightedCorrection_D_pos (N : ℕ) (hN : 2 ≤ N) : 0 < Dreal N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  unfold Dreal
  exact div_pos (mul_pos hn0 hn1) (by norm_num)

theorem weighted_target_correction_proof {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedAtSize R N) (hN : 2 ≤ N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (hH : (recordWeightedH R w).det ≠ 0) :
    let S := fun ω => ∑ d : Dyad N, recordWeightedBlockScore R w (recordWeightedBeta R w) ω d
    meanVec (repeatedLaw R N) S = 0 ∧
    meanMat (repeatedLaw R N) (fun ω => (Dreal N)⁻¹ • recordWeightedGram R w ω) = recordWeightedH R w ∧
    recordWeightedTarget R w = varMat (repeatedLaw R N) (fun ω =>
      (recordWeightedH R w)⁻¹.mulVec ((Real.sqrt N / Dreal N) • S ω)) ∧
    (∀ᵐ ω ∂ repeatedLaw R N, (recordWeightedGram R w ω).det ≠ 0 →
      Real.sqrt N • (recordWeightedOLS R w ω - recordWeightedBeta R w) =
      ((Dreal N)⁻¹ • recordWeightedGram R w ω)⁻¹.mulVec
        ((Real.sqrt N / Dreal N) • S ω)) := by
  have hc : Dreal N ≠ 0 := ne_of_gt (weightedCorrection_D_pos N hN)
  have h := repeatedCorrection_record_contract R hR w (Dreal N) hc hH
  simpa only [recordWeightedH, recordWeightedTarget] using h

end AronowAudit.P018.Wave1
