import SAP.P001a.Defs.WholeW1
import SAP.P001a.Bridge
import AronowAudit.P001.Wave1.Gap.DecideB

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

universe u v

namespace SAP.P001a.WH.W1

lemma derivative_of_eqOn {K : ℕ} (U : Set (Fin K → ℝ)) (hU : IsOpen U)
    (x : Fin K → ℝ) (hx : x ∈ U) (m m' : (Fin K → ℝ) → ℝ)
    (he : Set.EqOn m m' U) (k : Fin K) (a : ℝ)
    (hd : HasDerivAt (fun t => m (Function.update x k (x k + t))) a 0) :
    HasDerivAt (fun t => m' (Function.update x k (x k + t))) a 0 ∧
      partialAt m x k = partialAt m' x k := by
  have ht : Continuous (fun t : ℝ => Function.update x k (x k + t)) := by fun_prop
  have hn : ∀ᶠ t in nhds (0 : ℝ), Function.update x k (x k + t) ∈ U :=
    ht.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  have heq : (fun t => m (Function.update x k (x k + t))) =ᶠ[nhds 0]
      (fun t => m' (Function.update x k (x k + t))) := by
    filter_upwards [hn] with t ht using he ht
  exact ⟨hd.congr_of_eventuallyEq heq.symm, heq.deriv_eq⟩

lemma local_continuous_eq {K : ℕ} (U : Set (Fin K → ℝ)) (hU : IsOpen U)
    (m m' : U → ℝ) (hm : Continuous m) (hm' : Continuous m')
    (heq : ∀ᵐ x ∂(volume.restrict U), ∀ hx : x ∈ U, m ⟨x, hx⟩ = m' ⟨x, hx⟩) :
    m = m' := by
  let M : (Fin K → ℝ) → ℝ := fun x => if hx : x ∈ U then m ⟨x, hx⟩ else 0
  let M' : (Fin K → ℝ) → ℝ := fun x => if hx : x ∈ U then m' ⟨x, hx⟩ else 0
  have hc : ContinuousOn M U := by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa [M, Set.domRestrict] using hm
  have hc' : ContinuousOn M' U := by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa [M', Set.domRestrict] using hm'
  have hae : M =ᵐ[volume.restrict U] M' := by
    filter_upwards [heq, ae_restrict_mem hU.measurableSet] with x hx hxU
    simpa [M, M', hxU] using hx hxU
  have h := Measure.eqOn_open_of_ae_eq hae hU hc hc'
  funext x
  simpa [M, M', x.property] using h x.property

lemma cef_eq_on_positive_open {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X)
    (f : (Fin K → ℝ) → ℝ) (hf : HasVectorPDF (μ.map X) f)
    (U : Set (Fin K → ℝ)) (hU : IsOpen U) (hpositive : ∀ x ∈ U, 0 < f x)
    (m m' : (Fin K → ℝ) → ℝ) (hm : IsCEF μ X Y m) (hm' : IsCEF μ X Y m')
    (hc : ContinuousOn m U) (hc' : ContinuousOn m' U) : Set.EqOn m m' U := by
  have hcomp : m ∘ X =ᵐ[μ] m' ∘ X :=
    (AronowAudit.P001.isCEF_condExp μ X hX Y m hm).trans
      (AronowAudit.P001.isCEF_condExp μ X hX Y m' hm').symm
  have hmap : m =ᵐ[μ.map X] m' :=
    (ae_map_iff hX.aemeasurable (measurableSet_eq_fun hm.1 hm'.1)).mpr hcomp
  rw [hf.2.2.2] at hmap
  have hvol := (ae_withDensity_iff' hf.1.ennreal_ofReal).mp hmap
  apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (Fin K → ℝ))) _ hU hc hc'
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hvol] with x hx hxU
  exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (hpositive x hxU)))

lemma endpoint_degree (xy : ℝ × ℝ) : (wholeEndpointFit xy).natDegree ≤ 1 := by
  unfold wholeEndpointFit
  split_ifs
  · simp
  · calc
      _ ≤ (Polynomial.C (xy.2 / (xy.1 - 1))).natDegree +
          (Polynomial.X - Polynomial.C 1 : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 := by
        simp only [Polynomial.natDegree_C, zero_add]
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)

lemma endpoint_interpolates (xy : ℝ × ℝ) : (wholeEndpointFit xy).eval xy.1 = xy.2 := by
  unfold wholeEndpointFit
  split_ifs with hx
  · simp
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hx)

lemma endpoint_coeff_measurable (k : ℕ) :
    Measurable (fun xy : ℝ × ℝ => (wholeEndpointFit xy).coeff k) := by
  have he : (fun xy : ℝ × ℝ => (wholeEndpointFit xy).coeff k) =
      fun xy => if xy.1 = 1 then (if k = 0 then xy.2 else 0) else
        (if k = 1 then xy.2 / (xy.1 - 1) else 0) -
          (if k = 0 then xy.2 / (xy.1 - 1) else 0) := by
    funext xy
    by_cases hx : xy.1 = 1 <;>
      simp [wholeEndpointFit, hx, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_X,
        Polynomial.coeff_C, mul_ite, eq_comm]
  rw [he]
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · split_ifs <;> fun_prop
  · split_ifs <;> fun_prop

lemma endpoint_tail_zero :
    prob ((uniformLaw 0 1).prod (gaussianReal 0 1))
      {xy | (1 / 4 : ℝ) < |(wholeEndpointFit xy).eval 1|} = 0 := by
  have hu : uniformLaw 0 1 ({1} : Set ℝ) = 0 :=
    withDensity_absolutelyContinuous _ _ (by simp)
  have hn : ((uniformLaw 0 1).prod (gaussianReal 0 1))
      (({1} : Set ℝ) ×ˢ Set.univ) = 0 := by simp [Measure.prod_prod, hu]
  have hs : {xy : ℝ × ℝ | (1 / 4 : ℝ) < |(wholeEndpointFit xy).eval 1|} ⊆
      ({1} : Set ℝ) ×ˢ Set.univ := by
    intro xy hxy
    have hx : xy.1 = 1 := by
      by_contra hx
      norm_num [wholeEndpointFit, hx] at hxy
    simp [hx]
  unfold prob
  rw [measure_mono_null hs hn, ENNReal.toReal_zero]

lemma support_envelope_attained (a b : ℝ) (hab : a < b) {K : ℕ}
    (p : Fin K → Polynomial ℝ) :
    ∃ x ∈ Set.Icc a b, wholeSieveEnvelope a b p = ∑ k, ((p k).eval x)^2 ∧
      ∀ y ∈ Set.Icc a b, (∑ k, ((p k).eval y)^2) ≤ wholeSieveEnvelope a b p := by
  let f : ℝ → ℝ := fun x => ∑ k, ((p k).eval x)^2
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
  have hb : BddAbove (f '' Set.Icc a b) := isCompact_Icc.bddAbove_image hc.continuousOn
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc.continuousOn
  have hs : wholeSieveEnvelope a b p = f x := by
    apply le_antisymm
    · exact csSup_le (hne.image f) (by rintro _ ⟨y, hy, rfl⟩; exact hmax hy)
    · exact le_csSup hb ⟨x, hx, rfl⟩
  refine ⟨x, hx, hs, ?_⟩
  intro y hy
  exact le_csSup hb ⟨y, hy, rfl⟩

lemma measurable_matrix_inverse {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (A : Ω → Matrix (Fin p) (Fin p) ℝ) (hA : Measurable A) :
    Measurable (fun ω => (A ω)⁻¹) := by
  have hi : Measurable (fun B : Matrix (Fin p) (Fin p) ℝ => B⁻¹) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    have hd : Measurable (fun B : Matrix (Fin p) (Fin p) ℝ => B.det⁻¹) :=
      continuous_id.matrix_det.measurable.inv
    have ha : Measurable (fun B : Matrix (Fin p) (Fin p) ℝ => B.adjugate j k) :=
      (continuous_id.matrix_adjugate.matrix_elem j k).measurable
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
      Pi.mul_def] using hd.mul ha
  exact hi.comp hA

lemma measurable_wald {Ω : Type*} [MeasurableSpace Ω] {p L : ℕ}
    (R : Matrix (Fin L) (Fin p) ℝ) (B : Ω → Fin p → ℝ)
    (C : Ω → Matrix (Fin p) (Fin p) ℝ) (hB : Measurable B) (hC : Measurable C) :
    Measurable (fun ω => wholeWald R (B ω) (C ω)) := by
  have hS : Measurable (fun ω => R * C ω * R.transpose) :=
    (continuous_const.matrix_mul continuous_id |>.matrix_mul continuous_const).measurable.comp hC
  have hi := measurable_matrix_inverse _ hS
  have hR : Measurable (fun ω => R.mulVec (B ω)) :=
    (continuous_const.matrix_mulVec continuous_id).measurable.comp hB
  unfold wholeWald
  change Measurable (fun ω => ∑ j, (R.mulVec (B ω)) j *
    (∑ k, (R * C ω * R.transpose)⁻¹ j k * (R.mulVec (B ω)) k))
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_pi_apply j).comp hR).mul
    (Finset.measurable_sum _ (fun k _ =>
      ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hi)).mul
        ((measurable_pi_apply k).comp hR)))

lemma kernel_finite_identity {A : Type u} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (κ : Measure ℝ) (F G : WholeDensity A κ)
    (hentropy : (∀ᵐ x ∂ν, Integrable (fun y => F.density x y *
      Real.log (F.density x y)) κ) ∧ Integrable (wholeSectionEntropy F) ν)
    (hlog : WholeFiniteLog ν F G)
    (hsection : ∀ x, Integrable (fun y => F.density x y * Real.log (F.density x y)) κ →
      Integrable (fun y => Real.log (G.density x y)) (F.kernel x) →
      (∀ᵐ y ∂(F.kernel x), 0 < G.density x y) →
      InformationTheory.klDiv (F.kernel x) (G.kernel x) = ENNReal.ofReal
        (wholeSectionEntropy F x - ∫ y, Real.log (G.density x y) ∂(F.kernel x)) ∧
      0 ≤ wholeSectionEntropy F x - ∫ y, Real.log (G.density x y) ∂(F.kernel x)) :
    wholeAverageKL ν F G ≠ ∞ ∧
      (wholeAverageKL ν F G).toReal = (∫ x, wholeSectionEntropy F x ∂ν) -
        ∫ xy, Real.log (G.density xy.1 xy.2) ∂(ν ⊗ₘ F.kernel) := by
  let H : A → ℝ := fun x => ∫ y, Real.log (G.density x y) ∂(F.kernel x)
  have hi := (Measure.integrable_compProd_iff hlog.2.aestronglyMeasurable).mp hlog.2
  have hHm : StronglyMeasurable H :=
    G.measurable.log.stronglyMeasurable.integral_kernel_prod_right'
  have hHi : Integrable H ν := hi.2.mono' hHm.aestronglyMeasurable
    (ae_of_all ν (fun x => norm_integral_le_integral_norm _))
  have hs : ∀ᵐ x ∂ν,
      InformationTheory.klDiv (F.kernel x) (G.kernel x) =
        ENNReal.ofReal (wholeSectionEntropy F x - H x) ∧
      0 ≤ wholeSectionEntropy F x - H x := by
    filter_upwards [hentropy.1, hi.1, Measure.ae_ae_of_ae_compProd hlog.1] with x hx hy hz
    exact hsection x hx hy hz
  have hd : wholeAverageKL ν F G = ENNReal.ofReal
      (∫ x, wholeSectionEntropy F x - H x ∂ν) := by
    unfold wholeAverageKL
    rw [lintegral_congr_ae (hs.mono (fun _ h => h.1))]
    exact (ofReal_integral_eq_lintegral_ofReal
      (f := fun x => wholeSectionEntropy F x - H x)
      (hentropy.2.sub hHi) (hs.mono (fun _ h => h.2))).symm
  refine ⟨by rw [hd]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hd, ENNReal.toReal_ofReal (integral_nonneg_of_ae (hs.mono (fun _ h => h.2))),
    integral_sub hentropy.2 hHi, Measure.integral_compProd hlog.2]

lemma placebo_test_null {K L : ℕ} (γ : Fin (K + 1) → ℝ) :
    (wholePlaceboSelector K L).mulVec (wholeNullCoef γ) = 0 := by
  ext l
  simp [wholePlaceboSelector, Matrix.mulVec, dotProduct, ite_mul, wholeNullCoef]

lemma score_clt {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (Z i ω, D i ω))) (b : Fin p → ℝ)
    (h : WholeScoreMoments μ (Z 0) (D 0) b) :
    WeakLimit μ (wholeScoreSum Z D b) (normalVectorLaw (wholeOmega μ (Z 0) (D 0) b)) := by
  let f : (Fin p → ℝ) × ℝ → Fin p → ℝ := fun z => (z.2 - z.1 ⬝ᵥ b) • z.1
  let s : ℕ → Ω → Fin p → ℝ := fun i ω => f (Z i ω, D i ω)
  have hf : Measurable f := by dsimp [f, dotProduct]; fun_prop
  have hi : AronowAudit.P001.IID μ s :=
    ⟨fun i => hf.comp (hiid.1 i), hiid.2.1.comp (fun _ => f) (fun _ => hf),
      fun i => (hiid.2.2 i).comp hf⟩
  have hs2 (j : Fin p) : MemLp (fun ω => s 0 ω j) 2 μ := by
    simpa only [s, f, Pi.smul_apply, smul_eq_mul, wholeResidual, mul_comm] using h.secondScore j
  have hs0 (j : Fin p) : AronowAudit.P001.mean μ (fun ω => s 0 ω j) = 0 := by
    simpa only [AronowAudit.P001.mean, mean, s, f, Pi.smul_apply, smul_eq_mul, wholeResidual, mul_comm] using h.orthogonal j
  have hc (j k : Fin p) : wholeOmega μ (Z 0) (D 0) b j k =
      AronowAudit.P001.mean μ (fun ω => s 0 ω j * s 0 ω k) := by
    unfold wholeOmega AronowAudit.P001.mean
    apply integral_congr_ae
    exact ae_of_all μ (fun ω => by dsimp [s, f, wholeResidual]; ring)
  have ht := AronowAudit.P001.Wave1.DecideB_vector_clt μ s hi hs2 hs0
    (wholeOmega μ (Z 0) (D 0) b) h.positiveOmega hc
  have he : wholeScoreSum Z D b =
      fun (n : ℕ) (ω : Ω) => (Real.sqrt n)⁻¹ • (fun j => ∑ i ∈ Finset.range n, s i ω j) := by
    funext n ω j
    simp [wholeScoreSum, s, f, wholeResidual, Finset.sum_apply]
  rw [he]
  exact ht

end SAP.P001a.WH.W1
