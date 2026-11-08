import SAP.P001c.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W2.P.T39_L1

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001 AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical ContDiff

noncomputable section

def componentLaw (ρ : ℝ) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun z => ENNReal.ofReal (bivariatePDF 0 0 1 1 ρ z))

lemma rho_sq_pos (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < 1 - ρ ^ 2 := by
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have h2 : 0 < 1 + ρ := by linarith [hρ.1]
  nlinarith [mul_pos h1 h2]

lemma component_map_fst (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    (componentLaw ρ).map Prod.fst = gaussianReal 0 1 := by
  have hT : Measurable (bivariate_normal_transport 0 0 (ρ * 1 / 1)) := by
    unfold bivariate_normal_transport
    fun_prop
  change (volume.withDensity (fun z => ENNReal.ofReal
    (bivariateNormalPDF 0 0 1 1 ρ z))).map Prod.fst = _
  rw [bivariate_normal_eq_map 0 0 1 1 ρ (by norm_num) (by norm_num) hρ,
    Measure.map_map measurable_fst hT]
  have hcomp : Prod.fst ∘ bivariate_normal_transport 0 0 (ρ * 1 / 1) = Prod.fst := by
    funext z
    rfl
  rw [hcomp, bivariate_normal_source, Measure.map_fst_prod]
  rw [measure_univ, one_smul]
  have hv : bivariate_normal_sq 1 = (1 : ℝ≥0) := by
    apply Subtype.ext
    norm_num [bivariate_normal_sq]
  rw [hv]

lemma component_map_snd (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    (componentLaw ρ).map Prod.snd = gaussianReal 0 1 := by
  let d : ℝ := Real.sqrt (1 - ρ ^ 2)
  let η : Measure (ℝ × ℝ) := bivariate_normal_source 0 1 d
  let U : ℝ × ℝ → ℝ := fun z => ρ * z.1
  let V : ℝ × ℝ → ℝ := Prod.snd
  let vρ : ℝ≥0 := ⟨ρ ^ 2, sq_nonneg ρ⟩
  have hq : 0 < 1 - ρ ^ 2 := rho_sq_pos ρ hρ
  have hd : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hq.le
  have hfst : HasLaw (Prod.fst : ℝ × ℝ → ℝ)
      (gaussianReal 0 (bivariate_normal_sq 1)) η := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    dsimp [η, bivariate_normal_source]
    rw [Measure.map_fst_prod]
    simp
  have hsnd : HasLaw (Prod.snd : ℝ × ℝ → ℝ)
      (gaussianReal 0 (bivariate_normal_sq d)) η := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    dsimp [η, bivariate_normal_source]
    rw [Measure.map_snd_prod]
    simp
  have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd η := by
    dsimp [η, bivariate_normal_source]
    exact indepFun_prod measurable_id measurable_id
  have hind' : U ⟂ᵢ[η] V := by
    simpa [U, V, Function.comp_def] using
      hind.comp (by fun_prop : Measurable (fun x : ℝ => ρ * x)) measurable_id
  have hU : HasLaw U (gaussianReal 0 vρ) η := by
    refine ⟨by fun_prop, ?_⟩
    change η.map (fun z => ρ * z.1) = gaussianReal 0 vρ
    change η.map ((fun x : ℝ => ρ * x) ∘ Prod.fst) = _
    rw [← Measure.map_map (by fun_prop : Measurable (fun x : ℝ => ρ * x)) measurable_fst,
      hfst.map_eq, gaussianReal_map_const_mul]
    rw [mul_zero]
    have hv : vρ * bivariate_normal_sq 1 = vρ := by
      rw [show bivariate_normal_sq 1 = 1 by
        apply Subtype.ext
        norm_num [bivariate_normal_sq], mul_one]
    exact congrArg (gaussianReal 0) hv
  have hV : HasLaw V (gaussianReal 0 (bivariate_normal_sq d)) η := by
    simpa [V] using hsnd
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind' hU hV
  have hvar : vρ + bivariate_normal_sq d = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add]
    change ρ ^ 2 + d ^ 2 = 1
    have he : ρ ^ 2 + d ^ 2 = 1 := by
      dsimp [d]
      rw [hd]
      ring
    exact he
  have hT : Measurable (bivariate_normal_transport 0 0 (ρ * 1 / 1)) := by
    unfold bivariate_normal_transport
    fun_prop
  change (volume.withDensity (fun z => ENNReal.ofReal
    (bivariateNormalPDF 0 0 1 1 ρ z))).map Prod.snd = _
  rw [bivariate_normal_eq_map 0 0 1 1 ρ (by norm_num) (by norm_num) hρ,
    Measure.map_map measurable_snd hT]
  have hcomp : Prod.snd ∘ bivariate_normal_transport 0 0 (ρ * 1 / 1) = U + V := by
    funext z
    simp [U, V, bivariate_normal_transport]
  rw [hcomp]
  have hsource : bivariate_normal_source 0 1 (1 * Real.sqrt (1 - ρ ^ 2)) = η := by
    simp [η, d]
  rw [hsource]
  change η.map (U + V) = gaussianReal 0 1
  rw [hsum, hvar]
  simp

def halfMixture : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 / 2 : ℝ) • (componentLaw (3 / 5) + componentLaw (-3 / 5))

lemma halfMixture_eq_normalMixtureLaw : halfMixture = normalMixtureLaw := by
  have hp : ∀ z : ℝ × ℝ, 0 ≤ bivariatePDF 0 0 1 1 (3 / 5) z := by
    intro z
    exact bivariate_normal_density_nonneg 0 0 1 1 (3 / 5) (by norm_num) (by norm_num)
      (by norm_num) z
  have hm : ∀ z : ℝ × ℝ, 0 ≤ bivariatePDF 0 0 1 1 (-3 / 5) z := by
    intro z
    exact bivariate_normal_density_nonneg 0 0 1 1 (-3 / 5) (by norm_num) (by norm_num)
      (by norm_num) z
  have hdens : (fun z : ℝ × ℝ => ENNReal.ofReal (normalMixtureDensity z)) =
      ENNReal.ofReal (1 / 2 : ℝ) • (fun z => ENNReal.ofReal (bivariatePDF 0 0 1 1 (3 / 5) z)) +
      ENNReal.ofReal (1 / 2 : ℝ) • (fun z => ENNReal.ofReal (bivariatePDF 0 0 1 1 (-3 / 5) z)) := by
    funext z
    change ENNReal.ofReal ((bivariatePDF 0 0 1 1 (3 / 5) z +
      bivariatePDF 0 0 1 1 (-3 / 5) z) / 2) = _
    rw [show (bivariatePDF 0 0 1 1 (3 / 5) z + bivariatePDF 0 0 1 1 (-3 / 5) z) / 2 =
      (1 / 2 : ℝ) * (bivariatePDF 0 0 1 1 (3 / 5) z +
        bivariatePDF 0 0 1 1 (-3 / 5) z) by ring,
      ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ)),
      ENNReal.ofReal_add (hp z) (hm z)]
    rw [mul_add]
    simp [Pi.smul_apply, smul_eq_mul]
  unfold halfMixture
  change ENNReal.ofReal (1 / 2 : ℝ) •
      (componentLaw (3 / 5) + componentLaw (-3 / 5)) =
    volume.withDensity (fun z => ENNReal.ofReal (normalMixtureDensity z))
  have hfp : Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (bivariatePDF 0 0 1 1 (3 / 5) z)) := by
    exact Measurable.ennreal_ofReal (bivariate_normal_density_measurable 0 0 1 1 (3 / 5))
  have hfm : Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (bivariatePDF 0 0 1 1 (-3 / 5) z)) := by
    exact Measurable.ennreal_ofReal (bivariate_normal_density_measurable 0 0 1 1 (-3 / 5))
  rw [hdens, withDensity_add_left (hfp.const_smul (ENNReal.ofReal (1 / 2 : ℝ))),
    withDensity_smul (ENNReal.ofReal (1 / 2 : ℝ)) hfp,
    withDensity_smul (ENNReal.ofReal (1 / 2 : ℝ)) hfm]
  rw [smul_add]
  rfl

theorem proof : SAP.P001c.WH.W2.T39_L1 := by
  have hρp : (3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
  have hρm : (-3 / 5 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
  have hprobp := bivariate_normal_probability 0 0 1 1 (3 / 5) (by norm_num) (by norm_num) hρp
  have hprobm := bivariate_normal_probability 0 0 1 1 (-3 / 5) (by norm_num) (by norm_num) hρm
  have hpp : IsProbabilityMeasure (componentLaw (3 / 5)) := by
    change IsProbabilityMeasure (volume.withDensity (fun z => ENNReal.ofReal
      (bivariateNormalPDF 0 0 1 1 (3 / 5) z)))
    exact hprobp.1
  have hpm : IsProbabilityMeasure (componentLaw (-3 / 5)) := by
    change IsProbabilityMeasure (volume.withDensity (fun z => ENNReal.ofReal
      (bivariateNormalPDF 0 0 1 1 (-3 / 5) z)))
    exact hprobm.1
  have hmix := halfMixture_eq_normalMixtureLaw
  have hweight : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hfstp : (componentLaw (3 / 5)).map Prod.fst = gaussianReal 0 1 :=
    component_map_fst (3 / 5) hρp
  have hfstm : (componentLaw (-3 / 5)).map Prod.fst = gaussianReal 0 1 :=
    component_map_fst (-3 / 5) hρm
  have hsndp : (componentLaw (3 / 5)).map Prod.snd = gaussianReal 0 1 :=
    component_map_snd (3 / 5) hρp
  have hsndm : (componentLaw (-3 / 5)).map Prod.snd = gaussianReal 0 1 :=
    component_map_snd (-3 / 5) hρm
  have hprob : IsProbabilityMeasure normalMixtureLaw := by
    rw [← hmix]
    refine ⟨?_⟩
    change (ENNReal.ofReal (1 / 2 : ℝ) •
      (componentLaw (3 / 5) + componentLaw (-3 / 5))) Set.univ = 1
    calc
      _ = ((ENNReal.ofReal (1 / 2 : ℝ) • componentLaw (3 / 5)) +
          (ENNReal.ofReal (1 / 2 : ℝ) • componentLaw (-3 / 5))) Set.univ := by
        rw [smul_add]
      _ = 1 := by
        simp [Measure.smul_apply, Measure.add_apply, hpp.measure_univ, hpm.measure_univ]
        exact ENNReal.inv_two_add_inv_two
  have hmapfst : normalMixtureLaw.map Prod.fst = gaussianReal 0 1 := by
    rw [← hmix, halfMixture,
      Measure.map_smul (ENNReal.ofReal (1 / 2 : ℝ)) measurable_fst.aemeasurable,
      Measure.map_add _ _ measurable_fst, hfstp, hfstm]
    rw [smul_add, ← add_smul, hweight, one_smul]
  have hmapsnd : normalMixtureLaw.map Prod.snd = gaussianReal 0 1 := by
    rw [← hmix, halfMixture,
      Measure.map_smul (ENNReal.ofReal (1 / 2 : ℝ)) measurable_snd.aemeasurable,
      Measure.map_add _ _ measurable_snd, hsndp, hsndm]
    rw [smul_add, ← add_smul, hweight, one_smul]
  have hplus := hprobp.2
  have hminus := hprobm.2
  rcases hplus with ⟨hmeasp, hnnp, hintp, _⟩
  rcases hminus with ⟨hmeasm, hnnm, hintm, _⟩
  have hmeas : Measurable normalMixtureDensity := by
    unfold normalMixtureDensity bivariatePDF
    fun_prop
  have hint : Integrable normalMixtureDensity volume := by
    have h := hintp.add hintm
    convert h.div_const 2 using 1
    ext z
    rfl
  refine ⟨hprob, ?_, hmapfst, hmapsnd⟩
  refine ⟨hmeas.aemeasurable, ?_, hint, ?_⟩
  · intro z
    unfold normalMixtureDensity
    apply div_nonneg
    · apply add_nonneg
      · exact bivariate_normal_density_nonneg 0 0 1 1 (3 / 5) (by norm_num) (by norm_num)
          (by norm_num) z
      · exact bivariate_normal_density_nonneg 0 0 1 1 (-3 / 5) (by norm_num) (by norm_num)
          (by norm_num) z
    · norm_num
  · rfl

end
end SAP.P001c.WH.W2.P.T39_L1

theorem SAP.P001c.WH.W2.T39_L1_proof : SAP.P001c.WH.W2.T39_L1 := by
  exact SAP.P001c.WH.W2.P.T39_L1.proof
