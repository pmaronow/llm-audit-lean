import SAP.P019b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b.WH.W1.P.T12_L3

open MeasureTheory ProbabilityTheory
open SAP.P019b
noncomputable section
open Classical

def finiteLawMeasure {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (P : FiniteLaw I) : Measure I :=
  Measure.sum (fun i => ENNReal.ofReal (P.mass i) • Measure.dirac i)

lemma finiteLawMeasure_integral {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (P : FiniteLaw I) (f : I → ℝ) :
    (∫ i, f i ∂finiteLawMeasure P) = P.mean f := by
  rw [finiteLawMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), tsum_fintype]
  simp [FiniteLaw.mean, ENNReal.toReal_ofReal, P.nonneg, smul_eq_mul]

instance finiteLawMeasure_probability {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (P : FiniteLaw I) :
    IsProbabilityMeasure (finiteLawMeasure P) := by
  constructor
  rw [finiteLawMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ]
  simp [Set.indicator]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.nonneg i), P.total]
  norm_num

lemma map_encoding_law {Ω : Type} [MeasurableSpace Ω] (S : WholeStudy Ω)
    {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) :
    S.law.map e = finiteLawMeasure F.law := by
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply he.1 (MeasurableSet.singleton i)]
  change S.law {ω | e ω = i} = _
  rw [he.2.1 i]
  simpa [finiteLawMeasure] using
    (Measure.sum_smul_dirac_singleton (f := fun j => ENNReal.ofReal (F.law.mass j)) (a := i)).symm

lemma finite_indep_iff_factorization {m : ℕ} (F : Study (Fin m)) :
    IndepFun (fun i => (F.W i, F.X i, F.Y i)) F.Z (finiteLawMeasure F.law) ↔
      F.treatmentIndependent := by
  have hmeasF : Measurable (fun i => (F.W i, F.X i, F.Y i)) := measurable_of_finite _
  have hmeasZ : Measurable F.Z := measurable_of_finite _
  rw [indepFun_iff_integral_comp_mul (hfm := hmeasF) (hgm := hmeasZ)]
  constructor
  · intro hi f z
    let φ : ℕ × Bool × Bool → ℝ := fun t => f t.1 t.2.1 t.2.2
    let ψ : Bool → ℝ := fun b => if b = z then 1 else 0
    have hφ : Measurable φ := measurable_of_countable φ
    have hψ : Measurable ψ := measurable_of_finite ψ
    have hfa : Integrable (φ ∘ (fun i => (F.W i, F.X i, F.Y i)))
        (finiteLawMeasure F.law) := by
      exact ⟨(measurable_of_finite _).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩
    have hza : Integrable (ψ ∘ F.Z) (finiteLawMeasure F.law) := by
      exact ⟨(measurable_of_finite _).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩
    have h := hi hφ hψ hfa hza
    rw [finiteLawMeasure_integral, finiteLawMeasure_integral,
      finiteLawMeasure_integral] at h
    change F.law.mean (fun i => if F.Z i = z then f (F.W i) (F.X i) (F.Y i) else 0) =
      F.law.prob (fun i => F.Z i = z) * F.law.mean
        (fun i => f (F.W i) (F.X i) (F.Y i))
    simpa [FiniteLaw.prob, FiniteLaw.mean, φ, ψ, mul_comm, mul_left_comm, mul_assoc] using h
  · intro h φ ψ hφ hψ hφi hψi
    let a : Fin m → ℝ := fun i => φ (F.W i, F.X i, F.Y i)
    let b : Fin m → ℝ := fun i => ψ (F.Z i)
    have h0 := h (fun w x y => φ (w, x, y)) false
    have h1 := h (fun w x y => φ (w, x, y)) true
    have hsplit : ∀ i, a i * b i =
        (if F.Z i = false then a i * ψ false else 0) +
        (if F.Z i = true then a i * ψ true else 0) := by
      intro i
      cases hz : F.Z i <;> simp [a, b, hz]
    have hmeanSplit : F.law.mean (fun i => a i * b i) =
        F.law.mean (fun i => if F.Z i = false then a i * ψ false else 0) +
        F.law.mean (fun i => if F.Z i = true then a i * ψ true else 0) := by
      simp only [FiniteLaw.mean]
      calc
        ∑ i, F.law.mass i * (a i * b i) =
            ∑ i, F.law.mass i * ((if F.Z i = false then a i * ψ false else 0) +
              (if F.Z i = true then a i * ψ true else 0)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hsplit i]
        _ = (∑ i, F.law.mass i * (if F.Z i = false then a i * ψ false else 0)) +
            ∑ i, F.law.mass i * (if F.Z i = true then a i * ψ true else 0) := by
              simp only [mul_add, Finset.sum_add_distrib]
    have hterms :
        F.law.mean (fun i => if F.Z i = false then a i * ψ false else 0) =
          F.law.prob (fun i => F.Z i = false) * F.law.mean a * ψ false ∧
        F.law.mean (fun i => if F.Z i = true then a i * ψ true else 0) =
          F.law.prob (fun i => F.Z i = true) * F.law.mean a * ψ true := by
      constructor
      ·
        have h0' : F.law.mean (fun i => if F.Z i = false then a i else 0) =
            F.law.prob (fun i => F.Z i = false) * F.law.mean a := by simpa [a] using h0
        calc
          F.law.mean (fun i => if F.Z i = false then a i * ψ false else 0) =
              F.law.mean (fun i => if F.Z i = false then a i else 0) * ψ false := by
                unfold FiniteLaw.mean
                calc
                  (∑ i, F.law.mass i * (if F.Z i = false then a i * ψ false else 0)) =
                      ∑ i, (F.law.mass i * (if F.Z i = false then a i else 0)) * ψ false := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        by_cases hz : F.Z i = false
                        · simp [hz]
                          ring
                        · simp [hz]
                  _ = (∑ i, F.law.mass i * (if F.Z i = false then a i else 0)) * ψ false := by
                        rw [Finset.sum_mul]
          _ = F.law.prob (fun i => F.Z i = false) * F.law.mean a * ψ false := by rw [h0']
      ·
        have h1' : F.law.mean (fun i => if F.Z i = true then a i else 0) =
            F.law.prob (fun i => F.Z i = true) * F.law.mean a := by simpa [a] using h1
        calc
          F.law.mean (fun i => if F.Z i = true then a i * ψ true else 0) =
              F.law.mean (fun i => if F.Z i = true then a i else 0) * ψ true := by
                unfold FiniteLaw.mean
                calc
                  (∑ i, F.law.mass i * (if F.Z i = true then a i * ψ true else 0)) =
                      ∑ i, (F.law.mass i * (if F.Z i = true then a i else 0)) * ψ true := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        by_cases hz : F.Z i = true
                        · simp [hz]
                          ring
                        · simp [hz]
                  _ = (∑ i, F.law.mass i * (if F.Z i = true then a i else 0)) * ψ true := by
                        rw [Finset.sum_mul]
          _ = F.law.prob (fun i => F.Z i = true) * F.law.mean a * ψ true := by rw [h1']
    have hψmean : F.law.mean b =
        F.law.prob (fun i => F.Z i = false) * ψ false +
        F.law.prob (fun i => F.Z i = true) * ψ true := by
      unfold FiniteLaw.mean FiniteLaw.prob
      have hfalse : (∑ i, if F.Z i = false then F.law.mass i * ψ false else 0) =
          (∑ i, if F.Z i = false then F.law.mass i else 0) * ψ false := by
        calc
          (∑ i, if F.Z i = false then F.law.mass i * ψ false else 0) =
              ∑ i, (if F.Z i = false then F.law.mass i else 0) * ψ false := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hz : F.Z i = false <;> simp [hz]
          _ = (∑ i, if F.Z i = false then F.law.mass i else 0) * ψ false := by
                rw [Finset.sum_mul]
      have htrue : (∑ i, if F.Z i = true then F.law.mass i * ψ true else 0) =
          (∑ i, if F.Z i = true then F.law.mass i else 0) * ψ true := by
        calc
          (∑ i, if F.Z i = true then F.law.mass i * ψ true else 0) =
              ∑ i, (if F.Z i = true then F.law.mass i else 0) * ψ true := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hz : F.Z i = true <;> simp [hz]
          _ = (∑ i, if F.Z i = true then F.law.mass i else 0) * ψ true := by
                rw [Finset.sum_mul]
      calc
        F.law.mean b =
            ∑ i, F.law.mass i * ψ (F.Z i) := rfl
        _ =
            ∑ i, ((if F.Z i = false then F.law.mass i * ψ false else 0) +
              (if F.Z i = true then F.law.mass i * ψ true else 0)) := by
                apply Finset.sum_congr rfl
                intro i hi
                cases F.Z i <;> simp
        _ = (∑ i, if F.Z i = false then F.law.mass i else 0) * ψ false +
            (∑ i, if F.Z i = true then F.law.mass i else 0) * ψ true := by
              rw [Finset.sum_add_distrib, hfalse, htrue]
        _ = (F.law.mean (fun i => if F.Z i = false then 1 else 0)) * ψ false +
            (F.law.mean (fun i => if F.Z i = true then 1 else 0)) * ψ true := by
              unfold FiniteLaw.mean
              simp only [mul_ite, mul_one, mul_zero]
        _ = (F.law.prob (fun i => F.Z i = false)) * ψ false +
            (F.law.prob (fun i => F.Z i = true)) * ψ true := by rfl
    have hfactor : F.law.mean (fun i => a i * b i) = F.law.mean a * F.law.mean b := by
      rw [hmeanSplit, hterms.1, hterms.2, hψmean]
      ring
    change (∫ i, a i * b i ∂finiteLawMeasure F.law) =
      (∫ i, a i ∂finiteLawMeasure F.law) * (∫ i, b i ∂finiteLawMeasure F.law)
    rw [finiteLawMeasure_integral, finiteLawMeasure_integral, finiteLawMeasure_integral]
    exact hfactor

end
end SAP.P019b.WH.W1.P.T12_L3

open SAP.P019b.WH.W1.P.T12_L3
open MeasureTheory ProbabilityTheory

theorem SAP.P019b.WH.W1.T12_L3_proof : SAP.P019b.WH.W1.T12_L3 := by
  intro Ω _ S m F e he
  have hmapE := map_encoding_law S F e he
  let sTriple : Ω → ℕ × Bool × Bool := fun ω => (S.W ω, S.X ω, S.Y ω)
  let fTriple : Fin m → ℕ × Bool × Bool := fun i => (F.W i, F.X i, F.Y i)
  let sJoint : Ω → (ℕ × Bool × Bool) × Bool := fun ω => (sTriple ω, S.Z ω)
  let fJoint : Fin m → (ℕ × Bool × Bool) × Bool := fun i => (fTriple i, F.Z i)
  have hsTripleMeas : Measurable sTriple := by
    exact S.measurable_W.prodMk (S.measurable_X.prodMk S.measurable_Y)
  have hsJointMeas : Measurable sJoint := hsTripleMeas.prodMk S.measurable_Z
  have hfTripleMeas : Measurable fTriple := measurable_of_finite _
  have hfJointMeas : Measurable fJoint := measurable_of_finite _
  have hae : sJoint =ᵐ[S.law] fun ω => fJoint (e ω) := by
    filter_upwards [he.2.2] with ω hω
    rcases hω with ⟨hW, hX, hY, hZ, hV⟩
    simp [sJoint, sTriple, fJoint, fTriple, hW, hX, hY, hZ]
  have hjoint : S.law.map sJoint = (finiteLawMeasure F.law).map fJoint := by
    calc
      S.law.map sJoint = S.law.map (fun ω => fJoint (e ω)) := Measure.map_congr hae
      _ = (S.law.map e).map fJoint := by
        symm
        exact Measure.map_map hfJointMeas he.1
      _ = (finiteLawMeasure F.law).map fJoint := by rw [hmapE]
  have hsTriple : S.law.map sTriple = (finiteLawMeasure F.law).map fTriple := by
    calc
      S.law.map sTriple = (S.law.map sJoint).map Prod.fst := by
        symm
        exact Measure.map_map measurable_fst hsJointMeas
      _ = ((finiteLawMeasure F.law).map fJoint).map Prod.fst := by rw [hjoint]
      _ = (finiteLawMeasure F.law).map fTriple := by
        exact Measure.map_map measurable_fst (measurable_of_finite fJoint)
  have hZ : S.law.map S.Z = (finiteLawMeasure F.law).map F.Z := by
    calc
      S.law.map S.Z = (S.law.map sJoint).map Prod.snd := by
        symm
        exact Measure.map_map measurable_snd hsJointMeas
      _ = ((finiteLawMeasure F.law).map fJoint).map Prod.snd := by rw [hjoint]
      _ = (finiteLawMeasure F.law).map F.Z := by
        exact Measure.map_map measurable_snd (measurable_of_finite fJoint)
  have hS : IndepFun sTriple S.Z S.law ↔
      fTriple ⟂ᵢ[finiteLawMeasure F.law] F.Z := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hsTripleMeas.aemeasurable S.measurable_Z.aemeasurable]
    rw [indepFun_iff_map_prod_eq_prod_map_map hfTripleMeas.aemeasurable
      (measurable_of_finite F.Z).aemeasurable]
    rw [hjoint, hsTriple, hZ]
  change IndepFun sTriple S.Z S.law ↔ F.treatmentIndependent
  rw [hS, SAP.P019b.WH.W1.P.T12_L3.finite_indep_iff_factorization]
