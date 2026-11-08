import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a.WH.W2.P.T12_L1

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

private theorem endpoints_ne {N : ℕ} (d : Dyad N) :
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

private theorem pair_preserving {U : Type u} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} (d : Dyad N) :
    MeasurePreserving (fun ω : Fin N → U =>
      (ω (firstUnit d), ω (secondUnit d)))
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
  have hind : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ : Fin N => μ)) := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => id)
        (fun _ => measurable_id.aemeasurable))
  have hpair := hind.indepFun (endpoints_ne d)
  refine ⟨(measurable_pi_apply (firstUnit d)).prodMk
    (measurable_pi_apply (secondUnit d)), ?_⟩
  rw [hpair.map_prod_eq_prod_map_map
    (measurable_pi_apply (firstUnit d)).aemeasurable
    (measurable_pi_apply (secondUnit d)).aemeasurable]
  rw [(measurePreserving_eval (fun _ : Fin N => μ) (firstUnit d)).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) (secondUnit d)).map_eq]

private theorem record_memLp {U : Type u} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k) (hR : WholeRecordRegular R N) :
    (∀ d t a, MemLp (fun ω : Fin N → U => repeatedX R ω d t a) ∞
      (repeatedLaw R N)) ∧
    (∀ d t, MemLp (fun ω : Fin N → U => repeatedY R ω d t) ∞
      (repeatedLaw R N)) := by
  letI : IsProbabilityMeasure R.μ := hR.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    dsimp only [repeatedLaw]
    infer_instance
  obtain ⟨C, hC, hbound⟩ := hR.2.2
  have hmeas (d : Dyad N) (t : Fin (R.T N d)) :
      Measurable (fun ω : Fin N → U => repeatedX R ω d t) ∧
      Measurable (fun ω : Fin N → U => repeatedY R ω d t) := by
    have hp : Measurable (fun ω : Fin N → U =>
        (ω (firstUnit d), ω (secondUnit d))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact ⟨(hR.2.1 d t).1.comp hp, (hR.2.1 d t).2.comp hp⟩
  have hbound' (d : Dyad N) (t : Fin (R.T N d)) :
      ∀ᵐ ω ∂ repeatedLaw R N,
        ‖repeatedX R ω d t‖ ≤ C ∧ |repeatedY R ω d t| ≤ C := by
    exact (pair_preserving R.μ d).quasiMeasurePreserving.tendsto_ae
      (hbound d t)
  constructor
  · intro d t a
    apply MemLp.of_bound
      ((measurable_pi_apply a).comp (hmeas d t).1).aestronglyMeasurable C
    filter_upwards [hbound' d t] with ω hω
    exact (norm_le_pi_norm (repeatedX R ω d t) a).trans hω.1
  · intro d t
    apply MemLp.of_bound (hmeas d t).2.aestronglyMeasurable C
    filter_upwards [hbound' d t] with ω hω
    simpa only [Real.norm_eq_abs] using hω.2

private theorem weighted_memLp {U : Type u} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k) (hR : WholeRecordRegular R N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) :
    (∀ a b, MemLp (fun ω : Fin N → U => recordWeightedGram R w ω a b) ∞
      (repeatedLaw R N)) ∧
    (∀ a, MemLp (fun ω : Fin N → U => recordWeightedXY R w ω a) ∞
      (repeatedLaw R N)) := by
  classical
  obtain ⟨hX, hY⟩ := record_memLp R hR
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

private theorem blockScore_memLp {U : Type u} [MeasurableSpace U]
    {k N : ℕ} (R : RepeatedKernel U k) (hR : WholeRecordRegular R N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) :
    ∀ d a, MemLp (fun ω : Fin N → U =>
      recordWeightedBlockScore R w β ω d a) ∞ (repeatedLaw R N) := by
  classical
  obtain ⟨hX, hY⟩ := record_memLp R hR
  intro d a
  have hdot (t : Fin (R.T N d)) :
      MemLp (fun ω : Fin N → U => dot (repeatedX R ω d t) β) ∞
        (repeatedLaw R N) := by
    simpa only [dot, Finset.sum_apply, mul_comm] using
      (memLp_finsetSum (univ : Finset (Fin k)) (fun b _ =>
        (hX d t b).const_mul (β b)))
  have hterm (t : Fin (R.T N d)) :
      MemLp (fun ω : Fin N → U =>
        (w d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β)) *
          repeatedX R ω d t a) ∞ (repeatedLaw R N) := by
    exact ((hY d t).sub (hdot t)).const_mul (w d t) |>.fun_mul (hX d t a)
  simpa only [recordWeightedBlockScore, Finset.sum_apply, score,
    Pi.smul_apply, smul_eq_mul] using
    (memLp_finsetSum (univ : Finset (Fin (R.T N d)))
      (fun t _ => hterm t))

end SAP.P018a.WH.W2.P.T12_L1

theorem SAP.P018a.WH.W2.T12_L1_proof : SAP.P018a.WH.W2.T12_L1 := by
  intro U _ k N R hR w
  obtain ⟨hG, hXY⟩ := SAP.P018a.WH.W2.P.T12_L1.weighted_memLp R hR w
  exact ⟨hG, hXY,
    SAP.P018a.WH.W2.P.T12_L1.blockScore_memLp R hR w⟩
