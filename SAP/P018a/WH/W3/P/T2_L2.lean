import SAP.P018a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable section
namespace SAP.P018a.WH.W3.P.T2_L2

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

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

private theorem pair_preserving {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ} (d : Dyad N) :
    MeasurePreserving (fun ω : Fin N → U =>
      (ω (firstUnit d), ω (secondUnit d)))
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
  exact AronowAudit.P018.Wave1.vc3_pair_preserving μ
    (firstUnit d) (secondUnit d) (endpoints_ne d)

theorem record_memLp {U : Type*} [MeasurableSpace U]
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
        (‖repeatedX R ω d t‖ ≤ C ∧ |repeatedY R ω d t| ≤ C) := by
    exact (pair_preserving R.μ d).quasiMeasurePreserving.tendsto_ae
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

end SAP.P018a.WH.W3.P.T2_L2

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

theorem SAP.P018a.WH.W3.T2_L2_proof : SAP.P018a.WH.W3.T2_L2 := by
  intro U _ k N R hR w β d a
  letI : IsProbabilityMeasure R.μ := hR.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    dsimp only [repeatedLaw]
    infer_instance
  obtain ⟨hX, hY⟩ := SAP.P018a.WH.W3.P.T2_L2.record_memLp R hR
  have hdot (t : Fin (R.T N d)) :
      MemLp (fun ω : Fin N → U => dot (repeatedX R ω d t) β) ∞
        (repeatedLaw R N) := by
    simpa [dot, mul_comm] using
      (memLp_finsetSum (univ : Finset (Fin k)) (fun b _ =>
        (hX d t b).const_mul (β b)))
  have hres (t : Fin (R.T N d)) :
      MemLp (fun ω : Fin N → U =>
        repeatedY R ω d t - dot (repeatedX R ω d t) β) ∞
        (repeatedLaw R N) := by
    exact (hY d t).sub (hdot t)
  have hterm (t : Fin (R.T N d)) :
      MemLp (fun ω : Fin N → U =>
        score (repeatedX R ω d t)
          (w d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β)) a) ∞
        (repeatedLaw R N) := by
    have hm : MemLp (fun ω : Fin N → U =>
        (w d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β)) *
          repeatedX R ω d t a) ∞ (repeatedLaw R N) :=
      ((hres t).const_mul (w d t)).fun_mul (hX d t a)
    simpa only [score, Pi.smul_apply, smul_eq_mul] using hm
  have hsum : MemLp (fun ω : Fin N → U =>
      recordWeightedBlockScore R w β ω d a) ∞ (repeatedLaw R N) := by
    simpa only [recordWeightedBlockScore, Finset.sum_apply, score,
      Pi.smul_apply, smul_eq_mul] using
      (memLp_finsetSum (univ : Finset (Fin (R.T N d))) (fun t _ => hterm t))
  exact hsum.mono_exponent (by norm_num)
