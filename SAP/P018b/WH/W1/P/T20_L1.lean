import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018b.WH.W1.P.T20_L1

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

theorem sampled_record_memLp {U : Type} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hsize : wholeRepeatedAtSize R N)
    (d : Dyad N) (t : Fin (R.T N d)) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun ω => repeatedX R ω d t a) p (repeatedLaw R N) ∧
    MemLp (fun ω => repeatedY R ω d t) p (repeatedLaw R N) := by
  letI : IsProbabilityMeasure R.μ := hsize.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    unfold repeatedLaw
    infer_instance
  obtain ⟨C, hC, hb⟩ := hsize.2.2.2
  let φ : (Fin N → U) → U × U := fun ω => (ω (firstUnit d), ω (secondUnit d))
  have hφ : Measurable φ :=
    (measurable_pi_apply (firstUnit d)).prodMk (measurable_pi_apply (secondUnit d))
  have hpair := AronowAudit.P018.Wave1.vc3_pair_preserving R.μ
    (firstUnit d) (secondUnit d)
    (AronowAudit.P018.Wave1.WeightedConsistency.firstUnit_ne_secondUnit d)
  have hbω : ∀ᵐ ω ∂repeatedLaw R N,
      ‖repeatedX R ω d t‖ ≤ C ∧ |repeatedY R ω d t| ≤ C := by
    have h := hb d t
    rw [← hpair.map_eq] at h
    have h' := ae_of_ae_map hφ.aemeasurable h
    filter_upwards [h'] with ω hω
    simpa only [φ, Function.comp_def, repeatedX, repeatedY] using hω
  constructor
  · apply MemLp.of_bound
      (((measurable_pi_apply a).comp
        ((hsize.2.2.1 d t).1.comp hφ)).aestronglyMeasurable) C
    filter_upwards [hbω] with ω hω
    exact (norm_le_pi_norm (repeatedX R ω d t) a).trans hω.1
  · apply MemLp.of_bound
      (((hsize.2.2.1 d t).2.comp hφ).aestronglyMeasurable) C
    filter_upwards [hbω] with ω hω
    exact hω.2

theorem weighted_block_score_memLp {U : Type} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hsize : wholeRepeatedAtSize R N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k)
    (d : Dyad N) (a : Fin k) :
    MemLp (fun ω => wholeWeightedBlockScore R w β ω d a) 2 (repeatedLaw R N) := by
  letI : IsProbabilityMeasure R.μ := hsize.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    unfold repeatedLaw
    infer_instance
  simp only [wholeWeightedBlockScore, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul]
  apply memLp_finsetSum
  intro t ht
  have hdot : MemLp (fun ω => dot (repeatedX R ω d t) β) ∞ (repeatedLaw R N) := by
    unfold dot
    apply memLp_finsetSum
    intro b hb
    exact (sampled_record_memLp R hsize d t b ∞).1.mul_const (β b)
  exact (((sampled_record_memLp R hsize d t a ∞).2.sub hdot).const_mul (w d t)).mul
    (sampled_record_memLp R hsize d t a 2).1

theorem weighted_score_sum_coord_memLp {U : Type} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hsize : wholeRepeatedAtSize R N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (a : Fin k) :
    MemLp (fun ω => (∑ d : Dyad N, wholeWeightedBlockScore R w β ω d) a)
      2 (repeatedLaw R N) := by
  letI : IsProbabilityMeasure R.μ := hsize.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    unfold repeatedLaw
    infer_instance
  simp only [Finset.sum_apply]
  exact memLp_finsetSum univ (fun d _ => weighted_block_score_memLp R hsize w β d a)

theorem linear_transform_score_sum_memLp {U : Type} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hsize : wholeRepeatedAtSize R N)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (P : Mat k) (c : ℝ) (β : Vec k) (a : Fin k) :
    MemLp (fun ω => (P.mulVec (c •
      (∑ d : Dyad N, wholeWeightedBlockScore R w β ω d))) a)
      2 (repeatedLaw R N) := by
  letI : IsProbabilityMeasure R.μ := hsize.1
  letI : IsProbabilityMeasure (repeatedLaw R N) := by
    unfold repeatedLaw
    infer_instance
  let S : (Fin N → U) → Vec k := fun ω =>
    ∑ d : Dyad N, wholeWeightedBlockScore R w β ω d
  have hS (b : Fin k) : MemLp (fun ω => S ω b) 2 (repeatedLaw R N) := by
    simpa only [S] using weighted_score_sum_coord_memLp R hsize w β b
  change MemLp (fun ω => ∑ b : Fin k, P a b * (c * S ω b)) 2 (repeatedLaw R N)
  apply memLp_finsetSum
  intro b hb
  have heq : (fun ω => P a b * (c * S ω b)) =
      (fun ω => S ω b * (c * P a b)) := by
    funext ω
    ring
  rw [heq]
  exact (hS b).mul_const (c * P a b)

end SAP.P018b.WH.W1.P.T20_L1

theorem SAP.P018b.WH.W1.T20_L1_proof : SAP.P018b.WH.W1.T20_L1 := by
  intro U hU k N R w hsize P c β a
  exact SAP.P018b.WH.W1.P.T20_L1.linear_transform_score_sum_memLp
    R hsize w P c β a
