import AronowAudit.P018.Wave1.WeightedConsistency.M3
import AronowAudit.P018.Wave1.WeightedConsistency.M0

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem record_memLp_all {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (d : Dyad N) (t : Fin (R.T N d)) (a : Fin k) (p : ℝ≥0∞) :
    MemLp (fun ω => repeatedX R ω d t a) p (repeatedLaw R N) ∧
      MemLp (fun ω => repeatedY R ω d t) p (repeatedLaw R N) := by
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  letI instSampleProbability : IsProbabilityMeasure (repeatedLaw R N) :=
    repeatedLaw_probability R hR N
  obtain ⟨B, hB, hb⟩ := hreg.2
  constructor
  · apply MemLp.of_bound (((measurable_pi_apply a).comp (hreg.1 N d t).1).aestronglyMeasurable) B
    filter_upwards [hb N d t] with ω hω
    exact (norm_le_pi_norm (repeatedX R ω d t) a).trans hω.1
  · exact MemLp.of_bound (hreg.1 N d t).2.aestronglyMeasurable B
      ((hb N d t).mono fun ω hω => hω.2)

theorem blockScore_memLp {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (v : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (d : Dyad N) (a : Fin k)
    (p : ℝ≥0∞) :
    MemLp (fun ω => recordWeightedBlockScore R v β ω d a) p (repeatedLaw R N) := by
  simp only [recordWeightedBlockScore, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul]
  apply memLp_finsetSum
  intro t ht
  have hdot : MemLp (fun ω => dot (repeatedX R ω d t) β) ∞ (repeatedLaw R N) :=
    memLp_finsetSum _ (fun b _ => (record_memLp_all R hR hreg d t b ∞).1.mul_const _)
  exact (((record_memLp_all R hR hreg d t a ∞).2.sub hdot).const_mul (v d t)).mul
    (record_memLp_all R hR hreg d t a p).1

theorem blockScore_measurable {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hreg : RecordRegular R)
    (v : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (d : Dyad N) (a : Fin k) :
    Measurable (fun ω => recordWeightedBlockScore R v β ω d a) := by
  simp only [recordWeightedBlockScore, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul, dot]
  apply Finset.measurable_fun_sum
  intro t ht
  exact (measurable_const.mul ((hreg.1 N d t).2.sub
    (Finset.measurable_fun_sum _ (fun b _ =>
      (((measurable_pi_apply b).comp (hreg.1 N d t).1).mul measurable_const))))).mul
    ((measurable_pi_apply a).comp (hreg.1 N d t).1)

theorem blockScore_support {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (v : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (β : Vec k) (d : Dyad N) (ω ω' : Fin N → U)
    (h : ∀ i ∈ members d, ω i = ω' i) :
    recordWeightedBlockScore R v β ω d = recordWeightedBlockScore R v β ω' d := by
  simp only [recordWeightedBlockScore, repeatedX, repeatedY,
    h _ (firstUnit_mem d), h _ (secondUnit_mem d)]

theorem m8_proof : M8.{u} := by
  intro g2 U _ k R X Y dir v C H hS hreg hcent N hN
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hS.1 N
  let β := popBeta R.μ X Y
  let q := fun d : Dyad N => fun ω : Fin N → U => recordWeightedBlockScore R (v N) β ω d
  have hLp (d : Dyad N) (a : Fin k) : MemLp (fun ω => q d ω a) 2 (repeatedLaw R N) :=
    blockScore_memLp R hS.1 hreg (v N) β d a 2
  have hcov (d f : Dyad N) (hdf : ¬(members d ∩ members f).Nonempty) :
      covMat (repeatedLaw R N) (q d) (q f) = 0 := by
    ext a b
    exact g2 R.μ (members d) (members f) (fun ω => q d ω a) (fun ω => q f ω b)
      (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hdf))
      (blockScore_measurable R hreg (v N) β d a)
      (blockScore_measurable R hreg (v N) β f b)
      (fun ω ω' h => congrFun (blockScore_support R (v N) β d ω ω' h) a)
      (fun ω ω' h => congrFun (blockScore_support R (v N) β f ω ω' h) b)
      (hLp d a) (hLp f b)
  have hv := variance_sparse_identity (repeatedLaw R N) members q hLp (hcent N) hcov
  unfold scaledMeatAt targetMeat
  rw [meanMat_scale]
  congr 1
  rw [hv]
  ext a b
  change (∫ ω, (meat members (fun d => q d ω)) a b ∂repeatedLaw R N) = _
  simp only [meat, Matrix.sum_apply, matrix_ite_apply, outer, Matrix.zero_apply, Pi.zero_apply]
  have hi (d f : Dyad N) : Integrable
      (fun ω => if (members d ∩ members f).Nonempty then q d ω a * q f ω b else 0)
        (repeatedLaw R N) := by
    split_ifs
    · exact (hLp d a).integrable_mul (hLp f b)
    · exact integrable_const _
  rw [integral_finsetSum _ (fun d _ => integrable_finset_sum _ (fun f _ => hi d f))]
  simp_rw [integral_finsetSum _ (fun f _ => hi _ f)]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs <;> simp [meanMat, outer]

end
end AronowAudit.P018.Wave1.WeightedConsistency
