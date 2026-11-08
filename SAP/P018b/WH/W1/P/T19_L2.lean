import SAP.P018b.WH.W1.Leaves
import AronowAudit.P018.Wave1.Gap.TailBRareFinite
import AronowAudit.P018.Wave1.Gap.GP0182B2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018b.WH.W1.P.T19_L2

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise

private lemma kernel_pair_square_integrable {N : ℕ} (d : AronowAudit.P018.Dyad N) :
    Integrable
      (fun ω : Fin N → AronowAudit.P018.RareUnit =>
        (AronowAudit.P018.rareS (ω (AronowAudit.P018.firstUnit d))
          (ω (AronowAudit.P018.secondUnit d)))^2)
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  let K : AronowAudit.P018.RareUnit × AronowAudit.P018.RareUnit → ℝ :=
    fun uv => (AronowAudit.P018.rareS uv.1 uv.2)^2
  have hKmeas : Measurable K := measurable_of_countable _
  have hKbound (uv : AronowAudit.P018.RareUnit × AronowAudit.P018.RareUnit) :
      |K uv| ≤ 1 := by
    dsimp [K]
    exact AronowAudit.P018.Wave1.tb09_rare_s2_bound uv
  have hK : MemLp K 2
      (AronowAudit.P018.rareLaw.prod AronowAudit.P018.rareLaw) := by
    apply MemLp.of_bound hKmeas.aestronglyMeasurable 1
    filter_upwards [] with uv
    simpa only [Real.norm_eq_abs] using hKbound uv
  have hpair := AronowAudit.P018.Wave1.GP0182B2b_kernel_pair_memLp
    (fun i : Fin N => fun ω : Fin N → AronowAudit.P018.RareUnit => ω i)
    (iIndepFun_pi (fun _ => aemeasurable_id))
    (fun i => measurePreserving_eval (fun _ : Fin N => AronowAudit.P018.rareLaw) i)
    hK (AronowAudit.P018.Wave1.WeightedConsistency.firstUnit_ne_secondUnit d)
  exact hpair.integrable one_le_two

private lemma kernel_pair_square_integral {N : ℕ} (d : AronowAudit.P018.Dyad N) :
    (∫ ω : Fin N → AronowAudit.P018.RareUnit,
      (AronowAudit.P018.rareS (ω (AronowAudit.P018.firstUnit d))
        (ω (AronowAudit.P018.secondUnit d)))^2
        ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) =
      AronowAudit.P018.rareQ := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  have h := AronowAudit.P018.Wave1.GP0182B2b_kernel_pair_integral
    (fun i : Fin N => fun ω : Fin N → AronowAudit.P018.RareUnit => ω i)
    (iIndepFun_pi (fun _ => aemeasurable_id))
    (fun i => measurePreserving_eval (fun _ : Fin N => AronowAudit.P018.rareLaw) i)
    (K := fun uv : AronowAudit.P018.RareUnit × AronowAudit.P018.RareUnit =>
      (AronowAudit.P018.rareS uv.1 uv.2)^2)
    (measurable_of_countable _)
    (AronowAudit.P018.Wave1.WeightedConsistency.firstUnit_ne_secondUnit d)
  simpa only [AronowAudit.P018.rareQ, AronowAudit.P018.repeatedLaw,
    AronowAudit.P018.rareRepeated] using h

private lemma integral_rare_S (N : ℕ) :
    (∫ ω : Fin N → AronowAudit.P018.RareUnit,
      AronowAudit.P018.Wave1.TailB_rare_S ω
        ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) =
      AronowAudit.P018.Dreal N * AronowAudit.P018.rareQ := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
    infer_instance
  change (∫ ω : Fin N → AronowAudit.P018.RareUnit,
    ∑ d : AronowAudit.P018.Dyad N,
      (AronowAudit.P018.rareS (ω (AronowAudit.P018.firstUnit d))
        (ω (AronowAudit.P018.secondUnit d)))^2
      ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) = _
  rw [integral_finsetSum univ (fun d _ => kernel_pair_square_integrable d)]
  simp_rw [kernel_pair_square_integral]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    AronowAudit.P018.Wave1.printed_card_real]

private lemma integral_rare_S_integrable (N : ℕ) :
    Integrable (AronowAudit.P018.Wave1.TailB_rare_S :
      (Fin N → AronowAudit.P018.RareUnit) → ℝ)
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
    infer_instance
  unfold AronowAudit.P018.Wave1.TailB_rare_S
  exact integrable_finset_sum univ (fun d _ => kernel_pair_square_integrable d)

private lemma mean_rare_gram (N : ℕ) :
    AronowAudit.P018.meanMat
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N)
      (AronowAudit.P018.repeatedGram AronowAudit.P018.rareRepeated) =
      !![2*AronowAudit.P018.Dreal N, 2*AronowAudit.P018.Dreal N;
        2*AronowAudit.P018.Dreal N,
        2*AronowAudit.P018.Dreal N + 2*AronowAudit.P018.Dreal N*AronowAudit.P018.rareQ] := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
    infer_instance
  have hS := integral_rare_S N
  have hSi := integral_rare_S_integrable N
  have hbr : (∫ ω : Fin N → AronowAudit.P018.RareUnit,
      2*AronowAudit.P018.Dreal N + 2*AronowAudit.P018.Wave1.TailB_rare_S ω
        ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) =
      2*AronowAudit.P018.Dreal N + 2*AronowAudit.P018.Dreal N*AronowAudit.P018.rareQ := by
    rw [integral_add (integrable_const _) (hSi.const_mul 2)]
    rw [integral_const, integral_const_mul, hS]
    simp
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AronowAudit.P018.meanMat, AronowAudit.P018.Wave1.TailB_rare_gram,
      hS, hbr]

end SAP.P018b.WH.W1.P.T19_L2

open SAP.P018b.WH.W1
open AronowAudit.P018 MeasureTheory

theorem SAP.P018b.WH.W1.T19_L2_proof : SAP.P018b.WH.W1.T19_L2 := by
  intro N hN
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  have hto : SAP.P018b.Bridge.toRepeated
      (SAP.P018b.wholeRareKernel SAP.P018b.WH.W1.rareModel) =
      AronowAudit.P018.rareRepeated := rfl
  have hL' : AronowAudit.P018.repeatedL AronowAudit.P018.rareRepeated N =
      2*AronowAudit.P018.Dreal N := by
    simp [AronowAudit.P018.repeatedL, AronowAudit.P018.rareRepeated]
    rw [AronowAudit.P018.Wave1.printed_dyads_card_real]
    ring
  have hL : SAP.P018b.repeatedL
      (SAP.P018b.wholeRareKernel SAP.P018b.WH.W1.rareModel) N =
      2*SAP.P018b.Dreal N := by
    rw [SAP.P018b.Bridge.repeatedL_eq, hto, hL']
    rfl
  have hd : AronowAudit.P018.Dreal N ≠ 0 :=
    (AronowAudit.P018.Wave1.TailB_rare_D_pos hN).ne'
  have hq : SAP.P018b.wholeRareQ SAP.P018b.WH.W1.rareModel =
      AronowAudit.P018.rareQ := rfl
  have hMean : SAP.P018b.meanMat
      (SAP.P018b.repeatedLaw (SAP.P018b.wholeRareKernel SAP.P018b.WH.W1.rareModel) N)
      (SAP.P018b.repeatedGram (SAP.P018b.wholeRareKernel SAP.P018b.WH.W1.rareModel)) =
      !![2*AronowAudit.P018.Dreal N, 2*AronowAudit.P018.Dreal N;
        2*AronowAudit.P018.Dreal N,
        2*AronowAudit.P018.Dreal N + 2*AronowAudit.P018.Dreal N*AronowAudit.P018.rareQ] := by
    rw [SAP.P018b.Bridge.meanMat_eq,
      SAP.P018b.Bridge.repeatedLaw_eq, SAP.P018b.Bridge.repeatedGram_eq, hto]
    exact SAP.P018b.WH.W1.P.T19_L2.mean_rare_gram N
  change (SAP.P018b.repeatedL
      (SAP.P018b.wholeRareKernel SAP.P018b.WH.W1.rareModel) N)⁻¹ •
    SAP.P018b.meanMat
      (SAP.P018b.repeatedLaw (SAP.P018b.wholeRareKernel SAP.P018b.WH.W1.rareModel) N)
      (SAP.P018b.repeatedGram (SAP.P018b.wholeRareKernel SAP.P018b.WH.W1.rareModel)) =
      !![1,1;1,1+AronowAudit.P018.rareQ]
  rw [hL, hMean]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, SAP.P018b.Bridge.Dreal_eq] <;>
    field_simp [hd] <;> ring

end
