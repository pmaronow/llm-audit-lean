import SAP.P018b.Defs.WholeW1
import SAP.P018b.Bridge
import AronowAudit.P018.Wave1.Gap.GLP0181B3
import AronowAudit.P018.Wave1.Gap.GP0181B2
import AronowAudit.P018.Wave1.WeightedConsistency

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The existing rare-category construction, with all four used coordinates exposed. -/
def rareModel : WholeRareModel AronowAudit.P018.RareUnit :=
  ⟨AronowAudit.P018.rareLaw, fun u => u.m, fun u => u.label.val, fun u => u.A, fun u => u.B⟩

theorem rareScale_eq {N : ℕ} (ω : Fin N → AronowAudit.P018.RareUnit) :
    wholeRareScale rareModel ω = AronowAudit.P018.Wave1.TailB_rare_s ω := rfl

theorem rareSignal_eq {N : ℕ} (ω : Fin N → AronowAudit.P018.RareUnit) :
    wholeRareSignal rareModel ω = AronowAudit.P018.Wave1.TailB_rare_a ω := rfl

theorem rareVariance_eq {N : ℕ} (ω : Fin N → AronowAudit.P018.RareUnit) :
    repeatedVariance (wholeRareKernel rareModel) ω =
      AronowAudit.P018.repeatedVariance AronowAudit.P018.rareRepeated ω := rfl

theorem rareModel_law : wholeRareLaw rareModel := by
  refine ⟨AronowAudit.P018.Wave1.TailB_rare_probability,
    measurable_of_countable _, measurable_of_countable _, measurable_of_countable _,
    measurable_of_countable _, fun u => u.label.isLt, ?_⟩
  intro m c a b
  have he : {u : AronowAudit.P018.RareUnit | u.m = m ∧ u.label.val = c.val ∧ u.A = a ∧ u.B = b} =
      {AronowAudit.P018.RareUnit.mk m c a b} := by
    ext u
    constructor
    · rintro ⟨hm, hc, ha, hb⟩
      cases u with | mk n d e f =>
        dsimp only at hm hc ha hb
        subst n; subst e; subst f
        have hd : d = c := Fin.ext hc
        subst d
        rfl
    · intro h
      cases Set.mem_singleton_iff.mp h
      exact ⟨rfl,rfl,rfl,rfl⟩
  change AronowAudit.P018.rareLaw {u | u.m=m ∧ u.label.val=c.val ∧ u.A=a ∧ u.B=b} = _
  rw [he, AronowAudit.P018.Wave1.TailB_rare_atom]
  rfl

theorem rareModel_bounds : wholeRareBounds rareModel := by
  constructor
  · intro N d t u v j
    have hs := AronowAudit.P018.Wave1.TailB_rare_s_bounds u v
    change 0 ≤ (![1,1+(if t.val=0 then AronowAudit.P018.rareS u v else -AronowAudit.P018.rareS u v)] : Vec 2) j ∧
      (![1,1+(if t.val=0 then AronowAudit.P018.rareS u v else -AronowAudit.P018.rareS u v)] : Vec 2) j ≤ 2
    fin_cases j
    · norm_num
    · change 0 ≤ 1+(if t.val=0 then AronowAudit.P018.rareS u v else -AronowAudit.P018.rareS u v) ∧
        1+(if t.val=0 then AronowAudit.P018.rareS u v else -AronowAudit.P018.rareS u v) ≤ 2
      split_ifs <;> constructor <;> linarith
  · intro N d t u v
    have ha := AronowAudit.P018.Wave1.TailB_rare_a_bound u v
    have hb : |signValue u.B + signValue v.B| ≤ 2 := by
      cases u.B <;> cases v.B <;> norm_num [signValue]
    change |signValue u.B + signValue v.B +
      (if t.val=0 then AronowAudit.P018.rareA u v else -AronowAudit.P018.rareA u v)| ≤ 4
    have ht : |if t.val=0 then AronowAudit.P018.rareA u v else -AronowAudit.P018.rareA u v| ≤ 2 := by
      split_ifs <;> simpa only [abs_neg] using ha
    exact (abs_add_le _ _).trans (by linarith)

theorem rareModel_finite : wholeRareFiniteFit rareModel := by
  intro N hN ω
  refine ⟨AronowAudit.P018.Wave1.TailB_rare_S_pos hN ω,
    AronowAudit.P018.Wave1.TailB_rare_gram_det ω,
    AronowAudit.P018.Wave1.TailB_rare_gram_pos hN ω, ?_, ?_,
    AronowAudit.P018.Wave1.TailB_rare_residual_bound hN ω, ?_⟩
  · have h := AronowAudit.P018.Wave1.TailB_rare_exact_fit hN ω
    rw [AronowAudit.P018.Wave1.TailB_rare_U_mean hN ω] at h
    exact h
  · intro d t
    have h := AronowAudit.P018.Wave1.TailB_rare_residual_formula hN ω d t
    rw [AronowAudit.P018.Wave1.TailB_rare_U_mean hN ω] at h
    have hb : repeatedOLS (wholeRareKernel rareModel) ω 1 =
        AronowAudit.P018.Wave1.TailB_rare_W ω / AronowAudit.P018.Wave1.TailB_rare_S ω :=
      congrFun (AronowAudit.P018.Wave1.TailB_rare_exact_fit hN ω) 1
    rw [hb]
    convert h using 1 <;> first | rfl | (simp only [wholeRareSignal, wholeRareScale,
      wholeRareMeanB, AronowAudit.P018.Wave1.TailB_rare_a,
      AronowAudit.P018.Wave1.TailB_rare_s, AronowAudit.P018.Wave1.TailB_rare_u,
      AronowAudit.P018.Wave1.TailB_rare_Bbar, mul_comm]; rfl)
  · dsimp only
    have h := AronowAudit.P018.Wave1.TailB_rare_variance_formula hN ω
    have hb : repeatedOLS (wholeRareKernel rareModel) ω 1 =
        AronowAudit.P018.Wave1.TailB_rare_W ω / AronowAudit.P018.Wave1.TailB_rare_S ω :=
      congrFun (AronowAudit.P018.Wave1.TailB_rare_exact_fit hN ω) 1
    rw [rareVariance_eq, hb, h]
    simp only [wholeRareSsq, rareScale_eq, rareSignal_eq,
      AronowAudit.P018.Wave1.TailB_rare_r]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro f hf
    by_cases ho : overlap d f
    · simp only [show AronowAudit.P018.overlap d f from ho, ho, if_true]
      ring
    · simp only [show ¬ AronowAudit.P018.overlap d f from ho, ho, if_false]

theorem rareModel_moments : wholeRareMoments rareModel := by
  exact ⟨AronowAudit.P018.Wave1.TailB_rare_coefficient_integrals,
    fun N hN => ⟨AronowAudit.P018.Wave1.TailB_rare_positive_part_integral N hN,
      AronowAudit.P018.Wave1.TailB_rare_negative_part_integral N hN⟩⟩

theorem rareModel_limits : wholeRareLimits rareModel := by
  have hv : 0 < wholeRareV rareModel := AronowAudit.P018.Wave1.tb09_rare_limit_variance_pos
  refine ⟨hv, ?_, ?_, AronowAudit.P018.Wave1.tb09_rare_variance_limit,
    AronowAudit.P018.Wave1.tb09_rare_gaussian_limit⟩
  · apply AronowAudit.P018.positive_definite_two
    · linarith
    · nlinarith
  · norm_num [wholeRareLimitMatrix, Matrix.det_fin_two]
    ring

/-- Direct consequence of Gaussian full support, for the actual finite input law. -/
theorem simulation_positive_of_nhds {N T : ℕ} {s : Set (SimulationIndex N T → ℝ)}
    {ω : SimulationIndex N T → ℝ} (hs : s ∈ 𝓝 ω) : 0 < simulationLaw N T s := by
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  change 0 < Measure.pi (fun _ : SimulationIndex N T => gaussianReal 0 1) s
  exact MeasureTheory.Measure.measure_pos_of_mem_nhds _ hs

end SAP.P018b.WH.W1
