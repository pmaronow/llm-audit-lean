import SAP.P001d.Defs
import SAP.P001d.Bridge
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.TailA.HeavyMedian
import AronowAudit.P001.Wave1.Gap.TailA.MedianMoments
import AronowAudit.P001.Wave1.Gap.GP0014B1
import AronowAudit.P001.Wave1.Gap.WP001dB1
import SAP.P001d.WH.W1.Proofs.T74
import SAP.P001d.WH.W1.Proofs.T76
import SAP.P001d.WH.W1.Proofs.T66
import SAP.P001d.WH.W1.Proofs.T68
import SAP.P001d.WH.W1.Proofs.T69
import SAP.P001d.WH.W2.Proofs.T70
import SAP.P001d.WH.W2.Proofs.T73
import SAP.P001d.WH.W2.Proofs.T58
import SAP.P001d.WH.W2.Proofs.T61
import SAP.P001d.WH.W2.Proofs.T62
import SAP.P001d.WH.W3.Proofs.T64
import SAP.P001d.WH.W3.Proofs.T65

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d

theorem T58 : SAP.P001d.T58WholeStatement := SAP.P001d.WH.W2.T58_whole

theorem T59 : T59Statement := by
  intro n hn X K hp hnorm heven h hh
  simpa only [Bridge.kernelDensity_eq, Bridge.kernelCDF_eq] using
    AronowAudit.P001.nonnegative_kernel_cdf hn X K (integrable_of_integral_eq_one hnorm)
      hp hnorm heven h hh

theorem T60 : T60Statement := by
  intro n hn X h hh
  exact ⟨fun K hK x => AronowAudit.P001.kernel_cdf_correct_integrand hn X K hK h hh x,
    fun x hb => AronowAudit.P001.rectangular_kernel_empirical_cdf_identity hn X h hh x hb⟩

theorem T61 : SAP.P001d.T61WholeStatement := SAP.P001d.WH.W2.T61_whole

theorem T62 : SAP.P001d.T62WholeStatement := SAP.P001d.WH.W2.T62_whole

theorem T63 {Ω : Type*} [MeasurableSpace Ω] : T63Statement Ω := by
  intro μ hμ m hm X hiid h2
  have hiid' := (Bridge.iid_iff μ X).mp hiid
  have h := AronowAudit.P001.cluster_mean_properties μ hm X hiid' h2
  let g : (Fin m → ℝ) → ℝ := fun x => (∑ j, x j)/(m : ℝ)
  have hg : Measurable g := by unfold g; fun_prop
  have hW : IID μ (clusterAverage X) :=
    ⟨fun i => hg.comp (hiid.1 i), hiid.2.1.comp (fun _ => g) (fun _ => hg),
      fun i => (hiid.2.2 i).comp hg⟩
  refine ⟨hW, fun l hl => ⟨(h.1 l hl).1, (h.1 l hl).2.1⟩, h.2.1, ?_,
    Bridge.cp_succ μ _ _ h.2.2⟩
  intro l hl
  exact ⟨(h.1 l hl).2.2,
    AronowAudit.P001.cluster_variance_double_covariance_sum μ hm X hiid' h2 l hl⟩

theorem T64 : SAP.P001d.T64WholeStatement := SAP.P001d.WH.W3.T64_whole

theorem T65 : SAP.P001d.T65WholeStatement := SAP.P001d.WH.W3.T65_whole

theorem T66 : SAP.P001d.T66WholeStatement := SAP.P001d.WH.W1.T66_whole

theorem T67 {Ω : Type*} [MeasurableSpace Ω] : T67Statement Ω := by
  intro μ hμ K X hX ε hε hz σ2 hσ hv hXX hεXX hA
  have h := AronowAudit.P001.homoskedastic_population_moments μ X hX ε hε
    ((Bridge.cef_iff _ _ _ _).mp hz) σ2 hσ ((Bridge.cef_iff _ _ _ _).mp hv) hXX hεXX
  have he : populationMeat μ X ε = σ2 • populationGram μ X := by
    ext j k
    exact h.2 j k
  refine ⟨(Bridge.cef_iff _ _ _ _).mpr h.1, he, ?_⟩
  rw [he]
  exact AronowAudit.P001.homoskedastic_sandwich_identity (populationGram μ X) hA σ2

theorem T68 : SAP.P001d.T68WholeStatement := SAP.P001d.WH.W1.T68_whole

theorem T69 : SAP.P001d.T69WholeStatement := SAP.P001d.WH.W1.T69_whole

theorem T70 : SAP.P001d.T70WholeStatement := SAP.P001d.WH.W2.T70_whole

theorem T71 : T71Statement := by
  intro n K hn X Y
  have hz (b : Fin (K+1) → ℝ) : lassoCriterion X Y 0 b = olsRSS X Y b/(n : ℝ) :=
    (AronowAudit.P001.lasso_zero_penalty_ols X Y b).1
  have hp := AronowAudit.P001.slope_penalty_seminorm_and_unpenalized_intercept
    (0 : Fin (K+1) → ℝ) 0
  refine ⟨hz, ?_, ?_, hp.2.2.2.1, hp.2.2.2.2, ?_⟩
  · intro b
    simp only [hz, div_le_div_iff_of_pos_right (show (0 : ℝ) < n by exact_mod_cast hn)]
  · intro b c
    have h := AronowAudit.P001.slope_penalty_seminorm_and_unpenalized_intercept b c
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro lam hlam
    exact AronowAudit.P001.lasso_convex hn X Y lam hlam

theorem T72 : T72Statement := by
  intro K x b s hs
  have hc := Bridge.normalDensity_certificates (∑ k, x k*b k) s hs
  have h := AronowAudit.P001.classical_linear_positive_scale_cef x b s hs
  exact ⟨hc.1, hc.2.1, hc.2.2, h.1, h.2, by simp [normalDensity], by simp [normalDensity]⟩

theorem T73 : SAP.P001d.T73WholeStatement := SAP.P001d.WH.W2.T73_whole

theorem T74 : SAP.P001d.T74WholeStatement := SAP.P001d.WH.W1.T74_whole

theorem T75 : T75Statement := by
  intro K x b h hh
  have he := AronowAudit.P001.binary_choice_fixed_argument_mean x b h hh
  refine ⟨he.1, ?_⟩
  rw [show binaryChoiceMean x b h = h (∑ k, x k*b k) from he.1]
  exact he.2

theorem T76 : SAP.P001d.T76WholeStatement := SAP.P001d.WH.W1.T76_whole

end SAP.P001d
