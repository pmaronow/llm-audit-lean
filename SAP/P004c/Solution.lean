import SAP.P004c.Defs
import SAP.P004c.Bridge
import AronowAudit.P004.P004_RegressionCompletion
import AronowAudit.P004.P004_VarianceComponentsCompletion
import AronowAudit.P004.P004_VarianceOrderCompletion
import AronowAudit.P004.P004_KernelCompletion
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P004c SAP.P004c.Bridge MeasureTheory Filter
open scoped BigOperators Classical

theorem SAP.P004c.T31.{u} : T31Statement.{u} := by
  constructor
  · intro N X Y
    rfl
  · intro N R z
    have hc : armCount z true + armCount z false = N :=
      AronowAudit.P004.MatrixCompletion.counts_total z
    refine ⟨(AronowAudit.P004.MatrixCompletion.sum_bit z).symm, by linarith, ?_, ?_⟩
    · unfold armCount
      apply Finset.sum_congr rfl
      intro i _
      cases z i <;> norm_num [bit]
    · intro h1 h0
      refine ⟨(AronowAudit.P004.hajek_ols R z h1 h0).2, ?_⟩
      intro e
      constructor
      · intro K
        exact AronowAudit.P004.sandwich_sum_identity z e K
      · intro values vectors horth
        dsimp only
        obtain ⟨hQ, hD, hEQ, hED, hSQ, hSD, hV⟩ :=
          AronowAudit.P004.spectral_psd_order values vectors horth z e h1 h0
        refine ⟨spectral_difference values vectors, (psd_correspondence _).mp hQ,
          (psd_correspondence _).mp hD, (psd_correspondence _).mp hEQ,
          (psd_correspondence _).mp hED, (psd_correspondence _).mp hSQ,
          (psd_correspondence _).mp hSD, ?_⟩
        have hK : sandwich z e (spectralKernel values vectors false) 1 1 =
            kernelVariance z e (spectralKernel values vectors false) :=
          AronowAudit.P004.MatrixCompletion.sandwich_treatment z h1 h0 e _
        have hQ' : sandwich z e (spectralKernel values vectors true) 1 1 =
            kernelVariance z e (spectralKernel values vectors true) :=
          AronowAudit.P004.MatrixCompletion.sandwich_treatment z h1 h0 e _
        rw [hK, hQ']
        exact hV

theorem SAP.P004c.T32.{u} : T32Statement.{u} := by
  refine ⟨?_, ?_, diagonal_rate, ?_, ?_⟩
  · intro N p R B hN hp hself houtside
    refine ⟨ht_expansion p R B hN hp hself houtside, ?_⟩
    rw [ht_upper_correspondence, ht_expansion p R B hN hp hself houtside]
    exact le_add_of_nonneg_right
      (div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _))
  · intro N p b R B hN hp hb hself hsymm houtside
    have hc : 0 ≤ htDiagonal p R ∧ htDiagonal p R ≤ b^2/(N*p)+b^2/(N*(1-p)) ∧
        ∀ a c : Bool, |htPairCov p R B a c| ≤ 2*b^2*((maxDegree B : ℝ)-1)/N :=
      AronowAudit.P004.ht_variance_components p b R B hN hp hb hself
    exact ⟨⟨hc.1, hc.2.1⟩, hc.2.2,
      (AronowAudit.P004.ht_variance_bound p b R B hN hp hb hself hsymm houtside).2⟩
  · intro p b R B D hp hseq
    exact (component_rates p b R B D hp hseq).2
  · intro Space _ _ P p d hp hd hP hWD
    exact AronowAudit.P004.ht_variance_order (toSequence P) p d hp hd hP hWD

theorem SAP.P004c.T33 : T33Statement := by
  constructor
  · intro N p R B hN hp hself houtside
    dsimp only
    have hv : variance (fun _ => p) (linearHajek (fun _ => p) R) =
        secondMomentBound (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a) -
          homophilyQ (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a)/N :=
      AronowAudit.P004.hajek_variance_identity p R B hN hp hself houtside
    have hh : secondMomentBound (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a) -
        variance (fun _ => p) (linearHajek (fun _ => p) R) =
          homophilyQ (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a)/N ∧
        (variance (fun _ => p) (linearHajek (fun _ => p) R) ≤
          secondMomentBound (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a) ↔
            0 ≤ homophilyQ (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a)) :=
      AronowAudit.P004.hajek_homophily_identity (fun _ => p) R B hN (fun _ => hp) hself houtside
    simp only [homophily_correspondence] at hh
    exact ⟨hv.trans (expansion_correspondence _ _ _ _ hself), hh.1, hh.2, hh.2.mpr⟩
  · intro N p R hN hp hv
    exact AronowAudit.P004.ht_standardized_summands (fun _ => p) R hN (fun _ => hp) hv

theorem SAP.P004c.T34 : T34Statement := by
  refine ⟨?_, ?_, denominator_rate, AronowAudit.P004.missing_absolute_witness⟩
  · intro N z p S hN h1 hp
    exact AronowAudit.P004.denominator_absolute_identity N (armCount z true) p S
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)) h1.ne' hp.1.ne'
  · intro N z e D K b Kmax hN hb hK hs hD
    exact AronowAudit.P004.kernel_cross_sum_bound z e D K b Kmax hN hb hK hs hD

theorem SAP.P004c.T39 : T39Statement := by
  intro N p R _ hp
  have h : expect (fun _ => p) (ht (fun _ => p) R) = ame (fun _ => p) R :=
    AronowAudit.P004.ht_unbiased (fun _ => p) R (fun _ => hp)
  have hm (i : Fin N) (a : Bool) : marginal (fun _ => p) R i a =
      expect (fun _ => p) (fun z => R i (Function.update z i a)) :=
    AronowAudit.P004.marginal_is_marginalization (fun _ => p) R i a (fun _ => hp)
  simp only [ame, nodeEffect, hm] at h
  exact h

theorem SAP.P004c.T40.{u} : T40Statement.{u} := by
  intro N A _ _ P d w g f _ hw hwpos hY hWD
  exact AronowAudit.P004.additive_spatial_design_invariance (toPopulation P) d w hw hwpos g f hY hWD

theorem SAP.P004c.T41.{u} : T41Statement.{u} := by
  intro Space _ _ P p d hp hd hP hWD
  exact ⟨AronowAudit.P004.ht_variance_order (toSequence P) p d hp hd hP hWD,
    AronowAudit.P004.ht_central_limit (toSequence P) p d hp hd hP hWD⟩

theorem SAP.P004c.T42.{u} : T42Statement.{u} := by
  intro Space _ _ P p d hp hd hP hWD hv
  exact AronowAudit.P004.Wave1.hajek_central_limit_proof (toSequence P) p d hp hd hP hWD hv

theorem SAP.P004c.T44.{u} : T44Statement.{u} := by
  intro Space _ _ P p d hp hd hb hWD hNED hmetric hspacing
  obtain ⟨hu, hv, hr, hn⟩ :=
    AronowAudit.P004.Wave1.ned_headline_under_uniform_spacing
      (toSequence P) p d hp hd hb hWD hNED hmetric hspacing
  exact ⟨fun N _ _ => hu N, hv, hr, hn⟩
