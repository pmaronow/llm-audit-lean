import SAP.P045a.Defs.WholeW1
import SAP.P045a.Bridge
import AronowAudit.P045.P045_Spillover
import AronowAudit.P045.Wave1.Gap.GLP041P042P045P045B2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W1
open SAP.P045a.Bridge

theorem retained_T1 : T1Statement := by
  rcases AronowAudit.P045.bernoulli_ratio_counterexample with
    ⟨hcard,htotal,hmarg,hcount,hdirect,hcorr,hp1,hp0,hpI,hpT,hI,hT,hpAll,hIAll,hTAll,hmean,hO⟩
  refine ⟨⟨hcard,htotal,hmarg,hcount,hdirect,hp1,hp0,hpI,hpT,hI,hT,hpAll,hIAll,hTAll,hmean,hO⟩,?_,
    AronowAudit.P045.bernoulli_direct_failure_means,
    AronowAudit.P045.bernoulli_direct_failure.2.2.2.1,
    AronowAudit.P045.bernoulli_direct_failure.2.1⟩
  rcases AronowAudit.P045.bernoulli_count_counterexample with ⟨_,_,hA,hB,hC,hD,_⟩
  exact ⟨(hcorr (1/2) (by norm_num) (by norm_num) true).trans hA,
    (hcorr (1/2) (by norm_num) (by norm_num) false).trans hB,
    (hcorr (1/4) (by norm_num) (by norm_num) true).trans hC,
    (hcorr (1/4) (by norm_num) (by norm_num) false).trans hD⟩

theorem retained_T2 : T2Statement := by
  rcases AronowAudit.P045.marginal_estimator_correction with ⟨h1,h2,h3,h4,h5,h6⟩
  refine ⟨?_,?_,?_,?_,h4,?_,?_,?_,AronowAudit.P045.co_members_group_ht_expectation⟩
  · exact @AronowAudit.P045.bernoulli_group_ht_unbiased
  · intro G C hC hCG n hn p hp hp1 y b
    have h := h2 G C hC hCG n hn (fun _ => AronowAudit.P045.bernoulli p)
      (fun g z => (AronowAudit.P045.bernoulliDesign (n g) p (le_of_lt hp) (le_of_lt hp1)).nonneg z)
      (fun g => AronowAudit.P045.bernoulli_total (n g) p)
      (fun g => AronowAudit.P045.groupHT p (y g) b)
    refine h.trans ?_
    congr 1
    funext g
    exact (h1 (n g) (hn g) p hp hp1 (y g) b).2
  · exact @AronowAudit.P045.cr_group_arm_unbiased
  · intro G C hC hCG n k hk y b
    have hn : ∀ g, 0 < n g := fun g => lt_trans (hk g).1 (hk g).2
    have h := h2 G C hC hCG n hn (fun g => AronowAudit.P045.crMass (n g) (k g))
      (fun g z => (AronowAudit.P045.cr_mass_probability (le_of_lt (hk g).2)).1 z)
      (fun g => (AronowAudit.P045.cr_mass_probability (le_of_lt (hk g).2)).2)
      (fun g => AronowAudit.P045.armMean (y g) b)
    refine h.trans ?_
    congr 1
    funext g
    exact h3 (n g) (k g) (hk g).1 (hk g).2 (y g) b
  · intro n hn q y
    exact h5 n hn (design q) y
  · intro G C hC hCG n hn q y
    have h := h2 G C hC hCG n hn (fun g => (q g).mass)
      (fun g z => (q g).nonneg z) (fun g => (q g).total)
      (fun g => AronowAudit.P045.groupOverall (y g))
    refine h.trans ?_
    congr 1
    funext g
    exact h5 (n g) (hn g) (design (q g)) (y g)
  · intro p hp hp1 z
    exact AronowAudit.P045.co_members_group_ht_formula p z

theorem retained_T3 : T3Statement := by
  exact ⟨AronowAudit.P045.singleton_variance_counterexample,
    AronowAudit.P045.singleton_group_finite_moments⟩

theorem retained_T5 : T5Statement := by
  exact AronowAudit.P045.full_neighborhood_counterexample

theorem retained_T7 : T7Statement := by
  refine ⟨AronowAudit.P045.faulty_copy_counterexample, ?_⟩
  have h := AronowAudit.P045.faulty_copy_full_counterexample
  simp only [matrixExposure_pred, decode_d01, decode_d00] at h
  exact h

end SAP.P045a.WH.W1
