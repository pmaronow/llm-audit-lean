import SAP.P016a.Defs
import SAP.P016a.Bridge
import AronowAudit.P016.P016_Interference
import AronowAudit.P016.Wave1.Gap.GLP027P016P031P016B2
import AronowAudit.P016.Wave1.Gap.FidP016

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P016a
open scoped BigOperators

theorem SAP.P016a.T1 : T1Statement := by
  exact ⟨AronowAudit.P016.complete4_support, AronowAudit.P016.blocked4_support, AronowAudit.P016.t1_pairing_witness,
    AronowAudit.P016.t1_design_tables, AronowAudit.P016.t1_design_probabilities⟩

theorem SAP.P016a.T2 : T2Statement := by
  refine ⟨@AronowAudit.P016.t2_least_squares, @AronowAudit.P016.t2_decomposition, @AronowAudit.P016.t2_tail_equivalence, ?_,
    @AronowAudit.P016.t2_group_moments, @AronowAudit.P016.t2_margin_invariance, ?_, AronowAudit.P016.t2_network_alignment,
    AronowAudit.P016.t2_scalar_ks_witness, (fun u z _ _ => AronowAudit.P016.rss_groups u z), ?_⟩
  · intro n Ω _ P hn u zobs assign h0 h1 hsize
    exact AronowAudit.P016.t2_tail_probability (Bridge.toLaw P) hn u zobs assign h0 h1 hsize
  · intro n Ω _ P hn u assign n0 n1 h0 h1 hsize
    exact AronowAudit.P016.t2_design_dependence (Bridge.toLaw P) hn u assign n0 n1 h0 h1 hsize
  · intro n u z h0 h1
    exact (AronowAudit.P016.t10_general_least_squares u z h0 h1 (basicX z)).1

theorem SAP.P016a.T3 : T3Statement := by
  exact ⟨AronowAudit.P016.t3_four_unit_exposure, AronowAudit.P016.t3_six_unit_exposure, AronowAudit.P016.t3_determinants,
    AronowAudit.P016.t3_table_not_affine, AronowAudit.P016.t3_cutoff_witness⟩

theorem SAP.P016a.T4 : T4Statement := by
  refine ⟨@AronowAudit.P016.t4_application_mapping, @AronowAudit.P016.t4_standardization, ?_,
    AronowAudit.P016.t4_centering_not_rescaling, @AronowAudit.P016.t4_tail_coverage,
    AronowAudit.P016.t4_cutoff_difference, SAP.P016a.T3⟩
  intro n N hn s bank hbank z m hz hm
  have h := AronowAudit.P016.t4_similarity_orientation hn s bank hbank z m hz hm
  exact ⟨h.1, h.2.1, fun hD _hS => h.2.2 hD⟩

theorem SAP.P016a.T6 : T6Statement := by
  exact ⟨@AronowAudit.P016.t6_printed_general_model_consistency, AronowAudit.P016.t6_printed_cutoff⟩

theorem SAP.P016a.T7 : T7Statement := by
  refine ⟨AronowAudit.P016.complete4_support, AronowAudit.P016.t7_mean_witness,
    AronowAudit.P016.t7_mean_rejects_truth, ?_, ?_,
    AronowAudit.P016.Wave1.t7_ks_witness_proof, ?_, ?_⟩
  · intro α hα
    have hzero : ∀ k : Fin 6, mass (uniformLaw (Fin 6)) (fun j =>
        meanDifference u4 (complete4 j) ≥
          meanDifference (additiveGenerate u4 (complete4 k) 10) (complete4 k)) = 0 :=
      fun k => (AronowAudit.P016.t7_mean_witness k).2.2.2.1
    simp only [hzero, hα]
    exact AronowAudit.P016.mass_all (AronowAudit.P016.uniformLaw (Fin 6))
  · intro k
    exact (AronowAudit.P016.t8_additive_mapping u4 (complete4 k) 10 10).2
  · intro z i j hi hj
    norm_num [additiveGenerate, bit, hi, hj]
    have hi8 : (i.val : ℝ) < 8 := by exact_mod_cast i.isLt
    have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    linarith
  · norm_num

theorem SAP.P016a.T8 : T8Statement := by
  refine ⟨@AronowAudit.P016.t8_additive_mapping, ?_, @AronowAudit.P016.t8_raw_mean_shift⟩
  intro n Ω _ P assign y0 t T α hα hα1
  exact AronowAudit.P016.t8_corrected_comparison (Bridge.toLaw P) assign y0 t T α hα hα1

theorem SAP.P016a.T9 : T9Statement := by
  refine ⟨AronowAudit.P016.t9_signed_ks_witness, AronowAudit.P016.t9_pooled_witness, AronowAudit.P016.t9_intercept_witness, ?_, ?_⟩
  · intro k
    exact (AronowAudit.P016.t1_design_tables.1 k).1
  · intro n hn Ω _ P u assign z
    refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
    all_goals simpa [mass, lowerP, upperP] using P.total

theorem SAP.P016a.T10 : T10Statement := by
  exact ⟨@AronowAudit.P016.t2_least_squares, @AronowAudit.P016.t10_general_least_squares,
    @AronowAudit.P016.t10_ks_supremum, @AronowAudit.P016.Wave1.t10_symmetric_network⟩

theorem SAP.P016a.T11 : T11Statement := by
  refine ⟨AronowAudit.P016.t11_ks_witness, AronowAudit.P016.t11_rss_witness, ?_, ?_⟩
  · intro i
    have hc : (fun j => !(complete4 5 j)) = complete4 0 := by
      funext j
      fin_cases j <;> rfl
    have h : ecdf u4 (complete4 5) true (u4 i) - ecdf u4 (complete4 5) false (u4 i) =
        (![-1/2,-1,-1/2,0] : Outcome 4) i := AronowAudit.P016.t9_signed_ks_witness.1 i
    have ht := AronowAudit.P016.ecdf_swap_labels u4 (complete4 5) true (u4 i)
    have hf := AronowAudit.P016.ecdf_swap_labels u4 (complete4 5) false (u4 i)
    change ecdf u4 (fun j => !(complete4 5 j)) true (u4 i) =
      ecdf u4 (complete4 5) false (u4 i) at ht
    change ecdf u4 (fun j => !(complete4 5 j)) false (u4 i) =
      ecdf u4 (complete4 5) true (u4 i) at hf
    rw [hc] at ht hf
    rw [ht, hf]
    fin_cases i <;> norm_num at h ⊢ <;> linarith
  · refine ⟨AronowAudit.P016.t12_ks_not_effect_increasing.1, AronowAudit.P016.t12_ks_not_effect_increasing.2, ?_, ?_⟩
    · intro h
      have hd : ∀ i : Fin 4, if complete4 0 i then
          (![0,2,0,2] : Outcome 4) i ≤ (![1,2,0,2] : Outcome 4) i
          else (![1,2,0,2] : Outcome 4) i ≤ (![0,2,0,2] : Outcome 4) i := by
        intro i
        fin_cases i <;> norm_num [complete4]
      have hi := h (complete4 0) ![0,2,0,2] ![1,2,0,2] hd
      have hb : rss ![0,2,0,2] (complete4 0) = 4 := AronowAudit.P016.t11_rss_witness.1
      have hl : rss ![1,2,0,2] (complete4 0) = 5/2 := AronowAudit.P016.t11_rss_witness.2.1
      rw [hb, hl] at hi
      norm_num at hi
    · intro h
      have hd : ∀ i : Fin 4, if complete4 0 i then
          (![0,2,0,2] : Outcome 4) i ≤ (![0,3,0,2] : Outcome 4) i
          else (![0,3,0,2] : Outcome 4) i ≤ (![0,2,0,2] : Outcome 4) i := by
        intro i
        fin_cases i <;> norm_num [complete4]
      have hi := h (complete4 0) ![0,2,0,2] ![0,3,0,2] hd
      have hb : rss ![0,2,0,2] (complete4 0) = 4 := AronowAudit.P016.t11_rss_witness.1
      have hu : rss ![0,3,0,2] (complete4 0) = 13/2 := AronowAudit.P016.t11_rss_witness.2.2.1
      dsimp only at hi
      rw [hb, hu] at hi
      norm_num at hi
