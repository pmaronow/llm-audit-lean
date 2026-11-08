import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T9_L5

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
open Classical

noncomputable section

private abbrev frcLaw := AronowAudit.P019.Wave1.frc_law
private abbrev frcProduct := AronowAudit.P019.Wave1.t19_product frcLaw
private abbrev frcSample := AronowAudit.P019.Wave1.t19_sample (Ω := Fin 128)
private abbrev srcStudy := AronowAudit.P019.sequentialStudy

private lemma source_cellCount_eq {n : ℕ} (j : Fin 5) (s : Fin n → Fin 128)
    (z y : Bool) :
    (srcStudy j).cellCount s z y =
      (SAP.P019a.sequentialStudy j).cellCount s z y := by
  unfold AronowAudit.P019.Study.cellCount SAP.P019a.Study.cellCount
  apply Finset.sum_congr rfl
  intro i hi
  have hseq := SAP.P019a.Bridge.sequentialStudy_eq j
  have hz : (srcStudy j).Z = (SAP.P019a.sequentialStudy j).Z := by
    have hh := congrArg (fun S : AronowAudit.P019.Study (Fin 128) => S.Z) hseq
    simpa [srcStudy, SAP.P019a.Bridge.toStudy] using hh.symm
  have hy : (srcStudy j).Y = (SAP.P019a.sequentialStudy j).Y := by
    have hh := congrArg (fun S : AronowAudit.P019.Study (Fin 128) => S.Y) hseq
    simpa [srcStudy, SAP.P019a.Bridge.toStudy] using hh.symm
  have hcell : (srcStudy j).cell z y (s i) ↔
      (SAP.P019a.sequentialStudy j).cell z y (s i) := by
    change ((srcStudy j).Z (s i) = z ∧ (srcStudy j).Y (s i) = y) ↔
      ((SAP.P019a.sequentialStudy j).Z (s i) = z ∧
        (SAP.P019a.sequentialStudy j).Y (s i) = y)
    rw [hz, hy]
  by_cases hc : (SAP.P019a.sequentialStudy j).cell z y (s i)
  · have hs : (srcStudy j).cell z y (s i) := hcell.mpr hc
    simp [hc, hs]
  · have hs : ¬ (srcStudy j).cell z y (s i) := fun hs => hc (hcell.mp hs)
    simp [hc, hs]

private lemma cell_count_eventually_ae (j : Fin 5) (z : Bool) :
    ∀ᵐ ω ∂frcProduct, ∀ᶠ n in atTop,
      2 ≤ (srcStudy j).cellCount (frcSample n ω) z true := by
  have hs := (AronowAudit.P019.Wave1.fisher_sequential_finite_proof.1 j).1
  have hp : 0 < frcLaw.prob ((srcStudy j).cell z true) :=
    (hs.2.2.2.1 z true).1
  have h := AronowAudit.P019.Wave1.GP019B3b_cell_ae frcLaw
    (fun _ : Fin 128 => (0 : ℝ)) ((srcStudy j).cell z true) 0 hp
  filter_upwards [h] with ω hω
  exact hω.2.1

private lemma variance_positive_eventually_ae (j : Fin 5) :
    ∀ᵐ ω ∂frcProduct, ∀ᶠ n in atTop,
      0 < (srcStudy j).betaVarianceHat (frcSample n ω) 0 := by
  filter_upwards [AronowAudit.P019.Wave1.frc_variance_consistency j] with ω hω
  have hlarge := hω.eventually
    (Ioi_mem_nhds (AronowAudit.P019.Wave1.frc_v_pos j))
  filter_upwards [hlarge, Filter.eventually_gt_atTop (0 : ℕ)] with n hlarge hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hprod : 0 < (n : ℝ) * (srcStudy j).betaVarianceHat (frcSample n ω) 0 := hlarge
  rcases mul_pos_iff.mp hprod with ⟨_, hv⟩ | ⟨hnneg, _⟩
  · exact hv
  · exact (lt_asymm hnpos hnneg).elim

private lemma whole_defined_eventually_ae :
    ∀ᵐ ω ∂frcProduct, ∀ᶠ n in atTop,
      SAP.P019a.wholeT9Defined (frcSample n ω) := by
  have hc : ∀ᵐ ω ∂frcProduct, ∀ j : Fin 5,
      (∀ᶠ n in atTop, 2 ≤ (srcStudy j).cellCount (frcSample n ω) true true) ∧
      (∀ᶠ n in atTop, 2 ≤ (srcStudy j).cellCount (frcSample n ω) false true) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [cell_count_eventually_ae j true,
      cell_count_eventually_ae j false] with ω ht hf
    exact ⟨ht, hf⟩
  have hv : ∀ᵐ ω ∂frcProduct, ∀ j : Fin 5,
      ∀ᶠ n in atTop, 0 < (srcStudy j).betaVarianceHat (frcSample n ω) 0 := by
    rw [ae_all_iff]
    exact variance_positive_eventually_ae
  filter_upwards [hc, hv] with ω hcounts hvars
  have hgood : ∀ᶠ n in atTop, ∀ j : Fin 5,
      2 ≤ (srcStudy j).cellCount (frcSample n ω) true true ∧
      2 ≤ (srcStudy j).cellCount (frcSample n ω) false true ∧
      0 < (srcStudy j).betaVarianceHat (frcSample n ω) 0 := by
    rw [Filter.eventually_all]
    intro j
    filter_upwards [(hcounts j).1, (hcounts j).2, hvars j] with n hct hcf hvj
    exact ⟨hct, hcf, hvj⟩
  filter_upwards [hgood] with n hn
  intro j
  refine ⟨?_, ?_, ?_⟩
  · rw [← source_cellCount_eq j (frcSample n ω) true true]
    exact (hn j).1
  · rw [← source_cellCount_eq j (frcSample n ω) false true]
    exact (hn j).2.1
  · rw [SAP.P019a.Bridge.sequential_betaVarianceHat_eq j (frcSample n ω) 0]
    exact (hn j).2.2

private lemma indicator_transfer_to_one :
    Tendsto (fun n : ℕ => (frcLaw.iid n).prob
      (fun s => SAP.P019a.wholeT9Defined s)) atTop (nhds 1) := by
  let E : (n : ℕ) → (Fin n → Fin 128) → Prop := fun _ _ => ∃ _ : Unit, True
  have he : ∀ᵐ ω ∂frcProduct, ∀ᶠ n in atTop,
      (SAP.P019a.wholeT9Defined (frcSample n ω) ↔ E n (frcSample n ω)) := by
    filter_upwards [whole_defined_eventually_ae] with ω hω
    filter_upwards [hω] with n hn
    simp [E, hn]
  have htr := AronowAudit.P019.Wave1.t19_indicator_transfer frcLaw
    (fun n s => SAP.P019a.wholeT9Defined s) E he
  have htrue (n : ℕ) :
      @AronowAudit.P019.FiniteLaw.prob (Fin n → Fin 128) inferInstance
        (frcLaw.iid n) (E n) (fun s => Classical.propDecidable (E n s)) = 1 := by
    rw [AronowAudit.P019.FiniteLaw.prob]
    have hE : (fun s : Fin n → Fin 128 =>
        @ite ℝ (E n s) (Classical.propDecidable (E n s)) 1 0) = fun _ => 1 := by
      funext s
      exact if_pos ⟨(), trivial⟩
    calc
      _ = (frcLaw.iid n).mean (fun _ => (1 : ℝ)) :=
        congrArg (frcLaw.iid n).mean hE
      _ = 1 := AronowAudit.P019.mean_const _ _
  have h := htr.add_const 1
  have h' : Tendsto (fun n : ℕ =>
      ((frcLaw.iid n).prob (fun s => SAP.P019a.wholeT9Defined s) - 1) + 1)
      atTop (nhds (0 + 1)) := by
    convert h using 1
    · funext n
      rw [htrue n]
  simpa only [sub_add_cancel, zero_add] using h'

end

end SAP.P019a.WH.W1.P.T9_L5

open SAP.P019a.WH.W1.P.T9_L5
open Filter

theorem SAP.P019a.WH.W1.T9_L5_proof : SAP.P019a.WH.W1.T9_L5 := by
  classical
  let P : SAP.P019a.FiniteLaw (Fin 128) := SAP.P019a.uniformFin 128 (by norm_num)
  have hunif : SAP.P019a.Bridge.toLaw P = frcLaw := by
    dsimp [P, frcLaw]
    exact SAP.P019a.Bridge.uniformFin_eq 128 (by norm_num)
  have hprob (n : ℕ) :
      (P.iid n).prob (fun s => SAP.P019a.wholeT9Defined s) =
        (frcLaw.iid n).prob (fun s => SAP.P019a.wholeT9Defined s) := by
    calc
      _ = (SAP.P019a.Bridge.toLaw (P.iid n)).prob
          (fun s => SAP.P019a.wholeT9Defined s) :=
            (SAP.P019a.Bridge.prob_eq (P.iid n)
              (fun s => SAP.P019a.wholeT9Defined s)).symm
      _ = ((SAP.P019a.Bridge.toLaw P).iid n).prob
          (fun s => SAP.P019a.wholeT9Defined s) := by
            rw [← SAP.P019a.Bridge.iid_eq]
      _ = _ := by rw [hunif]
  change Tendsto (fun n => (P.iid n).prob
    (fun s => SAP.P019a.wholeT9Defined s)) atTop (nhds 1)
  apply (indicator_transfer_to_one).congr'
  filter_upwards [] with n
  exact hprob n

