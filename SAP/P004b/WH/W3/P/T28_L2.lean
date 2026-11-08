import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.Gap.TailBNedHac

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped BigOperators Matrix Classical Topology
open SAP.P004b

noncomputable section

theorem SAP.P004b.WH.W3.T28_L2_proof : SAP.P004b.WH.W3.T28_L2 := by
  intro p R Q V E hp hV hclt hbias herr hbad α hα0 hα1
  let π : ∀ N, Fin N → ℝ := fun _ _ => p
  let U : ∀ N, Assignment N → ℝ := fun N z =>
    hajek (R N) z - ame (fun _ => p) (R N)
  let W : ∀ N, Assignment N → ℝ := fun N z =>
    kernelVariance z (residual (R N) z) (Q N)
  have hπ : AronowAudit.P004.Wave1.DesignLimits.AdmissibleSeq π := by
    intro N i
    exact hp
  have hVpos : ∀ᶠ N in atTop, 0 < V N := by
    obtain ⟨v, hv0, hvN⟩ := hV
    filter_upwards [hvN, eventually_gt_atTop 0] with N hfloor hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact (pos_of_mul_pos_right (hv0.trans_le hfloor) hN'.le)
  have hshort : ∀ η : ℝ, 0 < η → η < 1 →
      Tendsto (fun N => prob (π N) (fun z => W N z < (1-η)*V N))
        atTop (nhds 0) := by
    intro η hη _
    obtain ⟨v, hv0, hvN⟩ := hV
    have he : 0 < η*v/2 := by positivity
    apply squeeze_zero' (g := fun N => prob (π N)
      (fun z => η*v/2 < |(N : ℝ)*(W N z-E N)|))
    · exact Eventually.of_forall (fun N =>
        AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_nonneg
          (π N) (hπ N) _)
    · filter_upwards [hvN, hbias (η*v/2) he, eventually_gt_atTop 0]
        with N hfloor hbiasN hN
      apply AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_mono
        (π N) (hπ N)
      intro z hz
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hscaled := mul_lt_mul_of_pos_left hz hN'
      have hfloor' := mul_le_mul_of_nonneg_left hfloor hη.le
      have habs := neg_le_abs ((N : ℝ)*(W N z-E N))
      nlinarith
    · exact herr _ he
  have honeside :=
    AronowAudit.P004.Wave1.GP0042B2b_capped_pd_one_sided_wald
      π hπ U W V hVpos hclt hshort α ⟨hα0, hα1⟩
  obtain ⟨_, hstrict, _, hneg, hquant, _, _⟩ :=
    AronowAudit.P004.Wave1.DesignLimits.nf_proof
  have hqlow : AronowAudit.P004.normalQuantile (α/2) =
      -AronowAudit.P004.normalQuantile (1-α/2) := by
    apply hstrict.injective
    rw [hquant (α/2) (by linarith) (by linarith), hneg,
      hquant (1-α/2) (by linarith) (by linarith)]
    ring
  intro ε hε
  have hgood := honeside (ε/2) (by linarith)
  have hbadP : Tendsto (fun N => AronowAudit.P004.prob
      (fun _ : Fin N => p) (fun z : Assignment N => ¬ ValidArms z))
      atTop (nhds 0) := by
    simpa only [show ∀ N (A : Assignment N → Prop),
      prob (fun _ : Fin N => p) A = AronowAudit.P004.prob (fun _ => p) A
        from fun N A => rfl] using hbad
  have hbadsmall : ∀ᶠ N in atTop,
      AronowAudit.P004.prob (fun _ : Fin N => p)
        (fun z : Assignment N => ¬ ValidArms z) < ε/2 := by
    exact (tendsto_order.mp hbadP).2 _ (by linarith)
  filter_upwards [hgood, hbadsmall] with N hgoodN hbadN
  let A : Assignment N → Prop := fun z =>
    0 < W N z ∧ |U N z| ≤ AronowAudit.P004.normalQuantile (1-α/2)*Real.sqrt (W N z)
  let C : Assignment N → Prop := fun z =>
    wholeCovered p (R N) (Q N) (normalQuantile (α/2))
      (normalQuantile (1-α/2)) z
  have hcover : ∀ z, A z → ¬ (fun _ : Assignment N => False) z →
      ¬ (fun z : Assignment N => ¬ ValidArms z) z → C z := by
    intro z hz _ hnotbad
    have hvalid : ValidArms z := by
      by_contra hn
      exact hnotbad hn
    have hs : 0 < Real.sqrt (W N z) := Real.sqrt_pos.mpr hz.1
    have hquot : |U N z/Real.sqrt (W N z)| ≤
        AronowAudit.P004.normalQuantile (1-α/2) := by
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      exact hz.2
    have hbounds := abs_le.mp hquot
    change wholeCovered p (R N) (Q N) (normalQuantile (α/2))
      (normalQuantile (1-α/2)) z
    unfold wholeCovered ValidInterval
    refine ⟨⟨hvalid, hz.1⟩, ?_, ?_⟩
    · change AronowAudit.P004.normalQuantile (α/2) ≤
        U N z/Real.sqrt (W N z)
      rw [hqlow]
      exact hbounds.1
    · change U N z/Real.sqrt (W N z) ≤
        AronowAudit.P004.normalQuantile (1-α/2)
      exact hbounds.2
  have hdiff :=
    AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_difference
      (π N) (hπ N) A (fun _ : Assignment N => False)
      (fun z : Assignment N => ¬ ValidArms z) C hcover
  have hfalse : AronowAudit.P004.prob (π N)
      (fun _ : Assignment N => False) = 0 := by
    simp [AronowAudit.P004.prob, AronowAudit.P004.expect]
  have hineq : AronowAudit.P004.prob (π N) A -
      AronowAudit.P004.prob (π N) (fun z : Assignment N => ¬ ValidArms z) ≤
        AronowAudit.P004.prob (π N) C := by
    calc
      AronowAudit.P004.prob (π N) A -
          AronowAudit.P004.prob (π N)
            (fun z : Assignment N => ¬ ValidArms z) =
          (AronowAudit.P004.prob (π N) A -
            AronowAudit.P004.prob (π N) (fun _ : Assignment N => False) -
              AronowAudit.P004.prob (π N) (fun z : Assignment N => ¬ ValidArms z)) := by
        rw [hfalse]
        ring
      _ ≤ AronowAudit.P004.prob (π N) C := hdiff
  have hgoodN' : 1-α-ε/2 ≤ AronowAudit.P004.prob (π N) A := by
    simpa [A, U, W] using hgoodN
  have hbadN' : AronowAudit.P004.prob (π N)
      (fun z : Assignment N => ¬ ValidArms z) < ε/2 := hbadN
  have hfinal : 1-α-ε ≤ AronowAudit.P004.prob (π N) C := by
    linarith
  simpa only [show ∀ N (A : Assignment N → Prop),
    prob (fun _ : Fin N => p) A = AronowAudit.P004.prob (fun _ => p) A
      from fun N A => rfl] using hfinal

end
