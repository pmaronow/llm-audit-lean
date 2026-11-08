import SAP.P001c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open AronowAudit.P001.Wave1.TailA
open scoped ENNReal NNReal Topology Classical

set_option maxHeartbeats 800000

theorem SAP.P001c.WH.W1.T57_L3_proof : SAP.P001c.WH.W1.T57_L3 := by
  intro Ω mΩ mE bE μ pμ D H θ T L hd Z hD r hr ν pν hconc hw
  let X : ℕ → Ω → CDFSpace := fun n ω => r n • (Z n ω - θ)
  let R : ℕ → Ω → ℝ := fun n ω =>
    r n * (T (Z n ω) - T θ) - L (X n ω)
  have hd' : AronowAudit.P001.HadamardAt D H T θ L := by
    simpa only [SAP.P001c.Bridge.hadamardDerivative_eq] using hd
  have hw' : AronowAudit.P001.OuterWeakLimit μ X ν := by
    simpa only [SAP.P001c.Bridge.outerWeakConvergence_eq] using hw
  have hw'' : AsymptoticStatistics.WeakConvergesOuter (fun _ => μ) X ν :=
    (outer_weak_donor_iff μ X ν).mp hw'
  have hrpos : ∀ᶠ n in atTop, 0 < r n := hr.eventually_gt_atTop 0
  have ht0 : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hr
  change AronowAudit.P001.CP μ R 0
  intro ε hε
  have hzero : limsup (fun n => μ {ω | ε ≤ dist (R n ω) 0}) atTop ≤ 0 := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro η hη
    obtain ⟨K, hK, hKH, hmass⟩ := hconc η hη
    obtain ⟨δ, hδ, huniform⟩ :=
      delta_hadamard_uniform_compact D H θ T L hd' K hK hKH ε hε
    have htsmall : ∀ᶠ n in atTop, (r n)⁻¹ < δ := ht0.eventually_lt_const hδ
    have hbound : ∀ᶠ n in atTop,
        μ {ω | ε ≤ dist (R n ω) 0} ≤
          μ.outerMeasureStar (X n ⁻¹' (Metric.thickening δ K)ᶜ) := by
      filter_upwards [hrpos, htsmall, hD] with n hn hnt hnD
      rw [delta_outer_mass_eq]
      apply measure_mono
      intro ω hω
      change X n ω ∉ Metric.thickening δ K
      intro hnear
      have hrecover : θ + (r n)⁻¹ • X n ω = Z n ω := by
        dsimp only [X]
        rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
        abel
      have hrem := huniform (r n)⁻¹ (inv_pos.mpr hn) hnt (X n ω) hnear
        (by simpa only [hrecover] using hnD ω)
      have heq :
          (T (θ + (r n)⁻¹ • X n ω) - T θ) / (r n)⁻¹ - L (X n ω) = R n ω := by
        rw [hrecover, div_inv_eq_mul]
        dsimp only [R]
        ring
      have hsmall : dist (R n ω) 0 < ε := by
        simpa only [heq, Real.dist_eq, sub_zero] using hrem
      exact (not_lt_of_ge hω) hsmall
    calc
      limsup (fun n => μ {ω | ε ≤ dist (R n ω) 0}) atTop
          ≤ limsup (fun n =>
            μ.outerMeasureStar (X n ⁻¹' (Metric.thickening δ K)ᶜ)) atTop :=
        limsup_le_limsup hbound
      _ ≤ ν (Metric.thickening δ K)ᶜ :=
        AsymptoticStatistics.limsup_outerMeasureStar_preimage_isClosed_le hw''
          Metric.isOpen_thickening.isClosed_compl
      _ ≤ ν Kᶜ := measure_mono (Set.compl_subset_compl.mpr
        (Metric.self_subset_thickening hδ K))
      _ ≤ η := hmass
  have ht : Tendsto (fun n => μ {ω | ε ≤ dist (R n ω) 0}) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le bot_le hzero
  simpa only [Function.comp_def, AronowAudit.P001.prob, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
