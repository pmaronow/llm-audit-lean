import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.Gap.GLP0042B2
import AronowAudit.P004.Wave1.DesignLimits.DL3
import AronowAudit.P004.Wave1.DesignLimits.DL4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P004b.WH.W3.P.T27_L11

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
open AronowAudit.P004
open AronowAudit.P004.Wave1.DesignLimits
noncomputable section

lemma half_admissible : AdmissibleSeq (fun _ _ => (1/2 : ℝ)) := by
  intro N i
  norm_num

lemma prob_eq_donor {N : ℕ} (p : Fin N → ℝ) (A : Assignment N → Prop) :
    _root_.SAP.P004b.prob p A = AronowAudit.P004.prob p A := rfl

lemma reciprocal_tendsto_zero :
    Tendsto (fun N : ℕ => (40 : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hrec : Tendsto (fun N : ℕ => (1 : ℝ)/(N : ℝ)) atTop (nhds 0) := by
    exact hconst.div_atTop hnat
  have hm := hrec.const_mul (40 : ℝ)
  convert hm using 1 <;> simp [div_eq_mul_inv, mul_comm]

lemma inprob_of_uniform_bound
    (U : ∀ N : ℕ, Assignment N → ℝ)
    (hU : ∀ᶠ N : ℕ in atTop, ∀ z, |U N z| ≤ (40 : ℝ)/(N : ℝ)) :
    InProb (fun _ _ => (1/2 : ℝ)) U := by
  intro ε hε
  have hs := reciprocal_tendsto_zero.eventually (eventually_lt_nhds hε)
  have heq : (fun N => prob (fun _ : Fin N => (1/2 : ℝ))
      (fun z => ε < |U N z|)) =ᶠ[atTop] fun _ => (0 : ℝ) := by
    filter_upwards [hU, hs] with N hbound hsmall
    have hzero : ∀ z : Assignment N, ¬ ε < |U N z| := by
      intro z hz
      have := hbound z
      linarith
    simp [prob, expect, hzero]
  exact (tendsto_congr' heq).2 tendsto_const_nhds

lemma sparse_count_range {N : ℕ} (hN : 10 ≤ N) (z : Assignment N)
    (hg : AronowAudit.P004.Wave1.T27_good z) :
    2*(N : ℝ)/5 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ 3*(N : ℝ)/5 := by
  have hpos : 0 < N := by omega
  have hfirst : wholeFirst z = z ⟨0, hpos⟩ := by
    simp [wholeFirst, hpos]
  have hc := AronowAudit.P004.Wave1.T27_count_complement z
  have hg' := hg
  unfold AronowAudit.P004.Wave1.T27_good at hg'
  change 2*(N : ℝ)/5 ≤ armCount z (wholeFirst z) ∧
    armCount z (wholeFirst z) ≤ 3*(N : ℝ)/5
  rw [hfirst]
  cases hz : z ⟨0, hpos⟩ with
  | true =>
      have hgLocal : 2*(N : ℝ)/5 ≤ _root_.SAP.P004b.armCount z true ∧
          _root_.SAP.P004b.armCount z true ≤ 3*(N : ℝ)/5 := by
        simpa [_root_.SAP.P004b.armCount, AronowAudit.P004.armCount] using hg'
      exact hgLocal
  | false =>
      have hcLocal : _root_.SAP.P004b.armCount z true +
          _root_.SAP.P004b.armCount z false = (N : ℝ) := by
        simpa [_root_.SAP.P004b.armCount, AronowAudit.P004.armCount] using hc
      have hgLocal : 2*(N : ℝ)/5 ≤ _root_.SAP.P004b.armCount z true ∧
          _root_.SAP.P004b.armCount z true ≤ 3*(N : ℝ)/5 := by
        simpa [_root_.SAP.P004b.armCount, AronowAudit.P004.armCount] using hg'
      constructor <;> linarith

lemma sparse_hac_bound {N : ℕ} (hN : 10 ≤ N) (z : Assignment N)
    (hg : AronowAudit.P004.Wave1.T27_good z) :
    |wholeSparseHac N z| ≤ (25/4 : ℝ)/(N : ℝ)^2 := by
  have hpos : 0 < N := by omega
  have hrange := sparse_count_range hN z hg
  have hfirst : wholeFirst z = z ⟨0, hpos⟩ := by simp [wholeFirst, hpos]
  have hc := AronowAudit.P004.Wave1.T27_count_complement z
  have hg' := hg
  unfold AronowAudit.P004.Wave1.T27_good at hg'
  have hNreal : 10 ≤ (N : ℝ) := by exact_mod_cast hN
  have htrue : 0 < AronowAudit.P004.armCount z true := by linarith [hg'.1]
  have hfalse : 0 < AronowAudit.P004.armCount z false := by linarith [hc, hg'.2, hNreal]
  have hcircle : wholeSparseR N = sparseTable N := AronowAudit.P004.Wave1.T27_circle N
  have hq : wholeSparseQ z = AronowAudit.P004.armCount z (z ⟨0,hpos⟩) := by
    simp [_root_.SAP.P004b.wholeSparseQ, _root_.SAP.P004b.wholeFirst, hpos,
      _root_.SAP.P004b.armCount, AronowAudit.P004.armCount]
  have hkernel :
      _root_.SAP.P004b.kernelVariance z
        (_root_.SAP.P004b.residual (_root_.SAP.P004b.sparseTable N) z)
        (_root_.SAP.P004b.distanceKernel (_root_.SAP.P004b.nodeSeparation
          (_root_.SAP.P004b.sparsePopulation N)) _root_.SAP.P004b.uniformKernel
          (_root_.SAP.P004b.sparseBandwidth N)) =
      AronowAudit.P004.kernelVariance z
        (AronowAudit.P004.residual (AronowAudit.P004.sparseTable N) z)
        (AronowAudit.P004.distanceKernel (AronowAudit.P004.nodeSeparation
          (AronowAudit.P004.sparsePopulation N)) AronowAudit.P004.uniformKernel
          (AronowAudit.P004.sparseBandwidth N)) := by rfl
  have hformula : wholeSparseHac N z =
      (1/4+3/4*bit (z ⟨0,hpos⟩))^2 *
        (wholeSparseQ z-1)/(wholeSparseQ z)^3 := by
    rw [wholeSparseHac, hcircle, wholeSparseQmat, hkernel]
    rw [AronowAudit.P004.Wave1.T27_spike_variance (by omega) z htrue hfalse]
    rw [hq]
    simp only [_root_.SAP.P004b.bit, AronowAudit.P004.bit]
  have hqlo : 0 < wholeSparseQ z := by linarith [hrange.1]
  have hqone : 1 ≤ wholeSparseQ z := by linarith
  have hy : (1/4+3/4*bit (z ⟨0,hpos⟩))^2 ≤ 1 := by
    cases z ⟨0,hpos⟩ <;> norm_num [bit]
  have hnumerator :
      (1/4+3/4*bit (z ⟨0,hpos⟩))^2 * (wholeSparseQ z-1) ≤ wholeSparseQ z := by
    calc
      _ ≤ 1 * (wholeSparseQ z-1) :=
        mul_le_mul_of_nonneg_right hy (by linarith)
      _ ≤ wholeSparseQ z := by ring_nf; linarith
  have hfrac :
      (1/4+3/4*bit (z ⟨0,hpos⟩))^2 *
        (wholeSparseQ z-1)/(wholeSparseQ z)^3 ≤ 1/(wholeSparseQ z)^2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hnumerator (sq_nonneg (wholeSparseQ z))]
  have hlast : 1/(wholeSparseQ z)^2 ≤ (25/4 : ℝ)/(N : ℝ)^2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [hrange.1, sq_nonneg (wholeSparseQ z - (2*(N:ℝ)/5))]
  rw [hformula, abs_of_nonneg (by positivity)]
  exact hfrac.trans hlast

lemma sparse_hac_v1_domination (hbounds : WholeSparseVarianceBounds) :
    ∀ᶠ N : ℕ in atTop, ∀ z, AronowAudit.P004.Wave1.T27_good z →
      |N*(wholeSparseHac N z-wholeSparseV1 N z)| ≤ (40 : ℝ)/(N : ℝ) := by
  filter_upwards [eventually_ge_atTop 10] with N hN z hg
  have hv := sparse_hac_bound hN z hg
  have hvb := hbounds N (by omega)
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hV1 : |wholeSparseV1 N z| ≤ 4/(N:ℝ)^2 := by
    simpa only [abs_of_nonneg (hvb.1 z).1] using (hvb.1 z).2
  calc
    |N*(wholeSparseHac N z-wholeSparseV1 N z)| =
        N*|wholeSparseHac N z-wholeSparseV1 N z| := by
          rw [abs_mul, abs_of_nonneg hpos.le]
    _ ≤ N*(|wholeSparseHac N z|+|wholeSparseV1 N z|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) hpos.le
    _ ≤ N*((25/4 : ℝ)/(N:ℝ)^2+4/(N:ℝ)^2) :=
          mul_le_mul_of_nonneg_left (add_le_add hv hV1) hpos.le
    _ ≤ 40/(N:ℝ) := by
          have hNne : (N:ℝ) ≠ 0 := ne_of_gt hpos
          field_simp
          nlinarith

end
end SAP.P004b.WH.W3.P.T27_L11

namespace SAP.P004b.WH.W3

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
open AronowAudit.P004.Wave1.DesignLimits
noncomputable section

theorem T27_L11_proof : SAP.P004b.WH.W3.T27_L11 := by
  intro hbounds hfinite
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨16, ?_⟩
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hv := hbounds N hN
    have hsup : sSup (Set.range (fun z : Assignment N => |wholeSparseV2 N z|)) ≤
        16/(N : ℝ)^2 := by
      apply csSup_le (Set.range_nonempty _)
      rintro x ⟨z, rfl⟩
      simpa only [abs_of_nonneg (hv.2.1 z).1] using (hv.2.1 z).2
    have hsup0 : 0 ≤ sSup (Set.range (fun z : Assignment N => |wholeSparseV2 N z|)) := by
      exact (abs_nonneg (wholeSparseV2 N (fun _ : Fin N => false))).trans
        (le_csSup (Set.finite_range _).bddAbove
          (Set.mem_range_self (fun _ : Fin N => false)))
    have hrate : 0 ≤ (N : ℝ)^(-2 : ℤ) := by positivity
    have hrewrite : |(N : ℝ)^(-2 : ℤ)| = 1/(N : ℝ)^2 := by
      norm_num [zpow_neg, inv_pow]
    have hnorm : ‖(N : ℝ)^(-2 : ℤ)‖ = 1/(N : ℝ)^2 := by
      rw [Real.norm_eq_abs, hrewrite]
    calc
      ‖sSup (Set.range (fun z : Assignment N => |wholeSparseV2 N z|))‖ =
          sSup (Set.range (fun z : Assignment N => |wholeSparseV2 N z|)) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hsup0]
      _ ≤ 16/(N : ℝ)^2 := hsup
      _ = 16*‖(N : ℝ)^(-2 : ℤ)‖ := by rw [hnorm]; ring
  constructor
  · intro ε hε
    refine ⟨7, by norm_num, ?_⟩
    have hbad : Tendsto (fun N => prob (fun _ : Fin N => (1/2 : ℝ))
        (fun z => ¬ AronowAudit.P004.Wave1.T27_good z)) atTop (nhds 0) := by
      simpa only [_root_.SAP.P004b.WH.W3.P.T27_L11.prob_eq_donor] using
        AronowAudit.P004.Wave1.T27_bad_limit
    have heps := hbad.eventually (eventually_lt_nhds hε)
    filter_upwards [eventually_ge_atTop 10, heps] with N hN hsmall
    have hpos : 0 < N := by omega
    have hrate : |(N : ℝ)^(-2 : ℤ)| = 1/(N : ℝ)^2 := by
      norm_num [zpow_neg, inv_pow]
    have hprobD :
        AronowAudit.P004.prob (fun _ : Fin N => (1/2 : ℝ))
          (fun z => 7*|(N : ℝ)^(-2 : ℤ)| < |wholeSparseHac N z|) ≤
        AronowAudit.P004.prob (fun _ : Fin N => (1/2 : ℝ))
          (fun z => ¬ AronowAudit.P004.Wave1.T27_good z) := by
      rw [AronowAudit.P004.prob, AronowAudit.P004.prob]
      apply AronowAudit.P004.expect_mono _ (fun _ => by norm_num)
      intro z
      by_cases hg : AronowAudit.P004.Wave1.T27_good z
      · have hv := _root_.SAP.P004b.WH.W3.P.T27_L11.sparse_hac_bound hN z hg
        have hlt : (25/4 : ℝ)/(N:ℝ)^2 ≤ 7/(N:ℝ)^2 :=
          (div_le_div_of_nonneg_right (by norm_num : (25/4:ℝ) ≤ 7) (by positivity))
        have hs : |wholeSparseHac N z| ≤ 7*|(N : ℝ)^(-2 : ℤ)| := by
          calc
            |wholeSparseHac N z| ≤ (25/4 : ℝ)/(N:ℝ)^2 := hv
            _ ≤ 7*(1/(N:ℝ)^2) := by simpa [div_eq_mul_inv] using hlt
            _ = 7*|(N : ℝ)^(-2 : ℤ)| := by rw [hrate]
        have hnot : ¬ 7*|(N : ℝ)^(-2 : ℤ)| < |wholeSparseHac N z| := not_lt_of_ge hs
        have hnot' : ¬ 7*((N:ℝ)^2)⁻¹ < |wholeSparseHac N z| := by
          simpa only [hrate, one_div] using hnot
        simp [hg, hnot']
      · simp [hg]
        split_ifs <;> norm_num
    have hprob :
        prob (fun _ : Fin N => (1/2 : ℝ))
          (fun z => 7*|(N : ℝ)^(-2 : ℤ)| < |wholeSparseHac N z|) ≤
        prob (fun _ : Fin N => (1/2 : ℝ))
          (fun z => ¬ AronowAudit.P004.Wave1.T27_good z) := by
      simpa only [_root_.SAP.P004b.WH.W3.P.T27_L11.prob_eq_donor] using hprobD
    exact hprob.trans_lt hsmall
  · constructor
    · have hdom := _root_.SAP.P004b.WH.W3.P.T27_L11.sparse_hac_v1_domination hbounds
      have hdomD : ∀ᶠ N : ℕ in atTop, ∀ z,
          AronowAudit.P004.Wave1.T27_good z →
            |N*(wholeSparseHac N z-wholeSparseV1 N z)| ≤ |(40 : ℝ)/(N : ℝ)| := by
        filter_upwards [hdom, eventually_ge_atTop 10] with N hdomN hN z hg
        have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        have h40 : 0 ≤ (40 : ℝ)/(N : ℝ) := div_nonneg (by norm_num) hpos.le
        rw [abs_of_nonneg h40]
        exact hdomN z hg
      have hWlocal : InProb (fun _ _ => (1/2 : ℝ))
          (fun N _ => (40 : ℝ)/(N : ℝ)) :=
        _root_.SAP.P004b.WH.W3.P.T27_L11.inprob_of_uniform_bound
          (fun N _ => (40 : ℝ)/(N : ℝ)) (by
            filter_upwards [eventually_ge_atTop 1] with N hN _
            rw [abs_of_nonneg (by positivity)])
      have hW : AronowAudit.P004.InProb (fun _ _ => (1/2 : ℝ))
          (fun N _ => (40 : ℝ)/(N : ℝ)) := by
        intro ε hε
        simpa only [_root_.SAP.P004b.WH.W3.P.T27_L11.prob_eq_donor] using hWlocal ε hε
      have hbad : Tendsto (fun N => prob (fun _ : Fin N => (1/2 : ℝ))
          (fun z => ¬ AronowAudit.P004.Wave1.T27_good z)) atTop (nhds 0) := by
        simpa only [_root_.SAP.P004b.WH.W3.P.T27_L11.prob_eq_donor] using
          AronowAudit.P004.Wave1.T27_bad_limit
      have hI : AronowAudit.P004.InProb (fun _ _ => (1/2 : ℝ))
          (fun N z => N*(wholeSparseHac N z-wholeSparseV1 N z)) :=
        AronowAudit.P004.Wave1.DesignLimits.dl3_proof _
          _root_.SAP.P004b.WH.W3.P.T27_L11.half_admissible
          (fun N z => N*(wholeSparseHac N z-wholeSparseV1 N z))
          (fun N z => (40 : ℝ)/(N : ℝ))
          (fun _ z => AronowAudit.P004.Wave1.T27_good z) hbad hdomD hW
      intro ε hε
      simpa only [_root_.SAP.P004b.WH.W3.P.T27_L11.prob_eq_donor] using hI ε hε
    · constructor
      · apply _root_.SAP.P004b.WH.W3.P.T27_L11.inprob_of_uniform_bound
        filter_upwards [eventually_ge_atTop 3] with N hN z
        have hv := hbounds N hN
        have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        have h1 : |wholeSparseV1 N z| ≤ 4/(N:ℝ)^2 := by
          simpa only [abs_of_nonneg (hv.1 z).1] using (hv.1 z).2
        have h2 : |wholeSparseV2 N z| ≤ 16/(N:ℝ)^2 := by
          simpa only [abs_of_nonneg (hv.2.1 z).1] using (hv.2.1 z).2
        calc
          |N*(wholeSparseV1 N z-wholeSparseV2 N z)| =
              N*|wholeSparseV1 N z-wholeSparseV2 N z| := by
                rw [abs_mul, abs_of_nonneg hpos.le]
          _ ≤ N*(|wholeSparseV1 N z|+|wholeSparseV2 N z|) :=
                mul_le_mul_of_nonneg_left (abs_sub _ _) hpos.le
          _ ≤ N*(4/(N:ℝ)^2+16/(N:ℝ)^2) :=
                mul_le_mul_of_nonneg_left (add_le_add h1 h2) hpos.le
          _ ≤ 40/(N:ℝ) := by
                have hNne : (N:ℝ) ≠ 0 := ne_of_gt hpos
                field_simp
                nlinarith
      · apply _root_.SAP.P004b.WH.W3.P.T27_L11.inprob_of_uniform_bound
        filter_upwards [eventually_ge_atTop 3] with N hN z
        have hv := hbounds N hN
        have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        have hV2 : |wholeSparseV2 N z| ≤ 16/(N:ℝ)^2 := by
          simpa only [abs_of_nonneg (hv.2.1 z).1] using (hv.2.1 z).2
        have he : expect (fun _ => (1/2 : ℝ)) (wholeSparseV2 N) =
            17*((N : ℝ)-1)/(8*(N : ℝ)^3) := hv.2.2
        have he_nonneg : 0 ≤ expect (fun _ => (1/2 : ℝ)) (wholeSparseV2 N) := by
          rw [he]
          have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
          positivity
        have he_abs : |expect (fun _ => (1/2 : ℝ)) (wholeSparseV2 N)| ≤
            17/(8*(N:ℝ)^2) := by
          rw [abs_of_nonneg he_nonneg, he]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          have hsub : (N : ℝ)-1 ≤ (N : ℝ) := by linarith
          nlinarith [mul_le_mul_of_nonneg_right hsub (sq_nonneg (N : ℝ))]
        calc
          |N*(wholeSparseV2 N z-
              expect (fun _ => (1/2 : ℝ)) (wholeSparseV2 N))| =
              N*|wholeSparseV2 N z-
                expect (fun _ => (1/2 : ℝ)) (wholeSparseV2 N)| := by
                  rw [abs_mul, abs_of_nonneg hpos.le]
          _ ≤ N*(|wholeSparseV2 N z|+
              |expect (fun _ => (1/2 : ℝ)) (wholeSparseV2 N)|) :=
                mul_le_mul_of_nonneg_left (abs_sub _ _) hpos.le
          _ ≤ N*(16/(N:ℝ)^2+17/(8*(N:ℝ)^2)) :=
                mul_le_mul_of_nonneg_left (add_le_add hV2 he_abs) hpos.le
          _ ≤ 40/(N:ℝ) := by
                have hNne : (N:ℝ) ≠ 0 := ne_of_gt hpos
                field_simp
                nlinarith

end
end SAP.P004b.WH.W3
