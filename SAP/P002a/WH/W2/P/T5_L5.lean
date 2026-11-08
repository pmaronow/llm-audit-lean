import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T5_L5

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

private lemma residuals_zero_of_small_B
    (hL1 : SAP.P002a.WH.W2.T5_L1) {n k : ℕ}
    (P : SAP.P002a.CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hBpos : 0 < B) (hP : SAP.P002a.Xi P δ e A B r)
    (hn : 2 ≤ n) (hthreshold : B^2 < ((n : ℝ)-1)/(n : ℝ)) :
    ∀ a i, SAP.P002a.residual P a (SAP.P002a.late P.pop) i = 0 := by
  have hQ : AronowAudit.P002.Xi (toCovPopulation P) δ e A B r :=
    (xi_eq P δ e A B r).mp hP
  have hmean (a : Bool) :
      SAP.P002a.mean (SAP.P002a.residual P a (SAP.P002a.late P.pop)) = 0 := by
    rw [mean_eq, residual_eq P, late_eq P.pop]
    exact AronowAudit.P002.Wave1.T2C_residual_centered (toCovPopulation P).x _
      (AronowAudit.P002.Wave1.T2C_Xi_residual_score (toCovPopulation P) δ e A B r
        he hQ a)
  have hvariance (a : Bool) :
      SAP.P002a.popVar (SAP.P002a.residual P a (SAP.P002a.late P.pop)) =
        (∑ i, (SAP.P002a.residual P a (SAP.P002a.late P.pop) i)^2) /
          ((n : ℝ)-1) := by
    unfold SAP.P002a.popVar
    rw [hmean a]
    simp only [sub_zero]
  have hzero (a : Bool) : ∀ i, SAP.P002a.residual P a (SAP.P002a.late P.pop) i = 0 := by
    let q := SAP.P002a.residual P a (SAP.P002a.late P.pop)
    have hfour : SAP.P002a.fourthNorm q ≤ B * Real.sqrt (SAP.P002a.popVar q) :=
      hP.2.2.2.2.2.2.1 a
    have hbound : SAP.P002a.fourthNorm q ≤
        B * Real.sqrt ((∑ i, q i^2) / ((n : ℝ)-1)) := by
      rw [← hvariance a]
      exact hfour
    have hz := hL1 q B hn (le_of_lt hBpos) hthreshold hbound
    simpa [q] using hz
  exact hzero

lemma uniform_coverage_of_small_B
    (hL1 : SAP.P002a.WH.W2.T5_L1) {k : ℕ} (δ e A B r α x : ℝ)
    (he : 0 < e) (hB : 0 < B) (hBlt : B < 1) (hr : 0 < r)
    (hx1 : x < 1) :
    ∀ᶠ n in atTop, ∀ P : SAP.P002a.CovPopulation n k,
      SAP.P002a.Xi P δ e A B r → x ≤ SAP.P002a.adjustedCoverage P (SAP.P002a.late P.pop) α := by
  have hgap : 0 < 1-B^2 := by nlinarith
  have hrecip : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)) atTop (nhds 0) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds.div_atTop hnat :
      Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)) atTop (nhds 0))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ B^2 < ((n : ℝ)-1)/(n : ℝ) := by
    have hrec := (tendsto_order.1 hrecip).2 (1-B^2) hgap
    filter_upwards [hrec, eventually_ge_atTop (2 : ℕ)] with n hnrec hn
    refine ⟨hn, ?_⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [lt_div_iff₀ hnR]
    have hmul0 : (1 : ℝ) < (1-B^2)*(n : ℝ) :=
      (div_lt_iff₀ hnR).mp hnrec
    nlinarith [hmul0]
  let H : ∀ n, AronowAudit.P002.CovPopulation n k → Prop := fun n P =>
    AronowAudit.P002.Xi P δ e A B r ∧ 2 ≤ n ∧ B^2 < ((n : ℝ)-1)/(n : ℝ)
  let G : ∀ n, AronowAudit.P002.CovPopulation n k → Prop := fun n P =>
    x ≤ AronowAudit.P002.adjustedCoverage P (AronowAudit.P002.late P.pop) α
  have hseq : ∀ (sizes : ℕ → ℕ), StrictMono sizes →
      ∀ (P : ∀ j, AronowAudit.P002.CovPopulation (sizes j) k),
        (∀ j, H (sizes j) (P j)) → ∀ᶠ j in atTop, G (sizes j) (P j) := by
    intro sizes hsizes P hP
    have hzero (j : ℕ) :
        AronowAudit.P002.Wave1.T2C_totalH (P j) = 0 := by
      let Q : SAP.P002a.CovPopulation (sizes j) k := fromCovPopulation (P j)
      have hQ : SAP.P002a.Xi Q δ e A B r := by
        rw [xi_eq Q δ e A B r, project_covPopulation_roundtrip]
        exact (hP j).1
      have hzlocal := residuals_zero_of_small_B hL1 Q δ e A B r he (by exact hB) hQ
        (hP j).2.1 (hP j).2.2
      have hzd (a : Bool) :
          AronowAudit.P002.residual (P j) a
              (AronowAudit.P002.late (P j).pop) = 0 := by
        have hzfun : SAP.P002a.residual Q a (SAP.P002a.late Q.pop) = 0 :=
          funext (hzlocal a)
        rw [residual_eq Q, late_eq Q.pop] at hzfun
        rw [project_covPopulation_roundtrip (P j)] at hzfun
        have hpop : toPopulation Q.pop = (P j).pop := by
          change toPopulation (fromPopulation (P j).pop) = (P j).pop
          exact project_population_roundtrip (P j).pop
        rw [hpop] at hzfun
        exact hzfun
      unfold AronowAudit.P002.Wave1.T2C_totalH AronowAudit.P002.Wave1.T2C_residualH
      simp [hzd, AronowAudit.P002.mean]
    have hz := AronowAudit.P002.Wave1.T2C_zero_coverage_seq sizes hsizes k P
      δ e A B r α he hr (fun j => (hP j).1) hzero x hx1
    filter_upwards [hz] with j hj
    exact hj.le
  have hU : ∀ᶠ n in atTop, ∀ P : AronowAudit.P002.CovPopulation n k,
      H n P → G n P :=
    AronowAudit.P002.Wave1.T2C_U_uniform_eventual H G hseq
  filter_upwards [hsmall, hU] with n hn hu P hP
  have hcoverage := hu (toCovPopulation P)
    ⟨(xi_eq P δ e A B r).mp hP, hn.1, hn.2⟩
  rw [adjustedCoverage_eq P, late_eq P.pop]
  change G n (toCovPopulation P)
  exact hcoverage

end
end SAP.P002a.WH.W2.P.T5_L5

namespace SAP.P002a.WH.W2

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

theorem T5_L5_proof : SAP.P002a.WH.W2.T5_L5 := by
  intro hL1 k δ e A B r α hk hδ he hA hB hr hα hlim
  by_contra hBnot
  have hBlt : B < 1 := lt_of_not_ge hBnot
  let x : ℝ := ((1-α)+1)/2
  have hx0 : 0 < x := by
    have h1a : 0 < 1-α := by linarith [hα.2]
    dsimp [x]
    linarith
  have hnominal_lt_x : 1-α < x := by dsimp [x]; linarith
  have hx1 : x < 1 := by dsimp [x]; linarith
  have hbot : atTop ⊓ Filter.principal (SAP.P002a.xiSizes k δ e A B r) ≠ ⊥ := by
    intro hb
    have htop : Filter.liminf (fun n => SAP.P002a.infCoverageXi n k δ e A B r α)
        (atTop ⊓ Filter.principal (SAP.P002a.xiSizes k δ e A B r)) = ⊤ := by
      rw [hb, Filter.liminf_bot]
    rw [htop] at hlim
    exact ENNReal.ofReal_ne_top hlim.symm
  have hxuniform := SAP.P002a.WH.W2.P.T5_L5.uniform_coverage_of_small_B (k := k) hL1 δ e A B r α x he hB hBlt
    hr.1 hx1
  have hlower : ENNReal.ofReal x ≤
      Filter.liminf (fun n => SAP.P002a.infCoverageXi n k δ e A B r α)
        (atTop ⊓ Filter.principal (SAP.P002a.xiSizes k δ e A B r)) := by
    apply (le_liminf_iff).mpr
    intro y hy
    have hyTop : y ≠ ⊤ := ne_top_of_lt hy
    have hyReal : y.toReal < x := (ENNReal.lt_ofReal_iff_toReal_lt hyTop).mp hy
    have hmax : max 0 y.toReal < x := max_lt_iff.mpr ⟨hx0, hyReal⟩
    obtain ⟨z, hyz, hzx⟩ := exists_between hmax
    have hyzReal : y.toReal < z := lt_of_le_of_lt (le_max_right 0 y.toReal) hyz
    have hz0 : 0 < z := lt_of_le_of_lt (le_max_left 0 y.toReal) hyz
    have hz1 : z < 1 := hzx.trans hx1
    have hzu := SAP.P002a.WH.W2.P.T5_L5.uniform_coverage_of_small_B (k := k) hL1 δ e A B r α z he hB hBlt
      hr.1 hz1
    apply eventually_inf_principal.mpr
    filter_upwards [hzu] with n hn hmem
    have hbound : ENNReal.ofReal z ≤ SAP.P002a.infCoverageXi n k δ e A B r α := by
      unfold SAP.P002a.infCoverageXi
      refine le_iInf fun β => le_iInf fun P => ?_
      apply ENNReal.ofReal_le_ofReal
      simpa only [P.property.2] using hn P.val P.property.1
    exact ((ENNReal.lt_ofReal_iff_toReal_lt hyTop).mpr hyzReal).trans_le hbound
  have hstrict : ENNReal.ofReal (1-α) < ENNReal.ofReal x := by
    rw [ENNReal.ofReal_lt_ofReal_iff hx0]
    exact hnominal_lt_x
  exact (not_le_of_gt hstrict) (hlower.trans_eq hlim)

end SAP.P002a.WH.W2
