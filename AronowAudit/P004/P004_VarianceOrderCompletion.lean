import AronowAudit.P004.P004_SpatialCLTCompletion

namespace AronowAudit.P004.OrderCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter CLTCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem variance_ht_le_degree {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (B : Fin N→Finset (Fin N)) (D : ℕ) (hN : 0<N)
    (hp : 0<p ∧ p<1) (hb : 0≤b) (hR : ∀i z,|R i z|≤b)
    (hdeg : ∀i,(B i).card≤D)
    (houtside : ∀i j,j∉B i→¬sharesSource R i j) :
    variance (fun _=>p) (ht (fun _=>p) R) ≤
      (D:ℝ)*(b/p+b/(1-p))^2/(N:ℝ) := by
  let π:=fun _:Fin N=>p
  let T:=residualContrast π R (fun _ _=>0)
  let C:=b/p+b/(1-p)
  have hC : 0≤C:=add_nonneg (div_nonneg hb hp.1.le) (div_nonneg hb (sub_nonneg.mpr hp.2.le))
  have hT (i : Fin N) (z : Assignment N) : |T i z|≤C:=raw_contrast_abs_le p b R hp hb hR i z
  have hv (i : Fin N) : variance π (T i)≤C^2:=by
    apply (variance_le_second π (T i)).trans
    rw [←expect_const π (C^2)]
    apply expect_mono π (fun _=>hp)
    intro z
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (T i z)) hC).mpr (hT i z)
  have hcov (i j : Fin N) : cov π (T i) (T j)≤C^2:=by
    have hh:=cov_young π (fun _=>hp) (T i) (T j)
    linarith [hv i,hv j]
  have he : ht π R=fun z=>(∑i,T i z)/(N:ℝ):=by
    funext z
    simp only [T,ht,residualContrast,sub_zero]
  have hlocal : (∑i,∑j,cov π (T i) (T j))=∑i,∑j∈B i,cov π (T i) (T j):=by
    apply Finset.sum_congr rfl
    intro i _
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj=>GraphCompletion.residual_cov_zero π R _ i j (houtside i j hj))
  have hsum : (∑i,∑j∈B i,cov π (T i) (T j))≤(N:ℝ)*(D:ℝ)*C^2:=by
    calc
      _ ≤ ∑i,(D:ℝ)*C^2:=by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∑_j∈B i,C^2:=Finset.sum_le_sum (fun j _=>hcov i j)
          _ = ((B i).card:ℝ)*C^2:=by simp
          _ ≤ (D:ℝ)*C^2:=mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hdeg i)) (sq_nonneg C)
      _ = _:=by simp [mul_assoc]
  change variance π (ht π R)≤_
  rw [he,variance_div,variance_sum,hlocal]
  apply (div_le_div_of_nonneg_right hsum (sq_nonneg (N:ℝ))).trans_eq
  have hn : (N:ℝ)≠0:=by exact_mod_cast hN.ne'
  field_simp
  <;> ring

end
end AronowAudit.P004.OrderCompletion

namespace AronowAudit.P004
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter OrderCompletion CLTCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {Space : ℕ→Type*} [∀N,MetricSpace (Space N)] [∀N,MeasurableSpace (Space N)]

/-- T32(c), the actual variance sequence is O(1/N) under C1–C4,
without the central-limit theorem's variance lower bound. -/
theorem ht_variance_order (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d) :
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹) := by
  obtain ⟨b,hb,hbout⟩:=hP.1
  obtain ⟨h,hh,hloc⟩:=hP.2.1
  obtain ⟨c,hc⟩:=hP.2.2
  let D:=Nat.ceil (c (h d))
  apply Asymptotics.IsBigO.of_bound ((D:ℝ)*(b/p+b/(1-p))^2)
  filter_upwards [eventually_gt_atTop 0,hbout,hWD,hloc d hd,hc (h d) (hh d hd)] with N hN hbN hwdN hlocN hcN
  rw [Real.norm_eq_abs,abs_of_nonneg (variance_nonneg _ (fun _=>hp) _),Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have hdeg : ∀i,(ball (nodeSeparation (P N)) i (h d)).card≤D:=by
    intro i
    exact_mod_cast (hcN i).trans (Nat.le_ceil (c (h d)))
  have hR : ∀i z,|circleAverage (P N) d i z|≤b:=
    circleAverage_abs_le (P N) d b hwdN (fun x z=>(hbN x z).le)
  have hbound:=variance_ht_le_degree p b (circleAverage (P N) d)
    (fun i=>ball (nodeSeparation (P N)) i (h d)) D hN hp hb.le hR hdeg (by
      intro i j hj
      apply hlocN i j
      simpa only [ball,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hj)
  simpa only [div_eq_mul_inv,mul_assoc] using hbound


end
end AronowAudit.P004
