import AronowAudit.P004.P004_VarianceComponentsCompletion

namespace AronowAudit.P004.KernelCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem bounded_neighbor_sum {N : ℕ} (B : Fin N→Finset (Fin N)) (D : ℕ)
    (C : ℝ) (hN : 0<N) (hC : 0≤C) (hdeg : ∀i,(B i).card≤D)
    (F : Fin N→Fin N→ℝ) (hF : ∀i j,j∈B i→|F i j|≤C) :
    |(∑i,∑j∈B i,F i j)/(N:ℝ)|≤C*(D:ℝ):=by
  have hn : 0<(N:ℝ):=Nat.cast_pos.mpr hN
  have hs : |∑i,∑j∈B i,F i j|≤(N:ℝ)*(D:ℝ)*C:=by
    calc
      _ ≤ ∑i,|∑j∈B i,F i j|:=Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i,∑j∈B i,|F i j|:=Finset.sum_le_sum (fun i _=>Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑i,∑_j∈B i,C:=Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j hj=>hF i j hj))
      _ = ∑i,((B i).card:ℝ)*C:=by simp
      _ ≤ ∑_i:Fin N,(D:ℝ)*C:=Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hdeg i)) hC)
      _ = _:=by simp [mul_assoc]
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  nlinarith

end
end AronowAudit.P004.KernelCompletion

namespace AronowAudit.P004
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter KernelCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- T34(b), the actual off-diagonal kernel sum is bounded by the kernel
bound, squared maximum residual, and maximum neighborhood count. -/
theorem kernel_cross_sum_bound {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b Kmax : ℝ)
    (hN : 0 < N) (hb : 0 < b) (hK : ∀ t, 0 ≤ t → |K t| ≤ Kmax)
    (hsupport : ∀ t, 1 < t → K t = 0) (hD : ∀ i j, 0 ≤ D i j) :
    |(∑ i, ∑ j ∈ Finset.univ.erase i, bit (z i)*bit (z j)*e i*e j*K (D i j/b))/N| ≤
      Kmax * (sSup (Set.range (fun i => |e i|)))^2 * maxDegree (fun i => ball D i b) := by
  let M:=sSup (Set.range (fun i=>|e i|))
  let C:=Kmax*M^2
  let B:=fun i=>ball D i b
  let F:=fun i j=>bit (z i)*bit (z j)*e i*e j*K (D i j/b)
  have hem (i : Fin N) : |e i|≤M:=le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
  have hm : 0≤M:=(abs_nonneg (e ⟨0,hN⟩)).trans (hem ⟨0,hN⟩)
  have hkmax : 0≤Kmax:=(abs_nonneg (K 0)).trans (hK 0 le_rfl)
  have hC : 0≤C:=mul_nonneg hkmax (sq_nonneg _)
  have hprod (i j : Fin N) : |e i*e j*K (D i j/b)|≤C:=by
    have hee : |e i*e j|≤M^2:=by
      rw [abs_mul]
      simpa only [pow_two] using mul_le_mul (hem i) (hem j) (abs_nonneg _) hm
    rw [abs_mul]
    have hh:=mul_le_mul hee (hK _ (div_nonneg (hD i j) hb.le)) (abs_nonneg (K (D i j/b))) (sq_nonneg M)
    simpa only [C,mul_comm] using hh
  have hF (i j : Fin N) : |F i j|≤C:=by
    cases hi : z i <;> cases hj : z j
    all_goals simp only [F,bit,hi,hj,Bool.false_eq_true,ite_false,ite_true,zero_mul,one_mul,abs_zero]
    all_goals first | exact hC | exact hprod i j
  have hout (i j : Fin N) (hj : j∉B i) : F i j=0:=by
    have hdij : b<D i j:=by simpa only [B,ball,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hj
    have harg : 1<D i j/b:=(lt_div_iff₀ hb).mpr (by simpa only [one_mul] using hdij)
    simp only [F,hsupport _ harg,mul_zero]
  have hlocal : (∑i,∑j∈Finset.univ.erase i,F i j)=∑i,∑j∈(B i).erase i,F i j:=by
    apply Finset.sum_congr rfl
    intro i _
    symm
    apply Finset.sum_subset (Finset.erase_subset_erase i (Finset.subset_univ _))
    intro j hj hnot
    apply hout i j
    intro hjB
    exact hnot (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,hjB⟩)
  have hdeg (i : Fin N) : ((B i).erase i).card≤maxDegree B:=
    (Finset.card_le_card (Finset.erase_subset _ _)).trans
      (Finset.le_sup (f:=fun i=>(B i).card) (Finset.mem_univ i))
  change |(∑i,∑j∈Finset.univ.erase i,F i j)/(N:ℝ)|≤C*(maxDegree B:ℝ)
  rw [hlocal]
  exact bounded_neighbor_sum (fun i=>(B i).erase i) (maxDegree B) C hN hC hdeg F (fun i j _=>hF i j)


end
end AronowAudit.P004
