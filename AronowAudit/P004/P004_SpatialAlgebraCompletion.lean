import AronowAudit.P004.P004_VarianceOrderCompletion

namespace AronowAudit.P004.AlgebraCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter CLTCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem expect_integral {N : ℕ} {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (p : Fin N→ℝ) (F : A→Assignment N→ℝ) (hi : ∀z,Integrable (fun x=>F x z) μ) :
    expect p (fun z=>∫x,F x z ∂μ)=∫x,expect p (F x) ∂μ := by
  unfold expect
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro z _
    exact (hi z).const_mul _

theorem marginal_circle_integral {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (p : Fin N→ℝ) (d : ℝ)
    (hp : ∀i,0<p i ∧ p i<1) (hWD : WellDefined P d) (i : Fin N) (a : Bool) :
    marginal p (circleAverage P d) i a=
      (∫x in region P i d,marginal p (fun _ z=>P.outcome x z) i a ∂P.zeta)/(P.zeta (region P i d)).toReal := by
  rw [marginal_is_marginalization p (circleAverage P d) i a hp]
  unfold circleAverage
  rw [expect_div,expect_integral (P.zeta.restrict (region P i d)) p
    (fun x z=>P.outcome x (Function.update z i a)) (fun z=>(hWD i).2.2.2 _)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact (marginal_is_marginalization p (fun _ z=>P.outcome x z) i a hp).symm

theorem marginal_point_integrable {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (p : Fin N→ℝ) (d : ℝ)
    (hp : ∀i,0<p i ∧ p i<1) (hWD : WellDefined P d) (i : Fin N) (a : Bool) :
    IntegrableOn (fun x=>marginal p (fun _ z=>P.outcome x z) i a) (region P i d) P.zeta := by
  have he : (fun x=>marginal p (fun _ z=>P.outcome x z) i a)=
      fun x=>∑z,designWeight p z*P.outcome x (Function.update z i a):=by
    funext x
    exact marginal_is_marginalization p (fun _ z=>P.outcome x z) i a hp
  rw [he]
  exact integrable_finsetSum _ (fun z _=>((hWD i).2.2.2 _).const_mul _)

end
end AronowAudit.P004.AlgebraCompletion

namespace AronowAudit.P004
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter CLTCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

open AlgebraCompletion

/-- T6(a–b), area aggregation over disjoint positive finite-mass bins,
using the actual integral. The same identity applies to marginalized effects. -/
theorem area_partition_identity {A : Type*} [MeasurableSpace A] {m : ℕ}
    (ζ : Measure A) (B : Fin m → Set A) (Y : A → ℝ)
    (hm : 0 < m) (hB : ∀ k, MeasurableSet (B k))
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hmass : ∀ k, 0 < ζ (B k) ∧ ζ (B k) < ⊤)
    (hint : ∀ k, IntegrableOn Y (B k) ζ) :
    (∫ x in ⋃ k, B k, Y x ∂ζ) / (ζ (⋃ k, B k)).toReal =
      ∑ k, (ζ (B k)).toReal / (∑ l, (ζ (B l)).toReal) *
        ((∫ x in B k, Y x ∂ζ) / (ζ (B k)).toReal) := by
  have hpos (k : Fin m) : 0<(ζ (B k)).toReal:=ENNReal.toReal_pos (hmass k).1.ne' (hmass k).2.ne
  rw [integral_iUnion_fintype hB hdis hint,measure_iUnion hdis hB,tsum_fintype,
    ENNReal.toReal_sum (fun k _=>(hmass k).2.ne),Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [(hpos k).ne']

/-- T30(2), the wrong equal-arm member differs by the displayed control
count term. Supplement A p. 13, eq. (33) correction. -/
theorem wrong_hajek_class_difference {N : ℕ} (p : ℝ) (R : CircleTable N)
    (z : Assignment N) (hN : 0 < N) (hp : 0 < p ∧ p < 1) :
    augmented (fun _ => p) R (fun _ _ => barMu (fun _ => p) R true) z -
      linearHajek (fun _ => p) R z =
      (barMu (fun _ => p) R true-barMu (fun _ => p) R false) *
        (armCount z false/(N*(1-p))-1) := by
  let a:=barMu (fun _=>p) R true
  let b:=barMu (fun _=>p) R false
  have hn : (N:ℝ)≠0:=by exact_mod_cast hN.ne'
  have hq : 1-p≠0:=(sub_pos.mpr hp.2).ne'
  have hc : (∑i,(1-bit (z i)))=armCount z false:=by
    unfold armCount
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [bit,hz]
  unfold linearHajek augmented
  rw [←sub_div,←Finset.sum_sub_distrib]
  change (∑i,((a-a+bit (z i)*(R i z-a)/p-(1-bit (z i))*(R i z-a)/(1-p))-
    (a-b+bit (z i)*(R i z-a)/p-(1-bit (z i))*(R i z-b)/(1-p))))/(N:ℝ)=_
  calc
    _ = (∑i,(a-b)*((1-bit (z i))/(1-p)-1))/(N:ℝ):=by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _:=by
      rw [←Finset.mul_sum,Finset.sum_sub_distrib,←Finset.sum_div,hc]
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,mul_one]
      dsimp [a,b]
      field_simp
      <;> ring


/-- T15(a): generalized disk/donut node effect is the ζ-average of
τᵢₓ, and AME is its node mean (p. 757 correction). -/
theorem band_effect_identity {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (p : Fin N → ℝ) (d : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hWD : WellDefined P d) :
    (∀ i, nodeEffect p (circleAverage P d) i =
      (∫ x in region P i d, pointEffect P p i x ∂P.zeta) / (P.zeta (region P i d)).toReal) ∧
    ame p (circleAverage P d) = (∑ i,
      (∫ x in region P i d, pointEffect P p i x ∂P.zeta) / (P.zeta (region P i d)).toReal) / N := by
  have he (i : Fin N) : nodeEffect p (circleAverage P d) i=
      (∫x in region P i d,pointEffect P p i x ∂P.zeta)/(P.zeta (region P i d)).toReal:=by
    rw [nodeEffect,marginal_circle_integral P p d hp hWD i true,
      marginal_circle_integral P p d hp hWD i false,←sub_div,
      ←integral_sub (marginal_point_integrable P p d hp hWD i true)
        (marginal_point_integrable P p d hp hWD i false)]
    rfl
  exact ⟨he,by simp only [ame,he]⟩

end
end AronowAudit.P004
