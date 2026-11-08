import SAP.P022.WH.W1.Leaves
import AronowAudit.P022.Wave1.Gap.TailBCorollaryMoments
import AronowAudit.Shared.MapTailB.QuantileBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T17_L1

open SAP.P022 Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

private def coord (t : Bool) (p : ℝ × ℝ) : ℝ := if t then p.1 else p.2

private theorem coord_continuous (t : Bool) : Continuous (coord t) := by
  cases t with
  | false => exact continuous_snd
  | true => exact continuous_fst

private def cubeTrunc (t : Bool) (n : ℕ) : BoundedContinuousFunction (ℝ × ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => min (n : ℝ) (|coord t p| ^ 3))
    (continuous_const.min ((coord_continuous t).abs.pow 3)) (n : ℝ) (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg n) (by positivity))]
      exact min_le_left _ _)

private theorem third_moment_integrable_of_bounded
    (S : ExperimentSequence) (H : JointLaw) (t : Bool)
    (hw : weakPopulationConvergence S H) (h3 : BoundedThirdMoments S) :
    Integrable (fun p : ℝ × ℝ => |coord t p| ^ 3) (H : Measure (ℝ × ℝ)) := by
  obtain ⟨M, hM⟩ := h3
  letI : IsProbabilityMeasure (H : Measure (ℝ × ℝ)) := H.property
  letI : IsFiniteMeasure (H : Measure (ℝ × ℝ)) := ⟨by simp⟩
  have hM0 : 0 ≤ M := by
    have h := hM 0 t
    exact le_trans (Finset.expect_nonneg (fun _ _ => by positivity)) h
  let f (p : ℝ × ℝ) := |coord t p| ^ 3
  let e (n : ℕ) (p : ℝ × ℝ) := min (n : ℝ) (f p)
  have hemeas (n : ℕ) : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (e n p)) := by
    exact (measurable_const.min ((coord_continuous t).measurable.abs.pow_const 3)).ennreal_ofReal
  have hmono : Monotone (fun n : ℕ => fun p : ℝ × ℝ => ENNReal.ofReal (e n p)) := by
    intro n m hnm p
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hpoint (p : ℝ × ℝ) :
      Tendsto (fun n : ℕ => ENNReal.ofReal (e n p)) atTop
        (𝓝 (ENNReal.ofReal (f p))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (f p))] with n hn
    exact congrArg ENNReal.ofReal (min_eq_right hn).symm
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (μ := (H : Measure (ℝ × ℝ)))
    (fun n => (hemeas n).aemeasurable) (Eventually.of_forall (fun p n m hnm => hmono hnm p))
    (Eventually.of_forall hpoint)
  have hbound (n : ℕ) :
      ∫⁻ p, ENNReal.ofReal (e n p) ∂(H : Measure (ℝ × ℝ)) ≤ ENNReal.ofReal M := by
    have hrow (q : ℕ) :
        finiteMean (fun i : Fin (S.design q).N =>
          e n (S.y1 i.val, S.y0 i.val)) ≤ M := by
      have hle : finiteMean (fun i : Fin (S.design q).N =>
          e n (S.y1 i.val, S.y0 i.val)) ≤
          finiteMean (fun i : Fin (S.design q).N =>
            |(if t then S.y1 else S.y0) i.val| ^ 3) := by
        unfold finiteMean
        apply Finset.expect_le_expect
        intro i hi
        have hc : coord t (S.y1 i.val, S.y0 i.val) =
            (if t then S.y1 else S.y0) i.val := by cases t <;> rfl
        dsimp [e, f]
        rw [hc]
        exact min_le_right _ _
      exact hle.trans (hM q t)
    have ht := hw (cubeTrunc t n)
    have hI : (∫ p, e n p ∂(H : Measure (ℝ × ℝ))) ≤ M := by
      apply le_of_tendsto ht
      filter_upwards [] with q
      simpa [cubeTrunc, e] using hrow q
    have hnonneg : 0 ≤ᵐ[(H : Measure (ℝ × ℝ))] fun p => e n p :=
      Eventually.of_forall (fun p => by positivity)
    have hint : Integrable (fun p => e n p) (H : Measure (ℝ × ℝ)) := by
      exact BoundedContinuousFunction.integrable
        (μ := (H : Measure (ℝ × ℝ))) (cubeTrunc t n)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    exact ENNReal.ofReal_le_ofReal hI
  have hlim_bound :
      (∫⁻ p, ENNReal.ofReal (f p) ∂(H : Measure (ℝ × ℝ))) ≤ ENNReal.ofReal M := by
    apply le_of_tendsto hlim
    exact Eventually.of_forall hbound
  have hfinite :
      (∫⁻ p, ENNReal.ofReal (f p) ∂(H : Measure (ℝ × ℝ))) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hlim_bound ENNReal.ofReal_lt_top)
  have hstrong : AEStronglyMeasurable (fun p : ℝ × ℝ => f p)
      (H : Measure (ℝ × ℝ)) := by
    exact ((coord_continuous t).abs.pow 3).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[(H : Measure (ℝ × ℝ))] fun p => f p :=
    Eventually.of_forall (fun p => by positivity)
  simpa [f] using (lintegral_ofReal_ne_top_iff_integrable hstrong hnonneg).mp hfinite

private theorem compatible_memLp_two (H J : JointLaw) (hc : J ∈ compatibleLaws H)
    (t : Bool)
    (hm : Integrable (fun p : ℝ × ℝ => coord t p ^ 2) (J : Measure (ℝ × ℝ))) :
    MemLp (fun p : ℝ × ℝ => coord t p) 2 (J : Measure (ℝ × ℝ)) := by
  exact (memLp_two_iff_integrable_sq (by cases t <;> simp [coord] <;> fun_prop)).2 hm

private theorem compatible_square_integral_eq (H J : JointLaw)
    (hc : J ∈ compatibleLaws H) (t : Bool)
    (hJ : Integrable (fun p : ℝ × ℝ => coord t p ^ 2) (J : Measure (ℝ × ℝ)))
    (hH : Integrable (fun p : ℝ × ℝ => coord t p ^ 2) (H : Measure (ℝ × ℝ))) :
    (∫ p, coord t p ^ 2 ∂(J : Measure (ℝ × ℝ))) =
      ∫ p, coord t p ^ 2 ∂(H : Measure (ℝ × ℝ)) := by
  obtain ⟨hfst, hsnd⟩ :=
    (TailB_compatibleLaws_iff_marginals H J).mp hc
  cases t
  · change (∫ p, p.2 ^ 2 ∂(J : Measure (ℝ × ℝ))) =
      ∫ p, p.2 ^ 2 ∂(H : Measure (ℝ × ℝ))
    calc
      _ = ∫ x : ℝ, x ^ 2 ∂((J : Measure (ℝ × ℝ)).map Prod.snd) := by
        symm
        exact integral_map measurable_snd.aemeasurable
          ((measurable_id.pow_const 2).aestronglyMeasurable)
      _ = ∫ x : ℝ, x ^ 2 ∂((H : Measure (ℝ × ℝ)).map Prod.snd) := by rw [hsnd]
      _ = _ := integral_map measurable_snd.aemeasurable
        ((measurable_id.pow_const 2).aestronglyMeasurable)
  · change (∫ p, p.1 ^ 2 ∂(J : Measure (ℝ × ℝ))) =
      ∫ p, p.1 ^ 2 ∂(H : Measure (ℝ × ℝ))
    calc
      _ = ∫ x : ℝ, x ^ 2 ∂((J : Measure (ℝ × ℝ)).map Prod.fst) := by
        symm
        exact integral_map measurable_fst.aemeasurable
          ((measurable_id.pow_const 2).aestronglyMeasurable)
      _ = ∫ x : ℝ, x ^ 2 ∂((H : Measure (ℝ × ℝ)).map Prod.fst) := by rw [hfst]
      _ = _ := integral_map measurable_fst.aemeasurable
        ((measurable_id.pow_const 2).aestronglyMeasurable)

private theorem compatible_variance_eq (H J : JointLaw) (hc : J ∈ compatibleLaws H)
    (t : Bool)
    (hJ : Integrable (fun p : ℝ × ℝ => coord t p ^ 2) (J : Measure (ℝ × ℝ)))
    (hH : Integrable (fun p : ℝ × ℝ => coord t p ^ 2) (H : Measure (ℝ × ℝ))) :
    lawVariance J t = lawVariance H t := by
  have hcOld : J ∈ AronowAudit.P022.compatibleLaws H := by
    simpa only [SAP.P022.Bridge.compatibleLaws_eq] using hc
  have mJ := compatible_memLp_two H J hc t hJ
  have mH := compatible_memLp_two H H (by intro t x; rfl) t hH
  have mJO : MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2
      (J : Measure (ℝ × ℝ)) := by simpa [coord] using mJ
  have mHO : MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2
      (H : Measure (ℝ × ℝ)) := by simpa [coord] using mH
  have hvOldJ := AronowAudit.P022.Wave1.TailB_lawVariance_eq_second J t mJO
  have hvOldH := AronowAudit.P022.Wave1.TailB_lawVariance_eq_second H t mHO
  have hmOld := TailB_lawMean_eq_of_compatible H J hcOld t
  have hsq := compatible_square_integral_eq H J hc t hJ hH
  have hsqOld : (∫ p, (if t then p.1 else p.2) ^ 2 ∂(J : Measure (ℝ × ℝ))) =
      ∫ p, (if t then p.1 else p.2) ^ 2 ∂(H : Measure (ℝ × ℝ)) := by
    simpa [coord] using hsq
  have hvOld : AronowAudit.P022.lawVariance J t = AronowAudit.P022.lawVariance H t := by
    rw [hvOldJ, hvOldH, hsqOld, hmOld]
  simpa only [SAP.P022.Bridge.lawVariance_eq] using hvOld

private theorem centered_square_integrable (H J : JointLaw)
    (hc : J ∈ compatibleLaws H) (t : Bool)
    (hm1 : Integrable (fun p : ℝ × ℝ => coord t p) (J : Measure (ℝ × ℝ)))
    (hm2 : Integrable (fun p : ℝ × ℝ => coord t p ^ 2) (J : Measure (ℝ × ℝ))) :
    Integrable (fun p : ℝ × ℝ => (coord t p - lawMean J t) ^ 2)
      (J : Measure (ℝ × ℝ)) := by
  have he : (fun p : ℝ × ℝ => (coord t p - lawMean J t) ^ 2) =
      fun p => coord t p ^ 2 - (2 * lawMean J t) * coord t p + (lawMean J t) ^ 2 := by
    funext p
    ring
  rw [he]
  exact (hm2.sub (hm1.const_mul (2 * lawMean J t))).add (integrable_const _)

private theorem centered_cross_integrable (J : JointLaw)
    (hx : Integrable (fun p : ℝ × ℝ => p.1) (J : Measure (ℝ × ℝ)))
    (hy : Integrable (fun p : ℝ × ℝ => p.2) (J : Measure (ℝ × ℝ)))
    (hxy : Integrable (fun p : ℝ × ℝ => p.1 * p.2) (J : Measure (ℝ × ℝ))) :
    Integrable (fun p : ℝ × ℝ => (p.1 - lawMean J true) * (p.2 - lawMean J false))
      (J : Measure (ℝ × ℝ)) := by
  have he : (fun p : ℝ × ℝ => (p.1 - lawMean J true) * (p.2 - lawMean J false)) =
      fun p => p.1 * p.2 - lawMean J false * p.1 - lawMean J true * p.2 +
        lawMean J true * lawMean J false := by
    funext p
    ring
  rw [he]
  exact ((hxy.sub (hx.const_mul (lawMean J false))).sub
    (hy.const_mul (lawMean J true))).add (integrable_const _)

private theorem covariance_abs_bound (H J : JointLaw) (hc : J ∈ compatibleLaws H)
    (hJ1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (J : Measure (ℝ × ℝ)))
    (hJ0 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (J : Measure (ℝ × ℝ)))
    (hH1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (H : Measure (ℝ × ℝ)))
    (hH0 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (H : Measure (ℝ × ℝ))) :
    |lawCovariance J| ≤ Real.sqrt (lawVariance H true) * Real.sqrt (lawVariance H false) := by
  let f : ℝ × ℝ → ℝ := fun p => p.1 - lawMean J true
  let g : ℝ × ℝ → ℝ := fun p => p.2 - lawMean J false
  have mJ1 := compatible_memLp_two H J hc true hJ1
  have mJ0 := compatible_memLp_two H J hc false hJ0
  have mf : MemLp f 2 (J : Measure (ℝ × ℝ)) := by
    dsimp [f]
    exact mJ1.sub (memLp_const _)
  have mg : MemLp g 2 (J : Measure (ℝ × ℝ)) := by
    dsimp [g]
    exact mJ0.sub (memLp_const _)
  have hprod : Integrable (fun p : ℝ × ℝ => f p * g p) (J : Measure (ℝ × ℝ)) :=
    mf.integrable_mul mg
  have hnorm := norm_integral_le_integral_norm
    (μ := (J : Measure (ℝ × ℝ))) (fun p : ℝ × ℝ => f p * g p)
  have mf' : MemLp f (ENNReal.ofReal (2 : ℝ)) (J : Measure (ℝ × ℝ)) := by simpa using mf
  have mg' : MemLp g (ENNReal.ofReal (2 : ℝ)) (J : Measure (ℝ × ℝ)) := by simpa using mg
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two mf' mg'
  have hv1 : lawVariance J true = lawVariance H true :=
    compatible_variance_eq H J hc true hJ1 hH1
  have hv0 : lawVariance J false = lawVariance H false :=
    compatible_variance_eq H J hc false hJ0 hH0
  have hnonneg1 : 0 ≤ lawVariance H true := integral_nonneg (fun _ => sq_nonneg _)
  have hnonneg0 : 0 ≤ lawVariance H false := integral_nonneg (fun _ => sq_nonneg _)
  have hcov : lawCovariance J = ∫ p, f p * g p ∂(J : Measure (ℝ × ℝ)) := by
    rfl
  have hcs' : (∫ p, |f p| * |g p| ∂(J : Measure (ℝ × ℝ))) ≤
      Real.sqrt (∫ p, f p ^ 2 ∂(J : Measure (ℝ × ℝ))) *
        Real.sqrt (∫ p, g p ^ 2 ∂(J : Measure (ℝ × ℝ))) := by
    have hfpower : (∫ p, ‖f p‖ ^ (2 : ℝ) ∂(J : Measure (ℝ × ℝ))) =
        ∫ p, f p ^ 2 ∂(J : Measure (ℝ × ℝ)) := by
      congr 1
      funext p
      calc
        ‖f p‖ ^ (2 : ℝ) = ‖f p‖ ^ (2 : ℕ) := Real.rpow_natCast _ _
        _ = f p ^ 2 := by rw [Real.norm_eq_abs]; exact sq_abs _
    have hgpower : (∫ p, ‖g p‖ ^ (2 : ℝ) ∂(J : Measure (ℝ × ℝ))) =
        ∫ p, g p ^ 2 ∂(J : Measure (ℝ × ℝ)) := by
      congr 1
      funext p
      calc
        ‖g p‖ ^ (2 : ℝ) = ‖g p‖ ^ (2 : ℕ) := Real.rpow_natCast _ _
        _ = g p ^ 2 := by rw [Real.norm_eq_abs]; exact sq_abs _
    have hleft : (∫ p, ‖f p‖ * ‖g p‖ ∂(J : Measure (ℝ × ℝ))) =
        ∫ p, |f p| * |g p| ∂(J : Measure (ℝ × ℝ)) := by
      simp only [Real.norm_eq_abs]
    calc
      _ = ∫ p, ‖f p‖ * ‖g p‖ ∂(J : Measure (ℝ × ℝ)) := hleft.symm
      _ ≤ (∫ p, ‖f p‖ ^ (2 : ℝ) ∂(J : Measure (ℝ × ℝ))) ^ (1 / 2) *
          (∫ p, ‖g p‖ ^ (2 : ℝ) ∂(J : Measure (ℝ × ℝ))) ^ (1 / 2) := hcs
      _ = Real.sqrt (∫ p, f p ^ 2 ∂(J : Measure (ℝ × ℝ))) *
          Real.sqrt (∫ p, g p ^ 2 ∂(J : Measure (ℝ × ℝ))) := by
        rw [hfpower, hgpower, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hvar1 : (∫ p, f p ^ 2 ∂(J : Measure (ℝ × ℝ))) = lawVariance H true := by
    have hvarJ : (∫ p, f p ^ 2 ∂(J : Measure (ℝ × ℝ))) = lawVariance J true := by
      rfl
    exact hvarJ.trans (compatible_variance_eq H J hc true hJ1 hH1)
  have hvar0 : (∫ p, g p ^ 2 ∂(J : Measure (ℝ × ℝ))) = lawVariance H false := by
    have hvarJ : (∫ p, g p ^ 2 ∂(J : Measure (ℝ × ℝ))) = lawVariance J false := by
      rfl
    exact hvarJ.trans (compatible_variance_eq H J hc false hJ0 hH0)
  have habs : |lawCovariance J| ≤ ∫ p, |f p| * |g p| ∂(J : Measure (ℝ × ℝ)) := by
    calc
      |lawCovariance J| = ‖∫ p, f p * g p ∂(J : Measure (ℝ × ℝ))‖ := by
        rw [Real.norm_eq_abs, hcov]
      _ ≤ ∫ p, ‖f p * g p‖ ∂(J : Measure (ℝ × ℝ)) := hnorm
      _ = ∫ p, |f p| * |g p| ∂(J : Measure (ℝ × ℝ)) := by
        congr 1
        funext p
        simp [Real.norm_eq_abs]
  rw [hcov]
  rw [hvar1, hvar0] at hcs'
  exact habs.trans hcs'

end
end SAP.P022.WH.W1.P.T17_L1

open SAP.P022.WH.W1.P.T17_L1
open SAP.P022 MeasureTheory

theorem SAP.P022.WH.W1.T17_L1_proof : SAP.P022.WH.W1.T17_L1 := by
  intro S H θ ρ h h3 hns
  have h3old : AronowAudit.P022.BoundedThirdMoments (SAP.P022.Bridge.toSequence S) := by
    rw [SAP.P022.Bridge.BoundedThirdMoments_eq]
    exact h3
  have hUIold := AronowAudit.P022.Wave1.tb13_square_integrability
    (SAP.P022.Bridge.toSequence S) h3old
  have hUI : UniformSquareIntegrability S := by
    rw [← SAP.P022.Bridge.UniformSquareIntegrability_eq]
    exact hUIold
  have hOld : AronowAudit.P022.Conditions123 (SAP.P022.Bridge.toSequence S) H θ ρ := by
    rw [SAP.P022.Bridge.Conditions123_eq]
    exact h
  have hnsOld : AronowAudit.P022.NonsingularLaw H := by
    rw [SAP.P022.Bridge.NonsingularLaw_eq]
    exact hns
  obtain ⟨hm, hcross, hpop, _hcons⟩ :=
    SAP.P022.Bridge.TailB_proposition1 S H θ ρ h hUI
  have hrefl : H ∈ compatibleLaws H := by
    intro t x
    rfl
  have hw := h.2.2.2.2.2.2.1
  have hthird (t : Bool) :
      Integrable (fun p : ℝ × ℝ => |coord t p| ^ 3) (H : Measure (ℝ × ℝ)) :=
    third_moment_integrable_of_bounded S H t hw h3
  have hthird' : LawThirdMomentsFinite H := by
    intro t
    simpa [coord] using hthird t
  have hH1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (H : Measure (ℝ × ℝ)) := by
    simpa [coord] using hm H hrefl true 2 (by norm_num)
  have hH0 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (H : Measure (ℝ × ℝ)) := by
    simpa [coord] using hm H hrefl false 2 (by norm_num)
  have hcoord1 (J : JointLaw) (hc : J ∈ compatibleLaws H) (t : Bool) :
      Integrable (fun p : ℝ × ℝ => coord t p) (J : Measure (ℝ × ℝ)) := by
    simpa [coord] using hm J hc t 1 (by norm_num)
  have hcoord2 (J : JointLaw) (hc : J ∈ compatibleLaws H) (t : Bool) :
      Integrable (fun p : ℝ × ℝ => coord t p ^ 2) (J : Measure (ℝ × ℝ)) := by
    simpa [coord] using hm J hc t 2 (by norm_num)
  have hLaw : LawFunctionalsDefined H := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro J hc
      refine ⟨?_, ?_⟩
      · intro t
        have h1 := hcoord1 J hc t
        have h2 := hcoord2 J hc t
        refine ⟨?_, ?_, ?_⟩
        · simpa [coord] using h1
        · simpa [coord] using h2
        · simpa [coord] using centered_square_integrable H J hc t h1 h2
      · exact centered_cross_integrable J (by simpa [coord] using hcoord1 J hc true)
          (by simpa [coord] using hcoord1 J hc false) (hcross J hc)
    · exact ⟨lawCovariance H, ⟨H, hrefl, rfl⟩⟩
    · let C := Real.sqrt (lawVariance H true) * Real.sqrt (lawVariance H false)
      refine ⟨C, ?_⟩
      rintro x ⟨J, hc, rfl⟩
      have hJ1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (J : Measure (ℝ × ℝ)) := by
        simpa [coord] using hcoord2 J hc true
      have hJ0 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (J : Measure (ℝ × ℝ)) := by
        simpa [coord] using hcoord2 J hc false
      have hb := covariance_abs_bound H J hc hJ1 hJ0 hH1 hH0
      dsimp [C]
      exact (abs_le.mp hb).2
    · let C := Real.sqrt (lawVariance H true) * Real.sqrt (lawVariance H false)
      refine ⟨-C, ?_⟩
      rintro x ⟨J, hc, rfl⟩
      have hJ1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (J : Measure (ℝ × ℝ)) := by
        simpa [coord] using hcoord2 J hc true
      have hJ0 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (J : Measure (ℝ × ℝ)) := by
        simpa [coord] using hcoord2 J hc false
      have hb := covariance_abs_bound H J hc hJ1 hJ0 hH1 hH0
      dsimp [C]
      exact (abs_le.mp hb).1
  have hvPosOld := AronowAudit.P022.Wave1.tb13_limiting_variance_pos
    (SAP.P022.Bridge.toSequence S) H θ ρ hOld hUIold hnsOld
  have hvPos : 0 < limitingTrueVariance H θ ρ := by
    simpa only [SAP.P022.Bridge.limitingTrueVariance_eq] using hvPosOld
  have hvLeOld := AronowAudit.P022.Wave1.tb13_true_le_bound
    (SAP.P022.Bridge.toSequence S) H θ ρ hOld hUIold
  have hvLe : limitingTrueVariance H θ ρ ≤ limitingBound H θ ρ .H := by
    simpa only [SAP.P022.Bridge.limitingTrueVariance_eq,
      SAP.P022.Bridge.limitingBound_eq, SAP.P022.Bridge.fromSide_H] using hvLeOld
  exact ⟨hLaw, hthird', hvPos, hvLe, hpop .H⟩
