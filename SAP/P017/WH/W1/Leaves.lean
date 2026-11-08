import SAP.P017.Defs.WholeW1
import SAP.P017.Bridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v
namespace SAP.P017.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- Conditional means strictly straddle the threshold when both sides have
positive mass. Adapt the positive centered-indicator integrals in
`AronowAudit.P017.straddling_weight_representation`: integrate
`(t-τ)1{τ<t}` and `(τ-t)1{τ>t}`, whose supports have positive mass.
Expand their integrals and divide by the positive side probabilities.
All indicator integrals are integrable restrictions of the assumed integrable effect. -/
def T2_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ), Measurable τ → Integrable τ G → ∀ t : ℝ,
    0 < pr G {ω | τ ω < t} → 0 < pr G {ω | t < τ ω} →
    lowerMean G τ t < t ∧ t < upperMean G τ t

/-- Exact bounded two-region weight certificate for an arbitrary coefficient
strictly between zero and one. Each summand is a constant times a measurable
indicator. Integrability of its product with τ follows from integrability of
the restricted effect. Integral linearity gives weight mean one and weighted
effect mean `a*m₋+(1-a)*m₊`; pointwise indicator bounds give the stated bound.
No independence, bounded-effect, or atom assumption is needed. -/
def T2_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (G : Measure Ω) [IsProbabilityMeasure G]
    (τ : Ω → ℝ), Measurable τ → Integrable τ G → ∀ t : ℝ,
    0 < pr G {ω | τ ω < t} → 0 < pr G {ω | t < τ ω} →
    ∀ a : ℝ, 0 < a → a < 1 →
    AdmissibleWeight G τ (twoRegionWeight G τ t a) ∧
    (∀ ω, 0 ≤ twoRegionWeight G τ t a ω ∧
      twoRegionWeight G τ t a ω ≤
        a / pr G {ω | τ ω < t} + (1 - a) / pr G {ω | t < τ ω}) ∧
    (∫ ω, twoRegionWeight G τ t a ω ∂G) = 1 ∧
    (∫ ω, twoRegionWeight G τ t a ω * τ ω ∂G) =
      a * lowerMean G τ t + (1 - a) * upperMean G τ t

/-- A probability law concentrated on a finite set has finite nonempty closed
support, all of whose points are positive atoms. Remove zero-mass points from
the finite set; a finite union of null singletons is null. The remaining finite
set is closed and conull, so `Measure.support_subset_of_isClosed` puts the
support inside it. Conull support and probability mass one imply nonemptiness.
This is a statement about the law, so zero-probability values in the original
finite set are correctly excluded. -/
def T3_L1 : Prop :=
  ∀ (Q : Measure ℝ) [IsProbabilityMeasure Q] (S : Finset ℝ),
    (∀ᵐ x ∂Q, x ∈ S) →
    Q.support.Finite ∧ Q.support.Nonempty ∧ ∀ x ∈ Q.support, 0 < Q.real {x}

theorem T2_assembly (h1 : T2_L1.{u}) (h2 : T2_L2.{u}) : T2WholeStatement.{u} := by
  intro Ω mΩ G hG τ hτm hτi
  refine ⟨AronowAudit.P017.weighted_mean_characterization G τ hτm hτi,
    AronowAudit.P017.weighted_support_consequences G τ hτm hτi, ?_, ?_⟩
  · intro t hp
    let S := {ω | τ ω = t}
    let p := pr G S
    have hm : MeasurableSet S := measurableSet_eq_fun hτm measurable_const
    have hp' : 0 < p := hp
    have hwi : Integrable (atomWeight G τ t) G :=
      (integrable_const (1 / p)).indicator hm
    have hprod : (fun ω => atomWeight G τ t ω * τ ω) =
        S.indicator (fun _ => t / p) := by
      funext ω
      by_cases hω : τ ω = t <;> simp [atomWeight, S, p, hω]
      all_goals ring
    have hd : (∫ ω, atomWeight G τ t ω ∂G) = 1 := by
      change (∫ ω, S.indicator (fun _ => 1 / p) ω ∂G) = 1
      rw [integral_indicator_const (1 / p) hm]
      change p * (1 / p) = 1
      field_simp [hp'.ne']
    have hn : (∫ ω, atomWeight G τ t ω * τ ω ∂G) = t := by
      rw [hprod, integral_indicator_const (t / p) hm]
      change p * (t / p) = t
      field_simp [hp'.ne']
    have hb : ∀ ω, 0 ≤ atomWeight G τ t ω ∧ atomWeight G τ t ω ≤ 1 / p := by
      intro ω
      by_cases hω : τ ω = t
      · have hv : atomWeight G τ t ω = 1 / p := by simp [atomWeight, hω, p, S]
        rw [hv]
        exact ⟨(one_div_pos.mpr hp').le, le_rfl⟩
      · have hv : atomWeight G τ t ω = 0 := by simp [atomWeight, hω]
        rw [hv]
        exact ⟨le_rfl, (one_div_pos.mpr hp').le⟩
    refine ⟨⟨measurable_const.indicator hm, fun ω => (hb ω).1, hwi, ?_, ?_⟩,
      hb, hd, hn⟩
    · rw [hd]; norm_num
    · rw [hprod]
      exact (integrable_const (t / p)).indicator hm
  · intro t hl hu
    obtain ⟨hml, hmu⟩ := h1 G τ hτm hτi t hl hu
    have hd : 0 < upperMean G τ t - lowerMean G τ t := by linarith
    have ha : 0 < mixtureCoefficient G τ t := div_pos (sub_pos.mpr hmu) hd
    have ha1 : mixtureCoefficient G τ t < 1 := by
      change (upperMean G τ t - t) / (upperMean G τ t - lowerMean G τ t) < 1
      exact (div_lt_one hd).mpr (by linarith)
    have halg : mixtureCoefficient G τ t * lowerMean G τ t +
        (1 - mixtureCoefficient G τ t) * upperMean G τ t = t := by
      unfold mixtureCoefficient
      field_simp [hd.ne']
      ring
    obtain ⟨hw, hb, hi, hm⟩ := h2 G τ hτm hτi t hl hu _ ha ha1
    exact ⟨hml, hmu, hd, ha, ha1, hw, hb, hi, hm.trans halg⟩

theorem T3_assembly (h1 : T3_L1) : T3WholeStatement.{u, v} := by
  intro Ω mΩ G hG τ hτm hτi hc
  have base := AronowAudit.P017.Wave1.corrected_proposition1_proof G τ hτm hτi hc
    (Measure.dirac (0 : ℝ)) (fun _ _ => 0) (fun _ => measurable_const)
  have hull (x : ℝ) : supportInf (effectSupport G τ) ≤
      (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ∧
      (clipTarget (populationMean G τ) (effectRadius G τ) x : EReal) ≤
        supportSup (effectSupport G τ) := ⟨(base.1 x).1, (base.1 x).2.1⟩
  have endpoints (htop : effectRadius G τ ≠ ⊤) :
      supportInf (effectSupport G τ) ≤
        ((populationMean G τ - (effectRadius G τ).toReal : ℝ) : EReal) ∧
      ((populationMean G τ + (effectRadius G τ).toReal : ℝ) : EReal) ≤
        supportSup (effectSupport G τ) := by
    have hl : clipTarget (populationMean G τ) (effectRadius G τ)
        (populationMean G τ - (effectRadius G τ).toReal) =
        populationMean G τ - (effectRadius G τ).toReal := by
      simp only [clipTarget, htop, ↓reduceIte]
      apply (AronowAudit.P017.clipReal_eq_self_iff _ _ _ ENNReal.toReal_nonneg).mpr
      rw [show populationMean G τ - (effectRadius G τ).toReal - populationMean G τ =
        -(effectRadius G τ).toReal by ring, abs_neg,
        abs_of_nonneg ENNReal.toReal_nonneg]
    have hu : clipTarget (populationMean G τ) (effectRadius G τ)
        (populationMean G τ + (effectRadius G τ).toReal) =
        populationMean G τ + (effectRadius G τ).toReal := by
      simp only [clipTarget, htop, ↓reduceIte]
      apply (AronowAudit.P017.clipReal_eq_self_iff _ _ _ ENNReal.toReal_nonneg).mpr
      rw [add_sub_cancel_left, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ⟨by simpa only [hl] using (hull (populationMean G τ - (effectRadius G τ).toReal)).1,
      by simpa only [hu] using (hull (populationMean G τ + (effectRadius G τ).toReal)).2⟩
  refine ⟨base.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨(AronowAudit.P017.clipTarget_eq_self_iff _ _ _).mpr hx.le,
      base.2.1 x hx, ?_⟩
    intro htop
    have habs : |x - populationMean G τ| < (effectRadius G τ).toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) htop).mp hx
    have hab := abs_lt.mp habs
    exact ⟨(endpoints htop).1, by linarith, by linarith, (endpoints htop).2⟩
  · intro htop
    have hull' (x : ℝ) : supportInf (effectSupport G τ) ≤ (x : EReal) ∧
        (x : EReal) ≤ supportSup (effectSupport G τ) := by
      simpa only [clipTarget, htop, ↓reduceIte] using hull x
    refine ⟨(EReal.eq_bot_iff_forall_lt _).mpr ?_,
      (EReal.eq_top_iff_forall_lt _).mpr ?_, base.2.2.1 (Or.inl htop)⟩
    · intro y
      exact (hull' (y - 1)).1.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    · intro y
      exact (EReal.coe_lt_coe_iff.mpr (show y < y + 1 by linarith)).trans_le
        (hull' (y + 1)).2
  · intro _ hatoms
    exact base.2.2.1 (Or.inr hatoms)
  · rintro ⟨S, hS⟩
    have hSQ : ∀ᵐ x ∂G.map τ, x ∈ S :=
      (mem_ae_map_iff hτm.aemeasurable S.measurableSet).mpr hS
    obtain ⟨hfin, hne, hatoms⟩ := h1 (G.map τ) S hSQ
    have himage : ((fun x : ℝ => (x : EReal)) '' (G.map τ).support).Nonempty := hne.image _
    have hifin : ((fun x : ℝ => (x : EReal)) '' (G.map τ).support).Finite := hfin.image _
    have hlow : supportInf (effectSupport G τ) ∈
        (fun x : ℝ => (x : EReal)) '' (G.map τ).support := himage.csInf_mem hifin
    have hupp : supportSup (effectSupport G τ) ∈
        (fun x : ℝ => (x : EReal)) '' (G.map τ).support := himage.csSup_mem hifin
    apply base.2.2.1
    right
    intro t _ ht
    have htmem : t ∈ (G.map τ).support := by
      rcases ht with ht | ht
      · obtain ⟨x, hx, hxeq⟩ := hlow
        have hxt : x = t := EReal.coe_eq_coe_iff.mp (hxeq.trans ht.symm)
        simpa only [hxt] using hx
      · obtain ⟨x, hx, hxeq⟩ := hupp
        have hxt : x = t := EReal.coe_eq_coe_iff.mp (hxeq.trans ht.symm)
        simpa only [hxt] using hx
    have hp := hatoms t htmem
    change 0 < (G {ω | τ ω = t}).toReal
    change 0 < ((G.map τ) {t}).toReal at hp
    rw [Measure.map_apply hτm (measurableSet_singleton t)] at hp
    exact hp
  · intro Ξ mΞ P hP hat hhm hroot
    let hat' : ℕ → Ξ → ℝ := fun n => if n = 0 then fun _ => 0 else hat n
    have hhm' : ∀ n, Measurable (hat' n) := by
      intro n
      by_cases hn : n = 0
      · simpa only [hat', hn, ↓reduceIte] using (measurable_const : Measurable (fun _ : Ξ => (0 : ℝ)))
      · simpa only [hat', hn, ↓reduceIte] using hhm n (by omega)
    have hroot' : RootNNormal P hat' (populationMean G τ) := by
      obtain ⟨v, hv, hw⟩ := hroot
      refine ⟨v, hv, TendstoInDistribution.congr ?_ (ae_of_all _ (fun _ => rfl)) hw⟩
      intro n
      apply ae_of_all
      intro ω
      by_cases hn : n = 0 <;> simp [hat', hn, sqrtN]
    have hlim := (AronowAudit.P017.Wave1.corrected_proposition1_proof G τ hτm hτi hc
      P hat' hhm').2.2.2 hroot'
    constructor
    · apply hlim.1.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      simp only [hat', show n ≠ 0 by omega, ↓reduceIte]
      rfl
    · apply hlim.2.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      simp only [hat', show n ≠ 0 by omega, ↓reduceIte]
      rfl

theorem T14_assembly : T14WholeStatement.{u, v} := by
  have h : T5Statement := SAP.P017.Bridge.T5_correspondence.mpr
    AronowAudit.P017.Wave1.normal_shift_probability_counterexample_proof
  obtain ⟨hm, hi, hμ, hS, hc, hroot, hrem, hu, hN, hcentral, hrate, hnot⟩ := h
  refine ⟨SAP.P017.Bridge.T14_correspondence.mpr (@AronowAudit.P017.proposition3),
    hm, hi, hμ, hS, hc, hroot, hrem, hu, ?_, ?_, ?_, ?_⟩
  · intro n s
    simp [shiftedDifference, hμ, hc, clipTarget]
  · intro n hn
    have hh := hN n hn
    exact ⟨hh.1, fun _ => rfl, hh.2.2.2.1, hh.2.2.2.2.2.1⟩
  · intro n
    by_cases hn : n = 0
    · simp [positiveReciprocal, hn]
    · simp only [positiveReciprocal, hn, ↓reduceIte]
      exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  · intro hpos
    apply hnot
    intro η hη
    apply (hpos η hη).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [positiveReciprocal, show n ≠ 0 by omega]

theorem T15_assembly : T15WholeStatement.{u, v} := by
  have h := AronowAudit.P017.Wave1.normal_shift_mse_counterexample_proof
  obtain ⟨hm, hi, hμ, hS, hc, hrem, he, hsecond, hcentral, hp, hlower,
    htail, htailbound, h6, hgap, hpos⟩ := h
  have hμ' : populationMean normalPopulation normalEffect = 0 := hμ
  have hc' : effectRadius normalPopulation normalEffect = 1 := hc
  have hmeanm : Measurable (normalMean 25) := by
    unfold normalMean sampleMean
    fun_prop
  have hDm : Measurable (shiftedDifference 25) := by
    unfold shiftedDifference clipReal shiftedNormalMean normalMean sampleMean
    fun_prop
  obtain ⟨_, _, _, _, _, _, _, _, hN, _⟩ :=
    AronowAudit.P017.Wave1.normal_shift_probability_counterexample_proof
  have hmean2 : Integrable (fun s => normalMean 25 s ^ 2) (iidSamples normalPopulation) := by
    have hg : Integrable (fun x : ℝ => x ^ 2)
        ((iidSamples normalPopulation).map (normalMean 25)) := by
      have hlaw : (iidSamples normalPopulation).map (normalMean 25) =
          gaussianReal 0 (1 / 25) := (hN 25 (by norm_num)).1
      rw [hlaw]
      have h2 : MemLp (id : ℝ → ℝ) (2 : ℝ≥0∞) (gaussianReal 0 (1 / 25)) :=
        memLp_id_gaussianReal 2
      have hgi : Integrable (fun x : ℝ => ‖id x‖ ^ 2) (gaussianReal 0 (1 / 25)) :=
        h2.integrable_norm_pow'
      simpa only [id_eq, Real.norm_eq_abs, sq_abs] using hgi
    exact hg.comp_measurable hmeanm
  have hD2 : Integrable (fun s => shiftedDifference 25 s ^ 2) (iidSamples normalPopulation) := by
    apply ((hmean2.const_mul 2).add (integrable_const 2)).mono'
      (hDm.pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro s
    have hb := AronowAudit.P017.clipReal_bounds 0 1 (shiftedNormalMean 25 s) (by norm_num)
    have hy2 : clipReal 0 1 (shiftedNormalMean 25 s) ^ 2 ≤ 1 := by
      change 0 - 1 ≤ clipReal 0 1 (shiftedNormalMean 25 s) ∧
        clipReal 0 1 (shiftedNormalMean 25 s) ≤ 0 + 1 at hb
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - clipReal 0 1 (shiftedNormalMean 25 s))
        (by linarith : 0 ≤ 1 + clipReal 0 1 (shiftedNormalMean 25 s))]
    change ‖shiftedDifference 25 s ^ 2‖ ≤ 2 * normalMean 25 s ^ 2 + 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (shiftedDifference 25 s))]
    change (normalMean 25 s - clipReal 0 1 (shiftedNormalMean 25 s)) ^ 2 ≤
      2 * normalMean 25 s ^ 2 + 2
    nlinarith [sq_nonneg (normalMean 25 s + clipReal 0 1 (shiftedNormalMean 25 s))]
  refine ⟨?_, hm, hi, hμ', hS, hc', hrem, he, hsecond, ?_, hcentral, hp, hD2, hgap, hpos⟩
  · intro Ω Ξ mΩ mΞ G hG τ hτm hτi hc P hP hat Z ε hhm var hv hr he
    let hat' : ℕ → Ξ → ℝ := fun n => if n = 0 then fun _ => 0 else hat n
    have hhm' : ∀ n, Measurable (hat' n) := by
      intro n
      by_cases hn : n = 0
      · simpa only [hat', hn, ↓reduceIte] using (measurable_const : Measurable (fun _ : Ξ => (0 : ℝ)))
      · simpa only [hat', hn, ↓reduceIte] using hhm n (by omega)
    have hr' : NormalRemainder P hat' Z ε (populationMean G τ) var := by
      refine ⟨hr.1, hr.2.1, ?_⟩
      intro n hn
      simpa only [hat', show n ≠ 0 by omega, ↓reduceIte] using hr.2.2 n hn
    have hlim := AronowAudit.P017.Wave1.proposition4_proof G τ hτm hτi hc P
      hat' Z ε hhm' var hv hr' he
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp only [hat', show n ≠ 0 by omega, ↓reduceIte]
    rfl
  · intro n s
    simp [shiftedDifference, clipTarget, hμ', hc']

end
end SAP.P017.WH.W1
