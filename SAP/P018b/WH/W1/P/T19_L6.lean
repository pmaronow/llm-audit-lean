import SAP.P018b.WH.W1.Leaves
import AronowAudit.P018.Wave1.Gap.TailBRarePopulation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018b.WH.W1.P.T19_L6

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private abbrev U := AronowAudit.P018.RareUnit
private abbrev μ₀ := AronowAudit.P018.rareLaw

private def flipA (u : U) : U := ⟨u.m, u.label, !u.A, u.B⟩

private theorem flipA_involutive (u : U) : flipA (flipA u) = u := by
  cases u with
  | mk m c a b => cases a <;> rfl

private theorem flipA_sign (u : U) :
    AronowAudit.P018.signValue (flipA u).A = -AronowAudit.P018.signValue u.A := by
  cases u with
  | mk m c a b => cases a <;> norm_num [flipA, AronowAudit.P018.signValue]

private theorem flipA_mp : MeasurePreserving flipA μ₀ μ₀ := by
  classical
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro u
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton u)]
  have hp : flipA ⁻¹' ({u} : Set U) = {flipA u} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      calc
        v = flipA (flipA v) := (flipA_involutive v).symm
        _ = flipA u := congrArg flipA h
    · intro h
      rw [h]
      exact flipA_involutive u
  rw [hp, AronowAudit.P018.Wave1.TailB_rare_atom,
    AronowAudit.P018.Wave1.TailB_rare_atom]
  rfl

private def flipAt {N : ℕ} (i : Fin N) (ω : Fin N → U) : Fin N → U :=
  fun j => if j = i then flipA (ω j) else ω j

private theorem flipAt_involutive {N : ℕ} (i : Fin N) (ω : Fin N → U) :
    flipAt i (flipAt i ω) = ω := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flipAt, flipA_involutive]
  · simp [flipAt, h]

private def flipAtEquiv {N : ℕ} (i : Fin N) : (Fin N → U) ≃ (Fin N → U) where
  toFun := flipAt i
  invFun := flipAt i
  left_inv := flipAt_involutive i
  right_inv := flipAt_involutive i

private def flipAtMeasurableEquiv {N : ℕ} (i : Fin N) :
    (Fin N → U) ≃ᵐ (Fin N → U) :=
  { flipAtEquiv i with
    measurable_toFun := measurable_of_countable _
    measurable_invFun := measurable_of_countable _ }

private theorem flipAt_mp {N : ℕ} (i : Fin N) :
    MeasurePreserving (flipAt i) (Measure.pi fun _ : Fin N => μ₀)
      (Measure.pi fun _ : Fin N => μ₀) := by
  classical
  letI : IsProbabilityMeasure μ₀ := AronowAudit.P018.Wave1.TailB_rare_probability
  have hcoord : ∀ j : Fin N,
      MeasurePreserving (fun u : U => if j = i then flipA u else u) μ₀ μ₀ := by
    intro j
    by_cases h : j = i
    · simpa [h] using flipA_mp
    · convert (MeasurePreserving.id μ₀) using 1 <;> funext u <;> simp [h]
  have h := measurePreserving_pi (fun _ : Fin N => μ₀) (fun _ => μ₀) hcoord
  convert h using 1 <;> funext ω j <;> simp [flipAt]

private def sA {N : ℕ} (ω : Fin N → U) (i : Fin N) : ℝ :=
  AronowAudit.P018.signValue (ω i).A

private theorem flipAt_sign {N : ℕ} (i j : Fin N) (ω : Fin N → U) :
    sA (flipAt i ω) j = if j = i then -sA ω j else sA ω j := by
  by_cases h : j = i
  · subst j
    simp [sA, flipAt, flipA_sign]
  · simp [sA, flipAt, h]

private theorem flip_invariant_integral_zero {N : ℕ} (i : Fin N)
    (E : Set (Fin N → U)) (hE : ∀ ω, (flipAt i ω ∈ E) ↔ ω ∈ E) :
    (∫ ω, Set.indicator E (sA · i) ω ∂(Measure.pi fun _ : Fin N => μ₀)) = 0 := by
  let ν : Measure (Fin N → U) := Measure.pi fun _ : Fin N => μ₀
  have hp := flipAt_mp i
  have hc : (fun ω => Set.indicator E (sA · i) (flipAt i ω)) =
      fun ω => -Set.indicator E (sA · i) ω := by
    funext ω
    by_cases he : ω ∈ E
    · simp [Set.indicator_apply, hE ω, he, flipAt_sign]
    · have hne : flipAt i ω ∉ E := by
        intro hx
        exact he ((hE ω).mp hx)
      simp [Set.indicator_apply, he, hne]
  have hi := MeasurePreserving.integral_comp' (f := flipAtMeasurableEquiv i) hp
      (fun ω => Set.indicator E (sA · i) ω)
  have hce : (fun ω => Set.indicator E (sA · i) ((flipAtMeasurableEquiv i) ω)) =
      fun ω => -Set.indicator E (sA · i) ω := by
    simpa [flipAtMeasurableEquiv, flipAtEquiv] using hc
  rw [hce, integral_neg] at hi
  change (∫ ω, Set.indicator E (sA · i) ω ∂ν) = 0
  have hz : (∫ ω, Set.indicator E (sA · i) ω ∂ν) =
      -(∫ ω, Set.indicator E (sA · i) ω ∂ν) := by simpa using hi.symm
  linarith

private theorem flip_invariant_pair_zero {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (E : Set (Fin N → U)) (hE : ∀ ω, (flipAt i ω ∈ E) ↔ ω ∈ E) :
    (∫ ω, Set.indicator E (fun ω => sA ω i * sA ω j) ω
      ∂(Measure.pi fun _ : Fin N => μ₀)) = 0 := by
  let ν : Measure (Fin N → U) := Measure.pi fun _ : Fin N => μ₀
  have hp := flipAt_mp i
  have hc : (fun ω => Set.indicator E (fun z => sA z i * sA z j) (flipAt i ω)) =
      fun ω => -Set.indicator E (fun z => sA z i * sA z j) ω := by
    funext ω
    by_cases he : ω ∈ E
    · have hne : flipAt i ω ∈ E := (hE ω).mpr he
      simp only [Set.indicator_of_mem he, Set.indicator_of_mem hne]
      rw [flipAt_sign i i ω, flipAt_sign i j ω]
      simp [Ne.symm hij]
    · have hne : flipAt i ω ∉ E := by
        intro hx
        exact he ((hE ω).mp hx)
      simp [Set.indicator_apply, he, hne]
  have hi := MeasurePreserving.integral_comp' (f := flipAtMeasurableEquiv i) hp
      (fun ω => Set.indicator E (fun z => sA z i * sA z j) ω)
  have hce : (fun ω => Set.indicator E (fun z => sA z i * sA z j)
      ((flipAtMeasurableEquiv i) ω)) =
      fun ω => -Set.indicator E (fun z => sA z i * sA z j) ω := by
    simpa [flipAtMeasurableEquiv, flipAtEquiv] using hc
  rw [hce, integral_neg] at hi
  change (∫ ω, Set.indicator E (fun ω => sA ω i * sA ω j) ω ∂ν) = 0
  have hz : (∫ ω, Set.indicator E (fun ω => sA ω i * sA ω j) ω ∂ν) =
      -(∫ ω, Set.indicator E (fun ω => sA ω i * sA ω j) ω ∂ν) := by simpa using hi.symm
  linarith

private theorem sA_sq (N : ℕ) (ω : Fin N → U) (i : Fin N) :
    (sA ω i)^2 = 1 := by
  cases (ω i).A <;> norm_num [sA, AronowAudit.P018.signValue]

private theorem sA_abs {N : ℕ} (ω : Fin N → U) (i : Fin N) : |sA ω i| = 1 := by
  simpa [sA] using AronowAudit.P018.Wave1.TailB_rare_sign_abs (ω i).A

private theorem integrable_bounded {N : ℕ} (f : (Fin N → U) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ ω, |f ω| ≤ B) :
    Integrable f (Measure.pi fun _ : Fin N => μ₀) := by
  let ν : Measure (Fin N → U) := Measure.pi fun _ : Fin N => μ₀
  letI : IsProbabilityMeasure μ₀ := AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  exact (MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable B
    (ae_of_all _ hf) : MemLp f 2 ν).integrable one_le_two

private theorem integrable_pair {N : ℕ} (i j : Fin N) :
    Integrable (fun ω : Fin N → U => sA ω i * sA ω j)
      (Measure.pi fun _ : Fin N => μ₀) := by
  apply integrable_bounded (fun ω => sA ω i * sA ω j) 1 (by norm_num)
  intro ω
  rw [abs_mul, sA_abs, sA_abs]
  norm_num

private theorem pair_restrict_integral {N : ℕ} (i j : Fin N)
    (E : Set (Fin N → U)) (hE : ∀ ω, (flipAt i ω ∈ E) ↔ ω ∈ E)
    (hEm : MeasurableSet E) :
    (∫ ω, sA ω i * sA ω j ∂(Measure.pi fun _ : Fin N => μ₀).restrict E) =
      if i = j then ((Measure.pi fun _ : Fin N => μ₀) E).toReal else 0 := by
  let ν : Measure (Fin N → U) := Measure.pi fun _ : Fin N => μ₀
  by_cases hij : i = j
  · subst j
    rw [← integral_indicator hEm]
    have heq : Set.indicator E (fun ω => sA ω i * sA ω i) = Set.indicator E (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ E
      · have hsq : sA ω i * sA ω i = 1 := by rw [← pow_two, sA_sq]
        simp [hω, hsq]
      · simp [hω]
    rw [heq, integral_indicator_const 1 hEm]
    simp [Measure.real_def]
  · rw [← integral_indicator hEm]
    simpa [hij, ν] using flip_invariant_pair_zero i j hij E hE

private theorem dispersion_restrict_integral {N : ℕ} (hN : 0 < N)
    (E : Set (Fin N → U)) (hE : ∀ i ω, (flipAt i ω ∈ E) ↔ ω ∈ E)
    (hEm : MeasurableSet E) :
    (∫ ω, SAP.P018b.wholeRareDispersion
      (SAP.P018b.WH.W1.rareModel) ω ∂(Measure.pi fun _ : Fin N => μ₀).restrict E) =
      ((N : ℝ)-1) * ((Measure.pi fun _ : Fin N => μ₀) E).toReal := by
  let ν : Measure (Fin N → U) := Measure.pi fun _ : Fin N => μ₀
  letI : IsProbabilityMeasure μ₀ := AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hpair (i j : Fin N) : Integrable (fun ω : Fin N → U => sA ω i * sA ω j)
      (ν.restrict E) := (integrable_pair i j).restrict
  have hdouble : Integrable (fun ω : Fin N → U =>
      ∑ i : Fin N, ∑ j : Fin N, sA ω i * sA ω j) (ν.restrict E) := by
    apply integrable_finsetSum (s := Finset.univ)
    intro i hi
    apply integrable_finsetSum (s := Finset.univ)
    intro j hj
    exact hpair i j
  have hdouble_int :
      (∫ ω, (∑ i : Fin N, ∑ j : Fin N, sA ω i * sA ω j) ∂ν.restrict E) =
      (N : ℝ) * (ν E).toReal := by
    calc
      _ = ∑ i : Fin N, ∫ ω, (∑ j : Fin N, sA ω i * sA ω j) ∂ν.restrict E := by
        exact integral_finsetSum Finset.univ (fun i hi => by
          apply integrable_finsetSum (s := Finset.univ)
          intro j hj
          exact hpair i j)
      _ = ∑ i : Fin N, ∑ j : Fin N, ∫ ω, sA ω i * sA ω j ∂ν.restrict E := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum (s := Finset.univ) (fun j hj => hpair i j)
      _ = ∑ i : Fin N, ∑ j : Fin N,
          (if i = j then (ν E).toReal else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact pair_restrict_integral i j E (hE i) hEm
      _ = (N : ℝ) * (ν E).toReal := by simp
  have hpoint (ω : Fin N → U) :
      SAP.P018b.wholeRareDispersion
        (SAP.P018b.WH.W1.rareModel) ω =
      (N : ℝ) - (∑ i : Fin N, sA ω i)^2 / (N : ℝ) := by
    change (∑ i, (AronowAudit.P018.signValue (ω i).A -
        AronowAudit.P018.Wave1.TailB_rare_Abar ω)^2) = _
    rw [AronowAudit.P018.Wave1.TailB_rare_A_dispersion hN]
    simp only [sA]
    unfold AronowAudit.P018.Wave1.TailB_rare_Abar
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp [hn]
    <;> ring
  have hsum_point (ω : Fin N → U) :
      (∑ i : Fin N, sA ω i)^2 = ∑ i : Fin N, ∑ j : Fin N, sA ω i * sA ω j := by
    rw [pow_two]
    exact Finset.sum_mul_sum Finset.univ Finset.univ (fun i => sA ω i) (fun j => sA ω j)
  have hsum_int : Integrable (fun ω : Fin N → U => (∑ i : Fin N, sA ω i)^2)
      (ν.restrict E) := by
    convert hdouble using 1 <;> funext ω <;> exact hsum_point ω
  have hsum_integral :
      (∫ ω, (∑ i : Fin N, sA ω i)^2 ∂ν.restrict E) =
      (∫ ω, (∑ i : Fin N, ∑ j : Fin N, sA ω i * sA ω j) ∂ν.restrict E) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hsum_point
  have hpointFun : (fun ω => SAP.P018b.wholeRareDispersion
      (SAP.P018b.WH.W1.rareModel) ω) =
      fun ω => (N : ℝ) - (∑ i : Fin N, sA ω i)^2 / (N : ℝ) := funext hpoint
  rw [hpointFun]
  have hconst : Integrable (fun _ : Fin N → U => (N : ℝ)) (ν.restrict E) := integrable_const _
  rw [integral_sub hconst (hsum_int.div_const _)]
  rw [integral_const, measureReal_restrict_apply_univ, integral_div, hsum_integral, hdouble_int]
  simp only [smul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hn]
  rw [Measure.real_def]
  change (ν E).toReal * (N : ℝ) - (ν E).toReal =
    ((N : ℝ)-1) * (ν E).toReal
  ring

private theorem rare_event_flip_invariant (N m : ℕ) (i : Fin N) (ω : Fin N → U) :
    (flipAt i ω ∈ SAP.P018b.wholeRareEvent
      (SAP.P018b.WH.W1.rareModel) N m) ↔
    ω ∈ SAP.P018b.wholeRareEvent
      (SAP.P018b.WH.W1.rareModel) N m := by
  change ((∀ j, (flipAt i ω j).m = m) ∧
      Function.Injective (fun j => (flipAt i ω j).label.val)) ↔
    ((∀ j, (ω j).m = m) ∧ Function.Injective (fun j => (ω j).label.val))
  have hm (j : Fin N) : (flipAt i ω j).m = (ω j).m := by
    by_cases h : j = i
    · simp only [flipAt, if_pos h, flipA]
    · simp only [flipAt, if_neg h]
  have hc (j : Fin N) : (flipAt i ω j).label.val = (ω j).label.val := by
    by_cases h : j = i
    · unfold flipAt
      rw [if_pos h]
      rfl
    · unfold flipAt
      rw [if_neg h]
  constructor
  · rintro ⟨hl, hinj⟩
    refine ⟨?_, ?_⟩
    · intro j
      rw [← hm j]
      exact hl j
    · intro a b hab
      apply hinj
      change (flipAt i ω a).label.val = (flipAt i ω b).label.val
      rw [hc a, hc b]
      exact hab
  · rintro ⟨hl, hinj⟩
    refine ⟨?_, ?_⟩
    · intro j
      rw [hm j]
      exact hl j
    · intro a b hab
      apply hinj
      change (ω a).label.val = (ω b).label.val
      rw [← hc a, ← hc b]
      exact hab

private theorem rare_event_pos (N m : ℕ) (hNm : N ≤ m+1) :
    0 < (Measure.pi fun _ : Fin N => μ₀)
      (SAP.P018b.wholeRareEvent (SAP.P018b.WH.W1.rareModel) N m) := by
  classical
  let ω := AronowAudit.P018.Wave1.TailB_rare_sample N m hNm (fun _ => true) (fun _ => true)
  have hω : ω ∈ SAP.P018b.wholeRareEvent (SAP.P018b.WH.W1.rareModel) N m := by
    change ω ∈ AronowAudit.P018.Wave1.TailB_rare_event N m
    exact AronowAudit.P018.Wave1.TailB_rare_sample_event N m hNm (fun _ => true) (fun _ => true)
  have hmass : 0 < (Measure.pi fun _ : Fin N => μ₀) {ω} := by
    change 0 < AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N {ω}
    rw [AronowAudit.P018.Wave1.TailB_rare_row_atom]
    apply (pos_iff_ne_zero).2
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (ENNReal.ofReal_pos.mpr
      (AronowAudit.P018.Wave1.TailB_rare_p_pos (ω i).m)).ne'
  have hs : ({ω} : Set (Fin N → U)) ⊆
      SAP.P018b.wholeRareEvent (SAP.P018b.WH.W1.rareModel) N m := by
    intro z hz
    simpa [Set.mem_singleton_iff] using hz ▸ hω
  exact lt_of_lt_of_le hmass (measure_mono hs)

end SAP.P018b.WH.W1.P.T19_L6

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem SAP.P018b.WH.W1.T19_L6_proof : SAP.P018b.WH.W1.T19_L6 := by
  intro N hN
  let E : ℕ → Set (Fin N → AronowAudit.P018.RareUnit) := fun m =>
    SAP.P018b.wholeRareEvent SAP.P018b.WH.W1.rareModel N m
  let ν : Measure (Fin N → AronowAudit.P018.RareUnit) :=
    Measure.pi fun _ : Fin N => AronowAudit.P018.rareLaw
  have hprob : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw := hprob
  letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hmeas (m : ℕ) : MeasurableSet (E m) :=
    (Set.to_countable (E m)).measurableSet
  have hdisp (F : Set (Fin N → AronowAudit.P018.RareUnit))
      (hF : ∀ i ω, (SAP.P018b.WH.W1.P.T19_L6.flipAt i ω ∈ F) ↔ ω ∈ F)
      (hFm : MeasurableSet F) :=
    SAP.P018b.WH.W1.P.T19_L6.dispersion_restrict_integral (by omega) F hF hFm
  refine ⟨?_, ?_⟩
  · have h := hdisp Set.univ (by intro i ω; simp) MeasurableSet.univ
    change (∫ ω, SAP.P018b.wholeRareDispersion
      SAP.P018b.WH.W1.rareModel ω ∂ν) = (N : ℝ)-1
    simpa [ν, Measure.real_def] using h
  · intro m hNm
    have h := hdisp (E m)
      (by intro i ω; exact SAP.P018b.WH.W1.P.T19_L6.rare_event_flip_invariant N m i ω)
      (hmeas m)
    have hp := SAP.P018b.WH.W1.P.T19_L6.rare_event_pos N m hNm
    change (∫ ω, SAP.P018b.wholeRareDispersion
      SAP.P018b.WH.W1.rareModel ω ∂ν.restrict (E m)) /
      (ν (E m)).toReal = (N : ℝ)-1
    rw [h]
    have hp' : (ν (E m)).toReal ≠ 0 := by
      exact ne_of_gt (ENNReal.toReal_pos hp.ne' (measure_ne_top ν (E m)))
    field_simp [hp']
    <;> ring
