import SAP.P029b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W1.P.T16_L3

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

universe u v

private abbrev Obs (X : Type v) := (X × Bool × Bool × ℝ × ℝ) × Bool

private def obsProfile {X : Type v} (q : Obs X) : X := q.1.1

private def obsComplier {X : Type v} (q : Obs X) : Prop :=
  q.1.2.1 = false ∧ q.1.2.2.1 = true

private def obsTau {X : Type v} (q : Obs X) : ℝ :=
  q.1.2.2.2.2 - q.1.2.2.2.1

private def profileCell {X : Type v} (x : X) : Set (Obs X) :=
  {q | obsProfile q = x}

private def complierCell {X : Type v} (x : X) : Set (Obs X) :=
  {q | obsComplier q ∧ obsProfile q = x}

private def maskedTau {X : Type v} (x : X) (q : Obs X) : ℝ :=
  if obsComplier q ∧ obsProfile q = x then obsTau q else 0

theorem profile_mass_eq {Ω : Type u} {X : Type v} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure Ω)
    (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (i : ℕ)
    (h : IdentDistrib (jointVariables (U i) (Z i)) (jointVariables (U 0) (Z 0)) μ μ)
    (x : X) :
    mP μ {ω | (U i ω).x = x} = mP μ {ω | (U 0 ω).x = x} := by
  have hm := h.measure_mem_eq (s := profileCell x) (by
    change MeasurableSet ({q : Obs X | obsProfile q = x})
    exact (measurable_fst.comp measurable_fst) (measurableSet_singleton x))
  have heq :
      μ {ω | (U i ω).x = x} = μ {ω | (U 0 ω).x = x} := by
    simpa [profileCell, obsProfile, jointVariables] using hm
  exact congrArg ENNReal.toReal heq

theorem cell_mass_eq {Ω : Type u} {X : Type v} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure Ω)
    (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (i : ℕ)
    (h : IdentDistrib (jointVariables (U i) (Z i)) (jointVariables (U 0) (Z 0)) μ μ)
    (x : X) :
    mP μ {ω | (U i ω).complier ∧ (U i ω).x = x} =
      mP μ {ω | (U 0 ω).complier ∧ (U 0 ω).x = x} := by
  have hm := h.measure_mem_eq (s := complierCell x) (by
    have hprof : Measurable (fun q : Obs X => obsProfile q) :=
      measurable_fst.comp measurable_fst
    have hd0 : Measurable (fun q : Obs X => q.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hd1 : Measurable (fun q : Obs X => q.1.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hs : MeasurableSet {q : Obs X | obsProfile q = x} :=
      hprof (measurableSet_singleton x)
    have hd : MeasurableSet {q : Obs X | q.1.2.1 = false ∧ q.1.2.2.1 = true} := by
      exact (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
    exact hd.inter hs)
  have heq :
      μ {ω | (U i ω).complier ∧ (U i ω).x = x} =
        μ {ω | (U 0 ω).complier ∧ (U 0 ω).x = x} := by
    simpa [complierCell, obsComplier, obsProfile, jointVariables,
      PotentialUnit.complier] using hm
  exact congrArg ENNReal.toReal heq

theorem cell_tau_integral_eq {Ω : Type u} {X : Type v}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) (U : ℕ → Ω → PotentialUnit X) (Z : ℕ → Ω → Bool)
    (i : ℕ)
    (h : IdentDistrib (jointVariables (U i) (Z i)) (jointVariables (U 0) (Z 0)) μ μ)
    (hiv : ∀ j, IVAssumptions μ (U j) (Z j)) (x : X) :
    (∫ ω in {ω | (U i ω).complier ∧ (U i ω).x = x}, (U i ω).tau ∂μ) =
      (∫ ω in {ω | (U 0 ω).complier ∧ (U 0 ω).x = x}, (U 0 ω).tau ∂μ) := by
  let g : Obs X → ℝ := maskedTau x
  have hprof : Measurable (fun q : Obs X => obsProfile q) :=
    measurable_fst.comp measurable_fst
  have hd0 : Measurable (fun q : Obs X => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hd1 : Measurable (fun q : Obs X => q.1.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hcomp : MeasurableSet {q : Obs X | obsComplier q} := by
    change MeasurableSet {q : Obs X | q.1.2.1 = false ∧ q.1.2.2.1 = true}
    exact (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
  have hprofSet : MeasurableSet {q : Obs X | obsProfile q = x} :=
    hprof (measurableSet_singleton x)
  have htest : MeasurableSet {q : Obs X | obsComplier q ∧ obsProfile q = x} :=
    hcomp.inter hprofSet
  have hval : Measurable (fun q : Obs X => obsTau q) := by
    change Measurable (fun q : Obs X => q.1.2.2.2.2 - q.1.2.2.2.1)
    fun_prop
  have hg : Measurable g := by
    change Measurable (fun q : Obs X => if obsComplier q ∧ obsProfile q = x then obsTau q else 0)
    exact Measurable.ite htest hval measurable_const
  have hid := h.comp hg
  have hi := hid.integral_eq
  have hEi : MeasurableSet {ω | (U i ω).complier ∧ (U i ω).x = x} := by
    have hx : Measurable (fun ω => (U i ω).x) := (hiv i).1
    have hd0 : Measurable (fun ω => (U i ω).d0) := (hiv i).2.1
    have hd1 : Measurable (fun ω => (U i ω).d1) := (hiv i).2.2.1
    have hc : MeasurableSet {ω | (U i ω).complier} := by
      change MeasurableSet {ω | (U i ω).d0 = false ∧ (U i ω).d1 = true}
      exact (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
    exact hc.inter (hx (measurableSet_singleton x))
  have hE0 : MeasurableSet {ω | (U 0 ω).complier ∧ (U 0 ω).x = x} := by
    have hx : Measurable (fun ω => (U 0 ω).x) := (hiv 0).1
    have hd0 : Measurable (fun ω => (U 0 ω).d0) := (hiv 0).2.1
    have hd1 : Measurable (fun ω => (U 0 ω).d1) := (hiv 0).2.2.1
    have hc : MeasurableSet {ω | (U 0 ω).complier} := by
      change MeasurableSet {ω | (U 0 ω).d0 = false ∧ (U 0 ω).d1 = true}
      exact (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
    exact hc.inter (hx (measurableSet_singleton x))
  have hleft : (fun ω => g (jointVariables (U i) (Z i) ω)) =
      {ω | (U i ω).complier ∧ (U i ω).x = x}.indicator (fun ω => (U i ω).tau) := by
    funext ω
    classical
    by_cases hw : (U i ω).complier ∧ (U i ω).x = x
    · have hraw : ((U i ω).d0 = false ∧ (U i ω).d1 = true) ∧ (U i ω).x = x := by
        simpa [PotentialUnit.complier] using hw
      simp [g, maskedTau, obsComplier, obsProfile, obsTau, jointVariables,
        PotentialUnit.complier, PotentialUnit.tau, Set.indicator, hraw]
    · have hraw : ¬ (((U i ω).d0 = false ∧ (U i ω).d1 = true) ∧ (U i ω).x = x) := by
        simpa [PotentialUnit.complier] using hw
      simp [g, maskedTau, obsComplier, obsProfile, obsTau, jointVariables,
        PotentialUnit.complier, PotentialUnit.tau, Set.indicator, hraw]
  have hright : (fun ω => g (jointVariables (U 0) (Z 0) ω)) =
      {ω | (U 0 ω).complier ∧ (U 0 ω).x = x}.indicator (fun ω => (U 0 ω).tau) := by
    funext ω
    classical
    by_cases hw : (U 0 ω).complier ∧ (U 0 ω).x = x
    · have hraw : ((U 0 ω).d0 = false ∧ (U 0 ω).d1 = true) ∧ (U 0 ω).x = x := by
        simpa [PotentialUnit.complier] using hw
      simp [g, maskedTau, obsComplier, obsProfile, obsTau, jointVariables,
        PotentialUnit.complier, PotentialUnit.tau, Set.indicator, hraw]
    · have hraw : ¬ (((U 0 ω).d0 = false ∧ (U 0 ω).d1 = true) ∧ (U 0 ω).x = x) := by
        simpa [PotentialUnit.complier] using hw
      simp [g, maskedTau, obsComplier, obsProfile, obsTau, jointVariables,
        PotentialUnit.complier, PotentialUnit.tau, Set.indicator, hraw]
  change (∫ ω, g (jointVariables (U i) (Z i) ω) ∂μ) =
    (∫ ω, g (jointVariables (U 0) (Z 0) ω) ∂μ) at hi
  rw [hleft, hright] at hi
  rw [integral_indicator hEi, integral_indicator hE0] at hi
  exact hi

end
end SAP.P029b.WH.W1.P.T16_L3

open SAP.P029b
open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

theorem SAP.P029b.WH.W1.T16_L3_proof : SAP.P029b.WH.W1.T16_L3 := by
  intro Ω X _ _ _ _ μ hμ U Z s hraw hversions
  rcases hraw with ⟨hiv, hind, hident, hsm, hrange, hover, hcons⟩
  classical
  let c : X → ℝ := scoreAt μ (U 0)
  let m : X → ℝ := complierAt μ (U 0)
  have hscore (i : ℕ) (x : X) : scoreAt μ (U i) x = c x := by
    dsimp [c]
    change mP μ {ω | (U i ω).complier ∧ (U i ω).x = x} /
        mP μ {ω | (U i ω).x = x} =
      mP μ {ω | (U 0 ω).complier ∧ (U 0 ω).x = x} /
        mP μ {ω | (U 0 ω).x = x}
    rw [SAP.P029b.WH.W1.P.T16_L3.cell_mass_eq μ U Z i (hident i) x,
      SAP.P029b.WH.W1.P.T16_L3.profile_mass_eq μ U Z i (hident i) x]
  have hmean (i : ℕ) (x : X) : complierAt μ (U i) x = m x := by
    dsimp [m]
    change (∫ ω in {ω | (U i ω).complier ∧ (U i ω).x = x}, (U i ω).tau ∂μ) /
        mP μ {ω | (U i ω).complier ∧ (U i ω).x = x} =
      (∫ ω in {ω | (U 0 ω).complier ∧ (U 0 ω).x = x}, (U 0 ω).tau ∂μ) /
        mP μ {ω | (U 0 ω).complier ∧ (U 0 ω).x = x}
    rw [SAP.P029b.WH.W1.P.T16_L3.cell_tau_integral_eq μ U Z i (hident i) hiv x,
      SAP.P029b.WH.W1.P.T16_L3.cell_mass_eq μ U Z i (hident i) x]
  have hscoreVersions : ∀ i, ScoreVersions μ (U i) c m := by
    intro i
    rcases hversions i with ⟨hc, hm, hcc, hmc⟩
    have hc0 : Measurable c := by simpa [c] using (hversions 0).1
    have hm0 : Measurable m := by simpa [m] using (hversions 0).2.1
    refine ⟨hc0, hm0, ?_, ?_⟩
    · have heq : (fun ω => c (U i ω).x) =ᵐ[μ] fun ω => scoreAt μ (U i) (U i ω).x :=
        Filter.Eventually.of_forall (fun ω => (hscore i (U i ω).x).symm)
      exact heq.trans hcc
    · have heq : (fun ω => c (U i ω).x * m (U i ω).x) =ᵐ[μ]
        fun ω => scoreAt μ (U i) (U i ω).x * complierAt μ (U i) (U i ω).x :=
        Filter.Eventually.of_forall (fun ω =>
          congrArg₂ (fun a b : ℝ => a * b)
            (hscore i (U i ω).x).symm (hmean i (U i ω).x).symm)
      exact heq.trans hmc
  rcases hover with ⟨ε, hε, hpositive⟩
  refine {
    iv := hiv
    independent := hind
    identical := hident
    score := hscoreVersions
    overlap := ?_
    estimated_measurable := hsm
    estimated_range := hrange
    uniform_consistency := hcons
  }
  refine ⟨ε, hε, ?_⟩
  intro i
  have hcell := AronowAudit.P029.Wave1.wcl_ae_positive_cell
    (μ := μ) (T := fun ω => (U i ω).x)
  filter_upwards [hcell] with ω hω
  have hmass := SAP.P029b.WH.W1.P.T16_L3.profile_mass_eq μ U Z i (hident i) (U i ω).x
  have hpos0 : 0 < mP μ {η | (U 0 η).x = (U i ω).x} := by
    rw [← hmass]
    exact hω
  have hb := hpositive (U i ω).x hpos0
  simpa [c] using hb
