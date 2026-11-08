import SAP.P014.Defs.WholeW1
import SAP.P014.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014.WH.W1

open scoped BigOperators
open MeasureTheory
noncomputable section
universe u

/-- Finite assignment-law transfer. Sum the probabilities of the disjoint
measurable singleton fibers, discard zero fibers, and use the same finite fiber
decomposition for an arbitrary assignment event. An almost sure property holds
at every positive atom, and conversely, since the finitely many zero fibers
have null union. No finiteness of the original probability space is assumed.
Expected proof: about 60--100 lines. -/
def T2_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → TreatmentVector N), Measurable Z →
  IsDistribution (assignmentLaw μ Z) ∧
  (∀ P : TreatmentVector N → Prop,
    probability (assignmentLaw μ Z) P = eventProbability μ (fun ω => P (Z ω))) ∧
  (∀ P : TreatmentVector N → Prop,
    (∀ᵐ ω ∂μ, P (Z ω)) ↔ ∀ z ∈ (assignmentLaw μ Z).atoms, P z)

/-- Ordinary expectation transfer, including its integrability prerequisite.
Push μ forward by the measurable finite-valued assignment Z. Every real
function on that finite space is integrable. Apply integral_map and
integral_fintype, then remove zero-mass assignments from the sum. This is
change of variables, with no assumption about the score law. Expected proof:
about 40--70 lines. -/
def T2_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → TreatmentVector N), Measurable Z →
  ∀ f : TreatmentVector N → ℝ,
    Integrable (fun ω => f (Z ω)) μ ∧
    (∫ ω, f (Z ω) ∂μ) = expectation (assignmentLaw μ Z) f

/-- Uniform positive full-score atom masses force finite positive-atom
support, even before assuming discreteness. Apply
Measure.finite_const_le_meas_of_disjoint_iUnion to the measurable events
{X=x}, with ε=ofReal(1/k). They are pairwise disjoint, their union has finite
measure, and every positive atom has this positive mass. Expected proof:
about 30--60 lines; derive finiteness instead of assuming it. -/
def T6_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ), Measurable X →
  ∀ k : ℕ, 0 < k →
  (∀ x, 0 < eventProbability μ (fun ω => X ω = x) →
    eventProbability μ (fun ω => X ω = x) = 1 / (k : ℝ)) →
  Set.Finite {x : Fin N → ℝ | 0 < eventProbability μ (fun ω => X ω = x)}

/-- Realize a discrete score law once its finite positive-atom set H has been
derived. Give x its actual atom probability. Positivity is immediate. For
normalization and event transfer use sum_measureReal_preimage_singleton on H
and on its event filter; the discreteness premise makes the corresponding
finite union equal to the original event almost surely. P may be arbitrary:
outside this finite support its preimage is contained in a null set. Expected
proof: about 50--90 lines. -/
def T6_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ), Measurable X →
  ∀ H : Finset (Fin N → ℝ),
  (∀ x, x ∈ H ↔ 0 < eventProbability μ (fun ω => X ω = x)) →
  DiscreteScoreLaw μ X →
  let A : FiniteDistribution (Fin N → ℝ) :=
    ⟨H, fun x => eventProbability μ (fun ω => X ω = x)⟩
  IsDistribution A ∧
  (∀ P : (Fin N → ℝ) → Prop,
    probability A P = eventProbability μ (fun ω => P (X ω)))

/-- Glue the two assignment-law transfers to the existing complete finite
calculation. The remaining conditional-mean step is the integral of an
indicator over its event, followed by division by the positive arm mass. -/
theorem assignment_calculation (h1 : T2_L1.{u}) (h2 : T2_L2.{u}) :
    T2AssignmentWholePart.{u} := by
  classical
  intro Ω mΩ N μ hμ Z hZ S y m hm hmn hc hp
  let L := assignmentLaw μ Z
  obtain ⟨hL, hprob, hae⟩ := h1 μ Z hZ
  have hc' : ∀ z ∈ L.atoms, armSize S z true = m :=
    (hae (fun z => armSize S z true = m)).mp hc
  have hp' : ∀ i ∈ S, armProbability L i true = (m : ℝ) / S.card := by
    intro i hi
    calc
      _ = probability L (fun z => z i = true) :=
        AronowAudit.P014.armMass_as_prob (Bridge.toAudit L hL) i true
      _ = _ := (hprob _).trans (hp i hi)
  obtain ⟨hpos, harm, hfalse, hfixed, hmom, hspec, hlin, hcancel, hmain, hbracket⟩ :=
    Bridge.T2_proof L hL S y m hm hmn hc' hp'
  have hE := h2 μ Z hZ (differenceOfMeans S y)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hnm' : (0 : ℝ) < (S.card : ℝ) - m := by
    exact sub_pos.mpr (by exact_mod_cast hmn)
  have hpoint : ∀ z ∈ L.atoms,
      armSize S z true = m ∧ armSize S z false = (S.card : ℝ) - m ∧
      0 < armSize S z true ∧ 0 < armSize S z false ∧
      differenceOfMeans S y z = observedArmTotal S y z true / m -
        observedArmTotal S y z false / ((S.card : ℝ) - m) := by
    intro z hz
    obtain ⟨hf, he⟩ := hfixed z hz
    exact ⟨hc' z hz, hf, (hc' z hz).symm ▸ hm', hf.symm ▸ hnm', he⟩
  refine ⟨hL, hpos, ?_, ?_, hpoint, (hae _).mpr hpoint, ?_, hspec,
    hE.1, hE.2, hE.2.trans hlin, hE.2.trans hcancel, hE.2.trans hmain, hbracket⟩
  · intro i hi a
    have hpa : armProbability L i a = eventProbability μ (fun ω => Z ω i = a) :=
      (harm i hi a).trans (hprob _)
    have hset : (∫ ω in {ω | Z ω i = a}, y i (Z ω) ∂μ) = armMoment L y i a := by
      have hmeas : MeasurableSet {ω | Z ω i = a} :=
        measurableSet_eq_fun ((measurable_pi_apply i).comp hZ) measurable_const
      rw [← integral_indicator hmeas]
      simpa only [Set.indicator, Set.mem_ofPred_eq] using
        (h2 μ Z hZ (fun z => if z i = a then y i z else 0)).2.trans (hmom i hi a).1
    refine ⟨hpa, ?_, (h2 μ Z hZ (y i)).1,
      (h2 μ Z hZ (fun z => if z i = a then y i z else 0)).1⟩
    unfold conditionalAverage eventConditionalMean
    rw [hset, hpa]
  · intro i hi
    exact ⟨hp' i hi, hfalse i hi⟩
  · intro i hi a
    exact ⟨(h2 μ Z hZ (fun z => if z i = a then y i z else 0)).2.trans
      (hmom i hi a).1, (hmom i hi a).2⟩

theorem T2_assembly (h1 : T2_L1.{u}) (h2 : T2_L2.{u}) : T2WholeStatement.{u} := by
  classical
  have hassign : T2AssignmentWholePart.{u} := assignment_calculation h1 h2
  refine ⟨hassign, ?_⟩
  intro Ω mΩ N μ hμ X b S v m hb hv hw hm hmn hdef hl
  have hn : 2 ≤ S.card := by omega
  have hlocal := (Bridge.T6_general μ X b S v m hb hn hv hw hm hmn hdef hl).1
  have hc : ∀ᵐ ω ∂μ, armSize S (thresholdAssignment (X ω)) true = m := by
    filter_upwards [hlocal.1] with ω hω using hω.1
  have hp : ∀ i ∈ S,
      eventProbability μ (fun ω => thresholdAssignment (X ω) i = true) =
        (m : ℝ) / S.card := by
    intro i hi
    exact (hlocal.2.1 ⟨i, hi⟩).2.1
  have hZ : Measurable (fun ω => thresholdAssignment (X ω)) := by
    apply Measurable.of_eval
    intro i
    apply measurable_to_bool
    convert measurableSet_le (measurable_const (a := (0 : ℝ))) (hl.1 i) using 1
    ext ω
    simp only [thresholdAssignment, Set.mem_preimage, Set.mem_singleton_iff,
      decide_eq_true_eq, Set.mem_ofPred_eq]
  exact ⟨hc, hp, fun y => hassign μ _ hZ S y m hm hmn hc hp⟩

/-- A direct use of the donor's uniform finite event partition. -/
theorem local_arrangements_cover {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ)
    (hv : Function.Injective v) (hl : CorrectedLocalConditions μ X b S v) :
    ∀ᵐ ω ∂μ, ∃ σ : Equiv.Perm S, ∀ i : S, X ω i = v (σ i) := by
  classical
  let E : Equiv.Perm S → Set Ω := fun σ => {ω | ∀ i : S, X ω i = v (σ i)}
  have hmeas : ∀ σ, MeasurableSet (E σ) := by
    intro σ
    simpa only [E, Set.ofPred_forall] using MeasurableSet.iInter (fun i : S =>
      measurableSet_eq_fun (hl.1 i) (measurable_const (a := v (σ i))))
  have hdisj : Pairwise (fun σ τ => Disjoint (E σ) (E τ)) := by
    intro σ τ hne
    apply Set.disjoint_left.mpr
    intro ω hσ hτ
    apply hne
    apply Equiv.ext
    intro i
    exact hv ((hσ i).symm.trans (hτ i))
  apply AronowAudit.P014.uniform_partition_covers μ E hmeas hdisj
  intro σ
  simpa only [E, Fintype.card_perm, Fintype.card_coe, eventProbability,
    MeasureTheory.measureReal_def] using hl.2.2 σ

/-- The finite-fiber counting and reconstruction are existing project
theorems. Only obtaining the actual finite score law uses the two new leaves. -/
theorem printed_forward (h1 : T6_L1.{u}) (h2 : T6_L2.{u}) :
    T6PrintedForwardPart.{u} := by
  classical
  intro Ω mΩ N μ hμ X b S v m _hb _hn hv _hw _hm _hmn _hdef hl hd hmass
  have hX : Measurable X := Measurable.of_eval hl.1
  have hfin := h1 μ X hX S.card.factorial (Nat.factorial_pos _) hmass
  let H : Finset (Fin N → ℝ) := hfin.toFinset
  have hH : ∀ x, x ∈ H ↔ 0 < eventProbability μ (fun ω => X ω = x) := by
    intro x
    exact hfin.mem_toFinset
  let A : FiniteDistribution (Fin N → ℝ) :=
    ⟨H, fun x => eventProbability μ (fun ω => X ω = x)⟩
  obtain ⟨hA, hprob⟩ := h2 μ X hX H hH hd
  have hcover := local_arrangements_cover μ X b S v hv hl
  have hon : ∀ x ∈ H, ∃ σ : Equiv.Perm S, ∀ i : S, x i = v (σ i) := by
    intro x hx
    by_contra hno
    have hnot : ∀ᵐ ω ∂μ, ¬ X ω = x := by
      filter_upwards [hcover] with ω hω
      obtain ⟨σ, hσ⟩ := hω
      intro he
      exact hno ⟨σ, he ▸ hσ⟩
    have hz : μ {ω | X ω = x} = 0 := by simpa using ae_iff.mp hnot
    have hpos := (hH x).mp hx
    simp only [eventProbability, hz, ENNReal.toReal_zero, lt_self_iff_false] at hpos
  let f : (Fin N → ℝ) → S → ℝ := fun x i => x i
  have hlocal : ∀ a : S → ℝ, (∃ x ∈ H, f x = a) →
      probability A (fun x => f x = a) = 1 / (S.card.factorial : ℝ) := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := ha
    obtain ⟨σ, hσ⟩ := hon x hx
    have he : a = fun i : S => v (σ i) := hxa.symm.trans (funext hσ)
    rw [he]
    have heq : (fun x => f x = fun i : S => v (σ i)) =
        (fun x => ∀ i : S, x i = v (σ i)) := by
      funext x
      exact propext funext_iff
    rw [heq]
    exact (hprob (fun x => ∀ i : S, x i = v (σ i))).trans (hl.2.2 σ)
  have hfull : ∀ x ∈ A.atoms, A.weight x = 1 / (S.card.factorial : ℝ) := by
    intro x hx
    exact hmass x ((hH x).mp hx)
  have hinj : Set.InjOn f (H : Set (Fin N → ℝ)) :=
    (AronowAudit.P014.uniform_joint_iff_injective_local
      (Bridge.toAudit A hA) f S.card.factorial (Nat.factorial_pos _) hlocal).mp hfull
  have hcard : H.card = S.card.factorial :=
    AronowAudit.P014.uniform_finite_support_card (Bridge.toAudit A hA)
      S.card.factorial (Nat.factorial_pos _) hfull
  obtain ⟨g, hg⟩ := (AronowAudit.P014.injective_local_iff_reconstructible
    (Bridge.toAudit A hA) f).mp hinj
  refine ⟨H, hH, hcard, ?_, g, ?_⟩
  · intro σ
    have hpn : probability A (fun x => ∀ i : S, x i = v (σ i)) ≠ 0 := by
      rw [hprob, hl.2.2 σ]
      exact one_div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero S.card)
    have hex : ∃ x, x ∈ H ∧ ∀ i : S, x i = v (σ i) := by
      by_contra hno
      apply hpn
      unfold probability
      apply Finset.sum_eq_zero
      intro x hx
      exact ite_eq_right (fun he => hno ⟨x, hx, he⟩)
    obtain ⟨x, hx, hσ⟩ := hex
    refine ⟨x, ⟨hx, hσ⟩, ?_⟩
    intro x' hx'
    exact hinj hx'.1 hx (funext (fun i => (hx'.2 i).trans (hσ i).symm))
  · filter_upwards [hd] with ω hω
    have hx : X ω ∈ H := (hH (X ω)).mpr hω
    intro j _hj
    exact (congrFun (hg (X ω) hx) j).symm

theorem T6_assembly (h1 : T6_L1.{u}) (h2 : T6_L2.{u}) : T6WholeStatement.{u} :=
  ⟨Bridge.T6_general, printed_forward h1 h2, Bridge.T6_example⟩

end
end SAP.P014.WH.W1
