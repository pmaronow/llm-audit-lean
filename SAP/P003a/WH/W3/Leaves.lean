import SAP.P003a.Defs.WholeW3
import SAP.P003a.Bridge
import AronowAudit.P003.Wave1.Gap.GLP0031B1
import AronowAudit.P003.Wave1.Gap.GP0031B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3

open scoped BigOperators
open SAP.P003a.Bridge
attribute [local instance 0] Classical.propDecidable

/-- The seven base-case laws, at every rational value including values off the support.
Enumerate wholeBaseRows, evaluate randomStates and multiplicities (two assignments),
then split on equality to the two displayed atoms and use norm_num. Repeated atoms
give a point mass, not a mass of one half. About 60--120 lines of finite arithmetic. -/
def T15_L1 : Prop :=
  ∀ r ∈ wholeBaseRows, ∀ x : ℚ,
    wholeEstimatorMass r.1 1 x = wholeTwoPointMass r.2.1 r.2.2 x

/-- The four witness laws, at every rational value. Enumerate the four rows and their
randomStates; their weighted assignment counts are 6 or 3+3, with denominator
choose(4,2)=6. Evaluate estimateQ and split on equality to the displayed atoms.
The fourth row is (0,3,0,1), not its six-subject predecessor. About 80--140 lines. -/
def T15_L2 : Prop :=
  ∀ r ∈ wholeWitnessRows, ∀ x : ℚ,
    wholeEstimatorMass r.1 2 x = wholeTwoPointMass r.2.1 r.2.2 x

private theorem sd_from_donor (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hd : 1 ≤ v.b+v.c) :
    IsSD (scaledEstimatorMass v m) := by
  simpa only [to_scaledEstimatorMass, isSD_eq] using
    AronowAudit.P003.Wave1.discordant_estimator_sd_proof (toAudit v) m hm hn hd

private theorem removal_facts (a : Counts)
    (ha : a ∈ wholeRemovals10 ∨ a ∈ wholeRemovals01) :
    a.total = 2 ∧ a.b+a.c ≤ 2 := by
  rcases ha with ha | ha <;>
    simp only [wholeRemovals10, wholeRemovals01, List.mem_cons, List.not_mem_nil,
      or_false] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl <;> decide

/-- The full corrected lemma and proof-case facts, using just the two new finite laws. -/
theorem T15_assembly (h1 : T15_L1) (h2 : T15_L2) : T15WholeStatement := by
  refine ⟨sd_from_donor, ⟨?_,h1⟩, ?_, removal_facts, ?_, ?_, ?_⟩
  · rintro ⟨a,b,c,d⟩ hn hd
    change a+b+c+d = 2 at hn
    change 1 ≤ b+c at hd
    have ha : a ≤ 2 := by omega
    have hb : b ≤ 2 := by omega
    have hc : c ≤ 2 := by omega
    have he : d ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      norm_num [wholeBaseRows] at *
  · intro v m hm hn hd
    exact sd_from_donor v m hm hn (by rcases hd with hd | hd <;> omega)
  · intro v m hm hn hd
    refine ⟨by omega, ?_⟩
    intro a ha hav
    have hf := removal_facts a ha
    rcases hav with ⟨ha,hb,hc,he⟩
    dsimp [Counts.total] at hn
    dsimp [Counts.total] at hf
    have hm' : 1 ≤ m-1 := by omega
    have hu : (wholeCountsSub v a).total = 2*(m-1) := by
      dsimp [wholeCountsSub,Counts.total]
      omega
    have hd' : 1 ≤ (wholeCountsSub v a).b+(wholeCountsSub v a).c := by
      dsimp [wholeCountsSub]
      omega
    exact ⟨hu,hm',by dsimp [wholeCountsSub]; omega,hd',
      sd_from_donor _ _ hm' hu hd'⟩
  · norm_num [wholePrintedInductionCases,wholeCountsLE,wholeCountsSub,Counts.total]
  · intro r hr
    refine ⟨h2 r hr,sd_from_donor r.1 2 (by decide) ?_ ?_⟩ <;>
      simp only [wholeWitnessRows,List.mem_cons,List.not_mem_nil,or_false] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Coordinate and cardinality facts for the partner source. Identify the remaining
labels with Fin(n-2) (erase two distinct labels), then transport size-(m-1) subsets.
Fintype.card_finset_len gives the binomial count; Nat.choose_pos gives nonemptiness.
Choose any partner to get a source point. No denominator or residual positivity is
assumed: m=1 gives one empty residual subset. Estimated proof: 150--250 lines. -/
def T16_L1 : Prop :=
  ∀ (n m : ℕ), 0 < m → n = 2*m → ∀ i : Fin n,
    Nonempty (WholePairSource n m i) ∧
    ∀ j : WholePartner n i,
      Nonempty (Fin (n-2) ≃ WholeRemaining n i j.val) ∧
      Nonempty (WholeResidualAssignment n m i j.val) ∧
      Fintype.card (WholeResidualAssignment n m i j.val) = (n-2).choose (m-1)

/-- The treatment-set sampler is legal, and each legal size-m treatment set has
exactly m source points. For a target z, the orientation is determined by whether
the distinguished label is treated. Its partners are precisely the m labels in
the opposite arm; removing the treated member of the pair determines the residual
subset. Give an explicit fiber equivalence with this opposite arm. Estimated proof:
150--250 lines, using Finset.card_insert_of_notMem, card_sdiff, and card_congr. -/
def T16_L2 : Prop :=
  ∀ (n m : ℕ), 0 < m → n = 2*m → ∀ i : Fin n,
    (∀ ω : WholePairSource n m i, (wholePairSample ω).card = m) ∧
    (∀ z : Assignment n m,
      Fintype.card {ω : WholePairSource n m i // wholePairSample ω = z.val} = m)

/-- Transfer the cardinality facts into the two probability identities. These explicit
premises are discharged by L1 and L2 in the assembly. Sum the constant fibers over
assignments and over an arbitrary event, then cancel m>0. For a rectangle over j,
its event subtype is the product of the two event subtypes; constant residual fiber
size and card(WholePartner)=n-1 normalize the dependent sum. This proves the uniform
partner and conditional independence, without presuming that the sampler is uniform.
Estimated proof: 150--250 lines of finite cardinality and field arithmetic. -/
def T16_L3 : Prop :=
  ∀ (n m : ℕ), 0 < m → n = 2*m → ∀ i : Fin n,
    (∀ j : WholePartner n i,
      Fintype.card (WholeResidualAssignment n m i j.val) = (n-2).choose (m-1)) →
    (∀ ω : WholePairSource n m i, (wholePairSample ω).card = m) →
    (∀ z : Assignment n m,
      Fintype.card {ω : WholePairSource n m i // wholePairSample ω = z.val} = m) →
    (∀ E : Finset (Fin n) → Prop,
      uniformProb (fun ω : WholePairSource n m i => E (wholePairSample ω)) =
        uniformProb (fun z : Assignment n m => E z.val)) ∧
    (∀ (j : WholePartner n i) (E : Bool → Prop)
      (F : WholeResidualAssignment n m i j.val → Prop),
      uniformProb (wholePairRectangle j E F) =
        (1 / ((n-1 : ℕ) : ℝ)) * uniformProb E * uniformProb F)

/-- Split the balanced signed sum into the opposite-arm pair and the remainder.
Erase the two labels using Finset.sum_erase_add. Reindex the remainder with any
equivalence e, proving its treatment count m-1 by the same two-label deletion.
Apply corrected_signed_sum to the restricted table when m>1 and cancel the common
factor. When m=1, n=2 and the remaining-label set is empty, so its sum is zero.
This includes the coordinate form of (B.51) and never divides by m-1 at that boundary.
Estimated proof: 200--300 lines. -/
def T16_L4 : Prop :=
  ∀ (n m : ℕ), 0 < m → n = 2*m →
    ∀ (w : PotentialTable n) (z : Assignment n m) (i : Fin n) (j : WholePartner n i),
    (i ∈ z.val ↔ j.val ∉ z.val) →
    tableEstimator w z.val =
      (pairContribution (w i) (w j.val) (decide (i ∈ z.val)) : ℝ)/(m : ℝ) +
        wholeResidualContribution w z.val m i j.val ∧
    (m = 1 → wholeResidualContribution w z.val m i j.val = 0) ∧
    (∀ e : Fin (n-2) ≃ WholeRemaining n i j.val,
      (wholeRestrictedAssignment z.val e).card = m-1 ∧
      wholeResidualContribution w z.val m i j.val =
        (∑ k : Fin (n-2), wholeSignedTerm (wholeRestrictedTable w e)
          (wholeRestrictedAssignment z.val e) k)/(m : ℝ) ∧
      (1 < m → wholeResidualContribution w z.val m i j.val =
        ((m-1 : ℕ) : ℝ)/(m : ℝ) *
          tableEstimator (wholeRestrictedTable w e) (wholeRestrictedAssignment z.val e)))

private theorem fair_law_of_values (f : Bool → ℤ) (a b : ℤ)
    (ha : f true = a) (hb : f false = b) : WholeFairLaw f a b := by
  intro x
  have hu : (Finset.univ : Finset Bool) = {true,false} := rfl
  unfold uniformProb
  rw [hu]
  simp only [Finset.filter_insert,Finset.filter_singleton,ha,hb,Fintype.card_bool]
  by_cases hax : x = a <;> by_cases hbx : x = b <;> simp_all [eq_comm]
  all_goals norm_num

private theorem pair_laws : WholePairLaws := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    apply fair_law_of_values <;> rfl

/-- The sampler, deterministic decomposition, and actual fair pair laws assemble
the whole correction. No law for an unrelated fixed second subject is substituted. -/
theorem T16_assembly (h1 : T16_L1) (h2 : T16_L2) (h3 : T16_L3) (h4 : T16_L4) :
    T16WholeStatement := by
  refine ⟨?_,?_,h4,pair_laws⟩
  · intro n m hm hn w z
    simpa only [to_tableEstimator,wholeSignedTerm,bit_eq] using
      AronowAudit.P003.corrected_signed_sum w z.val m hm hn z.property
  · intro n m hm hn i
    obtain ⟨hsource,hrem⟩ := h1 n m hm hn i
    obtain ⟨hlegal,hfiber⟩ := h2 n m hm hn i
    obtain ⟨hpush,hprod⟩ := h3 n m hm hn i (fun j => (hrem j).2.2) hlegal hfiber
    exact ⟨hsource,fun j => ⟨(hrem j).1,(hrem j).2.1⟩,hlegal,hpush,hprod⟩

/-- The finite all-zero population's count vector and its observation under each
of the ten labeled assignments. Prove the finite equalities by kernel enumeration,
or use card(z)=2 and card(univ\z)=3. Fintype.card_finset_len gives choose(5,2)=10.
Estimated proof: 30--80 lines; no probability or real arithmetic is needed. -/
def T17_L1 : Prop :=
  Fintype.card (Assignment 5 2) = 10 ∧
  tableCounts wholeZeroTable = ⟨0,0,0,5⟩ ∧
  ∀ z : Assignment 5 2,
    unitObserved (unitOutcomes wholeZeroTable z.val) z.val = ⟨0,2,0,3⟩

/-- The one-(0,1)-subject population: its count vector, four assignments treating
label zero, six not treating it, and both pointwise observation vectors. Enumerate
the ten size-two subsets of Fin 5 with decide +kernel, or count the relevant subsets
as choose(4,1) and choose(4,2). Estimated proof: 40--100 lines. -/
def T17_L2 : Prop :=
  tableCounts wholeOneControlTable = ⟨0,0,1,4⟩ ∧
  (Finset.univ.filter fun z : Assignment 5 2 => (0 : Fin 5) ∈ z.val).card = 4 ∧
  (Finset.univ.filter fun z : Assignment 5 2 => (0 : Fin 5) ∉ z.val).card = 6 ∧
  ∀ z : Assignment 5 2,
    ((0 : Fin 5) ∈ z.val →
      unitObserved (unitOutcomes wholeOneControlTable z.val) z.val = ⟨0,2,0,3⟩) ∧
    ((0 : Fin 5) ∉ z.val →
      unitObserved (unitOutcomes wholeOneControlTable z.val) z.val = ⟨0,2,1,2⟩)

private theorem binary_q (a b : ℕ) (h : 0 < a+b) :
    wholeBinaryQ a b = (a : ℝ)*b/((a : ℝ)+b) := by
  have hp : (0 : ℝ) < (a : ℝ)+b := by exact_mod_cast h
  unfold wholeBinaryQ
  field_simp
  ring

private theorem printed_variance (o : Counts)
    (ht : 0 < o.a+o.b) (hc : 0 < o.c+o.d) :
    wholePrintedVariance o = varianceEstimate o := by
  have htp : (0 : ℝ) < (o.a : ℝ)+o.b := by exact_mod_cast ht
  have hcp : (0 : ℝ) < (o.c : ℝ)+o.d := by exact_mod_cast hc
  unfold wholePrintedVariance varianceEstimate
  rw [binary_q _ _ ht,binary_q _ _ hc]
  field_simp

private theorem studentized_facts (C : ℝ) (o v : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    0 ≤ varianceEstimate o ∧
    (standardError o = 0 ↔ o.a*o.b = 0 ∧ o.c*o.d = 0) ∧
    (standardError o = 0 → studentized C o v = C) ∧
    (0 < standardError o → studentized C o v = (estimate o-tau v)/standardError o) := by
  simpa only [to_varianceEstimate,to_standardError,to_a,to_b,to_c,to_d,
    to_studentized,to_estimate,to_tau] using
    AronowAudit.P003.studentized_extension C (toAudit o) (toAudit v) ho

/-- Q simplification is field algebra; the zero convention and exact tails use
proved donors. Rank validity is applied directly to the fixed labeled table's
absolute score, so its correctness does not depend on canonical labeling. -/
theorem T17_assembly (h1 : T17_L1) (h2 : T17_L2) : T17WholeStatement := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro o ht hc
    have h := studentized_facts 0 o o ⟨ht,hc⟩
    exact ⟨binary_q _ _ ht,binary_q _ _ hc,printed_variance o ht hc,h.1,h.2.1⟩
  · intro C o v ht hc
    have h := studentized_facts C o v ⟨ht,hc⟩
    refine ⟨?_,h.2.2⟩
    simp only [wholePrintedStudentized,printed_variance o ht hc,studentized,standardError]
    rfl
  · intro C K o v samples
    rfl
  · refine ⟨h1.1,h1.2.1,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [tableTau,wholeZeroTable,bit]
    · norm_num [tau,tauQ,Counts.effect,Counts.total]
    · intro z
      exact ⟨h1.2.2 z,by simp [tableEstimator,wholeZeroTable,bit]⟩
    · norm_num [estimate,estimateQ]
    · norm_num [varianceEstimate]
    · norm_num [standardError,varianceEstimate]
    · intro C
      norm_num [studentized,standardError,varianceEstimate]
  · refine ⟨h2.1,?_,?_,h2.2.1,h2.2.2.1,h2.2.2.2,?_,?_,?_,?_⟩
    · norm_num [tableTau,wholeOneControlTable,bit,Fin.sum_univ_succ]
    · norm_num [tau,tauQ,Counts.effect,Counts.total]
    · norm_num [standardError,varianceEstimate]
    · norm_num [estimate,estimateQ,tau,tauQ,Counts.effect,Counts.total]
    · norm_num [estimate,estimateQ]
    · norm_num [varianceEstimate]
  · intro n m K w C α hm hmn hK hα hα1
    have hcard : 0 < Fintype.card (Assignment n m) := by
      rw [Fintype.card_finset_len,Fintype.card_fin]
      exact Nat.choose_pos (by omega)
    have : Nonempty (Assignment n m) := Fintype.card_pos_iff.mp hcard
    let s : Assignment n m → ℝ := fun z =>
      |studentized C (unitObserved (unitOutcomes w z.val) z.val) (tableCounts w)|
    have h := AronowAudit.P003.Wave1.monte_rank_valid_finite_rank K s α hα
    rw [uniformProb_eq] at h
    have he (zs : Fin (K+1) → Assignment n m) :
        wholeObservedRank C
          (unitObserved (unitOutcomes w (zs 0).val) (zs 0).val) (tableCounts w)
          (fun i => unitObserved (unitOutcomes w (zs i.succ).val) (zs i.succ).val) =
        (∑ j : Fin (K+1), if s (zs 0) ≤ s (zs j) then (1 : ℝ) else 0)/(K+1) := by
      unfold wholeObservedRank
      rw [Fin.sum_univ_succ]
      simp only [s,le_refl,ite_true]
    simpa only [he] using h
  · simpa only [decode_designProb,decode_studentized,decode_observed,from_to,decode_mk] using
      AronowAudit.P003.extension_changes_test

end SAP.P003a.WH.W3
