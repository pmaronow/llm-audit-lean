import AronowAudit.P011.Wave1.Gap.GLP011B3
import Mathlib.Data.Nat.Size

namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

def t13FeasibleTest {n : ℕ} (P : DegreeProblem n) : Bool :=
  (List.finRange n).all (fun i =>
    decide (edgeDegree P.forced i ≤ min (P.cap i) (n - 1)))

def t13InputBits {n : ℕ} (P : DegreeProblem n) : ℕ :=
  (encodeDegreeInput (⟨n, P⟩ : DegreeInput)).length

def t13Maximum {n : ℕ} (P : DegreeProblem n)
    (J : Finset (GadgetEdge P)) : Prop :=
  IsMatching J ∧
    ∀ K : Finset (GadgetEdge P), IsMatching K →
      (∑ g ∈ K, gadgetWeight g) ≤ ∑ g ∈ J, gadgetWeight g

abbrev T13MatchingOracle :=
  (I : DegreeInput) → Finset (GadgetEdge I.2)

def t13Solve (a : T13MatchingOracle) :
    (I : DegreeInput) → Option (Finset (Edge I.1)) :=
  fun I =>
    if t13FeasibleTest I.2 = true then
      some (I.2.forced ∪ decodeMatching I.2 (a I))
    else none

private lemma t13_finite_edges {n : ℕ} (P : DegreeProblem n) :
    Finite (GadgetEdge P) :=
  Finite.of_equiv _ (gadgetEdgeEquiv P).symm

private lemma t13_no_loops {n : ℕ} {P : DegreeProblem n} (g : GadgetEdge P) :
    (gadgetEnds g).1 ≠ (gadgetEnds g).2 := by
  cases g <;> simp [gadgetEnds]

private lemma t13_unique_edges {n : ℕ} {P : DegreeProblem n} (g h : GadgetEdge P)
    (he : gadgetEnds g = gadgetEnds h ∨
      gadgetEnds g = ((gadgetEnds h).2, (gadgetEnds h).1)) : g = h := by
  cases g with
  | internal e =>
    cases h with
    | internal f => simpa [gadgetEnds] using he
    | external f side slot => simp [gadgetEnds] at he
  | external e side slot =>
    cases h with
    | internal f => simp [gadgetEnds] at he
    | external f side' slot' =>
      rcases he with he | he
      · have hp := congrArg Prod.fst he
        have hs := congrArg Prod.snd he
        simp only [gadgetEnds, Sum.inr.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        cases hs
        rfl
      · simp [gadgetEnds] at he

private lemma t13_empty_edges (S : Finset (Edge 0)) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e _
  exact Fin.elim0 e.val.1

private lemma t13_test_iff {n : ℕ} (P : DegreeProblem n) :
    t13FeasibleTest P = true ↔
      ∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n - 1) := by
  simp [t13FeasibleTest, List.all_eq_true]

private lemma t13_feasibility {n : ℕ} (P : DegreeProblem n) :
    t13FeasibleTest P = true ↔ ∃ S, EdgeFeasible P S := by
  rw [t13_test_iff]
  by_cases hn : 0 < n
  · exact (matching_reduction_proof hn P).1.symm
  · have hn : n = 0 := by omega
    subst n
    constructor
    · intro _
      exact ⟨P.forced, Finset.Subset.refl _, fun i => Fin.elim0 i⟩
    · intro _ i
      exact Fin.elim0 i

private lemma t13_L_pos {n : ℕ} (P : DegreeProblem n) : 0 < denominatorLCM P := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun e _ => (P.weight e).den_nz)

private lemma t13_M_pos {n : ℕ} (P : DegreeProblem n) : 0 < gadgetM P := by
  unfold gadgetM
  positivity

private lemma t13_integer_cast {n : ℕ} (P : DegreeProblem n) (e : Edge n)
    (he : e ∈ optionalEdges P) :
    (integerWeight P e : ℚ) = (denominatorLCM P : ℚ) * P.weight e := by
  have hd : (P.weight e).den ∣ denominatorLCM P := Finset.dvd_lcm he
  have hd' : ((P.weight e).den : ℤ) ∣ (denominatorLCM P : ℤ) :=
    Int.natCast_dvd_natCast.mpr hd
  rw [integerWeight, Rat.intCast_div _ _ (dvd_mul_of_dvd_left hd' _), Int.cast_mul,
    Int.cast_natCast, Int.cast_natCast, mul_div_assoc, Rat.num_div_den]


private lemma t13_maximum_exists {n : ℕ} (P : DegreeProblem n) :
    ∃ J : Finset (GadgetEdge P), t13Maximum P J := by
  let : Finite (GadgetEdge P) := t13_finite_edges P
  let := Fintype.ofFinite (GadgetEdge P)
  let s : Finset (Finset (GadgetEdge P)) := Finset.univ.filter IsMatching
  have hs : s.Nonempty := ⟨∅, by simp [s, IsMatching]⟩
  obtain ⟨J, hJ, hmax⟩ := s.exists_max_image (fun J => ∑ g ∈ J, gadgetWeight g) hs
  exact ⟨J, (Finset.mem_filter.mp hJ).2, fun K hK =>
    hmax K (by simp [s, hK])⟩

private lemma t13_nat_length (m : ℕ) :
    (encodeNatBits m).length = 2 * m.bits.length + 1 := by
  simp [encodeNatBits]
  omega

private lemma t13_rat_length (q : ℚ) :
    (encodeRatBits q).length =
      3 + 2 * q.num.natAbs.bits.length + 2 * q.den.bits.length := by
  simp [encodeRatBits, encodeIntBits, encodeNatBits]
  omega

private lemma t13_input_length {n : ℕ} (P : DegreeProblem n) :
    t13InputBits P =
      2 * n.bits.length + 1 +
      (∑ i, (2 * (P.cap i).bits.length + 1)) +
      ((edgeList n).map (fun e =>
        4 + 2 * (P.weight e).num.natAbs.bits.length +
          2 * (P.weight e).den.bits.length)).sum := by
  have he (e : Edge n) :
      ([decide (e ∈ P.forced)] ++ encodeRatBits (P.weight e)).length =
        4 + 2 * (P.weight e).num.natAbs.bits.length +
          2 * (P.weight e).den.bits.length := by
    simp only [List.length_append, List.length_singleton, t13_rat_length]
    omega
  simp only [t13InputBits, encodeDegreeInput, List.length_append, List.length_flatten,
    List.map_map, List.map_ofFn, Function.comp_def, he, t13_nat_length, List.sum_ofFn]

private lemma t13_mem_edgeList {n : ℕ} (e : Edge n) : e ∈ edgeList n := by
  rcases e with ⟨⟨i,j⟩,h⟩
  simp [edgeList, List.mem_flatMap, h]

private lemma t13_den_budget {n : ℕ} (P : DegreeProblem n) :
    ((edgeList n).map (fun e => (P.weight e).den.bits.length)).sum ≤ t13InputBits P := by
  have h := List.sum_le_sum (l := edgeList n)
    (f := fun e => (P.weight e).den.bits.length)
    (g := fun e => 4 + 2 * (P.weight e).num.natAbs.bits.length +
      2 * (P.weight e).den.bits.length) (fun e _ => by omega)
  rw [t13_input_length]
  omega

private lemma t13_num_budget {n : ℕ} (P : DegreeProblem n) (e : Edge n) :
    (P.weight e).num.natAbs.bits.length ≤ t13InputBits P := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨e, t13_mem_edgeList e, rfl⟩ :
    4 + 2 * (P.weight e).num.natAbs.bits.length + 2 * (P.weight e).den.bits.length ∈
      (edgeList n).map (fun e => 4 + 2 * (P.weight e).num.natAbs.bits.length +
        2 * (P.weight e).den.bits.length))
  rw [t13_input_length]
  omega

private lemma t13_product_pow {α : Type*} (l : List α) (f : α → ℕ) :
    (l.map f).prod ≤ 2 ^ (l.map (fun a => (f a).bits.length)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    exact Nat.mul_le_mul
      (Nat.le_of_lt (by simpa [Nat.size_eq_bits_len] using Nat.lt_size_self (f a))) ih

private lemma t13_L_bound {n : ℕ} (P : DegreeProblem n) :
    denominatorLCM P ≤ 2 ^ t13InputBits P := by
  have hd : denominatorLCM P ∣ ((edgeList n).map (fun e => (P.weight e).den)).prod := by
    apply Finset.lcm_dvd
    intro e _
    exact List.dvd_prod (List.mem_map.mpr ⟨e, t13_mem_edgeList e, rfl⟩)
  have hp : 0 < ((edgeList n).map (fun e => (P.weight e).den)).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
    exact (P.weight e).den_pos
  exact (Nat.le_of_dvd hp hd).trans ((t13_product_pow _ _).trans
    (Nat.pow_le_pow_right (by decide) (t13_den_budget P)))


private lemma t13_W_bound {n : ℕ} (P : DegreeProblem n) (e : Edge n) :
    (integerWeight P e).natAbs < 2 ^ (2 * t13InputBits P) := by
  have hn : (P.weight e).num.natAbs < 2 ^ t13InputBits P := by
    rw [← Nat.size_le, ← Nat.size_eq_bits_len]
    exact t13_num_budget P e
  calc
    (integerWeight P e).natAbs ≤ denominatorLCM P * (P.weight e).num.natAbs := by
      simpa [integerWeight, Int.natAbs_mul] using
        Int.natAbs_ediv_le_natAbs ((denominatorLCM P : ℤ) * (P.weight e).num)
          ((P.weight e).den : ℤ)
    _ ≤ 2 ^ t13InputBits P * (P.weight e).num.natAbs :=
      Nat.mul_le_mul_right _ (t13_L_bound P)
    _ < 2 ^ t13InputBits P * 2 ^ t13InputBits P :=
      Nat.mul_lt_mul_of_pos_left hn (by positivity)
    _ = 2 ^ (2 * t13InputBits P) := by rw [← pow_add]; congr 1; omega

private lemma t13_M_abs {n : ℕ} (P : DegreeProblem n) :
    (gadgetM P).natAbs =
      1 + (optionalEdges P).sup (fun e => (integerWeight P e).natAbs) := by
  unfold gadgetM
  norm_cast

private lemma t13_M_bound {n : ℕ} (P : DegreeProblem n) :
    (gadgetM P).natAbs ≤ 2 ^ (2 * t13InputBits P) := by
  rw [t13_M_abs]
  have hs : (optionalEdges P).sup (fun e => (integerWeight P e).natAbs) <
      2 ^ (2 * t13InputBits P) := (Finset.sup_lt_iff (show (0 : ℕ) < 2 ^ (2 * t13InputBits P) by
    positivity)).mpr (fun e _ => t13_W_bound P e)
  omega

private lemma t13_gadget_bound {n : ℕ} {P : DegreeProblem n} (g : GadgetEdge P) :
    (gadgetWeight g).natAbs ≤ 2 ^ (2 * t13InputBits P + 2) := by
  have hm := t13_M_bound P
  cases g with
  | internal e =>
    simp only [gadgetWeight, Int.natAbs_mul]
    norm_num
    rw [pow_add]
    norm_num
    omega
  | external e side slot =>
    have hw := t13_W_bound P e.val
    have ha := Int.natAbs_add_le (2 * gadgetM P) (integerWeight P e.val)
    norm_num [Int.natAbs_mul] at ha
    change (2 * gadgetM P + integerWeight P e.val).natAbs ≤ _
    rw [pow_add]
    norm_num
    omega

private lemma t13_bits_of_le_pow {x k : ℕ} (h : x ≤ 2 ^ k) :
    x.bits.length ≤ k + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

private lemma t13_bit_bounds {n : ℕ} (P : DegreeProblem n) :
    (denominatorLCM P).bits.length ≤ t13InputBits P + 1 ∧
    (∀ e ∈ optionalEdges P,
      (integerWeight P e).natAbs.bits.length ≤ 2 * t13InputBits P + 1) ∧
    (gadgetM P).natAbs.bits.length ≤ 2 * t13InputBits P + 2 ∧
    (∀ g : GadgetEdge P,
      (gadgetWeight g).natAbs.bits.length ≤ 2 * t13InputBits P + 4) := by
  refine ⟨t13_bits_of_le_pow (t13_L_bound P),
    fun e _ => t13_bits_of_le_pow (t13_W_bound P e).le, ?_, ?_⟩
  · have h := t13_bits_of_le_pow (t13_M_bound P)
    omega
  · intro g
    have h := t13_bits_of_le_pow (t13_gadget_bound g)
    omega

private lemma t13_empty_gadget (P : DegreeProblem 0) (J : Finset (GadgetEdge P)) :
    J = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g _
  cases g with
  | internal e => exact Fin.elim0 e.val.val.1
  | external e side slot => exact Fin.elim0 e.val.val.1

private lemma t13_decodes {n : ℕ} (P : DegreeProblem n) (ht : t13FeasibleTest P = true) :
    (∀ S : Finset (Edge n),
      EdgeFeasible P S ↔
        ∃ T : Finset (Edge n), T ⊆ optionalEdges P ∧
          (∀ i, edgeDegree T i ≤ remainingCap P i) ∧
          S = P.forced ∪ T) ∧
    (∀ J : Finset (GadgetEdge P), t13Maximum P J →
      EdgeFeasible P (P.forced ∪ decodeMatching P J) ∧
      (∀ S : Finset (Edge n), EdgeFeasible P S →
        edgeObjective P S ≤ edgeObjective P (P.forced ∪ decodeMatching P J)) ∧
      edgeObjective P (P.forced ∪ decodeMatching P J) =
        edgeObjective P P.forced +
          ((∑ e ∈ J, gadgetWeight e : ℤ) -
            4 * gadgetM P * (optionalEdges P).card : ℚ) /
            (2 * (denominatorLCM P : ℚ))) := by
  by_cases hn : 0 < n
  · have h := (matching_reduction_proof hn P).2.1 ((t13_test_iff P).mp ht)
    exact ⟨h.1, fun J hJ => h.2 J hJ.1 hJ.2⟩
  · have hn : n = 0 := by omega
    subst n
    constructor
    · intro S
      simp [t13_empty_edges, EdgeFeasible, optionalEdges]
    · intro J _
      rw [t13_empty_gadget P J]
      simp [t13_empty_edges, EdgeFeasible, optionalEdges, decodeMatching, edgeObjective]

private lemma t13_size_bounds {n : ℕ} (P : DegreeProblem n) :
    Nat.card (GadgetVertex P) ≤ 2 * n * (n - 1) ∧
    Nat.card (GadgetEdge P) ≤ (optionalEdges P).card * (2 * n - 1) ∧
    Nat.card (GadgetEdge P) ≤ 2 * n ^ 3 := by
  have hc := matching_gadget_exact_counts P
  have hv : Nat.card (GadgetVertex P) ≤ 2 * n * (n - 1) := by
    rw [hc.1]
    by_cases hn : 0 < n
    · exact (matching_reduction_proof hn P).2.2.1
    · have hn : n = 0 := by omega
      subst n
      simp [t13_empty_edges]
  have he : Nat.card (GadgetEdge P) ≤ (optionalEdges P).card * (2 * n - 1) := by
    rw [hc.2]
    by_cases hn : 0 < n
    · exact (matching_reduction_proof hn P).2.2.2
    · have hn : n = 0 := by omega
      subst n
      simp [t13_empty_edges]
  refine ⟨hv, he, he.trans ?_⟩
  have hq : (optionalEdges P).card ≤ n * n := by
    have hq : (optionalEdges P).card ≤ n * (n - 1) / 2 := by
      simpa [UpperCompletion.edge_card] using (optionalEdges P).card_le_univ
    exact hq.trans ((Nat.div_le_self _ _).trans
      (Nat.mul_le_mul_left n (Nat.sub_le n 1)))
  calc
    (optionalEdges P).card * (2 * n - 1) ≤ (n * n) * (2 * n) :=
      Nat.mul_le_mul hq (Nat.sub_le _ _)
    _ = 2 * n ^ 3 := by ring


private lemma t13_solver (a : T13MatchingOracle)
    (ha : ∀ I : DegreeInput, t13Maximum I.2 (a I)) :
    ExactDegreeSolver (t13Solve a) := by
  intro I
  constructor
  · by_cases ht : t13FeasibleTest I.2 = true
    · simp [t13Solve, ht, ← t13_feasibility I.2]
    · simp [t13Solve, ht, ← t13_feasibility I.2]
  · intro S hs
    unfold t13Solve at hs
    split_ifs at hs with ht
    · cases hs
      have hd := (t13_decodes I.2 ht).2 (a I) (ha I)
      exact ⟨hd.1, hd.2.1⟩

/-- Finite correctness and encoded size of the matching reduction.
The polynomial-time interpretation uses the external matching algorithm and
construction/decoding cost analysis; execution costs are outside this statement. -/
theorem corrected_polynomial_size_matching_reduction :
    (∀ (n : ℕ) (P : DegreeProblem n),
      (t13FeasibleTest P = true ↔ ∃ S, EdgeFeasible P S) ∧
      Finite (GadgetVertex P) ∧
      Finite (GadgetEdge P) ∧
      (∀ g : GadgetEdge P, (gadgetEnds g).1 ≠ (gadgetEnds g).2) ∧
      (∀ g h : GadgetEdge P,
        (gadgetEnds g = gadgetEnds h ∨
          gadgetEnds g = ((gadgetEnds h).2, (gadgetEnds h).1)) → g = h) ∧
      (Nat.card (GadgetVertex P) =
        2 * (optionalEdges P).card + ∑ i, remainingCap P i) ∧
      (Nat.card (GadgetEdge P) =
        (optionalEdges P).card +
          ∑ e ∈ optionalEdges P,
            (remainingCap P e.val.1 + remainingCap P e.val.2)) ∧
      (Nat.card (GadgetVertex P) ≤ 2 * n * (n - 1)) ∧
      (Nat.card (GadgetEdge P) ≤ (optionalEdges P).card * (2 * n - 1)) ∧
      (Nat.card (GadgetEdge P) ≤ 2 * n ^ 3) ∧
      (0 < denominatorLCM P) ∧
      (0 < gadgetM P) ∧
      (∀ e ∈ optionalEdges P,
        (integerWeight P e : ℚ) = (denominatorLCM P : ℚ) * P.weight e) ∧
      ((denominatorLCM P).bits.length ≤ t13InputBits P + 1) ∧
      (∀ e ∈ optionalEdges P,
        (integerWeight P e).natAbs.bits.length ≤ 2 * t13InputBits P + 1) ∧
      ((gadgetM P).natAbs.bits.length ≤ 2 * t13InputBits P + 2) ∧
      (∀ g : GadgetEdge P,
        (gadgetWeight g).natAbs.bits.length ≤ 2 * t13InputBits P + 4) ∧
      (∃ J : Finset (GadgetEdge P), t13Maximum P J) ∧
      (t13FeasibleTest P = true →
        (∀ S : Finset (Edge n),
          EdgeFeasible P S ↔
            ∃ T : Finset (Edge n), T ⊆ optionalEdges P ∧
              (∀ i, edgeDegree T i ≤ remainingCap P i) ∧
              S = P.forced ∪ T) ∧
        (∀ J : Finset (GadgetEdge P), t13Maximum P J →
          EdgeFeasible P (P.forced ∪ decodeMatching P J) ∧
          (∀ S : Finset (Edge n), EdgeFeasible P S →
            edgeObjective P S ≤
              edgeObjective P (P.forced ∪ decodeMatching P J)) ∧
          edgeObjective P (P.forced ∪ decodeMatching P J) =
            edgeObjective P P.forced +
              ((∑ e ∈ J, gadgetWeight e : ℤ) -
                4 * gadgetM P * (optionalEdges P).card : ℚ) /
                (2 * (denominatorLCM P : ℚ))))) ∧
    (∀ a : T13MatchingOracle,
      (∀ I : DegreeInput, t13Maximum I.2 (a I)) →
        ExactDegreeSolver (t13Solve a)) := by
  constructor
  · intro n P
    have hc := matching_gadget_exact_counts P
    have hb := t13_size_bounds P
    have hw := t13_bit_bounds P
    exact ⟨t13_feasibility P, inferInstance, t13_finite_edges P,
      t13_no_loops, fun g h he => t13_unique_edges g h he,
      hc.1, hc.2, hb.1, hb.2.1, hb.2.2,
      t13_L_pos P, t13_M_pos P, t13_integer_cast P,
      hw.1, hw.2.1, hw.2.2.1, hw.2.2.2,
      t13_maximum_exists P, t13_decodes P⟩
  · exact t13_solver

end
end AronowAudit.P011.Wave1
