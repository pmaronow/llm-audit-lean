import SAP.P012a.Defs.WholeW2
import SAP.P012a.Bridge
import AronowAudit.P012.P012_Identification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W2

open SAP.P012a Finset
open scoped Classical
noncomputable section

/-- Compatibility makes corrected cleanup the identity, including at isolated
sampled seeds. This proves the unchanged branch directly. -/
theorem cleanup_identity (D : Data) (H : State) (hH : Compatible D H) :
    cleanup D true H = H := by
  have hv : H.vertices.filter (fun v =>
      (true = true ∧ v ∈ sampledVertices D) ∨ graphDegree H v ≠ 0) = H.vertices := by
    apply filter_eq_self.mpr
    intro v hv
    by_cases hs : v ∈ sampledVertices D
    · exact Or.inl ⟨rfl, hs⟩
    · obtain ⟨i, hi, he⟩ := hH.2.2.2.2.1 v hv hs
      exact Or.inr (Nat.ne_of_gt (card_pos.mpr
        ⟨{s i, v}, mem_filter.mpr ⟨he, by simp⟩⟩))
  unfold cleanup
  rw [hv]

/-- The project private-leaf incidence theorem identifies the entire incident
edge filter as a singleton; compatibility supplies each sampled degree. -/
theorem leaf_structure (D : Data) (hD : Admissible D) (same : Bool) :
    W2LeafStructure D same := by
  have hH : Compatible D (leafCompletion D same) :=
    AronowAudit.P012.leafCompletion_compatible (Bridge.data D) hD same
  constructor
  · intro i hi k hk
    have hm : u i k ∈ unsampled D (leafCompletion D same) ∧
        ∀ j ∈ D.sampled, {s j, u i k} ∈ (leafCompletion D same).edges ↔ j = i :=
      AronowAudit.P012.private_leaf_member (Bridge.data D) hD same i k hi hk
    have hinc : ∀ e ∈ (leafCompletion D same).edges,
        u i k ∈ e → e = {s i, u i k} := by
      intro e he hv
      exact AronowAudit.P012.private_edge_incidence (Bridge.data D)
        (Bridge.state (leafCompletion D same)) hH i hi (u i k) hm.1 hm.2 e he hv
    have hf : (leafCompletion D same).edges.filter (fun e => u i k ∈ e) =
        {{s i, u i k}} := by
      ext e
      constructor
      · intro he
        exact mem_singleton.mpr (hinc e (mem_filter.mp he).1 (mem_filter.mp he).2)
      · intro he
        have heq := mem_singleton.mp he
        subst e
        exact mem_filter.mpr ⟨(hm.2 i hi).2 rfl, by simp⟩
    refine ⟨hm.1, ?_, hinc, ?_⟩
    · simp only [graphDegree, hf, card_singleton]
    · rfl
  · intro i hi
    have hbudget : recruitmentDegree D i + spare D i = D.degree i :=
      Nat.add_sub_of_le (hD.2.2.2 i hi)
    exact ⟨(hH.2.2.2.2.2 i hi).trans hbudget.symm, hbudget⟩

/-- The instrumentation follows the actual tail recursion. Each step has one
addition to a sufficient statistic; instrumentation itself is not charged. -/
theorem vertex_scan_cost (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanVertices D xs q).visits = q.visits + xs.length ∧
    (w2ScanVertices D xs q).additions = q.additions + xs.length := by
  induction xs generalizing q with
  | nil => simp [w2ScanVertices]
  | cons i xs ih =>
    have h := ih (w2VertexStep D i q)
    cases ht : D.trait i <;>
      simpa [w2ScanVertices, w2VertexStep, ht, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

/-- Edge records have the same visit/addition cost for each of the four binary
trait patterns. -/
theorem edge_scan_cost (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanEdges D xs q).visits = q.visits + xs.length ∧
    (w2ScanEdges D xs q).additions = q.additions + xs.length := by
  induction xs generalizing q with
  | nil => simp [w2ScanEdges]
  | cons j xs ih =>
    have h := ih (w2EdgeStep D j q)
    cases hp : D.trait (D.parent j) <;> cases ht : D.trait j <;>
      simpa [w2ScanEdges, w2EdgeStep, hp, ht, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

/-- Combining the two streaming recursions needs no graph-theoretic premise. -/
theorem scan_cost (D : Data) (xs ys : List ℕ) :
    (w2Scan D xs ys).visits = xs.length + ys.length ∧
    (w2Scan D xs ys).additions = xs.length + ys.length := by
  have hv := vertex_scan_cost D xs {}
  have he := edge_scan_cost D ys (w2ScanVertices D xs {})
  simpa only [w2Scan, hv.1, hv.2, Nat.zero_add] using he

/-- Exact rational arithmetic commutes with the real interpretation. The two
budget equalities explicitly justify the natural subtractions. -/
theorem finish_cast (q : W2HCounts) (S0 S1 : ℕ)
    (h0 : q.d0 = 2*q.zeros + q.mixed + S0)
    (h1 : q.d1 = 2*q.ones + q.mixed + S1) :
    ((w2Finish q).1 : ℝ) = phi q.ones q.zeros (q.mixed + (S0+S1)) ∧
    ((w2Finish q).2 : ℝ) = phi (q.ones + S1) (q.zeros + S0) q.mixed := by
  have hs0 : q.d0 - (2*q.zeros + q.mixed) = S0 := by omega
  have hs1 : q.d1 - (2*q.ones + q.mixed) = S1 := by omega
  simp only [w2Finish, hs0, hs1, phi, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_add]
  exact ⟨trivial, trivial⟩

end
end SAP.P012a.WH.W2
