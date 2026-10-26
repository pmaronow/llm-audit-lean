import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

/-!
# Algorithm 2: endpoint geometry and the number of pieces

The list induction keeps the additional invariant that every right endpoint of a
tail is strictly above the tail's initial left endpoint. This gives the full
pairwise ordering, rather than only the ordering of adjacent endpoints.
-/

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem step_geometry_n11 {M : ℕ} {g : Fin M → ℝ → ℝ} {α : ℝ}
    {J : List ℝ} {p : RecordedPiece M} {next : Option (RecordedPiece M)}
    (hJ : IntersectionList g J) (hleft : p.left < ⊤)
    (hstep : Algorithm2Step g α J p next) :
    (p.right = ⊤ ∨ ∃ e : ℝ, p.right = (e : EReal) ∧ e ∈ J) ∧
      p.left < p.right := by
  let C : Set ℝ := {β | p.left < (β : EReal) ∧
    ∃ m, g m ≠ g p.index ∧ g m β = g p.index β}
  have hend : (if C.Nonempty then
      ∃ e : ℝ, IsLeast C e ∧ p.right = (e : EReal)
    else p.right = ⊤) := hstep.1
  by_cases hC : C.Nonempty
  · rw [if_pos hC] at hend
    obtain ⟨e, he, hright⟩ := hend
    have heC : p.left < (e : EReal) ∧
        ∃ m, g m ≠ g p.index ∧ g m e = g p.index e := he.1
    obtain ⟨m, hm, hme⟩ := heC.2
    have heJ : e ∈ J := (hJ.2 e).mpr ⟨m, p.index, hm, hme⟩
    refine ⟨Or.inr ⟨e, hright, heJ⟩, ?_⟩
    rw [hright]
    exact heC.1
  · have hright : p.right = ⊤ := by
      simpa only [if_neg hC] using hend
    exact ⟨Or.inl hright, by rw [hright]; exact hleft⟩

/-- Every Algorithm 2 run has strictly increasing admissible right endpoints,
positive-width pieces, and at most one more piece than global crossings. -/
theorem n11_proof : N11 := by
  intro hcons M g α J pieces hRun
  obtain ⟨hJ, _hJne, hpiecesne, hinit, hsteps⟩ := hRun
  have htail : ∀ (rest : List (RecordedPiece M)) (p : RecordedPiece M),
      p.left < ⊤ →
      (∀ i : Fin (p :: rest).length,
        Algorithm2Step g α J ((p :: rest).get i) ((p :: rest)[i.val + 1]?)) →
      ((p :: rest).map (fun q => q.right)).Pairwise (· < ·) ∧
      (∀ q ∈ p :: rest, q.right = ⊤ ∨
        ∃ e : ℝ, q.right = (e : EReal) ∧ e ∈ J) ∧
      (∀ q ∈ p :: rest, q.left < q.right) ∧
      (∀ q ∈ p :: rest, p.left < q.right) := by
    intro rest
    induction rest with
    | nil =>
        intro p hleft hsteps'
        obtain ⟨hpstep, _⟩ :=
          (hcons (Algorithm2Step g α J) p []).mp hsteps'
        obtain ⟨hpright, hpwidth⟩ := step_geometry_n11 hJ hleft hpstep
        refine ⟨by simp, ?_, ?_, ?_⟩
        · intro q hq
          have hqp : q = p := List.mem_singleton.mp hq
          subst q
          exact hpright
        · intro q hq
          have hqp : q = p := List.mem_singleton.mp hq
          subst q
          exact hpwidth
        · intro q hq
          have hqp : q = p := List.mem_singleton.mp hq
          subst q
          exact hpwidth
    | cons q rest ih =>
        intro p hleft hsteps'
        obtain ⟨hpstep, hrest⟩ :=
          (hcons (Algorithm2Step g α J) p (q :: rest)).mp hsteps'
        obtain ⟨hpright, hpwidth⟩ := step_geometry_n11 hJ hleft hpstep
        have hpnotop : p.right ≠ ⊤ := hpstep.2.1
        have hmeet : q.left = p.right := hpstep.2.2.1
        have hqleft : q.left < ⊤ := by
          rw [hmeet]
          exact lt_top_iff_ne_top.mpr hpnotop
        obtain ⟨htailpair, htailright, htailwidth, htaillower⟩ :=
          ih q hqleft hrest
        have habove : ∀ r ∈ q :: rest, p.right < r.right := by
          intro r hr
          rw [← hmeet]
          exact htaillower r hr
        refine ⟨?_, ?_, ?_, ?_⟩
        · change (p.right :: (q :: rest).map (fun r => r.right)).Pairwise (· < ·)
          apply List.pairwise_cons.mpr
          refine ⟨?_, htailpair⟩
          intro u hu
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
          exact habove r hr
        · intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r
            exact hpright
          · exact htailright r hr
        · intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r
            exact hpwidth
          · exact htailwidth r hr
        · intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r
            exact hpwidth
          · exact lt_trans hpwidth (habove r hr)
  cases pieces with
  | nil => exact (hpiecesne rfl).elim
  | cons p rest =>
      have hbot : p.left = ⊥ := (hinit p rfl).1
      have hleft : p.left < ⊤ := by
        rw [hbot]
        exact bot_lt_top
      obtain ⟨hpair, hright, hwidth, _⟩ := htail rest p hleft hsteps
      have hsubset :
          (p :: rest).map (fun q => q.right) ⊆
            J.map (fun e : ℝ => (e : EReal)) ++ [⊤] := by
        intro u hu
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
        rcases hright q hq with htop | ⟨e, he, heJ⟩
        · rw [htop]
          exact List.mem_append.mpr (Or.inr (by simp))
        · exact List.mem_append.mpr
            (Or.inl (List.mem_map.mpr ⟨e, heJ, he.symm⟩))
      have hlen : (p :: rest).length ≤ J.length + 1 := by
        have hsubperm := List.subperm_of_subset hpair.nodup hsubset
        simpa only [List.length_map, List.length_append, List.length_singleton]
          using hsubperm.length_le
      exact ⟨hlen, hpair, hright, hwidth⟩

end
end AronowAudit.P002.Wave1.AlgorithmSupport
