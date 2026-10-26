import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Pairwise

/-!
# Algorithm 2: interior samples and absence of selected-curve crossings

A safe sample for a left endpoint lies to its right and strictly before every
global crossing to its right. The first sample is safe by sortedness of `J`.
Each successor sample is safe by the filtered list's least-element property,
including the empty-filter branch. A safe sample lies before the recorded right
endpoint, whether that endpoint is a selected-curve crossing or infinity.
-/

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem sample_inside_n13 {M : ℕ} {g : Fin M → ℝ → ℝ} {α : ℝ}
    {J : List ℝ} {p : RecordedPiece M} {next : Option (RecordedPiece M)}
    (hJ : IntersectionList g J) (hstep : Algorithm2Step g α J p next)
    (x : ℝ) (hleft : p.left < (x : EReal))
    (hbefore : ∀ e ∈ J, p.left < (e : EReal) → x < e) :
    x ∈ openInterval p.left p.right := by
  refine ⟨hleft, ?_⟩
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
    rw [hright]
    exact EReal.coe_lt_coe_iff.mpr (hbefore e heJ heC.1)
  · have hright : p.right = ⊤ := by
      simpa only [if_neg hC] using hend
    rw [hright]
    exact EReal.coe_lt_top x

private theorem no_crossing_n13 {M : ℕ} {g : Fin M → ℝ → ℝ} {α : ℝ}
    {J : List ℝ} {p : RecordedPiece M} {next : Option (RecordedPiece M)}
    (hstep : Algorithm2Step g α J p next) :
    ∀ s, g s ≠ g p.index → ∀ β ∈ openInterval p.left p.right,
      g s β ≠ g p.index β := by
  let C : Set ℝ := {β | p.left < (β : EReal) ∧
    ∃ m, g m ≠ g p.index ∧ g m β = g p.index β}
  have hend : (if C.Nonempty then
      ∃ e : ℝ, IsLeast C e ∧ p.right = (e : EReal)
    else p.right = ⊤) := hstep.1
  by_cases hC : C.Nonempty
  · rw [if_pos hC] at hend
    obtain ⟨e, he, hright⟩ := hend
    intro s hs β hβ heq
    have hβC : β ∈ C := ⟨hβ.1, s, hs, heq⟩
    have heβ : e ≤ β := he.2 hβC
    have hβe : β < e := EReal.coe_lt_coe_iff.mp (by
      simpa only [hright] using hβ.2)
    exact (not_le_of_gt hβe) heβ
  · intro s hs β hβ heq
    exact hC ⟨β, hβ.1, s, hs, heq⟩

/-- A successor's prescribed sample is safe for its new left endpoint. -/
private theorem next_sample_n13 {M : ℕ} {g : Fin M → ℝ → ℝ} {α : ℝ}
    {J : List ℝ} {p q : RecordedPiece M} (hJ : IntersectionList g J)
    (hstep : Algorithm2Step g α J p (some q)) :
    ∃ x : ℝ, q.left < (x : EReal) ∧
      (∀ e ∈ J, q.left < (e : EReal) → x < e) ∧
      q.index ∈ mcIndices g α x := by
  let C : Set ℝ := {β | p.left < (β : EReal) ∧
    ∃ m, g m ≠ g p.index ∧ g m β = g p.index β}
  let E : List ℝ := J.filter fun β => p.right < (β : EReal)
  have hend : (if C.Nonempty then
      ∃ e : ℝ, IsLeast C e ∧ p.right = (e : EReal)
    else p.right = ⊤) := hstep.1
  have hnext : p.right ≠ ⊤ ∧ q.left = p.right ∧
      q.index ∈ mcIndices g α
        (if E = [] then p.right.toReal + 1
          else (p.right.toReal + E.head!) / 2) := hstep.2
  have hC : C.Nonempty := by
    by_contra hC
    have htop : p.right = ⊤ := by
      simpa only [if_neg hC] using hend
    exact hnext.1 htop
  rw [if_pos hC] at hend
  obtain ⟨e, _he, hright⟩ := hend
  have hEmem : ∀ b : ℝ,
      b ∈ E ↔ b ∈ J ∧ p.right < (b : EReal) := by
    intro b
    simp only [E, List.mem_filter, decide_eq_true_eq]
  by_cases hE : E = []
  · refine ⟨e + 1, ?_, ?_, ?_⟩
    · rw [hnext.2.1, hright]
      apply EReal.coe_lt_coe_iff.mpr
      linarith only
    · intro b hb hqb
      have hpb : p.right < (b : EReal) := by
        rw [← hnext.2.1]
        exact hqb
      have hbE : b ∈ E := (hEmem b).mpr ⟨hb, hpb⟩
      rw [hE] at hbE
      simp at hbE
    · simpa only [if_pos hE, hright, EReal.toReal_coe] using hnext.2.2
  · have hEstrict : E.Pairwise (· < ·) := by
      dsimp only [E]
      exact List.Pairwise.filter _ hJ.1
    have hEweak : E.Pairwise (· ≤ ·) :=
      hEstrict.imp (fun {a b} hab => le_of_lt hab)
    have hVmem : E.head! ∈ E := List.head!_mem_self hE
    have hVright : p.right < (E.head! : EReal) := ((hEmem _).mp hVmem).2
    have heV : e < E.head! := EReal.coe_lt_coe_iff.mp (by
      rw [← hright]
      exact hVright)
    refine ⟨(e + E.head!) / 2, ?_, ?_, ?_⟩
    · rw [hnext.2.1, hright]
      apply EReal.coe_lt_coe_iff.mpr
      linarith only [heV]
    · intro b hb hqb
      have hpb : p.right < (b : EReal) := by
        rw [← hnext.2.1]
        exact hqb
      have hbE : b ∈ E := (hEmem b).mpr ⟨hb, hpb⟩
      have hVb : E.head! ≤ b := hEweak.head!_le hbE
      linarith only [heV, hVb]
    · simpa only [if_neg hE, hright, EReal.toReal_coe] using hnext.2.2

/-- Each recorded index is valid at an interior sample, and its curve meets no
globally distinct curve in the open piece. -/
theorem n13_proof : N13 := by
  intro hcons M g α J pieces hRun
  obtain ⟨hJ, _hJne, hpiecesne, hinit, hsteps⟩ := hRun
  have htail : ∀ (rest : List (RecordedPiece M)) (p : RecordedPiece M) (x : ℝ),
      (∀ i : Fin (p :: rest).length,
        Algorithm2Step g α J ((p :: rest).get i) ((p :: rest)[i.val + 1]?)) →
      p.left < (x : EReal) →
      (∀ e ∈ J, p.left < (e : EReal) → x < e) →
      p.index ∈ mcIndices g α x →
      ∀ q ∈ p :: rest,
        (∃ x₀ ∈ openInterval q.left q.right, q.index ∈ mcIndices g α x₀) ∧
        ∀ s, g s ≠ g q.index → ∀ β ∈ openInterval q.left q.right,
          g s β ≠ g q.index β := by
    intro rest
    induction rest with
    | nil =>
        intro p x hsteps' hleft hbefore hm q hq
        obtain ⟨hpstep, _⟩ :=
          (hcons (Algorithm2Step g α J) p []).mp hsteps'
        have hqp : q = p := List.mem_singleton.mp hq
        subst q
        exact ⟨⟨x, sample_inside_n13 hJ hpstep x hleft hbefore, hm⟩,
          no_crossing_n13 hpstep⟩
    | cons q rest ih =>
        intro p x hsteps' hleft hbefore hm r hr
        obtain ⟨hpstep, hrest⟩ :=
          (hcons (Algorithm2Step g α J) p (q :: rest)).mp hsteps'
        rcases List.mem_cons.mp hr with hr | hr
        · subst r
          exact ⟨⟨x, sample_inside_n13 hJ hpstep x hleft hbefore, hm⟩,
            no_crossing_n13 hpstep⟩
        · obtain ⟨y, hy, hybefore, hym⟩ := next_sample_n13 hJ hpstep
          exact ih q y hrest hy hybefore hym r hr
  cases pieces with
  | nil => exact (hpiecesne rfl).elim
  | cons p rest =>
      obtain ⟨hbot, hm⟩ := hinit p rfl
      have hleft : p.left < ((J.head! - 1 : ℝ) : EReal) := by
        rw [hbot]
        exact EReal.bot_lt_coe _
      have hJweak : J.Pairwise (· ≤ ·) :=
        hJ.1.imp (fun {a b} hab => le_of_lt hab)
      have hbefore : ∀ e ∈ J, p.left < (e : EReal) → J.head! - 1 < e := by
        intro e he _
        have hmin : J.head! ≤ e := hJweak.head!_le he
        linarith only [hmin]
      exact htail rest p (J.head! - 1) hsteps hleft hbefore hm

end
end AronowAudit.P002.Wave1.AlgorithmSupport
