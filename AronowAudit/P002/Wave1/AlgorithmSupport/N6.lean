import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Zip

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Generalize the initial left endpoint before inducting over the sorted list.
The extra lower-bound invariant excludes each removed head from later gaps. -/
theorem n6_proof : N6 := by
  have hsample (l u : EReal)
      (hl : l = ⊥ ∨ ∃ a : ℝ, l = (a : EReal))
      (hu : u = ⊤ ∨ ∃ b : ℝ, u = (b : EReal)) (hlu : l < u) :
      gapSample l u ∈ openInterval l u := by
    rcases hl with rfl | ⟨a, rfl⟩
    · rcases hu with rfl | ⟨b, rfl⟩
      · have hformula : gapSample (⊥ : EReal) ⊤ = 0 := by simp [gapSample]
        rw [hformula]
        exact ⟨EReal.bot_lt_coe 0, EReal.coe_lt_top 0⟩
      · have hformula : gapSample (⊥ : EReal) (b : EReal) = b - 1 := by
          simp [gapSample]
        rw [hformula]
        refine ⟨EReal.bot_lt_coe _, EReal.coe_lt_coe_iff.mpr ?_⟩
        linarith
    · rcases hu with rfl | ⟨b, rfl⟩
      · have hformula : gapSample (a : EReal) ⊤ = a + 1 := by simp [gapSample]
        rw [hformula]
        refine ⟨EReal.coe_lt_coe_iff.mpr ?_, EReal.coe_lt_top _⟩
        linarith
      · have hab : a < b := EReal.coe_lt_coe_iff.mp hlu
        have hformula : gapSample (a : EReal) (b : EReal) = (a + b) / 2 := by
          simp [gapSample]
        rw [hformula]
        constructor <;> apply EReal.coe_lt_coe_iff.mpr <;> linarith
  have haux : ∀ (J : List ℝ), J.Pairwise (· < ·) →
      ∀ (a : EReal), (a = ⊥ ∨ ∃ r : ℝ, a = (r : EReal)) →
      (∀ b ∈ J, a < (b : EReal)) →
      ∀ lu ∈ (a :: J.map (fun x => (x : EReal))).zip
          (J.map (fun x => (x : EReal)) ++ [⊤]),
        a ≤ lu.1 ∧ lu.1 < lu.2 ∧
        gapSample lu.1 lu.2 ∈ openInterval lu.1 lu.2 ∧
        ∀ β ∈ openInterval lu.1 lu.2, β ∉ J := by
    intro J
    induction J with
    | nil =>
        intro _hJ a ha _hbefore lu hlu
        change lu ∈ [(a, (⊤ : EReal))] at hlu
        have hlu' : lu = (a, (⊤ : EReal)) := by
          simpa only [List.mem_singleton] using hlu
        rcases hlu' with rfl
        have haTop : a < (⊤ : EReal) := by
          rcases ha with rfl | ⟨r, rfl⟩
          · exact bot_lt_top
          · exact EReal.coe_lt_top r
        refine ⟨le_rfl, haTop, hsample a ⊤ ha (Or.inl rfl) haTop, ?_⟩
        intro β _hβ
        exact List.not_mem_nil
    | cons b J ih =>
        intro hJ a ha hbefore lu hlu
        have hJ' : (∀ c ∈ J, b < c) ∧ J.Pairwise (· < ·) := List.pairwise_cons.mp hJ
        have hab : a < (b : EReal) := hbefore b (by simp)
        change lu ∈ (a, (b : EReal)) ::
          (((b : EReal) :: J.map (fun x => (x : EReal))).zip
            (J.map (fun x => (x : EReal)) ++ [⊤])) at hlu
        rcases List.mem_cons.mp hlu with hlu | hlu
        · rcases hlu with rfl
          refine ⟨le_rfl, hab, hsample a (b : EReal) ha (Or.inr ⟨b, rfl⟩) hab, ?_⟩
          intro β hβ hβJ
          rcases List.mem_cons.mp hβJ with hβb | hβJ
          · subst β
            exact (lt_irrefl (b : EReal)) hβ.2
          · have hbβ : (b : EReal) < (β : EReal) :=
              EReal.coe_lt_coe_iff.mpr (hJ'.1 β hβJ)
            exact (not_lt_of_ge hbβ.le) hβ.2
        · have hbefore' : ∀ c ∈ J, (b : EReal) < (c : EReal) := by
            intro c hc
            exact EReal.coe_lt_coe_iff.mpr (hJ'.1 c hc)
          have hrec := ih hJ'.2 (b : EReal) (Or.inr ⟨b, rfl⟩) hbefore' lu hlu
          refine ⟨hab.le.trans hrec.1, hrec.2.1, hrec.2.2.1, ?_⟩
          intro β hβ hβJ
          rcases List.mem_cons.mp hβJ with hβb | hβJ
          · have hbβ : (b : EReal) < (β : EReal) := lt_of_le_of_lt hrec.1 hβ.1
            subst β
            exact (lt_irrefl (b : EReal)) hbβ
          · exact hrec.2.2.2 β hβ hβJ
  intro J hJ lu hlu
  have hbefore : ∀ b ∈ J, (⊥ : EReal) < (b : EReal) :=
    fun b _ => EReal.bot_lt_coe b
  exact (haux J hJ ⊥ (Or.inl rfl) hbefore lu hlu).2

end
end AronowAudit.P002.Wave1.AlgorithmSupport
