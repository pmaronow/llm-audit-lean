/- Maximizing values are measurably represented as a finite supremum;
the selector need not be measurable. -/
import AronowAudit.P011.P011_HomoskedasticCompletion
import AronowAudit.P011.P011_CoverageCompletion
import Mathlib.MeasureTheory.Order.Lattice

namespace AronowAudit.P011.CorollaryCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma conservative_mono (F : Family) (V W : ∀k,(Fin (F.size k)→ℝ)→ℝ)
    (hV : Conservative F V) (hVW : ∀k y,V k y≤W k y) : Conservative F W := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  intro ε hε
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>?_) (hV ε hε)
  apply measureReal_mono (μ:=(F.model k).law) ?_ (measure_ne_top _ _)
  exact underestimation_event_inclusion _ _ _ (Nat.cast_nonneg _) (V k) (W k) (hVW k)

lemma V2_measurable {n : ℕ} (m : Model n) (B : Graph n) :
    Measurable (fun y=>V2 B (weighted m y)) := by
  unfold V2 sampleVariance centered average weighted
  fun_prop

lemma V2prime_measurable {n : ℕ} (m : Model n) :
    Measurable (fun y=>V2prime m.d (weighted m y)) := by
  unfold V2prime sampleVariance centered average weighted
  fun_prop

lemma maximum_measurable {n : ℕ} (m : Model n) (hv : Compatible m.R m.d m.G)
    (A : (Fin n→ℝ)→Graph n)
    (hm : ∀y,Maximizes m.R m.d (fun B=>V2 B (weighted m y)) (A y)) :
    Measurable (fun y=>V2 (A y) (weighted m y)) := by
  classical
  let S : Finset (Graph n) := Finset.univ.filter (Compatible m.R m.d)
  have hS : S.Nonempty := ⟨m.G,by simp [S,hv]⟩
  let φ : Graph n→(Fin n→ℝ)→ℝ := fun B y=>V2 B (weighted m y)
  have hM : Measurable (S.sup' hS φ) := Finset.measurable_sup' hS (fun B _=>V2_measurable m B)
  have he : (fun y=>V2 (A y) (weighted m y))=S.sup' hS φ := by
    funext y
    apply le_antisymm
    · have ha : A y∈S := by simpa [S] using (hm y).1
      exact (Finset.le_sup' (f:=φ) ha) y
    · have hb : S.sup' hS φ≤fun y=>V2 (A y) (weighted m y) := by
        apply (Finset.sup'_le_iff hS φ).mpr
        intro B hB z
        exact (hm z).2 B (by simpa [S] using hB)
      exact hb y
  rw [he]
  exact hM

lemma corollary_two_completed (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (hs : ∀ k, Homoskedastic (F.model k)) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V2 B (weighted (F.model k) y)) (A k y)) :
    Conservative F (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)) := by
  have h0 := proposition_two F c1 c2 c3 c4 h hs
  have hb (k : ℕ) (y : Fin (F.size k)→ℝ) := lemma_one (F.positive k)
    (F.model k).R (F.model k).G (A k y) (F.model k).d (hv k)
    (weighted (F.model k) y) (hm k y)
  have h1 := conservative_mono F _ _ h0 (fun k y=>(hb k y).1)
  exact ⟨h1,conservative_mono F _ _ h1 (fun k y=>(hb k y).2.1)⟩

lemma corollary_four_completed (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (hs : ∀ k, Homoskedastic (F.model k)) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V2 B (weighted (F.model k) y)) (A k y)) :
    ConservativeCoverage F (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
    ConservativeCoverage F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)) := by
  have hc := corollary_two_completed F c1 c2 c3 c4 h hs hv A hm
  exact ⟨(conditional_wald_coverage F c1 c2 c3 c4 h _
    (fun k=>maximum_measurable (F.model k) (hv k) (A k) (hm k))).2 hc.1,
    (conditional_wald_coverage F c1 c2 c3 c4 h _
      (fun k=>V2prime_measurable (F.model k))).2 hc.2⟩

end
end AronowAudit.P011.CorollaryCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem corollary_two (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (hs : ∀ k, Homoskedastic (F.model k)) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V2 B (weighted (F.model k) y)) (A k y)) :
    Conservative F (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)) := by
  exact CorollaryCompletion.corollary_two_completed F c1 c2 c3 c4 h hs hv A hm

theorem corollary_four (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (hs : ∀ k, Homoskedastic (F.model k)) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V2 B (weighted (F.model k) y)) (A k y)) :
    ConservativeCoverage F (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
    ConservativeCoverage F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)) := by
  exact CorollaryCompletion.corollary_four_completed F c1 c2 c3 c4 h hs hv A hm

end AronowAudit.P011

