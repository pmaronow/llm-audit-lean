import AronowAudit.P002.P002_Audit

/-!
# Finite quantiles and algorithm correctness (P002-T22, P002-T23, P002-T27, P002-T28)

This module contains finite-quantile, interval and algorithm geometry statements
for arbitrary families of real curves `g : Fin M → ℝ → ℝ`, together with lemmas
that combine them. The statements use the P002 definitions of empirical critical
values, quantile indices, confidence sets, crossings, gaps and algorithm runs.
None assumes a rank or interval-wide correctness conclusion.
-/

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Node 1 (P002-T27; main p. 14, (13) and (17)):
for `M > 0`, `0 < α < 1` and nonnegative squared curves at `β`, the empirical quantile
index set is nonempty and the empirical critical value is nonnegative. -/
def N1 : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α β : ℝ), 0 < M → (0 < α ∧ α < 1) →
    (∀ m, 0 ≤ g m β) →
    (mcIndices g α β).Nonempty ∧ 0 ≤ mcCritical g α β

/-- Node 2 (P002-T27; Supplement H.1 continuity step):
the empirical critical value of finitely many continuous squared curves is continuous.
The critical value of a vector is 1-Lipschitz in the sup norm, ties
included; this applies to the continuous square roots. -/
def N2 : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ), 0 < M → (0 < α ∧ α < 1) →
    (∀ m, Continuous (g m)) →
    Continuous (fun β => mcCritical g α β)

/-- Node 3 (P002-T27; single-curve form for Algorithm 2; main p. 14 Lemma 1(i)): if the selected
curve `g m` meets no
globally distinct curve inside the open interval and `m` is a quantile index at one
interior point, then `m` is a quantile index at every interior point. Crossings between
two unselected curves are allowed. The rank characterization and intermediate value theorem give
sign constancy. -/
def N3 : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (m : Fin M) (l u : EReal) (x₀ : ℝ),
    0 < M → (0 < α ∧ α < 1) → (∀ s, Continuous (g s)) → (∀ s β, 0 ≤ g s β) →
    x₀ ∈ openInterval l u →
    (∀ s, g s ≠ g m → ∀ β ∈ openInterval l u, g s β ≠ g m β) →
    m ∈ mcIndices g α x₀ →
    ∀ x ∈ openInterval l u, m ∈ mcIndices g α x

/-- Node 4 (P002-T27; main p. 14 Lemma 1(ii)-(iv)): continuity of the critical value extends
validity of an index from the
open interval to every real point of the closed interval, including finite endpoints.
No value at an infinite endpoint is involved since members are real. -/
def N4 : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (m : Fin M) (l u : EReal),
    (∀ s, Continuous (g s)) → Continuous (fun β => mcCritical g α β) → l < u →
    (∀ x ∈ openInterval l u, m ∈ mcIndices g α x) →
    ∀ β ∈ closedInterval l u, m ∈ mcIndices g α β

/-- Node 5 (P002-T22; corrected (H.1), Supplement p. 45): on a recorded piece whose index is
valid at every real point of its
closed interval, the selected squared curve is the square of the absolute critical value,
and the Step 4/5 piece set equals the Monte Carlo confidence set on that interval. -/
def N5 : Prop :=
  ∀ (M : ℕ) (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ) (p : RecordedPiece M),
    (∀ β, 0 ≤ f β) → (∀ s β, 0 ≤ g s β) →
    (∀ β ∈ closedInterval p.left p.right, p.index ∈ mcIndices g α β) →
    (∀ β ∈ closedInterval p.left p.right, g p.index β = (mcCritical g α β) ^ 2) ∧
    pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right

/-- Node 6 (P002-T23; main p. 15, Algorithm 1 Steps 2-3):
every gap of a strictly sorted list has strictly ordered endpoints, its prescribed sample
point lies in its open interior, and no list element lies in that interior. This also
holds for the empty list, whose sole gap is `(⊥, ⊤)` with sample `0`. -/
def N6 : Prop :=
  ∀ (J : List ℝ), J.Pairwise (· < ·) →
    ∀ lu ∈ gapEndpoints J, lu.1 < lu.2 ∧ gapSample lu.1 lu.2 ∈ openInterval lu.1 lu.2 ∧
      ∀ β ∈ openInterval lu.1 lu.2, β ∉ J

/-- Node 7 (P002-T28; main p. 15, Algorithm 1 Step 2): the closed gaps of any list cover the
real line. -/
def N7 : Prop :=
  ∀ (J : List ℝ) (β : ℝ), ∃ lu ∈ gapEndpoints J, β ∈ closedInterval lu.1 lu.2

/-- Node 8 (P002-T28; main p. 15 Step 1 and Remark 7):
a regular family (continuous, nonnegative, distinct pairs meet finitely often) has a
complete strictly sorted intersection list. -/
def N8 : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ), CurveRegularity g → ∃ J, IntersectionList g J

/-- Node 9 (P002-T28; main p. 15, Algorithm 1 Step 3): if every quantile index set is nonempty,
every complete
intersection list admits an Algorithm 1 run (choose an index at each gap sample). -/
def N9 : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ), IntersectionList g J →
    (∀ β, (mcIndices g α β).Nonempty) → ∃ pieces, Algorithm1Run g α J pieces

/-- Statement of Node 10 (P002-T22; main p. 16 Algorithm 2 Step 4 and the last-crossing branch):
from any left endpoint and
any starting index, the Step 4 loop can be run to termination. Recursion on the number
of list elements to the right of the current left endpoint. -/
def Alg2TailExists : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ), IntersectionList g J →
    (∀ β, (mcIndices g α β).Nonempty) →
    ∀ (l : EReal) (m : Fin M), ∃ pieces : List (RecordedPiece M),
      (∃ r, pieces.head? = some ⟨l, r, m⟩) ∧
      ∀ i : Fin pieces.length, Algorithm2Step g α J (pieces.get i) (pieces[i.val+1]?)

/-- Statement of Node 11 (P002-T22): every encoded Algorithm 2 run has at most `|J|+1` pieces,
strictly
increasing right endpoints, each right endpoint `⊤` or an element of `J`, and every piece
has `left < right`. -/
def Alg2RunEndpoints : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ) (pieces : List (RecordedPiece M)),
    Algorithm2Run g α J pieces →
    pieces.length ≤ J.length + 1 ∧
    (pieces.map (fun p => p.right)).Pairwise (· < ·) ∧
    (∀ p ∈ pieces, p.right = ⊤ ∨ ∃ e : ℝ, p.right = (e : EReal) ∧ e ∈ J) ∧
    (∀ p ∈ pieces, p.left < p.right)

/-- Statement of Node 12 (P002-T22; Supplement p. 45 H.2): the
closed pieces of every Algorithm 2 run cover the real line (first left endpoint `⊥`,
consecutive pieces meet, last right endpoint `⊤`). -/
def Alg2RunCover : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ) (pieces : List (RecordedPiece M)),
    Algorithm2Run g α J pieces →
    ∀ β : ℝ, ∃ p ∈ pieces, β ∈ closedInterval p.left p.right

/-- Statement of Node 13 (P002-T22; Supplement p. 45 H.2, corrected):
in every Algorithm 2 run, each piece's index is a quantile index at some point of the
piece's open interior (the initial sample `J.head!-1`, a midpoint `(e+V)/2`, or `e+1` in
the empty-`E` branch), and the selected curve meets no globally distinct curve inside the
open piece. -/
def Alg2RunSample : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ) (pieces : List (RecordedPiece M)),
    Algorithm2Run g α J pieces →
    ∀ p ∈ pieces, (∃ x₀ ∈ openInterval p.left p.right, p.index ∈ mcIndices g α x₀) ∧
      ∀ s, g s ≠ g p.index → ∀ β ∈ openInterval p.left p.right, g s β ≠ g p.index β

/-- Index bookkeeping for the `Fin`-indexed step condition of `Algorithm2Run`: the step
condition on `p :: rest` is the step from `p` to `rest.head?` together with the step
condition on `rest`. Generic in the step relation. -/
def StepsCons : Prop :=
  ∀ {X : Type} (R : X → Option X → Prop) (p : X) (rest : List X),
    (∀ i : Fin (p :: rest).length, R ((p :: rest).get i) ((p :: rest)[i.val+1]?)) ↔
      (R p rest.head? ∧ ∀ i : Fin rest.length, R (rest.get i) (rest[i.val+1]?))

/-- Node 10: construction of a terminating Step 4 loop (recursion on the number of list
elements to the right of the current left endpoint); uses `StepsCons`. -/
def N10 : Prop := StepsCons → Alg2TailExists
/-- Node 11: length, ordering and endpoint membership of every run; uses `StepsCons`. -/
def N11 : Prop := StepsCons → Alg2RunEndpoints
/-- Node 12: every run covers the real line; uses `StepsCons`. -/
def N12 : Prop := StepsCons → Alg2RunCover
/-- Node 13: sample points and the selected-curve crossing condition; uses `StepsCons`. -/
def N13 : Prop := StepsCons → Alg2RunSample
/-- Node 14: the step bookkeeping lemma. -/
def N14 : Prop := StepsCons

/-! ## Lemmas combining the statements -/

/-- The union of valid pieces covering the real line is the confidence set. -/
theorem glue_union {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ)
    (pieces : List (RecordedPiece M))
    (hcover : ∀ β : ℝ, ∃ p ∈ pieces, β ∈ closedInterval p.left p.right)
    (hpiece : ∀ p ∈ pieces, pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right) :
    returnedSet f g pieces = mcSet f g α := by
  ext β
  constructor
  · rintro ⟨p, hp, hβ⟩
    rw [hpiece p hp] at hβ
    exact hβ.1
  · intro hβ
    obtain ⟨p, hp, hc⟩ := hcover β
    exact ⟨p, hp, by rw [hpiece p hp]; exact ⟨hβ, hc⟩⟩

/-- Single-curve validity on a closed interval from Nodes 2-4. -/
theorem glue_closed_valid (h2 : N2) (h3 : N3) (h4 : N4) {M : ℕ} (g : Fin M → ℝ → ℝ)
    (α : ℝ) (hM : 0 < M) (hα : 0 < α ∧ α < 1) (hc : ∀ s, Continuous (g s))
    (hn : ∀ s β, 0 ≤ g s β) (m : Fin M) (l u : EReal) (x₀ : ℝ)
    (hx₀ : x₀ ∈ openInterval l u)
    (hsc : ∀ s, g s ≠ g m → ∀ β ∈ openInterval l u, g s β ≠ g m β)
    (hm : m ∈ mcIndices g α x₀) :
    ∀ β ∈ closedInterval l u, m ∈ mcIndices g α β :=
  h4 M g α m l u hc (h2 M g α hM hα hc) (lt_trans hx₀.1 hx₀.2)
    (h3 M g α m l u x₀ hM hα hc hn hx₀ hsc hm)

/-- Every piece of an Algorithm 1 run (any complete list, empty or not) is valid on its
closed gap and satisfies the corrected (H.1) set identity. -/
theorem glue_algorithm1_pieces (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6)
    {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ) (hM : 0 < M)
    (hα : 0 < α ∧ α < 1) (hc : ∀ s, Continuous (g s)) (hn : ∀ s β, 0 ≤ g s β)
    (hf : ∀ β, 0 ≤ f β) (J : List ℝ) (pieces : List (RecordedPiece M))
    (hRun : Algorithm1Run g α J pieces) :
    ∀ p ∈ pieces,
      (∀ β ∈ closedInterval p.left p.right,
        p.index ∈ mcIndices g α β ∧ g p.index β = (mcCritical g α β) ^ 2) ∧
      pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right := by
  intro p hp
  obtain ⟨hJ, hmap, hidx⟩ := hRun
  have hmem : (p.left, p.right) ∈ gapEndpoints J := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  obtain ⟨_, hsample, hnoJ⟩ := h6 J hJ.1 _ hmem
  have hsc : ∀ s, g s ≠ g p.index → ∀ β ∈ openInterval p.left p.right,
      g s β ≠ g p.index β := by
    intro s hs β hβ heq
    exact hnoJ β hβ ((hJ.2 β).mpr ⟨s, p.index, hs, heq⟩)
  have hvalid := glue_closed_valid h2 h3 h4 g α hM hα hc hn p.index p.left p.right
    (gapSample p.left p.right) hsample hsc (hidx p hp)
  have h5' := h5 M f g α p hf hn hvalid
  exact ⟨fun β hβ => ⟨hvalid β hβ, h5'.1 β hβ⟩, h5'.2⟩

/-- Algorithm 1 returns the Monte Carlo confidence set, for every complete list. -/
theorem glue_algorithm1_returned (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6)
    (h7 : N7) {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ) (hM : 0 < M)
    (hα : 0 < α ∧ α < 1) (hc : ∀ s, Continuous (g s)) (hn : ∀ s β, 0 ≤ g s β)
    (hf : ∀ β, 0 ≤ f β) (J : List ℝ) (pieces : List (RecordedPiece M))
    (hRun : Algorithm1Run g α J pieces) :
    returnedSet f g pieces = mcSet f g α := by
  apply glue_union f g α pieces
  · intro β
    obtain ⟨lu, hlu, hβ⟩ := h7 J β
    rw [← hRun.2.1] at hlu
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hlu
    subst hpe
    exact ⟨p, hp, hβ⟩
  · intro p hp
    exact (glue_algorithm1_pieces h2 h3 h4 h5 h6 f g α hM hα hc hn hf J pieces hRun p hp).2

/-- Algorithm 2 has a run whenever the complete list is nonempty. -/
theorem glue_algorithm2_exists (h1 : N1) (h10 : N10) (h14 : N14) {M : ℕ} (g : Fin M → ℝ → ℝ)
    (α : ℝ) (hM : 0 < M) (hα : 0 < α ∧ α < 1) (hn : ∀ s β, 0 ≤ g s β) (J : List ℝ)
    (hJ : IntersectionList g J) (hne : J ≠ []) :
    ∃ pieces, Algorithm2Run g α J pieces := by
  have hall : ∀ β, (mcIndices g α β).Nonempty :=
    fun β => (h1 M g α β hM hα (fun m => hn m β)).1
  obtain ⟨m₀, hm₀⟩ := hall (J.head! - 1)
  obtain ⟨pieces, ⟨r, hhead⟩, hsteps⟩ := h10 h14 M g α J hJ hall ⊥ m₀
  refine ⟨pieces, hJ, hne, ?_, ?_, hsteps⟩
  · intro h
    rw [h] at hhead
    simp at hhead
  · intro p hp
    rw [hhead] at hp
    cases hp
    exact ⟨rfl, hm₀⟩

/-- Every Algorithm 2 run satisfies the corrected Step 4/5 conclusions. -/
theorem glue_algorithm2_props (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h11 : N11)
    (h12 : N12) (h13 : N13) (h14 : N14) {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ)
    (hM : 0 < M) (hα : 0 < α ∧ α < 1) (hc : ∀ s, Continuous (g s))
    (hn : ∀ s β, 0 ≤ g s β) (hf : ∀ β, 0 ≤ f β) (J : List ℝ)
    (pieces : List (RecordedPiece M)) (hRun : Algorithm2Run g α J pieces) :
    pieces.length ≤ J.length + 1 ∧
      (pieces.map (fun p => p.right)).Pairwise (· < ·) ∧
      (∀ p ∈ pieces, p.right = ⊤ ∨ ∃ e : ℝ, p.right = (e : EReal) ∧ e ∈ J) ∧
      (∀ β : ℝ, ∃ p ∈ pieces, β ∈ closedInterval p.left p.right) ∧
      (∀ p ∈ pieces, ∀ β ∈ closedInterval p.left p.right, p.index ∈ mcIndices g α β) ∧
      (∀ p ∈ pieces, pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right) ∧
      returnedSet f g pieces = mcSet f g α := by
  obtain ⟨hlen, hpair, hright, _⟩ := h11 h14 M g α J pieces hRun
  have hcover := h12 h14 M g α J pieces hRun
  have hvalid : ∀ p ∈ pieces, ∀ β ∈ closedInterval p.left p.right,
      p.index ∈ mcIndices g α β := by
    intro p hp
    obtain ⟨⟨x₀, hx₀, hm⟩, hsc⟩ := h13 h14 M g α J pieces hRun p hp
    exact glue_closed_valid h2 h3 h4 g α hM hα hc hn p.index p.left p.right x₀ hx₀ hsc hm
  have hpiece : ∀ p ∈ pieces,
      pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right :=
    fun p hp => (h5 M f g α p hf hn (hvalid p hp)).2
  exact ⟨hlen, hpair, hright, hcover, hvalid, hpiece, glue_union f g α pieces hcover hpiece⟩


end
end AronowAudit.P002.Wave1.AlgorithmSupport
