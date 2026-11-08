import SAP.P012a.WH.W2.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W2

open SAP.P012a Finset
open scoped Classical
noncomputable section

/-- Unsampled-endpoint deletion trace. Extract replacement_properties and the
degree_remove_step/degree_add_step argument from corrected_graph_preserves.
The old endpoint cannot be the replacement: it was adjacent in the original
state, and a fresh choice is not in the pending vertex set. Identify its final
incident-edge filter with the original filter minus the deleted edge. Corrected
cleanup then gives exactly the sole-neighbour deletion criterion. About 100–160
lines; no positivity or nonempty-pool assumption is needed. -/
def T2_L1 : Prop :=
  ∀ (D : Data) (H : State) (i : ℕ) (j v : Vertex) (P : State),
    Admissible D → Compatible D H → i ∈ D.sampled → j ∈ H.vertices →
    s i ≠ j → {s i, j} ∈ H.edges → {s i, j} ∉ recruitmentEdges D →
    j ∉ sampledVertices D → Replacement D H (removeEdge H (s i) j) i v P →
    W2DeleteUnobserved D H i j v P

/-- Sampled-endpoint deletion trace, with the actual two replacement choices.
Use replacement_properties for the first choice. An edge from the first sampled
endpoint to an unsampled vertex cannot be an edge from the distinct second
sampled endpoint to any original pool member; this proves that the original
second pool remains valid. Apply replacement_properties again and the two
degree-step identities. Existing choices may coincide; fresh choices must only
be fresh at their own addition. About 100–180 lines, following the corresponding
case of corrected_graph_preserves. -/
def T2_L2 : Prop :=
  ∀ (D : Data) (H : State) (i j : ℕ) (v w : Vertex) (P Q : State),
    Admissible D → Compatible D H → i ∈ D.sampled → j ∈ D.sampled → i ≠ j →
    {s i, s j} ∈ H.edges → {s i, s j} ∉ recruitmentEdges D →
    Replacement D H (removeEdge H (s i) (s j)) i v P →
    Replacement D H (addEdge P (s i) v) j w Q → W2DeleteObserved D H i j v w P Q

/-- Addition-branch trace, including the shared-unsampled-vertex case.
Augmentedness forces j to be sampled because its neighbour w is unsampled.
recruitment_edge_sampled excludes both removed edges from recruitmentEdges;
pair_edge_eq and the distinct sampled endpoints make them distinct. Apply
degree_remove_step twice and degree_add_step once. Keep the two incidence
indicators separate, so a shared vertex loses two degrees. The cleanup
equivalences are mem_filter and the selected vertices' original membership.
About 100–160 lines; do not assume the selected unsampled vertices differ. -/
def T2_L3 : Prop :=
  ∀ (D : Data) (H : State) (i : ℕ) (j v w : Vertex),
    Admissible D → Compatible D H → i ∈ D.sampled → j ∈ H.vertices → s i ≠ j →
    {s i, j} ∉ H.edges → v ∈ unsampled D H → w ∈ unsampled D H →
    {s i, v} ∈ H.edges → {j, w} ∈ H.edges → W2AddObserved D H i j v w

/-- Only branch incidence specifications remain new. Compatibility, the
unchanged branch, and the complete trait execution description are proved. -/
theorem T2_assembly (h1 : T2_L1) (h2 : T2_L2) (h3 : T2_L3) : T2WholeStatement := by
  refine ⟨Bridge.corrected_proposal_preserves, h1, h2, h3, cleanup_identity, ?_⟩
  intro D H K hp
  cases hp with
  | flip v hv =>
    refine ⟨rfl, rfl, Or.inr ⟨v, hv, rfl, ?_, ?_⟩⟩
    · simp [flipTrait]
    · intro x hx
      simp [flipTrait, Function.update_of_ne hx]
  | empty hr hu => exact ⟨rfl, rfl, Or.inl ⟨hu, rfl⟩⟩

/-- Cardinality of the explicit private-leaf vertex set, with no admissibility
assumption. Ranges for different owners are disjoint by Sum.inr/Prod.fst
injectivity; each range image is injective by Prod.snd. Use card_biUnion,
card_image_of_injective, and card_union_of_disjoint, since sampled labels are
Sum.inl and leaves are Sum.inr. About 30–60 lines. Empty samples and zero spare
degrees are included and give their literal zero cardinalities. -/
def T3_L1 : Prop :=
  ∀ (D : Data) (same : Bool),
    (leafCompletion D same).vertices.card = D.sampled.card + totalSpare D

/-- The displayed quotient follows from the existing additive phi formula on
the positive-spare domain; no new mathematical leaf is needed. -/
private theorem lower_quotient (D : Data) (hS : 0 < totalSpare D) :
    hLower D = lowerQuotient D := by
  have hx : (0 : ℝ) < 2*(a D : ℝ) + ((cR D : ℝ) + totalSpare D) := by
    exact_mod_cast (show 0 < 2*a D + (cR D + totalSpare D) by omega)
  have hy : (0 : ℝ) < 2*(b D : ℝ) + ((cR D : ℝ) + totalSpare D) := by
    exact_mod_cast (show 0 < 2*b D + (cR D + totalSpare D) by omega)
  simpa only [hLower, lowerQuotient, add_assoc] using
    Bridge.phi_formula (a D) (b D) (cR D + totalSpare D) (ne_of_gt hx) (ne_of_gt hy)

/-- Existing binary incidence and graph_homophily_formula give positivity,
including data with only one sampled trait, when the spare total is positive. -/
private theorem opposite_denominator_positive (D : Data) (hD : Admissible D)
    (hS : 0 < totalSpare D) : 0 < hDenominator (leafCompletion D false) := by
  have hH : Compatible D (leafCompletion D false) :=
    AronowAudit.P012.leafCompletion_compatible (Bridge.data D) hD false
  have hb : traitDegree (leafCompletion D false) true =
      2*edgeCount (leafCompletion D false) true + mixedCount (leafCompletion D false) ∧
      traitDegree (leafCompletion D false) false =
      2*edgeCount (leafCompletion D false) false + mixedCount (leafCompletion D false) ∧
      (leafCompletion D false).edges.card =
        edgeCount (leafCompletion D false) true + edgeCount (leafCompletion D false) false +
          mixedCount (leafCompletion D false) :=
    AronowAudit.P012.binary_edge_counts (Bridge.state (leafCompletion D false)) hH.1.1
  have hc := (Bridge.opposite_leaf_counts D hD).2.2
  have h0 : 0 < traitDegree (leafCompletion D false) false := by
    rw [hb.2.1, hc]
    omega
  have h1 : 0 < traitDegree (leafCompletion D false) true := by
    rw [hb.1, hc]
    omega
  exact (AronowAudit.P012.graph_homophily_formula
    (Bridge.state (leafCompletion D false)) hH.1.1 h0 h1).2.2.1

/-- The full universal counterexample, its polynomial certificate, and the
rounding-robust failure of interval containment. -/
theorem T3_assembly (h1 : T3_L1) : T3WholeStatement := by
  have old : T3Statement := by
    refine ⟨?_, Bridge.table_counterexample, Bridge.uniform_leaf_bound,
      Bridge.uniform_integer_leaf_bound, Bridge.table_numeric_gaps⟩
    intro D hD hn hM hd
    have h := Bridge.table_counterexample D hD hn hM hd
    obtain ⟨hx, hy, hc⟩ := Bridge.opposite_leaf_counts D hD
    refine ⟨hx, hy, ?_, ?_⟩
    · simpa only [h.2.1] using hc
    · exact h.2.2.2.2.1.trans (lower_quotient D (by omega))
  refine ⟨old, ?_, ?_, by norm_num⟩
  · intro D hD hn hM hd
    have h := Bridge.table_counterexample D hD hn hM hd
    have hs : totalSpare D = 3445 := h.2.1
    have he : (recruitmentEdges D).card = 521 := by
      have ht : (recruitmentEdges D).card = D.sampled.card - D.seeds.card :=
        (AronowAudit.P012.recruitment_skeleton_counts (Bridge.data D) hD).2
      simpa only [hn, hM] using ht
    have hv : (leafCompletion D false).vertices.card = 3972 := by
      rw [h1, hn, hs]
    refine ⟨he, opposite_denominator_positive D hD (by omega), hv, by omega,
      leaf_structure D hD false, ?_⟩
    intro q hq L U hround
    have hqgap : (-1462/1983 : ℝ) < q - 1/20000 := by
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> norm_num
    have hr := (abs_le.mp hround).1
    have hb : hValue (leafCompletion D false) ≤ -1462/1983 := h.2.2.2.2.2.1
    have hlt : hValue (leafCompletion D false) < L := by linarith
    refine ⟨hlt, ?_⟩
    intro hsubset
    have hmem : hValue (leafCompletion D false) ∈ hValues D :=
      ⟨leafCompletion D false, h.1, by simp [homophily, h.2.2.2.1]⟩
    exact (not_le_of_gt hlt) (hsubset hmem).1
  · intro a b c ha hb hc hsum
    constructor
    · have he : c = 521-a-b := by linarith
      rw [he]
      ring
    · positivity

/-- The degree budgets by trait, retaining an equality before subtraction.
On recruitmentState, binary_edge_counts gives the trait degree totals
2a+c_R and 2b+c_R. Transfer the sums from sampledVertices using sum_image
and sum_filter. Sum d_i = d_i^r + spare_i over each trait group using
admissibility, then substitute the two recruitment totals. About 50–100 lines.
No positive trait sum or positive recruitment count is needed. -/
def T6_L1 : Prop :=
  ∀ (D : Data), Admissible D →
    sampledTraitDegree D false = 2*b D + cR D + traitSpare D false ∧
    sampledTraitDegree D true = 2*a D + cR D + traitSpare D true

/-- The two scans compute the five sufficient statistics for every duplicate-free
enumeration of the observed vertices and directed recruitment records. Prove
an arbitrary-initial-accumulator invariant for each tail recursion by list
induction, and convert the resulting list sums to finite sums using Nodup.
For edge counts, the child-to-undirected-edge map is injective on nonseeds:
reversal would contradict earlier recruitment times. Reuse the injectivity
argument in recruitment_skeleton_counts; classify a child record's two Boolean
traits to match edgeCount/mixedCount on the image. Counts must be accumulated
directly from records, as in w2EdgeStep. About 130–250 lines; includes empty
streams and data consisting only of seeds. -/
def T6_L2 : Prop :=
  ∀ (D : Data), Admissible D → ∀ vertices children : List ℕ,
    W2Enumerates D vertices children →
    let q := w2Scan D vertices children
    q.d0 = sampledTraitDegree D false ∧ q.d1 = sampledTraitDegree D true ∧
    q.ones = a D ∧ q.zeros = b D ∧ q.mixed = cR D

/-- Sharp homophily bounds come from the Bridge. The only additional leaves
are the trait budgets and scan statistics; casts, cost, and interval glue are
proved here or in Support. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) : T6WholeStatement := by
  refine ⟨⟨Bridge.exact_h_region, Bridge.phi_formula⟩, ?_⟩
  intro D hD h0 hpos
  have hregion := Bridge.exact_h_region D hD h0 hpos
  have hfull : FullHomophilyRegion D (hLower D) (hUpper D) :=
    hregion.2.2.2.2.2
  refine ⟨leaf_structure D hD false, leaf_structure D hD true, ?_, ?_⟩
  · intro L U
    constructor
    · intro hsub
      exact ⟨(hsub hfull.2.1.1).1, (hsub hfull.2.2.1).2⟩
    · rintro ⟨hL, hU⟩ r hr
      exact ⟨hL.trans (hfull.2.1.2 hr), (hfull.2.2.2 hr).trans hU⟩
  · intro vertices children hen
    obtain ⟨hd0, hd1, ha, hb, hc⟩ := h2 D hD vertices children hen
    have hbudget := h1 D hD
    let q := w2Scan D vertices children
    change q.d0 = sampledTraitDegree D false at hd0
    change q.d1 = sampledTraitDegree D true at hd1
    change q.ones = a D at ha
    change q.zeros = b D at hb
    change q.mixed = cR D at hc
    have hb0 : q.d0 = 2*q.zeros + q.mixed + traitSpare D false := by
      simpa only [hd0, hb, hc] using hbudget.1
    have hb1 : q.d1 = 2*q.ones + q.mixed + traitSpare D true := by
      simpa only [hd1, ha, hc] using hbudget.2
    have hs0 : q.d0 - (2*q.zeros + q.mixed) = traitSpare D false := by omega
    have hs1 : q.d1 - (2*q.ones + q.mixed) = traitSpare D true := by omega
    have hout := finish_cast q (traitSpare D false) (traitSpare D true) hb0 hb1
    have hpart : traitSpare D false + traitSpare D true = totalSpare D := by
      simpa only [Bridge.traitSpare_eq, Bridge.totalSpare_eq, Nat.add_comm] using
        (AronowAudit.P012.trait_spare_partition (Bridge.data D))
    have hpartR : (traitSpare D false : ℝ) + traitSpare D true = totalSpare D := by
      exact_mod_cast hpart
    have hlow : ((w2Finish q).1 : ℝ) = hLower D := by
      simpa only [ha, hb, hc, hpartR, hLower, Nat.cast_add] using hout.1
    have hupp : ((w2Finish q).2 : ℝ) = hUpper D := by
      simpa only [ha, hb, hc, hUpper, Nat.cast_add] using hout.2
    have hcost := scan_cost D vertices children
    have hn : vertices.length = D.sampled.card := by
      rw [← hen.2.1]
      exact (List.toFinset_card_of_nodup hen.1).symm
    have he : children.length = (recruitmentEdges D).card := by
      have hlen : children.length = (nonseeds D).card := by
        rw [← hen.2.2.2]
        exact (List.toFinset_card_of_nodup hen.2.2.1).symm
      have hcard : (recruitmentEdges D).card = D.sampled.card - D.seeds.card :=
        (AronowAudit.P012.recruitment_skeleton_counts (Bridge.data D) hD).2
      simpa only [nonseeds, card_sdiff_of_subset hD.1, hcard] using hlen
    exact ⟨hd0, hd1, ha, hb, hc, hb1, hb0, hs1, hs0, hlow, hupp,
      by simpa only [hn, he] using hcost.1,
      by simpa only [hn, he] using hcost.2⟩

end
end SAP.P012a.WH.W2
