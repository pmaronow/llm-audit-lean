import SAP.P012a.Defs.WholeW1
import SAP.P012a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1

open Finset
open scoped Classical
noncomputable section

theorem chronological_exists (D : Data) (hD : Admissible D) :
    ∃ order, WholeChronological D order := by
  let order := D.sampled.toList.mergeSort (fun i j => decide (D.time i ≤ D.time j))
  have hp := List.mergeSort_perm D.sampled.toList
    (fun i j => decide (D.time i ≤ D.time j))
  have hn : order.Nodup := hp.nodup_iff.mpr D.sampled.nodup_toList
  have hm : ∀ i, i ∈ order ↔ i ∈ D.sampled := by
    intro i
    simpa only [Finset.mem_toList] using hp.mem_iff
  have hs : order.toFinset = D.sampled := by ext i; simp only [List.mem_toFinset, hm]
  have hle : order.Pairwise (fun i j => D.time i ≤ D.time j) := by
    have hh := List.pairwise_mergeSort
      (le := fun i j => decide (D.time i ≤ D.time j))
      (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      D.sampled.toList
    simpa only [decide_eq_true_eq] using hh
  refine ⟨order, hn, hs, ?_⟩
  apply List.Pairwise.imp_of_mem ?_ (hle.and (List.nodup_iff_pairwise_ne.mp hn))
  intro a b ha hb hab
  exact lt_of_le_of_ne hab.1 (fun he => hab.2 (hD.2.1 a ((hm a).mp ha) b ((hm b).mp hb) he))

theorem run_clocks (records : List PWholeRecord) (st : PWholeState) :
    (records.foldl pWholeStep st).reads = st.reads + records.length ∧
    (records.foldl pWholeStep st).reciprocals = st.reciprocals +
      (records.filter (fun a => !a.seed)).length ∧
    (records.foldl pWholeStep st).work ≤ st.work + 32*records.length := by
  induction records generalizing st with
  | nil => simp
  | cons a rest ih =>
    have h := ih (pWholeStep st a)
    cases ha : a.seed <;>
      simp only [List.foldl_cons, pWholeStep, ha, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false, Bool.not_true, List.filter_cons, List.length_cons,
        Nat.sub_zero] at h ⊢ <;> constructor
    · omega
    · exact ⟨by omega, by omega⟩
    · omega
    · exact ⟨by omega, by omega⟩

theorem run_reads (D : Data) (order : List ℕ) :
    (pWholeRun D order).reads = order.length := by
  simpa [pWholeRun, pWholeInitial] using (run_clocks (order.map (pWholeRecord D)) pWholeInitial).1

theorem run_count_reciprocals (records : List PWholeRecord) (st : PWholeState)
    (h : st.count = st.reciprocals) :
    (records.foldl pWholeStep st).count = (records.foldl pWholeStep st).reciprocals := by
  induction records generalizing st with
  | nil => exact h
  | cons a rest ih =>
    apply ih
    cases ha : a.seed <;> simp [pWholeStep, ha, h]

theorem leaf_neighbors (D : Data) (hD : Admissible D) (same : Bool)
    (i k : ℕ) (hi : i ∈ D.sampled) (hk : k < spare D i) :
    wholeNeighbors (leafCompletion D same) (u i k) = {s i} := by
  let H := leafCompletion D same
  have hc : Compatible D H := AronowAudit.P012.leafCompletion_compatible (Bridge.data D) hD same
  have hp := AronowAudit.P012.private_leaf_member (Bridge.data D) hD same i k hi hk
  change u i k ∈ unsampled D H ∧
    (∀ j ∈ D.sampled, {s j,u i k} ∈ H.edges ↔ j = i) at hp
  have hnot := (mem_sdiff.mp hp.1).2
  ext w
  constructor
  · intro hw
    obtain ⟨hw,he⟩ := mem_filter.mp hw
    obtain ⟨j,hj,hje⟩ := hc.1.2 _ he
    have hjw : s j = w := by
      rcases mem_insert.mp hje with hju | hjw
      · exact False.elim (hnot (hju ▸ mem_image_of_mem s hj))
      · exact mem_singleton.mp hjw
    subst w
    have hji := (hp.2 j hj).mp (by simpa [Finset.pair_comm] using he)
    simp [hji]
  · intro hw
    have hw : w = s i := mem_singleton.mp hw
    subst w
    exact mem_filter.mpr ⟨hc.2.1 (mem_image_of_mem s hi),
      by simpa [Finset.pair_comm] using (hp.2 i hi).mpr rfl⟩

theorem sampled_degree_trait_bound (D : Data) (H : State) (hH : Compatible D H)
    (i : ℕ) (hi : i ∈ D.sampled) (t : Bool) (ht : D.trait i = t) :
    D.degree i ≤ traitDegree H t := by
  have hmem : s i ∈ H.vertices.filter (fun v => H.trait v = t) :=
    mem_filter.mpr ⟨hH.2.1 (mem_image_of_mem s hi), (hH.2.2.2.1 i hi).trans ht⟩
  have hh : graphDegree H (s i) ≤ traitDegree H t :=
    single_le_sum (fun _ _ => Nat.zero_le _) hmem
  simpa only [hH.2.2.2.2.2 i hi] using hh

theorem t11_supporting_bounds (D : Data) (H : State) (hH : Compatible D H)
    (i j : ℕ) (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : recruitmentDegree D i < D.degree i)
    (hdj : recruitmentDegree D j < D.degree j)
    (hzi : D.trait i = false) (hzj : D.trait j = true) :
    (D.degree j : ℝ) ≤ degreeTraitSum H ∧ 0 < D.degree j ∧
    (D.degree i : ℝ) ≤ 2*(H.edges.card : ℝ)-degreeTraitSum H ∧ 0 < D.degree i := by
  have hjb := sampled_degree_trait_bound D H hH j hj true hzj
  have hib := sampled_degree_trait_bound D H hH i hi false hzi
  have hq : degreeTraitSum H = (traitDegree H true : ℝ) :=
    AronowAudit.P012.degreeTraitSum_eq (Bridge.state H)
  have hpart : traitDegree H true + traitDegree H false = 2*H.edges.card :=
    (AronowAudit.P012.trait_degree_partition (Bridge.state H)).trans
      (AronowAudit.P012.degree_sum_twice_edges (Bridge.state H) hH.1.1)
  have hpartR : (traitDegree H true : ℝ) + traitDegree H false = 2*(H.edges.card : ℝ) := by
    exact_mod_cast hpart
  refine ⟨?_, by omega, ?_, by omega⟩
  · rw [hq]; exact_mod_cast hjb
  · rw [hq]
    have hibR : (D.degree i : ℝ) ≤ (traitDegree H false : ℝ) := by exact_mod_cast hib
    linarith

theorem coin_forget {D : Data} {H P : State} {i : ℕ} {coin : Bool}
    {v : Vertex} {Q : State} (h : WholeCoinReplacement D H P i coin v Q) :
    Replacement D H P i v Q := by
  cases h with
  | existing _ hv => exact Replacement.existing v hv
  | fresh _ hv t => exact Replacement.fresh v hv t

theorem printed_forget {D : Data} {H : State} {i : ℕ} {j : Vertex}
    {c₁ c₂ : Bool} {K : State} (h : WholePrintedRun D H i j c₁ c₂ K) :
    GraphProposal D false H K := by
  cases h with
  | deleteUnobserved v P hi hj hne he hr hju hp =>
    exact GraphProposal.deleteUnobserved i j v P hi hj hne he hr hju (coin_forget hp)
  | deleteObserved k hjk v w P Q hi hk hne he hr hp hq =>
    exact GraphProposal.deleteObserved i k v w P Q hi hk hne he hr (coin_forget hp) (coin_forget hq)
  | addObserved v w hi hj hne he hv hw hiv hjw =>
    exact GraphProposal.addObserved i j v w hi hj hne he hv hw hiv hjw
  | unchanged hi hj hne hd ha => exact GraphProposal.unchanged i j hi hj hne hd ha

theorem dyad_active_unique (H : State) (hH : Compatible emptyPoolData H) :
    WholeActiveEq H (dyad false true) := by
  have hD := Bridge.empty_trait_pool_counterexample.1
  have hz : ∀ i ∈ emptyPoolData.sampled,
      emptyPoolData.degree i = recruitmentDegree emptyPoolData i := by decide
  have hh := AronowAudit.P012.zero_spare_compatible_unique
    (Bridge.data emptyPoolData) hD hz (Bridge.state H) hH
  change H.vertices = sampledVertices emptyPoolData ∧
    H.edges = recruitmentEdges emptyPoolData ∧
    (∀ v ∈ H.vertices, H.trait v = (recruitmentState emptyPoolData).trait v) at hh
  refine ⟨hh.1.trans (by decide), hh.2.1.trans (by decide), ?_⟩
  intro v hv
  rw [hh.2.2 v hv]
  rw [hh.1] at hv
  simp only [sampledVertices, emptyPoolData, domainA, mem_image, mem_insert,
    mem_singleton] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  rcases hk with rfl | rfl <;> decide

theorem induced_compatible (D : Data) (H : State) (hD : Admissible D)
    (hH : Compatible D H) : InducedCompatible D (induced D H) := by
  have hg : GraphCompatible D H :=
    ⟨hH.1,hH.2.1,hH.2.2.1,hH.2.2.2.2.1,hH.2.2.2.2.2⟩
  exact (AronowAudit.P012.induced_compatibility (Bridge.data D) (Bridge.state H) hD hg).1

theorem cleanup_fixed_run (c₁ c₂ : Bool) (K : State) :
    WholePrintedRun cleanupData cleanupStart 1 (s 2) c₁ c₂ K ↔
      K = cleanup cleanupData false cleanupStart := by
  constructor
  · intro h
    cases h with
    | deleteUnobserved v P hi hj hne he hr hju hp =>
      exact False.elim (hju (by decide))
    | deleteObserved k hjk v w P Q hi hk hne he hr hp hq =>
      have hk2 : k = 2 := (Sum.inl.inj hjk).symm
      subst k
      exact False.elim (hr (by decide))
    | addObserved v w hi hj hne he hv hw hiv hjw =>
      exact False.elim (he (by decide))
    | unchanged hi hj hne hd ha => rfl
  · intro h
    subst K
    exact WholePrintedRun.unchanged (by decide) (by decide) (by decide)
      (by decide) (by decide)

/-- A sampled edge distinguishes graphs even after any allowed renaming. -/
theorem not_relabeling_of_sampled_edge (D : Data) (H K : State) (i j : ℕ)
    (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hH : {s i,s j} ∉ H.edges) (hK : {s i,s j} ∈ K.edges) :
    ¬ WholeRelabeling D H K := by
  rintro ⟨e,hfix,hv,he,ht⟩
  have him : ({s i,s j} : Finset Vertex).image e = {s i,s j} := by
    simp [hfix i hi,hfix j hj]
  rw [← he] at hK
  obtain ⟨a,ha,hea⟩ := mem_image.mp hK
  have hinj : Function.Injective (fun a : Finset Vertex => a.image e) :=
    Finset.image_injective e.injective
  exact hH ((hinj (hea.trans him.symm)) ▸ ha)


/-- T7, incidence and streaming denominators. Count each recruiter's outgoing
edges and its own incoming edge separately, using recruitment_edge_sampled and
pair_edge_eq. A chronological prefix contains exactly the earlier children;
partition all children at the current event. Admissibility removes every natural
subtraction truncation and gives remaining = b_j+s_r > 0. -/
def T7_L1 : Prop :=
  ∀ D : Data, Admissible D → ∀ order : List ℕ,
    WholeChronological D order → PWholeSchedule D order

/-- T7, triangular sum exchange. For each recruiter, interchange the sums over
ordered child pairs (event k occurs no later than event j). The suffix matching
count becomes the trait indicator times a prefix reciprocal sum. Apply the same
identity to nonmatches and rewrite (a+s)/(b+s)=1-(b-a)/(b+s). Cast the rational
finite sums to the reals. Use Finset.sum_comm, Finset.sum_filter, Rat.cast_div;
positive denominators follow from self-membership in laterChildren. -/
def T7_L2 : Prop :=
  ∀ D : Data, Admissible D → D.seeds.card < D.sampled.card →
    ∀ order : List ℕ, WholeChronological D order →
      ((pWholeForwardLow D order / ((nonseeds D).card : ℚ) : ℚ) : ℝ) = pLower D ∧
      ((pWholeForwardHigh D order / ((nonseeds D).card : ℚ) : ℚ) : ℝ) = pUpper D

/-- T7, prefix invariant of the actual rational fold. Induct over chronological
prefixes. A record initializes a new cell; a nonseed updates a distinct, already
initialized recruiter cell. Use the supplied PWholeSchedule for the residual,
and extend its reciprocal sum by the current event. Finset.sum_insert updates
the two accumulators, Function.update_self/update_of_ne the cells. Prove the
stated safety conjunct from the cell invariant. This leaf needs no endpoint
theorem: the triangular sum exchange is isolated in T7_L2. -/
def T7_L3 : Prop :=
  ∀ D : Data, Admissible D → ∀ order : List ℕ,
    WholeChronological D order → PWholeSchedule D order → PWholeInvariant D order

/-- T10, geometry of the explicit shared-neighbour construction. Unfold the
finite ranges, use card_erase_of_mem for the two omitted zero slots, and use
injectivity of u to separate owners. Recruitment edges have sampled endpoints.
Normalize unordered pairs with AronowAudit.P012.pair_edge_eq. This proves all
private/shared neighbourhoods and both induced edge sets; no compatibility or
trait argument is hidden in this leaf. -/
def T10_L1 : Prop :=
  ∀ D : Data, Admissible D → ∀ i j : ℕ,
    i ∈ D.sampled → j ∈ D.sampled → D.time i < D.time j →
    ¬ (j ∈ nonseeds D ∧ D.parent j = i) →
    recruitmentDegree D i < D.degree i → recruitmentDegree D j < D.degree j →
    R1WholeGeometry D i j

/-- T10, compatibility of the specified first graph for every trait extension.
Repeat the construction inside AronowAudit.P012.result1: merge slot (j,0)
into (i,0) in leafCompletion, and expose its exact edge/vertex sets. The existing
corrected_graph_preserves and compatible_same_graph give compatibility. An
alternative is direct incidence counting: every sampled vertex has precisely
its recruitment degree plus its specified spare incidences. -/
def T10_L2 : Prop :=
  ∀ D : Data, Admissible D → ∀ i j : ℕ,
    i ∈ D.sampled → j ∈ D.sampled → D.time i < D.time j →
    ¬ (j ∈ nonseeds D ∧ D.parent j = i) →
    recruitmentDegree D i < D.degree i → recruitmentDegree D j < D.degree j →
    ∀ τ : Vertex → Bool, (∀ k ∈ D.sampled, τ (s k) = D.trait k) →
      Compatible D (r1WholeStart D i j τ)

/-- T10, exact cleanup after the shared-neighbour move. In the intermediate
graph only u(i,0) becomes isolated among unsampled vertices; all other unsampled
vertices retain their private incident edge. Repaired cleanup keeps every
sampled vertex, including isolated seeds. Finset.ext and mem_filter therefore
identify its vertex set as precisely H.vertices.erase (u i 0). Edges and traits
are definitional. This is the new set calculation needed to apply the already
proved corrected graph proposal, rather than reproving its compatibility. -/
def T10_L3 : Prop :=
  ∀ D : Data, Admissible D → ∀ i j : ℕ,
    i ∈ D.sampled → j ∈ D.sampled → D.time i < D.time j →
    ¬ (j ∈ nonseeds D ∧ D.parent j = i) →
    recruitmentDegree D i < D.degree i → recruitmentDegree D j < D.degree j →
    ∀ τ : Vertex → Bool,
      let H := r1WholeStart D i j τ
      cleanup D true (addEdge (removeEdge (removeEdge H (s i) (u i 0))
        (s j) (u i 0)) (s i) (s j)) = r1WholeEnd D i j τ

/-- T11, legal swap for arbitrary private slots. Generalize the indices 0 in
AronowAudit.P012.private_leaf_swap_graph to x,y, using private_leaf_member at
those slots. The owners are distinct because their observed traits differ.
Delete the two present edges, add the two absent cross edges, count degrees
vertex by vertex, and transfer arbitrary other traits with compatible_same_graph.
No condition on the edge between the sampled owners is needed. -/
def T11_L1 : Prop :=
  ∀ D : Data, Admissible D → ∀ i j x y : ℕ,
    i ∈ D.sampled → j ∈ D.sampled →
    recruitmentDegree D i < D.degree i → recruitmentDegree D j < D.degree j →
    D.trait i = false → D.trait j = true → x < spare D i → y < spare D j →
    ∀ H : State, H.vertices = (leafCompletion D true).vertices →
      H.edges = (leafCompletion D true).edges →
      (∀ k ∈ D.sampled, H.trait (s k) = D.trait k) →
      let K := wholeSwap H i j x y
      Compatible D H ∧ Compatible D K ∧
      {s i,u i x} ∈ H.edges ∧ {s j,u j y} ∈ H.edges ∧
      {s i,u j y} ∉ H.edges ∧ {s j,u i x} ∉ H.edges ∧
      H.vertices = K.vertices ∧ H.trait = K.trait ∧ H.edges.card = K.edges.card ∧
      ∀ v, graphDegree H v = graphDegree K v

/-- T11, numerator change for arbitrary slots. Generalize
AronowAudit.P012.private_swap_true_edge_count: only the removed {j,u(j,y)}
has two true endpoints; the other removed/inserted edges have a false endpoint.
Thus edgeCount true drops by one. Apply numerator_edge_identity and
same_degree_h_denominator to cancel the degree-weighted null term. Simplicity
and all preservation facts required for those identities are explicit premises. -/
def T11_L2 : Prop :=
  ∀ (H : State) (i j x y : ℕ),
    let K := wholeSwap H i j x y
    Simple H → Simple K → {s j,u j y} ∈ H.edges →
    H.trait (s i) = false → H.trait (s j) = true →
    H.trait (u i x) = false → H.trait (u j y) = true →
    H.vertices = K.vertices → H.trait = K.trait → H.edges.card = K.edges.card →
    (∀ v, graphDegree H v = graphDegree K v) → hNumerator H-hNumerator K = 2

/-- T1(a), all executions at the specified initial i,j, including both coins.
Invert WholePrintedRun. The edge test forces deleteUnobserved; the other
constructors contradict concrete membership or the unsampled j. The current
replacement pool is empty, so invert WholeCoinReplacement to obtain precisely
one fresh vertex and trait. Conversely construct that branch for any fresh
vertex and either coin. The second coin is unused, as in the listing. -/
def T1_L1 : Prop :=
  ∀ c₁ c₂ K,
    WholePrintedRun proposalData proposalStart 1 (u 3 0) c₁ c₂ K ↔
      ∃ v, v ∉ proposalStart.vertices ∧ ∃ t : Bool,
        K = cleanup proposalData false (wholeBadPending proposalStart 1 (u 3 0) v t)

/-- T1(b), the second execution normal form. Use the same constructor inversion
as T1_L1, with the concrete empty pool at recruiter 2. All fresh identifiers,
both traits and both coin outcomes are quantified; there is no identification
of an arbitrary fresh label with the displayed name 5. -/
def T1_L2 : Prop :=
  ∀ c₁ c₂ K,
    WholePrintedRun proposalDataB proposalStartB 2 (u 4 0) c₁ c₂ K ↔
      ∃ v, v ∉ proposalStartB.vertices ∧ ∃ t : Bool,
        K = cleanup proposalDataB false (wholeBadPending proposalStartB 2 (u 4 0) v t)

/-- T1(a,b), output invariants for every fresh identifier. Freshness separates
the inserted name from the finitely many existing names. Expand addVertex,
removeEdge, addEdge and cleanup; every vertex has a retained incident edge.
The old unsampled vertex has only the fresh neighbour, while all sampled
degrees and traits are retained. Prove incompatibility using Definition 3(3)
or the no-unsampled-edge rule. Split Bool only if needed; no function values
outside the active vertex set are constrained. -/
def T1_L3 : Prop :=
  (∀ v, v ∉ proposalStart.vertices → ∀ t : Bool,
    WholeBadOutput proposalData proposalStart 1 (u 3 0) v t) ∧
  (∀ v, v ∉ proposalStartB.vertices → ∀ t : Bool,
    WholeBadOutput proposalDataB proposalStartB 2 (u 4 0) v t)

/-- T1(a,b), independence of fresh names. Use Equiv.swap of the arbitrary fresh
name with the displayed fresh name (u 4 0 in a, u 5 0 in b). It fixes every
old vertex and every sampled identity. Finset.image_insert/image_pair identify
the vertex and edge images; Function.update gives active trait transport.
The named cleanup identities are finite computations. -/
def T1_L4 : Prop :=
  (∀ v, v ∉ proposalStart.vertices → ∀ t : Bool,
    WholeRelabeling proposalData (wholeBadPending proposalStart 1 (u 3 0) v t)
      (proposalBad t)) ∧
  (∀ v, v ∉ proposalStartB.vertices → ∀ t : Bool,
    WholeRelabeling proposalDataB (wholeBadPending proposalStartB 2 (u 4 0) v t)
      (proposalBadB t))

theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3) :
    T7WholeStatement := by
  refine ⟨⟨Bridge.exact_p_region, ?_⟩, ?_, chronological_exists,
    fun D hD same i hi k hk => leaf_neighbors D hD same i k hi hk⟩
  · intro D hD hN j hj
    have hm : j ∈ laterChildren D j := mem_filter.mpr ⟨hj, rfl, le_rfl⟩
    exact ⟨hm, card_pos.mpr ⟨j,hm⟩⟩
  · intro D hD hN order ho
    have hinv := h3 D hD order ho (h1 D hD order ho)
    obtain ⟨hcount,hlow,hhigh,hcell⟩ := hinv.1 order [] (by simp)
    have hf : order.toFinset.filter (fun j => j ∈ nonseeds D) = nonseeds D := by
      rw [ho.2.1]
      ext j
      simp only [mem_filter, nonseeds, mem_sdiff]
      tauto
    rw [hf] at hcount
    have hpos : 0 < (nonseeds D).card := by
      rw [nonseeds, card_sdiff_of_subset hD.1]
      omega
    have hlen : order.length = D.sampled.card := by
      rw [← List.toFinset_card_of_nodup ho.1, ho.2.1]
    obtain ⟨hlo,hhi⟩ := h2 D hD hN order ho
    have hclock := run_clocks (order.map (pWholeRecord D)) pWholeInitial
    have hrecip := run_count_reciprocals (order.map (pWholeRecord D)) pWholeInitial rfl
    change (pWholeRun D order).count = (pWholeRun D order).reciprocals at hrecip
    refine ⟨?_, ?_, hcount, hcount ▸ hpos, ?_, hrecip ▸ hcount, ?_, ?_, hinv.2⟩
    · simpa only [pWholeOutput, hcount, hlow] using hlo
    · simpa only [pWholeOutput, hcount, hhigh] using hhi
    · rw [run_reads, hlen]
    · have hc : (pWholeRun D order).work ≤ 32 * order.length := by
        simpa only [pWholeRun, pWholeInitial, List.length_map, Nat.zero_add] using hclock.2.2
      omega
    · intro pre post heq
      obtain ⟨hc,hl,hh,hcells⟩ := hinv.1 pre post heq
      have hsub : pre.toFinset ⊆ D.sampled := by
        intro r hr
        rw [← ho.2.1, heq]
        simp only [List.toFinset_append, mem_union]
        exact Or.inl hr
      refine ⟨run_reads D pre, pre.toFinset, rfl, card_le_card hsub, ?_⟩
      intro r
      rw [hcells r]
      split <;> simp_all

theorem T9_assembly : T9WholeStatement := by
  have hqH : degreeTraitSum result2BadStart = 5 := by
    norm_num [degreeTraitSum, result2BadStart, graphDegree, z, s, u,
      Finset.filter_insert, Finset.filter_singleton]
  have hqK : degreeTraitSum result2BadEnd = 3 := by
    norm_num [degreeTraitSum, result2BadEnd, result2BadStart, removeEdge, addEdge,
      graphDegree, z, s, u, Finset.filter_insert, Finset.filter_singleton,
      Finset.filter_erase]
  have hdH : hDenominator result2BadStart = 35/12 := by
    have h := AronowAudit.P012.denominator_sum_identity (Bridge.state result2BadStart)
    change hDenominator result2BadStart = degreeTraitSum result2BadStart -
      degreeTraitSum result2BadStart ^ 2 / (2 * (result2BadStart.edges.card : ℝ)) at h
    rw [hqH] at h
    norm_num [result2BadStart, s, u] at h
    exact h
  have hdK : hDenominator result2BadEnd = 15/8 := by
    have h := AronowAudit.P012.denominator_sum_identity (Bridge.state result2BadEnd)
    change hDenominator result2BadEnd = degreeTraitSum result2BadEnd -
      degreeTraitSum result2BadEnd ^ 2 / (2 * (result2BadEnd.edges.card : ℝ)) at h
    rw [hqK] at h
    norm_num [result2BadEnd, result2BadStart, removeEdge, addEdge, s, u] at h
    exact h
  exact ⟨⟨Bridge.result2_proof_counterexample, by decide⟩, rfl, hqH, hqK, hdH, hdK,
    by rw [hdH]; norm_num, by rw [hdK]; norm_num, by rw [hdH,hdK]; norm_num⟩

theorem T10_assembly (h1 : T10_L1) (h2 : T10_L2) (h3 : T10_L3) :
    T10WholeStatement := by
  intro D hD i j hi hj ht hr hdi hdj
  have hg := h1 D hD i j hi hj ht hr hdi hdj
  refine ⟨hg, ?_⟩
  intro τ hτ
  let H := r1WholeStart D i j τ
  let K := r1WholeEnd D i j τ
  have hH : Compatible D H := h2 D hD i j hi hj ht hr hdi hdj τ hτ
  have hclean := h3 D hD i j hi hj ht hr hdi hdj τ
  obtain ⟨hu,hn,hprivate,habs,hpres,hindH,hindK⟩ := hg.2.2.2.2.2.2 τ
  change u i 0 ∈ unsampled D H at hu
  change wholeNeighbors H (u i 0) = {s i,s j} at hn
  have hij : i ≠ j := by intro he; subst j; exact lt_irrefl _ ht
  have hei : {s i,u i 0} ∈ H.edges := by
    have hh : s i ∈ wholeNeighbors H (u i 0) := by rw [hn]; simp
    simpa only [Finset.pair_comm] using (mem_filter.mp hh).2
  have hej : {s j,u i 0} ∈ H.edges := by
    have hh : s j ∈ wholeNeighbors H (u i 0) := by rw [hn]; simp
    simpa only [Finset.pair_comm] using (mem_filter.mp hh).2
  have hp := GraphProposal.addObserved (D := D) (repaired := true) (H := H)
    i (s j) (u i 0) (u i 0) hi (hH.2.1 (mem_image_of_mem s hj))
    (by simpa only [s, ne_eq, Sum.inl.injEq] using hij) habs hu hu hei hej
  have hK : Compatible D K := by
    have hh := Bridge.corrected_proposal_preserves D H _ hD hH (Or.inl hp)
    rw [hclean] at hh
    exact hh
  have hne : H ≠ K := by
    intro he
    have he' := congrArg State.edges he
    exact habs (he'.symm ▸ hpres)
  have hine : induced D H ≠ induced D K := by
    intro he
    have he' := congrArg State.edges he
    rw [hindH, hindK] at he'
    exact hg.2.2.1 (he'.symm ▸ mem_insert_self _ _)
  exact ⟨hH,hK,rfl,rfl,rfl,hclean,induced_compatible D H hD hH,
    induced_compatible D K hD hK,
    not_relabeling_of_sampled_edge D H K i j hi hj habs hpres,hne,hine⟩

theorem T11_assembly (h1 : T11_L1) (h2 : T11_L2) : T11WholeStatement := by
  refine ⟨⟨Bridge.result2, Bridge.result2_swap_formula, Bridge.a1_exact_instance⟩,
    ?_, fun D hD same i hi k hk => leaf_neighbors D hD same i k hi hk⟩
  intro D hD i j x y hi hj hdi hdj hzi hzj hx hy H hv he htraits hu1 hu2
  let K := wholeSwap H i j x y
  obtain ⟨hH,hK,hE1,hE2,hE3,hE4,hV,hT,hM,hG⟩ :=
    h1 D hD i j x y hi hj hdi hdj hzi hzj hx hy H hv he htraits
  have hb := t11_supporting_bounds D H hH i j hi hj hdi hdj hzi hzj
  refine ⟨?_, hb⟩
  have hden : hDenominator H = degreeTraitSum H -
      degreeTraitSum H ^ 2 / (2 * (H.edges.card : ℝ)) :=
    AronowAudit.P012.denominator_sum_identity (Bridge.state H)
  have hsame : hDenominator H = hDenominator K :=
    (AronowAudit.P012.same_degree_h_denominator (Bridge.state H) (Bridge.state K)
      hV hT hM hG).2
  have hm : 0 < H.edges.card := by
    have hle : graphDegree H (s j) ≤ H.edges.card := card_le_card (filter_subset _ _)
    rw [hH.2.2.2.2.2 j hj] at hle
    omega
  have hmR : (0 : ℝ) < 2*(H.edges.card : ℝ) := by positivity
  have hQ : 0 < degreeTraitSum H := by
    have hd : (0 : ℝ) < D.degree j := by exact_mod_cast hb.2.1
    exact lt_of_lt_of_le hd hb.1
  have hQ' : 0 < 2*(H.edges.card : ℝ)-degreeTraitSum H := by
    have hd : (0 : ℝ) < D.degree i := by exact_mod_cast hb.2.2.2
    exact lt_of_lt_of_le hd hb.2.2.1
  have hfact : hDenominator H =
      degreeTraitSum H * (2*(H.edges.card : ℝ)-degreeTraitSum H) /
        (2*(H.edges.card : ℝ)) := by
    rw [hden]
    field_simp
  have hpos : 0 < hDenominator H := by
    rw [hfact]
    exact div_pos (mul_pos hQ hQ') hmR
  have hnum : hNumerator H-hNumerator K = 2 :=
    h2 H i j x y hH.1.1 hK.1.1 hE2 ((htraits i hi).trans hzi)
      ((htraits j hj).trans hzj) hu1 hu2 hV hT hM hG
  have hdiff : hValue H-hValue K = 2/hDenominator H := by
    rw [hValue,hValue,← hsame,← sub_div,hnum]
  have hneq : hValue H ≠ hValue K := by
    intro hh
    have hpositive : (0 : ℝ) < 2/hDenominator H := div_pos (by norm_num) hpos
    rw [← hdiff,hh,sub_self] at hpositive
    exact lt_irrefl _ hpositive
  have hdefined : HomophilyDefined H := ⟨hm,ne_of_gt hpos⟩
  have hkdefined : HomophilyDefined K := ⟨hM ▸ hm,hsame ▸ ne_of_gt hpos⟩
  refine ⟨hH,hK,hE1,hE2,hE3,hE4,hV,hT,hM,hG,hden,hfact,hsame,hpos,?_,
    hdiff,hneq,hdefined,hkdefined⟩
  rw [hdiff]
  ring

theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) (h3 : T1_L3) (h4 : T1_L4) :
    T1WholeStatement := by
  refine ⟨⟨Bridge.proposal_counterexample, Bridge.proposal_counterexample_b,
    Bridge.cleanup_counterexample, Bridge.empty_trait_pool_counterexample⟩,
    ?_, h1, h2, ?_, ?_, cleanup_fixed_run, ?_, dyad_active_unique⟩
  · intro D H i j c₁ c₂ K h
    exact printed_forget h
  · intro v hv t
    exact ⟨h3.1 v hv t,h4.1 v hv t⟩
  · intro v hv t
    exact ⟨h3.2 v hv t,h4.2 v hv t⟩
  · decide

end
end SAP.P012a.WH.W1
