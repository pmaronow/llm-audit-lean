import SAP.P012a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W2.P.T6_L2

open SAP.P012a Finset
open scoped Classical
noncomputable section

private def childEdge (D : Data) (j : ℕ) : Finset Vertex :=
  {s (D.parent j), s j}

private def childOnes (D : Data) (j : ℕ) : Prop :=
  D.trait (D.parent j) = true ∧ D.trait j = true

private def childZeros (D : Data) (j : ℕ) : Prop :=
  D.trait (D.parent j) = false ∧ D.trait j = false

private def childMixed (D : Data) (j : ℕ) : Prop :=
  D.trait (D.parent j) ≠ D.trait j

private theorem scanV_d0 (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanVertices D xs q).d0 =
      q.d0 + (xs.map (fun i => if D.trait i = false then D.degree i else 0)).sum := by
  induction xs generalizing q with
  | nil => simp [w2ScanVertices]
  | cons i xs ih =>
    simp only [w2ScanVertices, List.map_cons, List.sum_cons]
    rw [ih]
    cases h : D.trait i <;> simp [w2VertexStep, h] <;> omega

private theorem scanV_d1 (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanVertices D xs q).d1 =
      q.d1 + (xs.map (fun i => if D.trait i = true then D.degree i else 0)).sum := by
  induction xs generalizing q with
  | nil => simp [w2ScanVertices]
  | cons i xs ih =>
    simp only [w2ScanVertices, List.map_cons, List.sum_cons]
    rw [ih]
    cases h : D.trait i <;> simp [w2VertexStep, h] <;> omega

private theorem scanV_ones (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanVertices D xs q).ones = q.ones := by
  induction xs generalizing q with
  | nil => rfl
  | cons i xs ih => cases h : D.trait i <;> simp [w2ScanVertices, w2VertexStep, h, ih]

private theorem scanV_zeros (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanVertices D xs q).zeros = q.zeros := by
  induction xs generalizing q with
  | nil => rfl
  | cons i xs ih => cases h : D.trait i <;> simp [w2ScanVertices, w2VertexStep, h, ih]

private theorem scanV_mixed (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanVertices D xs q).mixed = q.mixed := by
  induction xs generalizing q with
  | nil => rfl
  | cons i xs ih => cases h : D.trait i <;> simp [w2ScanVertices, w2VertexStep, h, ih]

private theorem scanE_d0 (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanEdges D xs q).d0 = q.d0 := by
  induction xs generalizing q with
  | nil => rfl
  | cons j xs ih =>
    have h := ih (w2EdgeStep D j q)
    cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
      simpa [w2ScanEdges, w2EdgeStep, hp, hj] using h

private theorem scanE_d1 (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanEdges D xs q).d1 = q.d1 := by
  induction xs generalizing q with
  | nil => rfl
  | cons j xs ih =>
    have h := ih (w2EdgeStep D j q)
    cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
      simpa [w2ScanEdges, w2EdgeStep, hp, hj] using h

private theorem scanE_ones (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanEdges D xs q).ones =
      q.ones + (xs.map (fun j => if childOnes D j then 1 else 0)).sum := by
  induction xs generalizing q with
  | nil => simp [w2ScanEdges]
  | cons j xs ih =>
    simp only [w2ScanEdges, List.map_cons, List.sum_cons]
    rw [ih]
    cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
      simp [w2EdgeStep, childOnes, hp, hj] <;> omega

private theorem scanE_zeros (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanEdges D xs q).zeros =
      q.zeros + (xs.map (fun j => if childZeros D j then 1 else 0)).sum := by
  induction xs generalizing q with
  | nil => simp [w2ScanEdges]
  | cons j xs ih =>
    simp only [w2ScanEdges, List.map_cons, List.sum_cons]
    rw [ih]
    cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
      simp [w2EdgeStep, childZeros, hp, hj] <;> omega

private theorem scanE_mixed (D : Data) (xs : List ℕ) (q : W2HCounts) :
    (w2ScanEdges D xs q).mixed =
      q.mixed + (xs.map (fun j => if childMixed D j then 1 else 0)).sum := by
  induction xs generalizing q with
  | nil => simp [w2ScanEdges]
  | cons j xs ih =>
    simp only [w2ScanEdges, List.map_cons, List.sum_cons]
    rw [ih]
    cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
      simp [w2EdgeStep, childMixed, hp, hj] <;> omega

private theorem child_edge_injective (D : Data) (hD : Admissible D) :
    Set.InjOn (childEdge D) (nonseeds D) := by
  intro j hj k hk heq
  have hjm : s j ∈ childEdge D k := by rw [← heq]; simp [childEdge]
  have hkm : s k ∈ childEdge D j := by rw [heq]; simp [childEdge]
  simp only [childEdge, Finset.mem_insert, Finset.mem_singleton, s, Sum.inl.injEq] at hjm hkm
  rcases hjm with hjp | hjk
  · rcases hkm with hkp | hkj
    · have htj := (hD.2.2.1 j hj).2
      have htk := (hD.2.2.1 k hk).2
      rw [← hkp] at htj
      rw [← hjp] at htk
      omega
    · exact hkj.symm
  · exact hjk

private theorem child_edge_traits (D : Data) (j : ℕ) :
    (∀ v ∈ childEdge D j, (recruitmentState D).trait v = true) ↔ childOnes D j := by
  cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
    simp [childEdge, childOnes, recruitmentState, s, hp, hj]

private theorem child_edge_zeros (D : Data) (j : ℕ) :
    (∀ v ∈ childEdge D j, (recruitmentState D).trait v = false) ↔ childZeros D j := by
  cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
    simp [childEdge, childZeros, recruitmentState, s, hp, hj]

private theorem child_edge_mixed (D : Data) (j : ℕ) :
    ((∃ v ∈ childEdge D j, (recruitmentState D).trait v = true) ∧
      ∃ v ∈ childEdge D j, (recruitmentState D).trait v = false) ↔ childMixed D j := by
  cases hp : D.trait (D.parent j) <;> cases hj : D.trait j <;>
    simp [childEdge, childMixed, recruitmentState, s, hp, hj]

private theorem recruitment_ones_image (D : Data) :
    ((nonseeds D).filter (childOnes D)).image (childEdge D) =
      (recruitmentEdges D).filter
        (fun e => ∀ v ∈ e, (recruitmentState D).trait v = true) := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩,
      (child_edge_traits D j).2 (Finset.mem_filter.mp hj).2⟩
  · intro he
    rcases Finset.mem_filter.mp he with ⟨he, hc⟩
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, (child_edge_traits D j).1 hc⟩, rfl⟩

private theorem recruitment_zeros_image (D : Data) :
    ((nonseeds D).filter (childZeros D)).image (childEdge D) =
      (recruitmentEdges D).filter
        (fun e => ∀ v ∈ e, (recruitmentState D).trait v = false) := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩,
      (child_edge_zeros D j).2 (Finset.mem_filter.mp hj).2⟩
  · intro he
    rcases Finset.mem_filter.mp he with ⟨he, hc⟩
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, (child_edge_zeros D j).1 hc⟩, rfl⟩

private theorem recruitment_mixed_image (D : Data) :
    ((nonseeds D).filter (childMixed D)).image (childEdge D) =
      (recruitmentEdges D).filter
        (fun e => (∃ v ∈ e, (recruitmentState D).trait v = true) ∧
          ∃ v ∈ e, (recruitmentState D).trait v = false) := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩,
      (child_edge_mixed D j).2 (Finset.mem_filter.mp hj).2⟩
  · intro he
    rcases Finset.mem_filter.mp he with ⟨he, hc⟩
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, (child_edge_mixed D j).1 hc⟩, rfl⟩

private theorem recruitment_ones_sum (D : Data) (hD : Admissible D) :
    a D = ∑ j ∈ nonseeds D, if childOnes D j then 1 else 0 := by
  change ((recruitmentEdges D).filter
    (fun e => ∀ v ∈ e, (recruitmentState D).trait v = true)).card = _
  rw [← recruitment_ones_image D]
  have hsub : (↑((nonseeds D).filter (childOnes D)) : Set ℕ) ⊆ (↑(nonseeds D) : Set ℕ) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hi := (child_edge_injective D hD).mono hsub
  rw [Finset.card_image_iff.mpr hi, Finset.card_filter]

private theorem recruitment_zeros_sum (D : Data) (hD : Admissible D) :
    b D = ∑ j ∈ nonseeds D, if childZeros D j then 1 else 0 := by
  change ((recruitmentEdges D).filter
    (fun e => ∀ v ∈ e, (recruitmentState D).trait v = false)).card = _
  rw [← recruitment_zeros_image D]
  have hsub : (↑((nonseeds D).filter (childZeros D)) : Set ℕ) ⊆ (↑(nonseeds D) : Set ℕ) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hi := (child_edge_injective D hD).mono hsub
  rw [Finset.card_image_iff.mpr hi, Finset.card_filter]

private theorem recruitment_mixed_sum (D : Data) (hD : Admissible D) :
    cR D = ∑ j ∈ nonseeds D, if childMixed D j then 1 else 0 := by
  change ((recruitmentEdges D).filter
    (fun e => (∃ v ∈ e, (recruitmentState D).trait v = true) ∧
      ∃ v ∈ e, (recruitmentState D).trait v = false)).card = _
  rw [← recruitment_mixed_image D]
  have hsub : (↑((nonseeds D).filter (childMixed D)) : Set ℕ) ⊆ (↑(nonseeds D) : Set ℕ) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hi := (child_edge_injective D hD).mono hsub
  rw [Finset.card_image_iff.mpr hi, Finset.card_filter]

private theorem vertex_list_sum_false (D : Data) (xs : List ℕ)
    (hn : xs.Nodup) (he : xs.toFinset = D.sampled) :
    (xs.map (fun i => if D.trait i = false then D.degree i else 0)).sum =
      sampledTraitDegree D false := by
  rw [← List.sum_toFinset (f := fun i => if D.trait i = false then D.degree i else 0) hn]
  rw [he]
  simpa [sampledTraitDegree] using
    (Finset.sum_filter (s := D.sampled) (p := fun i => D.trait i = false)
      (f := fun i => D.degree i)).symm

private theorem vertex_list_sum_true (D : Data) (xs : List ℕ)
    (hn : xs.Nodup) (he : xs.toFinset = D.sampled) :
    (xs.map (fun i => if D.trait i = true then D.degree i else 0)).sum =
      sampledTraitDegree D true := by
  rw [← List.sum_toFinset (f := fun i => if D.trait i = true then D.degree i else 0) hn]
  rw [he]
  simpa [sampledTraitDegree] using
    (Finset.sum_filter (s := D.sampled) (p := fun i => D.trait i = true)
      (f := fun i => D.degree i)).symm

theorem proof : SAP.P012a.WH.W2.T6_L2 := by
  intro D hD vertices children hen
  obtain ⟨hnv, hev, hnc, hec⟩ := hen
  let q := w2Scan D vertices children
  have hv0 := scanV_d0 D vertices {}
  have hv1 := scanV_d1 D vertices {}
  have hd0 := scanE_d0 D children (w2ScanVertices D vertices {})
  have hd1 := scanE_d1 D children (w2ScanVertices D vertices {})
  have hones := scanE_ones D children (w2ScanVertices D vertices {})
  have hzeros := scanE_zeros D children (w2ScanVertices D vertices {})
  have hmixed := scanE_mixed D children (w2ScanVertices D vertices {})
  change q.d0 = sampledTraitDegree D false ∧ q.d1 = sampledTraitDegree D true ∧
    q.ones = a D ∧ q.zeros = b D ∧ q.mixed = cR D
  have hq0 : q.d0 = sampledTraitDegree D false := by
    change (w2ScanEdges D children (w2ScanVertices D vertices {})).d0 = _
    rw [hd0, hv0]
    simpa using vertex_list_sum_false D vertices hnv hev
  have hq1 : q.d1 = sampledTraitDegree D true := by
    change (w2ScanEdges D children (w2ScanVertices D vertices {})).d1 = _
    rw [hd1, hv1]
    simpa using vertex_list_sum_true D vertices hnv hev
  have hqa : q.ones = a D := by
    change (w2ScanEdges D children (w2ScanVertices D vertices {})).ones = _
    rw [hones, scanV_ones]
    rw [← List.sum_toFinset (f := fun j => if childOnes D j then 1 else 0) hnc, hec]
    simpa using (recruitment_ones_sum D hD).symm
  have hqb : q.zeros = b D := by
    change (w2ScanEdges D children (w2ScanVertices D vertices {})).zeros = _
    rw [hzeros, scanV_zeros]
    rw [← List.sum_toFinset (f := fun j => if childZeros D j then 1 else 0) hnc, hec]
    simpa using (recruitment_zeros_sum D hD).symm
  have hqc : q.mixed = cR D := by
    change (w2ScanEdges D children (w2ScanVertices D vertices {})).mixed = _
    rw [hmixed, scanV_mixed]
    rw [← List.sum_toFinset (f := fun j => if childMixed D j then 1 else 0) hnc, hec]
    simpa using (recruitment_mixed_sum D hD).symm
  exact ⟨hq0, hq1, hqa, hqb, hqc⟩

end
end SAP.P012a.WH.W2.P.T6_L2

theorem SAP.P012a.WH.W2.T6_L2_proof : SAP.P012a.WH.W2.T6_L2 :=
  SAP.P012a.WH.W2.P.T6_L2.proof
