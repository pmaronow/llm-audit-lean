import SAP.P012a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P012a Finset
open scoped Classical
noncomputable section

theorem SAP.P012a.WH.W2.T2_L2_proof : SAP.P012a.WH.W2.T2_L2 := by
  intro D H i j v w P Q hD hH hi hj hne he hr hp hq
  let R := removeEdge H (s i) (s j)
  let A := addEdge P (s i) v
  let B := addEdge Q (s j) w
  let d := SAP.P012a.Bridge.data D
  let h := SAP.P012a.Bridge.state H
  let r := AronowAudit.P012.removeEdge h (AronowAudit.P012.s i) (AronowAudit.P012.s j)
  let p := SAP.P012a.Bridge.state P
  let a := AronowAudit.P012.addEdge p (AronowAudit.P012.s i) v
  have hH' : AronowAudit.P012.Compatible d h := by
    simpa [d, h] using hH
  have hbase : AronowAudit.P012.ProposalBase d h :=
    ⟨hH'.1, hH'.2.1, hH'.2.2.1, hH'.2.2.2.1⟩
  have hr' : {AronowAudit.P012.s i, AronowAudit.P012.s j} ∉ AronowAudit.P012.recruitmentEdges d := by
    simpa [d, SAP.P012a.Bridge.s_eq] using hr
  have hL := AronowAudit.P012.remove_edge_base d h (AronowAudit.P012.s i) (AronowAudit.P012.s j) hbase hr'
  have hpool₁ : ∀ z ∈ AronowAudit.P012.replacementPool d h i,
      {AronowAudit.P012.s i, z} ∉ r.edges := by
    intro z hz hze
    have hz' : z ∈ replacementPool D H i := by simpa [d, h] using hz
    have hze' : {s i, z} ∈ R.edges := by simpa [r, h] using hze
    exact (mem_filter.mp hz').2 (mem_erase.mp hze').2
  have hp' : AronowAudit.P012.Replacement d h r i v (SAP.P012a.Bridge.state P) := by
    simpa [d, h, r, SAP.P012a.Bridge.s_eq] using SAP.P012a.Bridge.replacement_forward hp
  have hpropsP := AronowAudit.P012.replacement_properties d h r p i v hH' hL
    (by intro x hx; exact hx) hpool₁ hp'
  have hvertsP : R.vertices ⊆ P.vertices := by
    simpa [r, h, p, R] using hpropsP.2.1
  have hVP : v ∈ P.vertices := by simpa [p] using hpropsP.2.2.1
  have hUS : v ∉ sampledVertices D := by simpa [d] using hpropsP.2.2.2.1
  have hEdgesP : P.edges = R.edges := by
    simpa [r, h, p, R] using hpropsP.2.2.2.2.1
  have hNoP : {s i, v} ∉ P.edges := by simpa [p, SAP.P012a.Bridge.s_eq] using hpropsP.2.2.2.2.2
  have hAltP : (v ∈ replacementPool D H i ∧ P = R) ∨
      (v ∉ R.vertices ∧ ∃ t : Bool, P = addVertex R v t) := by
    cases hp with
    | existing hv => exact Or.inl ⟨hv, rfl⟩
    | fresh hv t => exact Or.inr ⟨hv, t, rfl⟩
  have hFactsP : W2ReplacementFacts D H R i v P :=
    ⟨hVP, hUS, hEdgesP, hNoP, hAltP⟩
  have hsampleNe : ∀ x, x ∉ sampledVertices D → ∀ k ∈ D.sampled, s k ≠ x := by
    intro x hx k hk heq
    exact hx (heq ▸ mem_image_of_mem s hk)
  have hnv := hsampleNe v hUS i hi
  have hnv' : s i ≠ v := by simpa using hnv
  have hA' := AronowAudit.P012.add_edge_base d p i v hpropsP.1 hi hVP hnv'
  have hneqPool : ∀ z ∈ replacementPool D H j, {s j, z} ∉ A.edges := by
    intro z hz hze
    have hneq : ({s j, z} : Finset Vertex) ≠ {s i, v} := by
      intro heq
      have hs : s j ∈ ({s i, v} : Finset Vertex) := heq ▸ (by simp)
      rcases mem_insert.mp hs with hs | hs
      · exact hne (Sum.inl.inj hs.symm)
      · exact hsampleNe v hUS j hj (mem_singleton.mp hs)
    rcases mem_insert.mp hze with heq | hze
    · exact hneq heq
    · rw [hEdgesP] at hze
      exact (mem_filter.mp hz).2 (mem_erase.mp hze).2
  have hq' : AronowAudit.P012.Replacement d h a j w (SAP.P012a.Bridge.state Q) := by
    simpa [d, h, a, p, A, SAP.P012a.Bridge.s_eq] using SAP.P012a.Bridge.replacement_forward hq
  have hvertsQ : h.vertices ⊆ a.vertices := hpropsP.2.1
  have hpool₂ : ∀ z ∈ AronowAudit.P012.replacementPool d h j, {s j, z} ∉ a.edges := by
    intro z hz hze
    have hz' : z ∈ replacementPool D H j := by simpa [d, h] using hz
    have hze' : {s j, z} ∈ A.edges := by simpa [a, p, A] using hze
    exact hneqPool z hz' hze'
  have hpropsQ := AronowAudit.P012.replacement_properties d h a
    (SAP.P012a.Bridge.state Q) j w hH' hA' hvertsQ hpool₂ hq'
  have hVQ : w ∈ Q.vertices := by simpa using hpropsQ.2.2.1
  have hUSQ : w ∉ sampledVertices D := by simpa [d] using hpropsQ.2.2.2.1
  have hEdgesQ : Q.edges = A.edges := by simpa [a, p, A] using hpropsQ.2.2.2.2.1
  have hNoQ : {s j, w} ∉ Q.edges := by simpa [SAP.P012a.Bridge.s_eq] using hpropsQ.2.2.2.2.2
  have hAltQ : (w ∈ replacementPool D H j ∧ Q = A) ∨
      (w ∉ A.vertices ∧ ∃ t : Bool, Q = addVertex A w t) := by
    cases hq with
    | existing hw => exact Or.inl ⟨hw, rfl⟩
    | fresh hw t => exact Or.inr ⟨hw, t, rfl⟩
  have hFactsQ : W2ReplacementFacts D H A j w Q :=
    ⟨hVQ, hUSQ, hEdgesQ, hNoQ, hAltQ⟩
  have hsampleNe' : ∀ x, x ∉ AronowAudit.P012.sampledVertices d →
      ∀ k ∈ d.sampled, AronowAudit.P012.s k ≠ x := by
    intro x hx k hk heq
    exact hx (heq ▸ mem_image_of_mem AronowAudit.P012.s hk)
  have hdegR' : ∀ k ∈ d.sampled,
      AronowAudit.P012.graphDegree r (AronowAudit.P012.s k) + (if k = i then 1 else 0) +
        (if k = j then 1 else 0) = d.degree k := by
    intro k hk
    have he' : {AronowAudit.P012.s i, AronowAudit.P012.s j} ∈ h.edges := by
      simpa [h, SAP.P012a.Bridge.s_eq] using he
    have hd := AronowAudit.P012.degree_remove_step h
      (AronowAudit.P012.s i) (AronowAudit.P012.s j) (AronowAudit.P012.s k) he'
    have hHdeg' : AronowAudit.P012.graphDegree h (AronowAudit.P012.s k) = d.degree k := by
      simpa only [SAP.P012a.Bridge.s_eq] using hH'.2.2.2.2.2 k hk
    rw [hHdeg'] at hd
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [r, AronowAudit.P012.s, hki, hkj, hne, Ne.symm hne] at hd ⊢ <;> omega
  have hdegP' : ∀ x : AronowAudit.P012.Vertex,
      AronowAudit.P012.graphDegree p x = AronowAudit.P012.graphDegree r x := by
    intro x
    simp only [AronowAudit.P012.graphDegree, hpropsP.2.2.2.2.1]
  have hdegA' : ∀ k ∈ d.sampled,
      AronowAudit.P012.graphDegree a (AronowAudit.P012.s k) + (if k = j then 1 else 0) = d.degree k := by
    intro k hk
    have hd := AronowAudit.P012.degree_add_step p (AronowAudit.P012.s i) v
      (AronowAudit.P012.s k) hpropsP.2.2.2.2.2
    rw [hdegP' (AronowAudit.P012.s k)] at hd
    have hrdeg := hdegR' k hk
    have hkv := hsampleNe' v (by simpa [d] using hUS) k hk
    simp only [mem_insert, mem_singleton, hkv, or_false] at hd
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [a, AronowAudit.P012.s, hki, hkj, hne, Ne.symm hne] at hd hrdeg ⊢ <;> omega
  have hdegQ' : ∀ x : AronowAudit.P012.Vertex,
      AronowAudit.P012.graphDegree (SAP.P012a.Bridge.state Q) x =
        AronowAudit.P012.graphDegree a x := by
    intro x
    simp only [AronowAudit.P012.graphDegree, hpropsQ.2.2.2.2.1]
  have hdegB' : ∀ k ∈ d.sampled,
      AronowAudit.P012.graphDegree (AronowAudit.P012.addEdge
        (SAP.P012a.Bridge.state Q) (AronowAudit.P012.s j) w) (AronowAudit.P012.s k) = d.degree k := by
    intro k hk
    have hd := AronowAudit.P012.degree_add_step (SAP.P012a.Bridge.state Q)
      (AronowAudit.P012.s j) w (AronowAudit.P012.s k) hpropsQ.2.2.2.2.2
    rw [hdegQ' (AronowAudit.P012.s k)] at hd
    have ha := hdegA' k hk
    have hkw := hsampleNe' w (by simpa [d] using hUSQ) k hk
    simp only [mem_insert, mem_singleton, hkw, or_false] at hd
    by_cases hkj : k = j <;>
      simp [AronowAudit.P012.s, hkj] at hd ha ⊢ <;> omega
  have hdegR : ∀ k ∈ D.sampled,
      graphDegree R (s k) + (if k = i then 1 else 0) +
        (if k = j then 1 else 0) = graphDegree H (s k) := by
    intro k hk
    calc
      graphDegree R (s k) + (if k = i then 1 else 0) + (if k = j then 1 else 0) = D.degree k := by
        simpa [d, r, h, R, SAP.P012a.Bridge.removeEdge_eq,
          SAP.P012a.Bridge.graphDegree_eq, SAP.P012a.Bridge.s_eq] using hdegR' k (by simpa [d] using hk)
      _ = graphDegree H (s k) := (hH.2.2.2.2.2 k hk).symm
  have hdegP : ∀ x : Vertex, graphDegree P x = graphDegree R x := by
    intro x
    simp only [graphDegree, hEdgesP]
  have hdegA : ∀ k ∈ D.sampled,
      graphDegree A (s k) + (if k = j then 1 else 0) = graphDegree H (s k) := by
    intro k hk
    calc
      graphDegree A (s k) + (if k = j then 1 else 0) = D.degree k := by
        simpa [d, a, p, A, SAP.P012a.Bridge.addEdge_eq,
          SAP.P012a.Bridge.graphDegree_eq, SAP.P012a.Bridge.s_eq] using hdegA' k (by simpa [d] using hk)
      _ = graphDegree H (s k) := (hH.2.2.2.2.2 k hk).symm
  have hdegQ : ∀ x : Vertex, graphDegree Q x = graphDegree A x := by
    intro x
    simp only [graphDegree, hEdgesQ]
  have hdegB : ∀ k ∈ D.sampled, graphDegree B (s k) = graphDegree H (s k) := by
    intro k hk
    calc
      graphDegree B (s k) = D.degree k := by
        simpa [d, B, SAP.P012a.Bridge.addEdge_eq,
          SAP.P012a.Bridge.graphDegree_eq, SAP.P012a.Bridge.s_eq] using hdegB' k (by simpa [d] using hk)
      _ = graphDegree H (s k) := (hH.2.2.2.2.2 k hk).symm
  change W2DeleteObserved D H i j v w P Q
  unfold W2DeleteObserved
  dsimp only
  exact ⟨hFactsP, hFactsQ, hneqPool, hdegR, hdegP, hdegA, hdegQ, hdegB⟩
