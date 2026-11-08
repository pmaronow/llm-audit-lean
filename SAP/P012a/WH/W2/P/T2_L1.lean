import SAP.P012a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W2.P.T2_L1

open SAP.P012a Finset
open scoped Classical
noncomputable section

theorem degree_remove_step (H : SAP.P012a.State) (v w x : SAP.P012a.Vertex)
    (he : {v, w} ∈ H.edges) :
    graphDegree (removeEdge H v w) x +
        (if x ∈ ({v, w} : Finset SAP.P012a.Vertex) then 1 else 0) =
      graphDegree H x := by
  change ((H.edges.erase {v, w}).filter (fun e => x ∈ e)).card + _ = _
  rw [filter_erase]
  by_cases hx : x ∈ ({v, w} : Finset SAP.P012a.Vertex)
  · simp only [if_pos hx]
    exact card_erase_add_one (mem_filter.mpr ⟨he, hx⟩)
  · simp only [if_neg hx, Nat.add_zero]
    rw [erase_eq_of_notMem (by simp [hx])]
    rfl

theorem degree_add_step (H : SAP.P012a.State) (v w x : SAP.P012a.Vertex)
    (he : {v, w} ∉ H.edges) :
    graphDegree (addEdge H v w) x = graphDegree H x +
        (if x ∈ ({v, w} : Finset SAP.P012a.Vertex) then 1 else 0) := by
  change ((insert {v, w} H.edges).filter (fun e => x ∈ e)).card = _
  rw [filter_insert]
  by_cases hx : x ∈ ({v, w} : Finset SAP.P012a.Vertex)
  · simp only [if_pos hx]
    exact card_insert_of_notMem (fun h => he (mem_filter.mp h).1)
  · simp only [if_neg hx, Nat.add_zero]
    rfl

end
end SAP.P012a.WH.W2.P.T2_L1

namespace SAP.P012a.WH.W2

open SAP.P012a Finset
open SAP.P012a.WH.W2.P.T2_L1
open scoped Classical
noncomputable section

theorem T2_L1_proof : SAP.P012a.WH.W2.T2_L1 := by
  intro D H i j v P hD hH hi hj hne he hr hju hp
  let R := removeEdge H (s i) j
  let A := addEdge P (s i) v
  have hchoice :
      (v ∈ replacementPool D H i ∧ P = R) ∨
        (v ∉ R.vertices ∧ ∃ t : Bool, P = addVertex R v t) := by
    cases hp with
    | existing hv => exact Or.inl ⟨hv, rfl⟩
    | fresh hv t => exact Or.inr ⟨hv, t, rfl⟩
  have hRsubsetP : R.vertices ⊆ P.vertices := by
    cases hp with
    | existing _ => exact Subset.rfl
    | fresh _ _ => exact subset_insert _ _
  have hvP : v ∈ P.vertices := by
    cases hp with
    | existing hv =>
        have hvR : v ∈ R.vertices := by
          have hvH : v ∈ H.vertices :=
            (mem_sdiff.mp (mem_filter.mp hv).1).1
          simpa [R, removeEdge] using hvH
        exact hvR
    | fresh _ _ => simp [addVertex]
  have hvUnsampled : v ∉ sampledVertices D := by
    cases hp with
    | existing hv => exact (mem_sdiff.mp (mem_filter.mp hv).1).2
    | fresh hv _ =>
        intro hvs
        apply hv
        simpa [R, removeEdge] using hH.2.1 hvs
  have hEdges : P.edges = R.edges := by
    cases hp <;> rfl
  have hnewAbsent : ({s i, v} : Finset Vertex) ∉ P.edges := by
    cases hp with
    | existing hv =>
        intro h
        have hR : ({s i, v} : Finset Vertex) ∈ H.edges.erase {s i, j} := by
          change ({s i, v} : Finset Vertex) ∈ R.edges at h
          change ({s i, v} : Finset Vertex) ∈ H.edges.erase {s i, j} at h
          exact h
        exact (mem_filter.mp hv).2 (Finset.mem_erase.mp hR).2
    | fresh hv t =>
        intro h
        have hR : ({s i, v} : Finset Vertex) ∈ H.edges.erase {s i, j} := by
          change ({s i, v} : Finset Vertex) ∈ (addVertex R v t).edges at h
          change ({s i, v} : Finset Vertex) ∈ R.edges at h
          change ({s i, v} : Finset Vertex) ∈ H.edges.erase {s i, j} at h
          exact h
        have hHedge : ({s i, v} : Finset Vertex) ∈ H.edges :=
          (Finset.mem_erase.mp hR).2
        have hvH : v ∈ H.vertices := (hH.1.1 _ hHedge).2 (by simp)
        apply hv
        simpa [R, removeEdge] using hvH
  have hjR : j ∈ R.vertices := by
    simpa [R, removeEdge] using hj
  have hvj : v ≠ j := by
    intro hvj
    rcases hchoice with ⟨hpool, _⟩ | ⟨hfresh, _⟩
    · subst v
      exact (mem_filter.mp hpool).2 he
    · subst v
      exact hfresh hjR
  have hsi_ne_j : j ≠ s i := Ne.symm hne
  have hsi_ne_v : s i ≠ v := by
    intro h
    exact hvUnsampled (by
      rw [← h]
      exact mem_image_of_mem s hi)
  have hnewNotIncident : j ∉ ({s i, v} : Finset Vertex) := by
    simp [Finset.mem_insert, Finset.mem_singleton, hsi_ne_j, Ne.symm hvj]
  have hchoiceIndicator (k : ℕ) (hk : k ∈ D.sampled) :
      s k ∈ ({s i, j} : Finset Vertex) ↔ k = i := by
    have hskj : s k ≠ j := by
      intro h
      apply hju
      rw [← h]
      exact mem_image_of_mem s hk
    constructor
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact Sum.inl.inj h
      · exact False.elim (hskj h)
    · intro h
      subst k
      simp
  have hnewIndicator (k : ℕ) (hk : k ∈ D.sampled) :
      s k ∈ ({s i, v} : Finset Vertex) ↔ k = i := by
    have hskv : s k ≠ v := by
      intro h
      apply hvUnsampled
      rw [← h]
      exact mem_image_of_mem s hk
    constructor
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact Sum.inl.inj h
      · exact False.elim (hskv h)
    · intro h
      subst k
      simp
  have hFacts : W2ReplacementFacts D H R i v P := by
    exact ⟨hvP, hvUnsampled, hEdges, hnewAbsent, hchoice⟩
  have hRemove : ∀ k ∈ D.sampled,
      graphDegree R (s k) + (if k = i then 1 else 0) = graphDegree H (s k) := by
    intro k hk
    have hstep := degree_remove_step H (s i) j (s k) he
    simpa only [hchoiceIndicator k hk] using hstep
  have hPdegree : ∀ x : Vertex, graphDegree P x = graphDegree R x := by
    intro x
    simp [graphDegree, hEdges]
  have hSampledRestored : ∀ k ∈ D.sampled,
      graphDegree A (s k) = graphDegree H (s k) := by
    intro k hk
    have hstep := degree_add_step P (s i) v (s k) hnewAbsent
    rw [hPdegree (s k)] at hstep
    have hadd : graphDegree A (s k) =
        graphDegree R (s k) + (if k = i then 1 else 0) := by
      simpa only [A, hnewIndicator k hk] using hstep
    rw [hRemove k hk] at hadd
    simpa only using hadd
  have hjA : j ∈ A.vertices := by
    have hjP : j ∈ P.vertices := hRsubsetP hjR
    simpa [A, addEdge] using hjP
  have hCleanup : j ∉ (cleanup D true A).vertices ↔ graphDegree A j = 0 := by
    simp [cleanup, A, hjA, hju]
  have hAdegree : graphDegree A j = graphDegree R j := by
    have hstep := degree_add_step P (s i) v j hnewAbsent
    rw [hPdegree j] at hstep
    simpa [A, hnewNotIncident] using hstep
  have hRemoveOld : graphDegree R j + 1 = graphDegree H j := by
    have hstep := degree_remove_step H (s i) j j he
    simpa [R, removeEdge] using hstep
  have hDegreeOne : graphDegree H j = 1 ↔
      ∀ e ∈ H.edges, j ∈ e → e = ({s i, j} : Finset Vertex) := by
    rw [graphDegree]
    constructor
    · intro hcard e he' hj'
      have hmem : e ∈ H.edges.filter (fun e => j ∈ e) :=
        mem_filter.mpr ⟨he', hj'⟩
      have hpair : ({s i, j} : Finset Vertex) ∈
          H.edges.filter (fun e => j ∈ e) := by
        exact mem_filter.mpr ⟨he, by simp⟩
      obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
      have hfp : f = ({s i, j} : Finset Vertex) := by
        have : ({s i, j} : Finset Vertex) ∈
            ({f} : Finset (Finset Vertex)) := by
          rw [← hf]
          exact hpair
        have hpf : ({s i, j} : Finset Vertex) = f := by simpa using this
        exact hpf.symm
      have hef : e ∈ ({f} : Finset (Finset Vertex)) := by
        rw [← hf]
        exact hmem
      have hef' : e = f := by simpa using hef
      exact hef'.trans hfp
    · intro hall
      have hfilter : H.edges.filter (fun e => j ∈ e) =
          {({s i, j} : Finset Vertex)} := by
        ext e
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨he', hj'⟩
          exact hall e he' hj'
        · intro heq
          subst e
          exact ⟨he, by simp⟩
      rw [hfilter]
      simp
  have hOldCriterion : graphDegree R j = 0 ↔
      ∀ e ∈ H.edges, j ∈ e → e = ({s i, j} : Finset Vertex) := by
    constructor
    · intro hzero
      apply hDegreeOne.mp
      omega
    · intro honly
      have hone := hDegreeOne.mpr honly
      omega
  have hAOld : graphDegree A j = 0 ↔ graphDegree R j = 0 := by
    rw [hAdegree]
  change W2ReplacementFacts D H R i v P ∧
    (∀ k ∈ D.sampled,
      graphDegree R (s k) + (if k = i then 1 else 0) = graphDegree H (s k)) ∧
    (∀ x : Vertex, graphDegree P x = graphDegree R x) ∧
    (∀ k ∈ D.sampled, graphDegree A (s k) = graphDegree H (s k)) ∧
    (j ∉ (cleanup D true A).vertices ↔
      ∀ e ∈ H.edges, j ∈ e → e = {s i, j})
  exact ⟨hFacts, hRemove, hPdegree, hSampledRestored,
    hCleanup.trans (hAOld.trans hOldCriterion)⟩

end
end SAP.P012a.WH.W2
