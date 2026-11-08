import SAP.P012b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open Finset SAP.P012b.Bridge SAP.P012b.WH.W1

theorem SAP.P012b.WH.W1.T14_L1_proof : SAP.P012b.WH.W1.T14_L1 := by
  classical
  intro D H k hcompat hsamp hredge hd1 hd2
  let e12 : Finset Vertex := {s 1, s 2}
  let U : Finset Vertex := H.vertices \ {s 1, s 2}
  have hsampled : sampledVertices D = {s 1, s 2} := by
    simp [sampledVertices, hsamp, s]
  have hsimple : Simple H := hcompat.1.1
  have hdyad : e12 ∈ H.edges := by
    have h := hcompat.2.2.1
    rw [hredge] at h
    simpa [e12] using h (by simp)
  have hdegone : graphDegree H (s 1) = 1 := by
    have h := hcompat.2.2.2.2 1 (by simp [hsamp])
    simpa [hd1] using h
  have hincard : (H.edges.filter (fun e => s 1 ∈ e)).card = 1 := by
    simpa [graphDegree] using hdegone
  have hdyadinc : e12 ∈ H.edges.filter (fun e => s 1 ∈ e) := by
    simp [e12, hdyad]
  obtain ⟨e0, hfilter⟩ := Finset.card_eq_one.mp hincard
  have he0 : e0 = e12 := by
    have hm : e12 ∈ ({e0} : Finset (Finset Vertex)) := by
      rw [← hfilter]
      exact hdyadinc
    exact (Finset.mem_singleton.mp hm).symm
  have hincident_one (e : Finset Vertex) (he : e ∈ H.edges) (hv : s 1 ∈ e) : e = e12 := by
    have hm : e ∈ ({e0} : Finset (Finset Vertex)) := by
      rw [← hfilter]
      exact mem_filter.mpr ⟨he, hv⟩
    simpa [he0] using hm
  have hdisj : Disjoint U {s 1, s 2} := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    exact (Finset.mem_sdiff.mp hv).2 hu
  have hpairsub : ({s 1, s 2} : Finset Vertex) ⊆ H.vertices := by
    rw [← hsampled]
    exact hcompat.2.1
  have hvertices : H.vertices = {s 1, s 2} ∪ U := by
    ext v
    simp only [Finset.mem_union, U, Finset.mem_sdiff]
    constructor
    · intro hv
      by_cases hp : v ∈ ({s 1, s 2} : Finset Vertex)
      · exact Or.inl hp
      · exact Or.inr ⟨hv, hp⟩
    · intro hv
      rcases hv with hp | ⟨hv, _⟩
      · exact hpairsub hp
      · exact hv
  have hUvertex (v : Vertex) (hv : v ∈ U) : v ∈ H.vertices :=
    (Finset.mem_sdiff.mp hv).1
  have hUnotsampled (v : Vertex) (hv : v ∈ U) : v ∉ {s 1, s 2} :=
    (Finset.mem_sdiff.mp hv).2
  have hstarEdges : H.edges = insert e12 (U.image (fun v => ({s 2, v} : Finset Vertex))) := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_insert, Finset.mem_image]
    constructor
    · intro he
      by_cases h1 : s 1 ∈ e
      · left
        exact hincident_one e he h1
      · right
        obtain ⟨i, hi, hie⟩ := hcompat.1.2 e he
        have hi12 : i = 1 ∨ i = 2 := by
          simpa [hsamp] using hi
        rcases hi12 with hi1 | hi2
        · subst i
          exact False.elim (h1 (by simp [hie]))
        · subst i
          have htwo : s 2 ∈ e := by simpa using hie
          obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hsimple e he).1
          simp only [Finset.mem_insert, Finset.mem_singleton] at htwo
          rcases htwo with ha | hb
          · subst a
            have hbvert : b ∈ H.vertices := (hsimple _ he).2 (by simp)
            have hbnot1 : b ≠ s 1 := by
              intro hb1
              subst b
              exact h1 (by simp)
            have hbnot2 : b ≠ s 2 := hab.symm
            have hbuns : b ∉ ({s 1, s 2} : Finset Vertex) := by
              intro hm
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with h | h
              · exact hbnot1 h
              · exact hbnot2 h
            have hbu : b ∈ U := Finset.mem_sdiff.mpr ⟨hbvert, hbuns⟩
            exact ⟨b, hbu, rfl⟩
          · subst b
            have havert : a ∈ H.vertices := (hsimple _ he).2 (by simp)
            have hanot1 : a ≠ s 1 := by
              intro ha1
              subst a
              exact h1 (by simp)
            have hanot2 : a ≠ s 2 := hab
            have hauns : a ∉ ({s 1, s 2} : Finset Vertex) := by
              intro hm
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with h | h
              · exact hanot1 h
              · exact hanot2 h
            have hau : a ∈ U := Finset.mem_sdiff.mpr ⟨havert, hauns⟩
            exact ⟨a, hau, Finset.pair_comm (s 2) a⟩
    · intro he
      rcases he with he12 | ⟨v, hv, rfl⟩
      · rw [he12]
        exact hdyad
      · obtain ⟨i, hi, hie⟩ := hcompat.2.2.2.1 v (hUvertex v hv) (by
          rw [hsampled]
          exact hUnotsampled v hv)
        have hi12 : i = 1 ∨ i = 2 := by simpa [hsamp] using hi
        rcases hi12 with hi1 | hi2
        · subst i
          have he12' := hincident_one {s 1, v} hie (by simp)
          have hvpair : v ∈ ({s 1, s 2} : Finset Vertex) := by
            have hv' : v ∈ ({s 1, v} : Finset Vertex) := by simp
            rw [he12'] at hv'
            simpa [e12] using hv'
          exact False.elim (hUnotsampled v hv hvpair)
        · subst i
          exact hie
  have hdeg2 : graphDegree H (s 2) = k + 1 := by
    have h := hcompat.2.2.2.2 2 (by simp [hsamp])
    simpa [hd2] using h
  have hneighbors : H.vertices.filter (fun w => s 2 ≠ w ∧ {s 2, w} ∈ H.edges) =
      insert (s 1) U := by
    ext w
    constructor
    · intro hw
      have hwv := (Finset.mem_filter.mp hw).1
      have hwne := (Finset.mem_filter.mp hw).2.1
      rw [hvertices] at hwv
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hwv
      rcases hwv with hw12 | hwU
      · rcases hw12 with hw1 | hw2
        · simp [hw1]
        · exact False.elim (hwne hw2.symm)
      · exact Finset.mem_insert_of_mem hwU
    · intro hw
      simp only [Finset.mem_insert] at hw
      rcases hw with hw1 | hwU
      · subst w
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_, ?_⟩
        · rw [hvertices]
          simp
        · intro h
          exact (by decide : s 2 ≠ s 1) h
        · rw [hstarEdges]
          simp [e12]
      · apply Finset.mem_filter.mpr
        refine ⟨?_, ?_, ?_⟩
        · rw [hvertices]
          exact Finset.mem_union.mpr (Or.inr hwU)
        · intro h
          have hnot : w ∉ {s 1, s 2} := hUnotsampled w hwU
          exact hnot (by simp [h])
        · rw [hstarEdges]
          simp only [Finset.mem_insert]
          right
          exact Finset.mem_image.mpr ⟨w, hwU, rfl⟩
  have hcardU : U.card = k := by
    have hSimpleD : AronowAudit.P012.Simple (toState H) := by simpa using hsimple
    have hdegree := AronowAudit.P012.degree_eq_neighbor_card (toState H) hSimpleD (s 2)
    have hdegree' : graphDegree H (s 2) =
        (H.vertices.filter (fun x : Vertex => s 2 ≠ x ∧ {s 2, x} ∈ H.edges)).card := by
      exact hdegree
    rw [hdeg2, hneighbors] at hdegree'
    have hnot : s 1 ∉ U := by
      intro h
      exact hUnotsampled (s 1) h (by simp)
    simp [hnot] at hdegree'
    omega
  exact ⟨U, ⟨hdisj, hvertices, hstarEdges⟩, hcardU⟩

