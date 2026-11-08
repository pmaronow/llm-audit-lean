import SAP.P012a.WH.W1.Leaves
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P012a.WH.W1.P.T7_L1

open Finset
open scoped Classical

def recruitEdge (D : Data) (j : ℕ) : Finset Vertex :=
  {s (D.parent j), s j}

def childSet (D : Data) (i : ℕ) : Finset ℕ :=
  (nonseeds D).filter (fun j => D.parent j = i)

lemma recruitEdge_inj (D : Data) (hD : Admissible D) :
    Set.InjOn (recruitEdge D) (nonseeds D) := by
  intro j hj k hk h
  have hp := (AronowAudit.P012.pair_edge_eq (s (D.parent j)) (s j)
    (s (D.parent k)) (s k)).mp h
  rcases hp with ⟨_, he⟩ | ⟨hp, hkj⟩
  · exact Sum.inl.inj he
  · have hji : D.parent j = k := Sum.inl.inj hp
    have hkj' : j = D.parent k := Sum.inl.inj hkj
    have hjt := (hD.2.2.1 j hj).2
    have hkt := (hD.2.2.1 k hk).2
    rw [hji] at hjt
    rw [← hkj'] at hkt
    omega

lemma recruitment_incidence (D : Data) (hD : Admissible D)
    (i : ℕ) (hi : i ∈ D.sampled) :
    recruitmentDegree D i = pWholeDelta D i + (childSet D i).card := by
  let f := recruitEdge D
  let E := (nonseeds D).filter (fun j => D.parent j = i ∨ j = i)
  have himage : E.image f = (recruitmentEdges D).filter (fun e => s i ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨j, hj, rfl⟩ := mem_image.mp he
      have hj' := (mem_filter.mp hj).2
      apply mem_filter.mpr
      refine ⟨mem_image_of_mem f (mem_filter.mp hj).1, ?_⟩
      rcases hj' with hp | hji
      · simp [f, recruitEdge, hp]
      · simp [f, recruitEdge, hji]
    · intro he
      obtain ⟨heR, hiE⟩ := mem_filter.mp he
      obtain ⟨j, hj, rfl⟩ := mem_image.mp heR
      have hiE' : i = D.parent j ∨ i = j := by
        simpa only [recruitEdge, mem_insert, mem_singleton, s, Sum.inl.injEq] using hiE
      apply mem_image.mpr
      refine ⟨j, mem_filter.mpr ⟨hj, ?_⟩, rfl⟩
      rcases hiE' with hp | hji
      · exact Or.inl hp.symm
      · exact Or.inr hji.symm
  have hInj : Set.InjOn f E := by
    intro j hj k hk he
    exact recruitEdge_inj D hD (mem_filter.mp hj).1 (mem_filter.mp hk).1 he
  have hcard : (E.image f).card = E.card := card_image_iff.mpr hInj
  have hdecomp : E = childSet D i ∪ (if i ∈ nonseeds D then {i} else ∅) := by
    ext j
    by_cases hni : i ∈ nonseeds D
    · simp only [E, childSet, mem_filter, mem_union, if_pos hni, mem_singleton]
      constructor
      · rintro ⟨hj, hp | hji⟩
        · exact Or.inl ⟨hj, hp⟩
        · subst j
          exact Or.inr rfl
      · rintro (⟨hj, hp⟩ | hji)
        · exact ⟨hj, Or.inl hp⟩
        · subst j
          exact ⟨hni, Or.inr rfl⟩
    · simp only [E, childSet, mem_filter, mem_union, if_neg hni, notMem_empty, or_false]
      constructor
      · rintro ⟨hj, hp | hji⟩
        · exact ⟨hj, hp⟩
        · subst j
          exact False.elim (hni hj)
      · rintro ⟨hj, hp⟩
        exact ⟨hj, Or.inl hp⟩
  have hdisj : Disjoint (childSet D i) (if i ∈ nonseeds D then {i} else ∅) := by
    by_cases hni : i ∈ nonseeds D
    · rw [Finset.disjoint_left]
      intro j hjC hjI
      simp only [hni, ite_true, mem_singleton] at hjI
      subst j
      have hparent := (mem_filter.mp hjC).2
      have htime := (hD.2.2.1 i hni).2
      rw [hparent] at htime
      exact (lt_irrefl _ htime).elim
    · simp [hni]
  have hEcard : E.card = (childSet D i).card + (if i ∈ nonseeds D then 1 else 0) := by
    rw [hdecomp, card_union_of_disjoint hdisj]
    by_cases hni : i ∈ nonseeds D <;> simp [hni]
  have hdelta : pWholeDelta D i = if i ∈ nonseeds D then 1 else 0 := by
    unfold pWholeDelta
    by_cases hni : i ∈ nonseeds D
    · have hseed : i ∉ D.seeds := (mem_sdiff.mp hni).2
      simp [hni, hseed]
    · have hseed : i ∈ D.seeds := by
        by_contra hs
        exact hni (mem_sdiff.mpr ⟨hi, hs⟩)
      simp [hni, hseed]
  unfold recruitmentDegree
  rw [← himage, hcard, hEcard, hdelta]
  omega

lemma chronological_cross {D : Data} {order : List ℕ}
    (hC : WholeChronological D order) {pre post : List ℕ} {j k : ℕ}
    (hsplit : order = pre ++ j :: post) (hk : k ∈ pre) :
    D.time k < D.time j := by
  have hp := hC.2.2
  rw [hsplit] at hp
  have hc := (List.pairwise_append.mp hp).2.2
  exact hc k hk j (by simp)

lemma chronological_j_post {D : Data} {order : List ℕ}
    (hC : WholeChronological D order) {pre post : List ℕ} {j k : ℕ}
    (hsplit : order = pre ++ j :: post) (hk : k ∈ post) :
    D.time j < D.time k := by
  have hp := hC.2.2
  rw [hsplit] at hp
  have htail := (List.pairwise_append.mp hp).2.1
  have hc := (List.pairwise_cons.mp htail).1
  exact hc k hk

end SAP.P012a.WH.W1.P.T7_L1

open SAP.P012a.WH.W1.P.T7_L1
open Finset
open scoped Classical

theorem SAP.P012a.WH.W1.T7_L1_proof : SAP.P012a.WH.W1.T7_L1 := by
  intro D hD order hC
  constructor
  · intro r hr
    exact recruitment_incidence D hD r hr
  · intro pre j post hsplit hj
    have hjOrder : j ∈ order := by rw [hsplit]; simp
    have hjSample : j ∈ D.sampled := by
      have hmem : j ∈ order.toFinset := by simpa using hjOrder
      rw [hC.2.1] at hmem
      exact hmem
    have hparent := hD.2.2.1 j hj
    let r := D.parent j
    have hrSample : r ∈ D.sampled := hparent.1
    have hrOrder : r ∈ order := by
      have hmem : r ∈ order.toFinset := by rw [hC.2.1]; exact hrSample
      simpa using hmem
    have hrSplit : r ∈ pre ∨ r = j ∨ r ∈ post := by
      have hmem : r ∈ pre ++ j :: post := by simpa [hsplit] using hrOrder
      rcases List.mem_append.mp hmem with hp | ht
      · exact Or.inl hp
      · rcases List.mem_cons.mp ht with heq | hpost
        · exact Or.inr (Or.inl heq)
        · exact Or.inr (Or.inr hpost)
    have hrPre : r ∈ pre := by
      rcases hrSplit with hp | hrest
      · exact hp
      · rcases hrest with heq | hpost
        · have hrj : D.parent j = j := by simpa [r] using heq
          rw [hrj] at hparent
          exact False.elim (lt_irrefl _ hparent.2)
        · have hlt := chronological_j_post hC hsplit hpost
          have hlt' : D.time j < D.time (D.parent j) := by simpa [r] using hlt
          omega
    have hUnion : childSet D r = pWholeChildrenBefore D pre r ∪ laterChildren D j := by
      ext k
      constructor
      · intro hk
        have hk' := mem_filter.mp hk
        have hkOrder : k ∈ order := by
          have hm : k ∈ order.toFinset := by
            rw [hC.2.1]
            exact (mem_sdiff.mp hk'.1).1
          simpa using hm
        have hkSplit : k ∈ pre ∨ k = j ∨ k ∈ post := by
          have hm : k ∈ pre ++ j :: post := by simpa [hsplit] using hkOrder
          rcases List.mem_append.mp hm with hp | ht
          · exact Or.inl hp
          · rcases List.mem_cons.mp ht with heq | hpost
            · exact Or.inr (Or.inl heq)
            · exact Or.inr (Or.inr hpost)
        rcases hkSplit with hkp | htail
        · apply mem_union.mpr
          left
          apply mem_filter.mpr
          refine ⟨?_, ⟨hk'.1, hk'.2⟩⟩
          simpa using hkp
        · apply mem_union.mpr
          right
          apply mem_filter.mpr
          refine ⟨hk'.1, ?_⟩
          refine ⟨?_, ?_⟩
          · simpa [r] using hk'.2
          · rcases htail with heq | hpost
            · subst k
              exact le_rfl
            · exact (chronological_j_post hC hsplit hpost).le
      · intro hk
        rcases mem_union.mp hk with hp | hl
        · have hk' := mem_filter.mp hp
          exact mem_filter.mpr ⟨hk'.2.1, hk'.2.2⟩
        · have hk' := mem_filter.mp hl
          exact mem_filter.mpr ⟨hk'.1, by simpa [r] using hk'.2.1⟩
    have hDisj : Disjoint (pWholeChildrenBefore D pre r) (laterChildren D j) := by
      rw [Finset.disjoint_left]
      intro k hk hp
      have hkp := mem_filter.mp hk
      have hpre : k ∈ pre := by simpa using hkp.1
      have hlt := chronological_cross hC hsplit hpre
      have hlate := (mem_filter.mp hp).2.2
      omega
    have hCard : (childSet D r).card =
        (pWholeChildrenBefore D pre r).card + (laterChildren D j).card := by
      rw [hUnion, card_union_of_disjoint hDisj]
    have hInc := recruitment_incidence D hD r hrSample
    have hdeg := hD.2.2.2 r hrSample
    have hpoint : D.degree r = recruitmentDegree D r + spare D r :=
      (Nat.add_sub_of_le hdeg).symm
    have hres : D.degree r - pWholeDelta D r -
        (pWholeChildrenBefore D pre r).card = pWholeDenom D j := by
      unfold pWholeDenom
      have hrj : D.parent j = r := rfl
      rw [hrj]
      rw [hpoint, hInc, hCard]
      omega
    have hjLater : j ∈ laterChildren D j := by
      apply mem_filter.mpr
      exact ⟨hj, ⟨rfl, le_rfl⟩⟩
    have hcardpos : 0 < (laterChildren D j).card := card_pos.mpr ⟨j, hjLater⟩
    have hpos : 0 < pWholeDenom D j := by
      unfold pWholeDenom
      omega
    exact ⟨hrPre, hres, hpos⟩

