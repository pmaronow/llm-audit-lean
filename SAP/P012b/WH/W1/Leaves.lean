import SAP.P012b.WH.W1.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

namespace SAP.P012b.WH.W1

open Finset SAP.P012b.Bridge
noncomputable section

/-- Shared saturated-endpoint classification (also used in T22).
The compulsory dyad exhausts vertex 1. Every remaining edge therefore joins
vertex 2 to an unsampled vertex; condition 3 excludes all other vertices.
Use degree_eq_neighbor_card and equality of finite sets of equal cardinality
to obtain exactly k leaves. This includes k=0 and allows arbitrary unsampled
names, including unused sampled-name constructors. Expected: 150--250 lines. -/
def T14_L1 : Prop :=
  ∀ (D : Data) (H : State) (k : ℕ), GraphCompatible D H →
    D.sampled = {1,2} → recruitmentEdges D = {{s 1,s 2}} →
    D.degree 1 = 1 → D.degree 2 = k+1 →
    ∃ U : Finset Vertex, StarAtTwo H U ∧ U.card = k

/-- Three-leaf star statistics for arbitrary leaf names and binary traits.
With r one-trait leaves, m=4, q=5+r and the ordered trait-adjacency sum is
2(1+r). Use numerator_edge_identity and denominator_sum_identity after finite
degree counting. The only recruiter is vertex 1, with susceptible set {2},
so its recruitment deviation is zero. Expected: 100--200 lines. -/
def T14_L2 : Prop :=
  ∀ (H : State) (U : Finset Vertex), StarAtTwo H U → U.card = 3 →
    H.trait (s 1) = true → H.trait (s 2) = true →
    let r : ℝ := onesOn H U;
    H.edges.card = 4 ∧
    hNumerator H = 2*(1+r) - (5+r)^2/8 ∧
    hDenominator H = (5+r) - (5+r)^2/8 ∧
    preferential domainD H = some 0

/-- The one-leaf example's statistics after graph classification.
Expand the three-vertex ordered sums, with leaf v distinct from both sampled
vertices, or use graph_homophily_formula. The leaf trait false gives -1 and
true gives -1/3. The sole recruiter sees only vertex 2, giving p=0.
No assumption on the unused trait values or on the leaf's name is allowed.
Expected: 80--160 lines. -/
def T22_L1 : Prop :=
  ∀ (H : State) (v : Vertex), StarAtTwo H {v} →
    H.trait (s 1) = false → H.trait (s 2) = true →
    preferential oneLeafData H = some 0 ∧
    homophily H = some (if H.trait v then (-1/3) else (-1))

/-- Private-leaf graph facts and identification of the erased-edge counts.
Use private_leaf_member and private_edge_incidence for the degree-one leaf;
leaf_flip_edge_counts identifies the counts before/after the flip, and
graph_homophily_formula supplies both phi values. Positive trait-0 degree
gives 2y+c>0. The scalar difference and its strict sign are already proved in
leaf_flip_scalar and are supplied by the assembly. Expected: 120--250 lines. -/
def T22_L2 : Prop :=
  ∀ (D : Data), Admissible D →
    0 < sampledTraitDegree D false → 0 < sampledTraitDegree D true →
    ∀ i ∈ D.sampled, recruitmentDegree D i < D.degree i →
    let H := leafCompletion D true
    let K := flipTrait H (u i 0)
    let E := H.edges.erase {s i, u i 0}
    let x : ℝ := wholeEdgeCount E H.trait true
    let y : ℝ := wholeEdgeCount E H.trait false
    let c : ℝ := wholeMixedCount E H.trait
    HomophilyDefined H ∧ HomophilyDefined K ∧
      u i 0 ∈ unsampled D H ∧ graphDegree H (u i 0) = 1 ∧
      H.trait (u i 0) = D.trait i ∧ K.trait (u i 0) = !D.trait i ∧
      (D.trait i = true →
        0 < 2*y+c ∧
        hValue H = wholePhi (x+1) y c ∧ hValue K = wholePhi x y (c+1))

theorem T14_assembly (hstar : T14_L1) (hstats : T14_L2) : T14WholeStatement := by
  refine ⟨restricted14, domainA_all, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨dyad_raw.1, dyad_raw.2, fun H => by
      simp [nonseeds, domainB, domainA, pSum]⟩
  · intro H hH
    have hp := domainC_same H hH
    have hh := (pair_h_statistics H _ hp).2.2
    have hq := pair_p_congr domainC H _ restricted14.2.2.1.1 hH hp
    have he : H.edges = ∅ := hp.2.1
    refine ⟨hp, by simp [he], ?_, by decide,
      hh.trans restricted14.2.2.1.2.2.2.1,
      hq.trans restricted14.2.2.1.2.2.2.2⟩
    intro v _ w _
    simp [graphDegree, he]
  · intro H hH
    have hg : GraphCompatible domainD H :=
      ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.2⟩
    obtain ⟨U, hU, hc⟩ := hstar domainD H 3 hg rfl (by decide) rfl rfl
    have hs := hstats H U hU hc
      (hH.2.2.2.1 1 (by decide)) (hH.2.2.2.1 2 (by decide))
    dsimp only at hs
    obtain ⟨hm, hn, hd, hpr⟩ := hs
    have hr : onesOn H U ≤ 3 := by
      simpa [onesOn, hc] using card_filter_le U (fun v => H.trait v = true)
    refine ⟨U, hU, hc, hr, hpr, ?_, ?_, ?_, ?_⟩
    · intro hz
      norm_num [homophily, HomophilyDefined, hValue, hm, hn, hd, hz]
    · intro hz
      norm_num [homophily, HomophilyDefined, hValue, hm, hn, hd, hz]
    · intro hz
      norm_num [homophily, HomophilyDefined, hValue, hm, hn, hd, hz]
    · intro hz
      norm_num [homophily, HomophilyDefined, hn, hd, hz]
  · exact no_h_region domainA _ restricted14.1.2.1 restricted14.1.2.2.2.2.1
  · exact no_h_region domainD _ (restricted14.2.2.2.2.1 true true true)
      restricted14.2.2.2.2.2.2.2.1

theorem T15_assembly : T15WholeStatement := by
  refine ⟨restricted15, ?_, ?_, ?_, ?_⟩
  · intro H
    rw [traitDegree, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro v _
    cases ht : H.trait v <;> simp [z, ht]
  · intro H hS
    constructor
    · intro hd
      exact ⟨hd.1, ((restricted15.1 H hS hd.1).2.2.2.2.2.2.1).mp hd⟩
    · rintro ⟨hm, h0, h1⟩
      exact ((restricted15.1 H hS hm).2.2.2.2.2.2.1).mpr ⟨h0,h1⟩
  · intro D hD
    have hex : Compatible D (leafCompletion D true) := by
      sap_transfer (AronowAudit.P012.leafCompletion_compatible (toData D) hD true)
    refine ⟨⟨_, hex⟩, ?_, ?_⟩
    · rintro ⟨h0,h1⟩
      have hr : FullHomophilyRegion D
          (AronowAudit.P012.hLower (toData D)) (AronowAudit.P012.hUpper (toData D)) := by
        sap_transfer ((AronowAudit.P012.exact_h_region (toData D) hD h0 h1).2.2.2.2.2)
      refine ⟨_, _, hr, smallest_interval _ _ _ hr.2.1 hr.2.2, ?_⟩
      intro L' U' hr'
      exact ⟨hr'.2.1.unique hr.2.1, hr'.2.2.unique hr.2.2⟩
    · intro hN
      have hr : FullPreferentialRegion D
          (AronowAudit.P012.pLower (toData D)) (AronowAudit.P012.pUpper (toData D)) := by
        sap_transfer ((AronowAudit.P012.exact_p_region (toData D) hD hN).2.2.2.2.2)
      refine ⟨_, _, hr, smallest_interval _ _ _ hr.2.1 hr.2.2, ?_⟩
      intro L' U' hr'
      exact ⟨hr'.2.1.unique hr.2.1, hr'.2.2.unique hr.2.2⟩
  · have hn : ∀ H, Compatible domainA H → ¬ HomophilyDefined H := by
      intro H hH hd
      have hh := (domainA_all H hH).2.2.2.1
      rw [homophily, if_pos hd] at hh
      cases hh
    have he : hValues domainA = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro r ⟨H,hH,hh⟩
      rw [(domainA_all H hH).2.2.2.1] at hh
      cases hh
    have hp : pValues domainA = {0} := by
      ext r
      constructor
      · rintro ⟨H,hH,hr⟩
        rw [(domainA_all H hH).2.2.2.2] at hr
        exact Option.some.inj hr ▸ Set.mem_singleton 0
      · intro hr
        have hzero : r = 0 := Set.mem_singleton_iff.mp hr
        subst r
        exact ⟨_, restricted14.1.2.1, restricted14.1.2.2.2.2.2⟩
    refine ⟨?_, he, fun H hH => (domainA_all H hH).2.2.2.2, ?_⟩
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro H hH
      exact hn H hH.1 hH.2
    · refine ⟨?_, ?_, ?_⟩
      · exact (restricted15.2 domainA restricted14.1.1).2.2.1.mpr (by decide)
      · rw [hp]; exact ⟨by simp, by simp⟩
      · rw [hp]; exact ⟨by simp, by simp⟩

theorem T17_assembly : T17WholeStatement := by
  refine ⟨?_, t17_example⟩
  intro D H hD hH
  have hr := restricted17 D H hD hH
  refine ⟨hr.1, hr.2, ?_, ?_⟩
  · constructor
    · intro hn
      apply Subset.antisymm _ hH.2.1
      intro v hv
      by_contra hnot
      obtain ⟨i,hi,he⟩ := hH.2.2.2.1 v hv hnot
      exact hnot (hn i hi v hv he)
    · intro hv i _ v hv' _
      exact hv ▸ hv'
  · constructor
    · intro hv
      refine ⟨hv, ?_⟩
      symm
      apply filter_eq_self.mpr
      intro e he
      rw [← hv]
      exact (hH.1.1 e he).2
    · exact fun h => h.1

theorem T18_assembly : T18WholeStatement :=
  ⟨fun H K hp => (pair_h_statistics H K hp).2.2, history_examples⟩

theorem T22_assembly (hstar : T14_L1) (hstats : T22_L1) (hflip : T22_L2) :
    T22WholeStatement := by
  refine ⟨restricted22, ?_, oneLeaf_examples.1, oneLeaf_examples.2.2.2.1, ?_⟩
  · intro D hD h0 h1 i hi hdi
    obtain ⟨hdH, hdK, hv, hdeg, htH, htK, hphi⟩ := hflip D hD h0 h1 i hi hdi
    refine ⟨hdH, hdK, hv, hdeg, htH, htK, ?_⟩
    intro hti
    obtain ⟨hyc, hpH, hpK⟩ := hphi hti
    refine ⟨hyc, hpH, hpK, ?_, ?_⟩
    · rw [hpH, hpK]
      exact (leaf_flip_scalar _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hyc).1
    · rw [hpH, hpK]
      exact (leaf_flip_scalar _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hyc).2
  ·
    have hall : ∀ H, Compatible oneLeafData H → ∃ v : Vertex,
        StarAtTwo H {v} ∧ preferential oneLeafData H = some 0 ∧
        homophily H = some (if H.trait v then (-1/3) else (-1)) ∧
        H.vertices ≠ sampledVertices oneLeafData := by
      intro H hH
      have hg : GraphCompatible oneLeafData H :=
        ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.2⟩
      obtain ⟨U, hU, hc⟩ := hstar oneLeafData H 1 hg rfl (by decide) rfl rfl
      obtain ⟨v, rfl⟩ := card_eq_one.mp hc
      have hs := hstats H v hU
        (hH.2.2.2.1 1 (by decide)) (hH.2.2.2.1 2 (by decide))
      refine ⟨v, hU, hs.1, hs.2, ?_⟩
      have hvnot : v ∉ sampledVertices oneLeafData := by
        simpa [sampledVertices, oneLeafData] using
          (disjoint_left.mp hU.1 (mem_singleton_self v))
      intro heq
      apply hvnot
      rw [← heq, hU.2.1]
      simp
    have hh : hValues oneLeafData = {(-1 : ℝ), -1/3} := by
      ext r
      constructor
      · rintro ⟨H,hH,hr⟩
        obtain ⟨v,_,_,hv,_⟩ := hall H hH
        rw [hv] at hr
        have heq := Option.some.inj hr
        cases ht : H.trait v <;> simp [ht] at heq <;> simp [← heq]
      · intro hr
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, oneLeaf_examples.2.2.2.1 false, oneLeaf_examples.2.2.2.2.1⟩
        · exact ⟨_, oneLeaf_examples.2.2.2.1 true, oneLeaf_examples.2.2.2.2.2.1⟩
    have hp : pValues oneLeafData = {0} := by
      ext r
      constructor
      · rintro ⟨H,hH,hr⟩
        obtain ⟨v,_,hv,_,_⟩ := hall H hH
        rw [hv] at hr
        exact Option.some.inj hr ▸ Set.mem_singleton 0
      · intro hr
        have heq : r = 0 := Set.mem_singleton_iff.mp hr
        subst r
        exact ⟨_, oneLeaf_examples.2.2.2.1 false, oneLeaf_examples.2.2.2.2.2.2 false⟩
    have hmin : IsLeast (hValues oneLeafData) (-1) := by
      rw [hh]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> norm_num
    have hmax : IsGreatest (hValues oneLeafData) (-1/3) := by
      rw [hh]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> norm_num
    have pmin : IsLeast (pValues oneLeafData) 0 := by
      rw [hp]; exact ⟨by simp, by simp⟩
    have pmax : IsGreatest (pValues oneLeafData) 0 := by
      rw [hp]; exact ⟨by simp, by simp⟩
    have hreg : FullHomophilyRegion oneLeafData (-1) (-1/3) :=
      ⟨((restricted15.2 oneLeafData oneLeaf_examples.1).2.1).mpr
        oneLeaf_examples.2.1, hmin, hmax⟩
    have preg : FullPreferentialRegion oneLeafData 0 0 :=
      ⟨((restricted15.2 oneLeafData oneLeaf_examples.1).2.2.1).mpr
        oneLeaf_examples.2.2.1, pmin, pmax⟩
    exact ⟨hall, hh, hp, hreg, preg,
      smallest_interval _ _ _ hmin hmax, smallest_interval _ _ _ pmin pmax⟩

end
end SAP.P012b.WH.W1
