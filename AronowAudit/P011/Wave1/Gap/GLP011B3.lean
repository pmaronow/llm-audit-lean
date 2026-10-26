import AronowAudit.P011.P011_FiniteCompletion
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Rat.Lemmas

/-!
Finite reduction of the degree-constrained graph program to weighted matching.
The `mr_` prefix identifies the helpers for `matching_reduction_proof`.
-/

namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

private lemma mr_degree_mono {n : ℕ} {S T : Finset (Edge n)} (h : S ⊆ T)
    (i : Fin n) : edgeDegree S i ≤ edgeDegree T i :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

private lemma mr_degree_union {n : ℕ} {S T : Finset (Edge n)}
    (h : Disjoint S T) (i : Fin n) :
    edgeDegree (S ∪ T) i = edgeDegree S i + edgeDegree T i := by
  unfold edgeDegree
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

private lemma mr_degree_bound {n : ℕ} (S : Finset (Edge n)) (i : Fin n) :
    edgeDegree S i ≤ n-1 := by
  let f : Edge n → Fin n := fun e => if e.val.1 = i then e.val.2 else e.val.1
  have hi : ∀ e ∈ S.filter (fun e => e.val.1=i ∨ e.val.2=i), f e ≠ i := by
    intro e he
    have he := (Finset.mem_filter.mp he).2
    dsimp [f]
    split_ifs with h
    · intro hh
      have := e.property
      rw [h, hh] at this
      exact (lt_irrefl i) this
    · exact h
  have hf : Set.InjOn f ↑(S.filter (fun e => e.val.1=i ∨ e.val.2=i)) := by
    intro e he g hg hfg
    have he := (Finset.mem_filter.mp he).2
    have hg := (Finset.mem_filter.mp hg).2
    by_cases h : e.val.1=i <;> by_cases k : g.val.1=i
    · apply Subtype.ext
      exact Prod.ext (h.trans k.symm) (by simpa [f, h, k] using hfg)
    · have kg : g.val.2=i := hg.resolve_left k
      have hh : e.val.2=g.val.1 := by simpa [f, h, k] using hfg
      have hee := e.property
      have hgg := g.property
      rw [h, hh] at hee
      rw [kg] at hgg
      exact False.elim (lt_asymm hee hgg)
    · have he' : e.val.2=i := he.resolve_left h
      have hh : e.val.1=g.val.2 := by simpa [f, h, k] using hfg
      have hee := e.property
      have hgg := g.property
      rw [he'] at hee
      rw [k, ← hh] at hgg
      exact False.elim (lt_asymm hee hgg)
    · apply Subtype.ext
      exact Prod.ext (by simpa [f, h, k] using hfg)
        ((he.resolve_left h).trans (hg.resolve_left k).symm)
  have hc := Finset.card_le_card_of_injOn f
    (s := S.filter (fun e => e.val.1=i ∨ e.val.2=i))
    (t := Finset.univ.erase i) (fun e he => Finset.mem_erase.mpr ⟨hi e he, Finset.mem_univ _⟩) hf
  simpa [edgeDegree] using hc

private lemma mr_optional_disjoint {n : ℕ} (P : DegreeProblem n)
    {T : Finset (Edge n)} (hT : T ⊆ optionalEdges P) : Disjoint P.forced T := by
  apply Finset.disjoint_left.mpr
  intro e he ht
  exact (Finset.mem_sdiff.mp (hT ht)).2 he

private lemma mr_feasible_split {n : ℕ} (P : DegreeProblem n)
    (hP : ∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n-1))
    (S : Finset (Edge n)) :
    EdgeFeasible P S ↔ ∃ T : Finset (Edge n), T ⊆ optionalEdges P ∧
      (∀ i, edgeDegree T i ≤ remainingCap P i) ∧ S=P.forced ∪ T := by
  constructor
  · rintro ⟨hFS, hS⟩
    refine ⟨S \ P.forced, ?_, ?_, ?_⟩
    · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)
    · intro i
      have hd : Disjoint P.forced (S \ P.forced) := by
        exact Finset.disjoint_left.mpr (fun e he ht => (Finset.mem_sdiff.mp ht).2 he)
      have hu : P.forced ∪ (S \ P.forced) = S := Finset.union_sdiff_of_subset hFS
      have heq := mr_degree_union hd i
      rw [hu] at heq
      have hb := mr_degree_bound S i
      dsimp [remainingCap]
      have hp := hP i
      have hs := hS i
      omega
    · exact (Finset.union_sdiff_of_subset hFS).symm
  · rintro ⟨T, hT, hb, rfl⟩
    refine ⟨Finset.subset_union_left, fun i => ?_⟩
    rw [mr_degree_union (mr_optional_disjoint P hT)]
    have h := hb i
    have hp := hP i
    dsimp [remainingCap] at h
    have := min_le_left (P.cap i) (n-1)
    omega

private lemma mr_feasible_iff {n : ℕ} (P : DegreeProblem n) :
    (∃ S, EdgeFeasible P S) ↔ ∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n-1) := by
  constructor
  · rintro ⟨S, hS⟩ i
    exact le_min ((mr_degree_mono hS.1 i).trans (hS.2 i))
      ((mr_degree_mono hS.1 i).trans (mr_degree_bound S i))
  · intro h
    exact ⟨P.forced, Finset.Subset.refl _, fun i => (h i).trans (min_le_left _ _)⟩

private lemma mr_L_pos {n : ℕ} (P : DegreeProblem n) : 0 < denominatorLCM P := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun e _ => (P.weight e).den_nz)

private lemma mr_integer_cast {n : ℕ} (P : DegreeProblem n) (e : Edge n)
    (he : e ∈ optionalEdges P) :
    (integerWeight P e : ℚ) = (denominatorLCM P : ℚ) * P.weight e := by
  have hd : (P.weight e).den ∣ denominatorLCM P := Finset.dvd_lcm he
  have hd' : ((P.weight e).den : ℤ) ∣ (denominatorLCM P : ℤ) := Int.natCast_dvd_natCast.mpr hd
  rw [integerWeight, Rat.intCast_div _ _ (dvd_mul_of_dvd_left hd' _), Int.cast_mul,
    Int.cast_natCast, Int.cast_natCast, mul_div_assoc, Rat.num_div_den]

private lemma mr_M_pos {n : ℕ} (P : DegreeProblem n) : 0 < gadgetM P := by
  unfold gadgetM
  positivity

private lemma mr_weight_lt_M {n : ℕ} (P : DegreeProblem n)
    (e : {e // e ∈ optionalEdges P}) : integerWeight P e.val < gadgetM P := by
  have h := Finset.le_sup (f := fun e => (integerWeight P e).natAbs) e.property
  have hz : integerWeight P e.val ≤ ((integerWeight P e.val).natAbs : ℤ) := Int.le_natAbs
  dsimp [gadgetM]
  have hh : (integerWeight P e.val).natAbs < 1+(optionalEdges P).sup (fun e => (integerWeight P e).natAbs) := by omega
  exact lt_of_le_of_lt hz (by exact_mod_cast hh)

private lemma mr_cap_bound {n : ℕ} (P : DegreeProblem n) (i : Fin n) :
    remainingCap P i ≤ n-1 :=
  (Nat.sub_le _ _).trans (min_le_right _ _)

private lemma mr_size_bounds {n : ℕ} (hn : 0 < n) (P : DegreeProblem n) :
    (2*(optionalEdges P).card+∑ i, remainingCap P i ≤ 2*n*(n-1)) ∧
    ((optionalEdges P).card+∑ e ∈ optionalEdges P,
      (remainingCap P e.val.1+remainingCap P e.val.2) ≤ (optionalEdges P).card*(2*n-1)) := by
  have hq : (optionalEdges P).card ≤ n*(n-1)/2 := by
    simpa [UpperCompletion.edge_card] using (optionalEdges P).card_le_univ
  have hsum : ∑ i, remainingCap P i ≤ n*(n-1) := by
    calc
      _ ≤ ∑ _i : Fin n, (n-1) := Finset.sum_le_sum (fun i _ => mr_cap_bound P i)
      _ = _ := by simp
  constructor
  · have hq' : 2*(optionalEdges P).card ≤ n*(n-1) := by omega
    nlinarith
  · have hs : ∑ e ∈ optionalEdges P, (remainingCap P e.val.1+remainingCap P e.val.2) ≤
        (optionalEdges P).card * (2*(n-1)) := by
      calc
        _ ≤ ∑ _e ∈ optionalEdges P, (2*(n-1)) :=
          Finset.sum_le_sum (fun e _ => by
            have := mr_cap_bound P e.val.1
            have := mr_cap_bound P e.val.2
            omega)
        _ = _ := by simp
    have he : 2*n-1 = 1+2*(n-1) := by omega
    rw [he, Nat.mul_add, Nat.mul_one]
    omega

private def mr_owner {n : ℕ} {P : DegreeProblem n} :
    GadgetEdge P → {e // e ∈ optionalEdges P}
  | .internal e => e
  | .external e _ _ => e

private def mr_fiber {n : ℕ} {P : DegreeProblem n}
    (J : Finset (GadgetEdge P)) (e : {e // e ∈ optionalEdges P}) : Finset (GadgetEdge P) :=
  J.filter (fun g => mr_owner g = e)

private lemma mr_internal_free {n : ℕ} {P : DegreeProblem n}
    (e : {e // e ∈ optionalEdges P}) (g : GadgetEdge P) (h : mr_owner g ≠ e) :
    (gadgetEnds (.internal e : GadgetEdge P)).1 ≠ (gadgetEnds g).1 ∧
    (gadgetEnds (.internal e : GadgetEdge P)).1 ≠ (gadgetEnds g).2 ∧
    (gadgetEnds (.internal e : GadgetEdge P)).2 ≠ (gadgetEnds g).1 ∧
    (gadgetEnds (.internal e : GadgetEdge P)).2 ≠ (gadgetEnds g).2 := by
  cases g with
  | internal f =>
    change f ≠ e at h
    simp [gadgetEnds, Ne.symm h]
  | external f side slot =>
    change f ≠ e at h
    cases side <;> simp [gadgetEnds, Ne.symm h]

private lemma mr_matching_replace {n : ℕ} {P : DegreeProblem n}
    (J : Finset (GadgetEdge P)) (hJ : IsMatching J)
    (e : {e // e ∈ optionalEdges P}) :
    IsMatching (insert (.internal e) (J.filter (fun g => mr_owner g ≠ e))) := by
  intro g hg f hf hgf
  simp only [Finset.mem_insert, Finset.mem_filter] at hg hf
  rcases hg with rfl | ⟨hg,hge⟩
  · rcases hf with rfl | ⟨hf,hfe⟩
    · exact False.elim (hgf rfl)
    · exact mr_internal_free e f hfe
  · rcases hf with rfl | ⟨hf,hfe⟩
    · have h := mr_internal_free e g hge
      exact ⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩
    · exact hJ g hg f hf hgf

private lemma mr_internal_excludes {n : ℕ} {P : DegreeProblem n}
    {J : Finset (GadgetEdge P)} (hJ : IsMatching J)
    (e : {e // e ∈ optionalEdges P}) (he : GadgetEdge.internal e ∈ J)
    (side : Bool) (s : Fin (remainingCap P (endpoint e.val side))) :
    GadgetEdge.external e side s ∉ J := by
  intro hs
  have h := hJ (.internal e) he (.external e side s) hs (by simp)
  cases side <;> simp [gadgetEnds] at h

private lemma mr_external_unique {n : ℕ} {P : DegreeProblem n}
    {J : Finset (GadgetEdge P)} (hJ : IsMatching J)
    (e : {e // e ∈ optionalEdges P}) (side : Bool)
    (s t : Fin (remainingCap P (endpoint e.val side)))
    (hs : GadgetEdge.external e side s ∈ J) (ht : GadgetEdge.external e side t ∈ J) : s=t := by
  by_contra hst
  have h := hJ (.external e side s) hs (.external e side t) ht (by simpa using hst)
  exact h.1 rfl

private lemma mr_fiber_internal {n : ℕ} {P : DegreeProblem n}
    {J : Finset (GadgetEdge P)} (hJ : IsMatching J)
    (e : {e // e ∈ optionalEdges P}) (he : GadgetEdge.internal e ∈ J) :
    mr_fiber J e = {GadgetEdge.internal e} := by
  ext g
  change (g ∈ J.filter (fun a => mr_owner a=e)) ↔ _
  rw [Finset.mem_filter]
  cases g with
  | internal f =>
    simp only [mr_owner, Finset.mem_singleton, GadgetEdge.internal.injEq]
    exact ⟨And.right, fun h => by subst f; exact ⟨he,rfl⟩⟩
  | external f side slot =>
    by_cases hfe : f=e
    · subst f
      simp [mr_owner,mr_internal_excludes hJ e he side slot]
    · simp [mr_owner,hfe]

private lemma mr_fiber_external {n : ℕ} {P : DegreeProblem n}
    {J : Finset (GadgetEdge P)} (hJ : IsMatching J)
    (e : {e // e ∈ optionalEdges P})
    (s : Fin (remainingCap P (endpoint e.val false)))
    (t : Fin (remainingCap P (endpoint e.val true)))
    (hs : GadgetEdge.external e false s ∈ J) (ht : GadgetEdge.external e true t ∈ J) :
    mr_fiber J e = {GadgetEdge.external e false s, GadgetEdge.external e true t} := by
  have hi : GadgetEdge.internal e ∉ J := fun h => mr_internal_excludes hJ e h false s hs
  ext g
  change (g ∈ J.filter (fun a => mr_owner a=e)) ↔ _
  rw [Finset.mem_filter]
  cases g with
  | internal f =>
    by_cases hfe : f=e
    · subst f; simp [mr_owner,hi]
    · simp [mr_owner,hfe]
  | external f side slot =>
    by_cases hfe : f=e
    · subst f
      cases side
      · simp only [mr_owner, and_true, Finset.mem_insert,
          Finset.mem_singleton, GadgetEdge.external.injEq, true_and, Bool.false_eq_true,
          false_and, or_false, heq_eq_eq]
        exact ⟨fun h => mr_external_unique hJ e false slot s h hs,
          fun h => by subst slot; exact hs⟩
      · simp only [mr_owner, and_true, Finset.mem_insert,
          Finset.mem_singleton, GadgetEdge.external.injEq, true_and, Bool.true_eq_false,
          false_and, false_or, heq_eq_eq]
        exact ⟨fun h => mr_external_unique hJ e true slot t h ht,
          fun h => by subst slot; exact ht⟩
    · simp [mr_owner,hfe]

/-- Replacing one gadget by its internal edge gives a local lower bound at every maximum. -/
private lemma mr_local_lower_bound {n : ℕ} {P : DegreeProblem n}
    {J : Finset (GadgetEdge P)} (hJ : IsMatching J)
    (hmax : ∀ J' : Finset (GadgetEdge P), IsMatching J' →
      (∑ g ∈ J', gadgetWeight g) ≤ ∑ g ∈ J, gadgetWeight g)
    (e : {e // e ∈ optionalEdges P}) :
    4*gadgetM P ≤ ∑ g ∈ mr_fiber J e, gadgetWeight g := by
  have hm := hmax _ (mr_matching_replace J hJ e)
  have hn : GadgetEdge.internal e ∉ J.filter (fun g => mr_owner g ≠ e) := by
    rw [Finset.mem_filter]
    simp [mr_owner]
  rw [Finset.sum_insert hn] at hm
  have hsum := Finset.sum_filter_add_sum_filter_not J (fun g => mr_owner g=e) gadgetWeight
  change (∑ g ∈ mr_fiber J e, gadgetWeight g) +
    (∑ g ∈ J.filter (fun g => ¬mr_owner g=e), gadgetWeight g) = _ at hsum
  change 4*gadgetM P + (∑ g ∈ J.filter (fun g => mr_owner g ≠ e), gadgetWeight g) ≤
    ∑ g ∈ J, gadgetWeight g at hm
  linarith

private lemma mr_max_canonical {n : ℕ} {P : DegreeProblem n}
    {J : Finset (GadgetEdge P)} (hJ : IsMatching J)
    (hmax : ∀ J' : Finset (GadgetEdge P), IsMatching J' →
      (∑ g ∈ J', gadgetWeight g) ≤ ∑ g ∈ J, gadgetWeight g)
    (e : {e // e ∈ optionalEdges P}) :
    GadgetEdge.internal e ∈ J ∨
      ((∃ s, GadgetEdge.external e false s ∈ J) ∧
       (∃ t, GadgetEdge.external e true t ∈ J)) := by
  by_cases hi : GadgetEdge.internal e ∈ J
  · exact Or.inl hi
  right
  have hl := mr_local_lower_bound hJ hmax e
  have hp := mr_M_pos P
  have hw := mr_weight_lt_M P e
  have side_exists (side : Bool) : ∃ s, GadgetEdge.external e side s ∈ J := by
    by_contra hnone
    push Not at hnone
    have hsingle : ∃ g : Option (GadgetEdge P),
        mr_fiber J e = g.toFinset ∧
        (∀ a ∈ g.toFinset, gadgetWeight a = 2*gadgetM P+integerWeight P e.val) := by
      by_cases hother : ∃ s, GadgetEdge.external e (!side) s ∈ J
      · obtain ⟨s,hs⟩ := hother
        refine ⟨some (.external e (!side) s), ?_, ?_⟩
        · ext g
          change (g ∈ J.filter (fun a => mr_owner a=e)) ↔ _
          rw [Finset.mem_filter]
          cases g with
          | internal f =>
            by_cases hfe : f=e
            · subst f; simp [mr_owner,hi]
            · simp [mr_owner,hfe]
          | external f b slot =>
            by_cases hfe : f=e
            · subst f
              by_cases hb : b=side
              · subst b; simp [mr_owner,hnone]
              · have hb' : b=(!side) := by cases b <;> cases side <;> simp_all
                subst b
                simp only [mr_owner, and_true,
                  Option.toFinset_some, Finset.mem_singleton, GadgetEdge.external.injEq,
                  true_and, heq_eq_eq]
                exact ⟨fun h => mr_external_unique hJ e (!side) slot s h hs,
                  fun h => by subst slot; exact hs⟩
            · simp [mr_owner,hfe]
        · intro a ha
          simp only [Option.toFinset_some, Finset.mem_singleton] at ha
          subst a
          rfl
      · refine ⟨none, ?_, by simp⟩
        push Not at hother
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro g hg
        obtain ⟨hg,he⟩ := Finset.mem_filter.mp hg
        cases g with
        | internal f => dsimp [mr_owner] at he; subst f; exact hi hg
        | external f b slot =>
          dsimp [mr_owner] at he
          subst f
          by_cases hb : b=side
          · subst b; exact hnone slot hg
          · have hb' : b=(!side) := by cases b <;> cases side <;> simp_all
            subst b
            exact hother slot hg
    obtain ⟨g,hg,hweight⟩ := hsingle
    rw [hg] at hl
    cases g with
    | none => simp at hl; omega
    | some a =>
      have hh := hweight a (by simp)
      simp only [Option.toFinset_some, Finset.sum_singleton] at hl
      rw [hh] at hl
      omega
  exact ⟨side_exists false, side_exists true⟩

private lemma mr_decode_iff {n : ℕ} (P : DegreeProblem n)
    (J : Finset (GadgetEdge P)) (e : {e // e ∈ optionalEdges P}) :
    e.val ∈ decodeMatching P J ↔
      ((∃ s, GadgetEdge.external e false s ∈ J) ∧
       (∃ t, GadgetEdge.external e true t ∈ J)) := by
  unfold decodeMatching
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_,he,hs,ht⟩
    exact ⟨hs,ht⟩
  · intro h
    exact ⟨e.property,e.property,h⟩

private lemma mr_decode_subset {n : ℕ} (P : DegreeProblem n)
    (J : Finset (GadgetEdge P)) : decodeMatching P J ⊆ optionalEdges P :=
  Finset.filter_subset _ _

private lemma mr_move_slot {n : ℕ} (P : DegreeProblem n) {i j : Fin n}
    (h : i=j) (s : Fin (remainingCap P i)) :
    ∃ t : Fin (remainingCap P j), (⟨i,s⟩ : Σ k, Fin (remainingCap P k))=⟨j,t⟩ := by
  subst j
  exact ⟨s,rfl⟩

/-- Incident decoded edges inject into the slots used by the matching. -/
private lemma mr_decode_capacity {n : ℕ} (P : DegreeProblem n)
    (J : Finset (GadgetEdge P)) (hJ : IsMatching J) (i : Fin n) :
    edgeDegree (decodeMatching P J) i ≤ remainingCap P i := by
  let D := (decodeMatching P J).filter (fun e => e.val.1=i ∨ e.val.2=i)
  have hslot (e : ↥D) : ∃ s : Fin (remainingCap P i), ∃ g : GadgetEdge P,
      g ∈ J ∧ (mr_owner g).val=e.val ∧ (gadgetEnds g).2=Sum.inl ⟨i,s⟩ := by
    obtain ⟨he,hi⟩ := Finset.mem_filter.mp e.property
    obtain ⟨_,heP,⟨s,hs⟩,⟨t,ht⟩⟩ := Finset.mem_filter.mp he
    rcases hi with hi | hi
    · obtain ⟨s',hh⟩ := mr_move_slot P hi s
      exact ⟨s',.external ⟨e.val,heP⟩ false s,hs,rfl,congrArg Sum.inl hh⟩
    · obtain ⟨t',hh⟩ := mr_move_slot P hi t
      exact ⟨t',.external ⟨e.val,heP⟩ true t,ht,rfl,congrArg Sum.inl hh⟩
  choose slot g hg ho he using hslot
  have hinj : Function.Injective slot := by
    intro e f hef
    have hgf : g e=g f := by
      by_contra hne
      have hd := (hJ _ (hg e) _ (hg f) hne).2.2.2
      apply hd
      rw [he e, he f, hef]
    apply Subtype.ext
    exact (ho e).symm.trans ((congrArg (fun a => (mr_owner a).val) hgf).trans (ho f))
  have hh : D.card ≤ remainingCap P i := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective slot hinj
  exact hh

private lemma mr_canonical_weight {n : ℕ} (P : DegreeProblem n)
    (J : Finset (GadgetEdge P)) (hJ : IsMatching J)
    (hc : ∀ e : {e // e ∈ optionalEdges P}, GadgetEdge.internal e ∈ J ∨
      ((∃ s, GadgetEdge.external e false s ∈ J) ∧
       (∃ t, GadgetEdge.external e true t ∈ J))) :
    (∑ g ∈ J, gadgetWeight g) =
      4*gadgetM P*(optionalEdges P).card +
        2*∑ e ∈ decodeMatching P J, integerWeight P e := by
  have hlocal (e : {e // e ∈ optionalEdges P}) :
      (∑ g ∈ mr_fiber J e, gadgetWeight g) =
        4*gadgetM P + if e.val ∈ decodeMatching P J then 2*integerWeight P e.val else 0 := by
    rcases hc e with hi | ⟨⟨s,hs⟩,⟨t,ht⟩⟩
    · have hn : e.val ∉ decodeMatching P J := by
        intro hd
        obtain ⟨⟨s,hs⟩,_⟩ := (mr_decode_iff P J e).mp hd
        exact mr_internal_excludes hJ e hi false s hs
      rw [mr_fiber_internal hJ e hi]
      simp [hn,gadgetWeight]
    · have hd : e.val ∈ decodeMatching P J := (mr_decode_iff P J e).mpr ⟨⟨s,hs⟩,⟨t,ht⟩⟩
      rw [mr_fiber_external hJ e s t hs ht]
      simp [hd,gadgetWeight]
      ring
  have hfilt : (optionalEdges P).filter (fun e => e ∈ decodeMatching P J) = decodeMatching P J := by
    ext e
    rw [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => mr_decode_subset P J h)
  have hs : (∑ e : {e // e ∈ optionalEdges P},
      if e.val ∈ decodeMatching P J then 2*integerWeight P e.val else 0) =
        2*∑ e ∈ decodeMatching P J, integerWeight P e := by
    rw [Finset.sum_coe_sort (optionalEdges P)
      (fun e => if e ∈ decodeMatching P J then 2*integerWeight P e else 0),
      ← Finset.sum_filter, hfilt, Finset.mul_sum]
  calc
    _ = ∑ e : {e // e ∈ optionalEdges P}, ∑ g ∈ mr_fiber J e, gadgetWeight g :=
      (Finset.sum_fiberwise J mr_owner gadgetWeight).symm
    _ = ∑ e : {e // e ∈ optionalEdges P},
        (4*gadgetM P + if e.val ∈ decodeMatching P J then 2*integerWeight P e.val else 0) :=
      Finset.sum_congr rfl (fun e _ => hlocal e)
    _ = _ := by
      rw [Finset.sum_add_distrib, hs]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

private abbrev mr_Inc {n : ℕ} (T : Finset (Edge n)) (i : Fin n) :=
  ↥(T.filter (fun e => e.val.1=i ∨ e.val.2=i))

private def mr_slot {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i)) (e : Edge n) (he : e ∈ T)
    (side : Bool) : Fin (remainingCap P (endpoint e side)) :=
  ρ (endpoint e side) ⟨e,Finset.mem_filter.mpr ⟨he,by cases side <;> simp [endpoint]⟩⟩

private lemma mr_slot_injective {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i))
    (e f : Edge n) (he : e ∈ T) (hf : f ∈ T) (a b : Bool)
    (h : (⟨endpoint e a,mr_slot P T ρ e he a⟩ : Σ i, Fin (remainingCap P i)) =
      ⟨endpoint f b,mr_slot P T ρ f hf b⟩) : e=f := by
  let E : (Σ i, mr_Inc T i) ↪ (Σ i, Fin (remainingCap P i)) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl _) ρ
  have hh : E ⟨endpoint e a,⟨e,Finset.mem_filter.mpr ⟨he,by cases a <;> simp [endpoint]⟩⟩⟩ =
      E ⟨endpoint f b,⟨f,Finset.mem_filter.mpr ⟨hf,by cases b <;> simp [endpoint]⟩⟩⟩ := h
  exact congrArg (fun x : Σ i, mr_Inc T i => x.2.val) (E.injective hh)

private lemma mr_endpoint_injective {n : ℕ} (e : Edge n) : Function.Injective (endpoint e) := by
  intro a b hab
  have hne := ne_of_lt e.property
  cases a <;> cases b <;> simp_all [endpoint]

private def mr_piece {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i))
    (e : {e // e ∈ optionalEdges P}) : Finset (GadgetEdge P) :=
  if he : e.val ∈ T then
    {GadgetEdge.external e false (mr_slot P T ρ e.val he false),
     GadgetEdge.external e true (mr_slot P T ρ e.val he true)}
  else {GadgetEdge.internal e}

private def mr_liftSet {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i)) : Finset (GadgetEdge P) :=
  Finset.univ.biUnion (mr_piece P T ρ)

private lemma mr_lift_mem {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i)) (g : GadgetEdge P) :
    g ∈ mr_liftSet P T ρ ↔
      (∃ e : {e // e ∈ optionalEdges P}, e.val ∉ T ∧ g=GadgetEdge.internal e) ∨
      (∃ e : {e // e ∈ optionalEdges P}, ∃ he : e.val ∈ T, ∃ side : Bool,
        g=GadgetEdge.external e side (mr_slot P T ρ e.val he side)) := by
  unfold mr_liftSet
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨e,_,hg⟩
    unfold mr_piece at hg
    split_ifs at hg with he
    · rcases Finset.mem_insert.mp hg with h | h
      · exact Or.inr ⟨e,he,false,h⟩
      · exact Or.inr ⟨e,he,true,Finset.mem_singleton.mp h⟩
    · exact Or.inl ⟨e,he,Finset.mem_singleton.mp hg⟩
  · rintro (⟨e,he,rfl⟩ | ⟨e,he,side,rfl⟩)
    · exact ⟨e,Finset.mem_univ _,by simp [mr_piece,he]⟩
    · refine ⟨e,Finset.mem_univ _,?_⟩
      cases side <;> simp [mr_piece,he]

private lemma mr_lift_matching {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i)) : IsMatching (mr_liftSet P T ρ) := by
  intro g hg f hf hgf
  rw [mr_lift_mem] at hg hf
  rcases hg with ⟨e,he,rfl⟩ | ⟨e,he,a,rfl⟩
  · rcases hf with ⟨d,hd,rfl⟩ | ⟨d,hd,b,rfl⟩
    · have hde : d ≠ e := by intro h; subst d; exact hgf rfl
      exact mr_internal_free e (.internal d) hde
    · have hde : d ≠ e := by intro h; subst d; exact he hd
      exact mr_internal_free e (.external d b _) hde
  · rcases hf with ⟨d,hd,rfl⟩ | ⟨d,hd,b,rfl⟩
    · have hed : e ≠ d := by intro h; subst d; exact hd he
      have h := mr_internal_free d (.external e a (mr_slot P T ρ e.val he a)) hed
      exact ⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩
    · refine ⟨?_,by simp [gadgetEnds],by simp [gadgetEnds],?_⟩
      · intro h
        have hh : (e,a)=(d,b) := Sum.inr.inj h
        obtain ⟨hed,hab⟩ := Prod.mk.inj hh
        subst d
        subst b
        exact hgf rfl
      · intro h
        have hh : (⟨endpoint e.val a,mr_slot P T ρ e.val he a⟩ : Σ i, Fin (remainingCap P i)) =
            ⟨endpoint d.val b,mr_slot P T ρ d.val hd b⟩ := Sum.inl.inj h
        have hed : e=d := Subtype.ext (mr_slot_injective P T ρ e.val d.val he hd a b hh)
        subst d
        have hab : a=b := mr_endpoint_injective e.val (congrArg Sigma.fst hh)
        subst b
        exact hgf rfl

private lemma mr_lift_decode {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (hT : T ⊆ optionalEdges P) (ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i)) :
    decodeMatching P (mr_liftSet P T ρ) = T := by
  apply Finset.Subset.antisymm
  · intro e he
    let d : {e // e ∈ optionalEdges P} := ⟨e,mr_decode_subset P _ he⟩
    obtain ⟨⟨s,hs⟩,_⟩ := (mr_decode_iff P _ d).mp he
    rw [mr_lift_mem] at hs
    rcases hs with ⟨f,hf,h⟩ | ⟨f,hf,b,h⟩
    · cases h
    · have hh := congrArg (fun g => (mr_owner g).val) h
      change e=f.val at hh
      rw [hh]
      exact hf
  · intro e he
    let d : {e // e ∈ optionalEdges P} := ⟨e,hT he⟩
    apply (mr_decode_iff P _ d).mpr
    constructor
    · exact ⟨mr_slot P T ρ e he false,(mr_lift_mem P T ρ _).mpr (Or.inr ⟨d,he,false,rfl⟩)⟩
    · exact ⟨mr_slot P T ρ e he true,(mr_lift_mem P T ρ _).mpr (Or.inr ⟨d,he,true,rfl⟩)⟩

/-- Independent incidence embeddings at each vertex lift every feasible optional edge set. -/
private lemma mr_lift {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (hT : T ⊆ optionalEdges P) (hb : ∀ i, edgeDegree T i ≤ remainingCap P i) :
    ∃ J : Finset (GadgetEdge P), IsMatching J ∧ decodeMatching P J=T ∧
      (∑ g ∈ J, gadgetWeight g) =
        4*gadgetM P*(optionalEdges P).card + 2*∑ e ∈ T, integerWeight P e := by
  have hr (i : Fin n) : Nonempty (mr_Inc T i ↪ Fin (remainingCap P i)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_coe,Fintype.card_fin,edgeDegree] using hb i
  let ρ : ∀ i, mr_Inc T i ↪ Fin (remainingCap P i) := fun i => Classical.choice (hr i)
  have hJ := mr_lift_matching P T ρ
  have hd := mr_lift_decode P T hT ρ
  refine ⟨mr_liftSet P T ρ,hJ,hd,?_⟩
  rw [mr_canonical_weight P _ hJ,hd]
  intro e
  by_cases he : e.val ∈ T
  · right
    exact ⟨⟨mr_slot P T ρ e.val he false,
      (mr_lift_mem P T ρ _).mpr (Or.inr ⟨e,he,false,rfl⟩)⟩,
      ⟨mr_slot P T ρ e.val he true,
      (mr_lift_mem P T ρ _).mpr (Or.inr ⟨e,he,true,rfl⟩)⟩⟩
  · exact Or.inl ((mr_lift_mem P T ρ _).mpr (Or.inl ⟨e,he,rfl⟩))

private lemma mr_objective_union {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (hT : T ⊆ optionalEdges P) :
    edgeObjective P (P.forced ∪ T) = edgeObjective P P.forced + ∑ e ∈ T, P.weight e := by
  exact Finset.sum_union (mr_optional_disjoint P hT)

private lemma mr_integer_sum {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (hT : T ⊆ optionalEdges P) :
    ((∑ e ∈ T, integerWeight P e : ℤ) : ℚ) =
      (denominatorLCM P : ℚ) * ∑ e ∈ T, P.weight e := by
  rw [Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e he => mr_integer_cast P e (hT he))

private lemma mr_weight_cast {n : ℕ} (P : DegreeProblem n) (T : Finset (Edge n))
    (hT : T ⊆ optionalEdges P) (J : Finset (GadgetEdge P))
    (hW : (∑ g ∈ J, gadgetWeight g) =
      4*gadgetM P*(optionalEdges P).card + 2*∑ e ∈ T, integerWeight P e) :
    ((∑ g ∈ J, gadgetWeight g : ℤ) : ℚ) =
      4*(gadgetM P : ℚ)*(optionalEdges P).card +
        2*(denominatorLCM P : ℚ)*∑ e ∈ T, P.weight e := by
  rw [hW]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
  rw [mr_integer_sum P T hT]
  ring

private lemma mr_maximum_decodes {n : ℕ} (P : DegreeProblem n)
    (hP : ∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n-1))
    (J : Finset (GadgetEdge P)) (hJ : IsMatching J)
    (hmax : ∀ J' : Finset (GadgetEdge P), IsMatching J' →
      (∑ e ∈ J', gadgetWeight e) ≤ ∑ e ∈ J, gadgetWeight e) :
    EdgeFeasible P (P.forced ∪ decodeMatching P J) ∧
    (∀ S, EdgeFeasible P S → edgeObjective P S ≤ edgeObjective P (P.forced ∪ decodeMatching P J)) ∧
    edgeObjective P (P.forced ∪ decodeMatching P J) =
      edgeObjective P P.forced +
        ((∑ e ∈ J, gadgetWeight e : ℤ) - 4*gadgetM P*(optionalEdges P).card : ℚ)
          /(2*(denominatorLCM P : ℚ)) := by
  have hT := mr_decode_subset P J
  have hb := mr_decode_capacity P J hJ
  have hc := mr_max_canonical hJ hmax
  have hW := mr_canonical_weight P J hJ hc
  have hWq := mr_weight_cast P _ hT J hW
  have hL : (0 : ℚ) < denominatorLCM P := by exact_mod_cast mr_L_pos P
  refine ⟨(mr_feasible_split P hP _).mpr ⟨decodeMatching P J,hT,hb,rfl⟩,?_,?_⟩
  · intro S hS
    obtain ⟨U,hU,hbU,hSU⟩ := (mr_feasible_split P hP S).mp hS
    obtain ⟨K,hK,_,hWK⟩ := mr_lift P U hU hbU
    have hKq := mr_weight_cast P U hU K hWK
    have hcmp : ((∑ e ∈ K, gadgetWeight e : ℤ) : ℚ) ≤
        ((∑ e ∈ J, gadgetWeight e : ℤ) : ℚ) := by exact_mod_cast hmax K hK
    rw [hKq,hWq] at hcmp
    have hs : (∑ e ∈ U, P.weight e) ≤ ∑ e ∈ decodeMatching P J, P.weight e := by
      apply (mul_le_mul_iff_right₀ (show (0 : ℚ) < 2*(denominatorLCM P : ℚ) by positivity)).mp
      exact le_of_add_le_add_left hcmp
    calc
      edgeObjective P S = edgeObjective P P.forced + ∑ e ∈ U, P.weight e :=
        (congrArg (edgeObjective P) hSU).trans (mr_objective_union P U hU)
      _ ≤ edgeObjective P P.forced + ∑ e ∈ decodeMatching P J, P.weight e := add_le_add (le_refl _) hs
      _ = edgeObjective P (P.forced ∪ decodeMatching P J) := (mr_objective_union P _ hT).symm
  · rw [mr_objective_union P _ hT]
    congr 1
    apply (eq_div_iff (show (2 : ℚ)*(denominatorLCM P : ℚ) ≠ 0 by positivity)).mpr
    push_cast at hWq ⊢
    nlinarith only [hWq]

theorem matching_reduction_proof {n : ℕ} (hn : 0 < n) (P : DegreeProblem n) :
    ((∃ S, EdgeFeasible P S) ↔ ∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n-1)) ∧
    ((∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n-1)) →
      (∀ S, EdgeFeasible P S ↔ ∃ T : Finset (Edge n), T ⊆ optionalEdges P ∧
        (∀ i, edgeDegree T i ≤ remainingCap P i) ∧ S=P.forced ∪ T) ∧
      (∀ J : Finset (GadgetEdge P), IsMatching J →
        (∀ J' : Finset (GadgetEdge P), IsMatching J' →
          (∑ e ∈ J', gadgetWeight e) ≤ ∑ e ∈ J, gadgetWeight e) →
        EdgeFeasible P (P.forced ∪ decodeMatching P J) ∧
        (∀ S, EdgeFeasible P S → edgeObjective P S ≤ edgeObjective P (P.forced ∪ decodeMatching P J)) ∧
        edgeObjective P (P.forced ∪ decodeMatching P J) =
          edgeObjective P P.forced +
            ((∑ e ∈ J, gadgetWeight e : ℤ) - 4*gadgetM P*(optionalEdges P).card : ℚ)
              /(2*(denominatorLCM P : ℚ)))) ∧
    (2*(optionalEdges P).card+∑ i, remainingCap P i ≤ 2*n*(n-1)) ∧
    ((optionalEdges P).card+∑ e ∈ optionalEdges P,
      (remainingCap P e.val.1+remainingCap P e.val.2) ≤ (optionalEdges P).card*(2*n-1)) := by
  refine ⟨mr_feasible_iff P,?_,(mr_size_bounds hn P).1,(mr_size_bounds hn P).2⟩
  intro hP
  exact ⟨mr_feasible_split P hP,fun J hJ hmax => mr_maximum_decodes P hP J hJ hmax⟩

end
end AronowAudit.P011.Wave1
