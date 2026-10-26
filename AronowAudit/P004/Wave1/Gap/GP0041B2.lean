import AronowAudit.P004.P004_Spatial
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
Thin-rectangle counterexamples, diameter-based interference cutoffs,
and polygon counting bounds.
-/

namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section

set_option maxHeartbeats 1000000

/-! ## P004-T16: thin rectangles -/

/-- Transport the coordinate box through the volume-preserving `ofLp` map. -/
lemma spacing_rectangle_volume (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    volume (rectangle a b c d) = ENNReal.ofReal ((b-a)*(d-c)) := by
  have hbox : rectangle a b c d =
      (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹'
        Set.Icc (![a,c] : Fin 2 → ℝ) ![b,d] := by
    ext x
    change (a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d) ↔
      ((![a,c] : Fin 2 → ℝ) ≤ WithLp.ofLp x ∧
        WithLp.ofLp x ≤ (![b,d] : Fin 2 → ℝ))
    simp [Pi.le_def, Fin.forall_fin_two, and_assoc, and_left_comm, and_comm]
  rw [hbox, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (ENNReal.ofReal_mul (sub_nonneg.mpr hab)).symm

lemma spacing_dist_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0-y 0)^2 + (x 1-y 1)^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- One exhibited pair bounds the real infimum; no set-distance triangle rule is used. -/
lemma spacing_sInf_le {S T : Set (EuclideanSpace ℝ (Fin 2))}
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ S) (hy : y ∈ T) :
    sInf {r : ℝ | ∃ x ∈ S, ∃ y ∈ T, dist x y = r} ≤ dist x y := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨u, hu, v, hv, rfl⟩
    exact dist_nonneg
  · exact ⟨x, hx, y, hy, rfl⟩

lemma spacing_areas (n : ℕ) (hn : 0 < n) :
    ∀ i, volume (thinPolygon n i) = 1 := by
  intro i
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hi : i = 0
  · simp only [thinPolygon, if_pos hi]
    rw [spacing_rectangle_volume 0 1 0 1 (by norm_num) (by norm_num)]
    norm_num
  · simp only [thinPolygon, if_neg hi]
    have hw : (2 : ℝ) ≤ 2+n := by linarith
    have hh : 2*((i : ℝ)-1)/(n : ℝ) ≤
        (2*((i : ℝ)-1)+1)/(n : ℝ) := by
      apply (div_le_div_iff_of_pos_right hnR).mpr
      linarith
    rw [spacing_rectangle_volume _ _ _ _ hw hh]
    have harea : ((2+(n : ℝ))-2) *
        ((2*((i : ℝ)-1)+1)/(n : ℝ) - 2*((i : ℝ)-1)/(n : ℝ)) = 1 := by
      field_simp [ne_of_gt hnR] <;> ring
    rw [harea]
    norm_num

lemma spacing_disjoint (n : ℕ) (hn : 0 < n) :
    Pairwise (fun i j => Disjoint (thinPolygon n i) (thinPolygon n j)) := by
  intro i j hij
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by intro hj; exact hij (hi.trans hj.symm)
    simp only [thinPolygon, if_pos hi, rectangle, Set.mem_setOf_eq] at hx
    simp only [thinPolygon, if_neg hj, rectangle, Set.mem_setOf_eq] at hy
    linarith [hx.2.1, hy.1]
  · by_cases hj : j = 0
    · simp only [thinPolygon, if_neg hi, rectangle, Set.mem_setOf_eq] at hx
      simp only [thinPolygon, if_pos hj, rectangle, Set.mem_setOf_eq] at hy
      linarith [hx.1, hy.2.1]
    · simp only [thinPolygon, if_neg hi, rectangle, Set.mem_setOf_eq] at hx
      simp only [thinPolygon, if_neg hj, rectangle, Set.mem_setOf_eq] at hy
      have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · have hgap : (i : ℝ)+1 ≤ (j : ℝ) := by
          exact_mod_cast (show i.val+1 ≤ j.val by omega)
        have hedges : (2*((i : ℝ)-1)+1)/(n : ℝ) <
            2*((j : ℝ)-1)/(n : ℝ) := by
          apply (div_lt_div_iff_of_pos_right hnR).mpr
          linarith
        linarith [hx.2.2.2, hy.2.2.1]
      · have hgap : (j : ℝ)+1 ≤ (i : ℝ) := by
          exact_mod_cast (show j.val+1 ≤ i.val by omega)
        have hedges : (2*((j : ℝ)-1)+1)/(n : ℝ) <
            2*((i : ℝ)-1)/(n : ℝ) := by
          apply (div_lt_div_iff_of_pos_right hnR).mpr
          linarith
        linarith [hy.2.2.2, hx.2.2.1]

lemma spacing_nearby (n : ℕ) (hn : 0 < n) (i : Fin (n+1)) :
    sInf {r : ℝ | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i,
      dist x y = r} < 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hi : i = 0
  · subst i
    let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0,0]
    have hx : x ∈ thinPolygon n 0 := by norm_num [thinPolygon, rectangle, x]
    have hle := spacing_sInf_le hx hx
    have h0 : dist x x < 2 := by
      rw [dist_self]
      norm_num
    exact lt_of_le_of_lt hle h0
  · have hiNat : 1 ≤ i.val := by
      have hiNat0 : i.val ≠ 0 := by
        intro h
        apply hi
        exact Fin.ext h
      omega
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hiNat
    have hiBound : i.val < n+1 := i.isLt
    have hiN : (i : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show i.val ≤ n by omega)
    let a : ℝ := 2*((i : ℝ)-1)/(n : ℝ)
    have ha0 : 0 ≤ a := div_nonneg (by linarith) hnR.le
    have ha2 : a < 2 := by
      dsimp [a]
      apply (div_lt_iff₀ hnR).mpr
      linarith
    let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1,min a 1]
    let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![2,a]
    have hx : x ∈ thinPolygon n 0 := by
      simp only [thinPolygon, if_pos rfl, rectangle, Set.mem_setOf_eq]
      change 0 ≤ (1 : ℝ) ∧ 1 ≤ (1 : ℝ) ∧ 0 ≤ min a 1 ∧ min a 1 ≤ 1
      exact ⟨by norm_num, le_rfl, le_min ha0 (by norm_num), min_le_right _ _⟩
    have hy : y ∈ thinPolygon n i := by
      simp only [thinPolygon, if_neg hi, rectangle, Set.mem_setOf_eq]
      change (2 : ℝ) ≤ 2 ∧ 2 ≤ 2+(n : ℝ) ∧
        a ≤ a ∧ a ≤ (2*((i : ℝ)-1)+1)/(n : ℝ)
      refine ⟨le_rfl, by linarith, le_rfl, ?_⟩
      dsimp [a]
      apply (div_le_div_iff_of_pos_right hnR).mpr
      linarith
    have hsq : dist x y ^ 2 = 1+(min a 1-a)^2 := by
      calc
        dist x y ^ 2 = (x 0-y 0)^2+(x 1-y 1)^2 := spacing_dist_sq x y
        _ = 1+(min a 1-a)^2 := by
          change (1-2 : ℝ)^2+(min a 1-a)^2 = 1+(min a 1-a)^2
          norm_num
    have hdist : dist x y < 2 := by
      by_cases ha1 : a ≤ 1
      · rw [min_eq_left ha1] at hsq
        nlinarith [sq_nonneg (dist x y-2)]
      · have ha1' : 1 ≤ a := le_of_not_ge ha1
        rw [min_eq_right ha1'] at hsq
        have hprod : 0 < a*(2-a) := mul_pos (by linarith) (by linarith)
        have hs : (1-a)^2 < 1 := by nlinarith [hprod]
        nlinarith [sq_nonneg (dist x y-2)]
    exact lt_of_le_of_lt (spacing_sInf_le hx hy) hdist

theorem polygon_spacing_counterexample_proof :
    (∀ n : ℕ, 0 < n →
      (∀ i, volume (thinPolygon n i) = 1) ∧
      Pairwise (fun i j => Disjoint (thinPolygon n i) (thinPolygon n j)) ∧
      (∀ i : Fin (n+1), sInf {r : ℝ | ∃ x ∈ thinPolygon n 0, ∃ y ∈ thinPolygon n i, dist x y = r} < 2)) ∧
    (∀ C : ℝ, ∃ n : ℕ, 0 < n ∧ C < (n+1 : ℝ)) := by
  constructor
  · intro n hn
    exact ⟨spacing_areas n hn, spacing_disjoint n hn, spacing_nearby n hn⟩
  · intro C
    obtain ⟨k, hk⟩ := exists_nat_gt C
    refine ⟨k+1, Nat.succ_pos _, ?_⟩
    push_cast
    linarith

/-! ## P004-T17(a): finite source range plus a diameter bound -/

lemma diameter_separation_le {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) {i j : Fin N} {a b : A}
    (ha : a ∈ P.node i) (hb : b ∈ P.node j) :
    nodeSeparation P i j ≤ dist a b := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨x, hx, y, hy, rfl⟩
    exact dist_nonneg
  · exact ⟨a, ha, b, hb, rfl⟩

/-- An off-diagonal changed average yields a changed point in its actual region. -/
lemma diameter_affected_point {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (d dbar : ℝ)
    (hband : P.bands d ⊆ Set.Icc 0 d) (hWD : WellDefined P d)
    (hrange : FiniteSourceRange P dbar) {i l : Fin N}
    (hil : i ≠ l) (hinf : interferes (circleAverage P d) i l) :
    ∃ x ∈ region P i d, nodeDistance P i x ≤ d ∧ nodeDistance P l x ≤ dbar := by
  rcases hinf with hdiag | ⟨z, z', hflip, hchange⟩
  · exact (hil hdiag).elim
  · have hpoint : ∃ x ∈ region P i d, P.outcome x z ≠ P.outcome x z' := by
      by_contra hnone
      push_neg at hnone
      have hint : (∫ x in region P i d, P.outcome x z ∂P.zeta) =
          ∫ x in region P i d, P.outcome x z' ∂P.zeta :=
        setIntegral_congr_fun (hWD i).1 hnone
      apply hchange
      change (∫ x in region P i d, P.outcome x z ∂P.zeta) /
          (P.zeta (region P i d)).toReal =
        (∫ x in region P i d, P.outcome x z' ∂P.zeta) /
          (P.zeta (region P i d)).toReal
      rw [hint]
    obtain ⟨x, hx, hchangeX⟩ := hpoint
    have hnearI : nodeDistance P i x ≤ d := (hband hx).2
    have hnearL : nodeDistance P l x ≤ dbar := by
      apply le_of_not_gt
      intro hfar
      exact hchangeX (hrange l x z z' hflip hfar)
    exact ⟨x, hx, hnearI, hnearL⟩

/-- Keep the intermediate affected point, so the five-edge chain is explicit. -/
lemma diameter_localization {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (hcompact : ∀ i, IsCompact (P.node i))
    (d dbar : ℝ) (hband : P.bands d ⊆ Set.Icc 0 d) (hWD : WellDefined P d)
    (hrange : FiniteSourceRange P dbar) {i l : Fin N}
    (hil : i ≠ l) (hinf : interferes (circleAverage P d) i l) :
    ∃ x a, a ∈ P.node i ∧ ∃ u ∈ P.node l,
      dist a x ≤ d ∧ dist x u ≤ dbar := by
  obtain ⟨x, hx, hxi, hxl⟩ := diameter_affected_point P d dbar hband hWD hrange hil hinf
  obtain ⟨a, ha, hda⟩ := (hcompact i).exists_infDist_eq_dist (P.node_nonempty i) x
  obtain ⟨u, hu, hdu⟩ := (hcompact l).exists_infDist_eq_dist (P.node_nonempty l) x
  refine ⟨x, a, ha, u, hu, ?_, ?_⟩
  · rw [dist_comm]
    change Metric.infDist x (P.node i) ≤ d at hxi
    rwa [hda] at hxi
  · change Metric.infDist x (P.node l) ≤ dbar at hxl
    rwa [hdu] at hxl

theorem diameter_interference_cutoff_proof {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (hcompact : ∀ i, IsCompact (P.node i))
    (d dbar D : ℝ) (hd : 0 ≤ d) (hb : 0 ≤ dbar) (hD : 0 ≤ D)
    (hband : P.bands d ⊆ Set.Icc 0 d) (hWD : WellDefined P d)
    (hrange : FiniteSourceRange P dbar)
    (hdiam : ∀ i, ∀ x ∈ P.node i, ∀ y ∈ P.node i, dist x y ≤ D) :
    ∀ i j, i ≠ j → sharesSource (circleAverage P d) i j →
      nodeSeparation P i j ≤ 2*dbar+2*d+D := by
  intro i j hij hshare
  obtain ⟨l, hil, hjl⟩ := hshare
  by_cases hli : l = i
  · subst l
    obtain ⟨y, b, hbnode, u, hunode, hby, hyu⟩ :=
      diameter_localization P hcompact d dbar hband hWD hrange hij.symm hjl
    have hsep := diameter_separation_le P hunode hbnode
    have htri := dist_triangle u y b
    have huy : dist u y ≤ dbar := by simpa only [dist_comm] using hyu
    have hyb : dist y b ≤ d := by simpa only [dist_comm] using hby
    linarith
  · by_cases hlj : l = j
    · subst l
      obtain ⟨x, a, hanode, u, hunode, hax, hxu⟩ :=
        diameter_localization P hcompact d dbar hband hWD hrange hij hil
      have hsep := diameter_separation_le P hanode hunode
      have htri := dist_triangle a x u
      linarith
    · obtain ⟨x, a, hanode, u, hunode, hax, hxu⟩ :=
        diameter_localization P hcompact d dbar hband hWD hrange (Ne.symm hli) hil
      obtain ⟨y, b, hbnode, v, hvnode, hby, hyv⟩ :=
        diameter_localization P hcompact d dbar hband hWD hrange (Ne.symm hlj) hjl
      have huv : dist u v ≤ D := hdiam l u hunode v hvnode
      have hvy : dist v y ≤ dbar := by simpa only [dist_comm] using hyv
      have hyb : dist y b ≤ d := by simpa only [dist_comm] using hby
      exact (diameter_separation_le P hanode hbnode).trans
        (diameter_chain a x u v y b d dbar D hax hxu huv hvy hyb)

/-! ## P004-T17(c): count disjoint polygon interiors by area -/

lemma count_polygon_compact {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : Polygonal S) :
    IsCompact S := by
  obtain ⟨m, v, rfl⟩ := hS
  exact isCompact_iUnion fun i => (Set.finite_range (v i)).isCompact_convexHull ℝ

lemma count_polygon_frontier_null {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : Polygonal S) : volume (frontier S) = 0 := by
  obtain ⟨m, v, rfl⟩ := hS
  let T : Fin m → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i => convexHull ℝ (Set.range (v i))
  have hnull : ∀ i, volume (frontier (T i)) = 0 := by
    intro i
    exact (convex_convexHull ℝ (Set.range (v i))).addHaar_frontier volume
  have hsub : frontier (⋃ i, T i) ⊆ ⋃ i, frontier (T i) := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using
      (Finset.univ : Finset (Fin m)).frontier_biUnion_subset T
  exact measure_mono_null hsub (measure_iUnion_null hnull)

lemma count_polygon_area_interior {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : Polygonal S) : volume (interior S) = volume S := by
  rw [← self_sdiff_frontier]
  exact measure_sdiff_null (count_polygon_frontier_null hS)

/-- Attain the exact source-defined real `sInf`, via a compact product minimum. -/
lemma count_separation_attained {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (i j : Fin N)
    (hi : IsCompact (P.node i)) (hj : IsCompact (P.node j)) :
    ∃ a ∈ P.node i, ∃ b ∈ P.node j, dist a b = nodeSeparation P i j := by
  have hne : (P.node i ×ˢ P.node j).Nonempty :=
    (P.node_nonempty i).prod (P.node_nonempty j)
  have hcont : ContinuousOn (fun p : A × A => dist p.1 p.2)
      (P.node i ×ˢ P.node j) := (continuous_fst.dist continuous_snd).continuousOn
  obtain ⟨p, hp, hmin⟩ := (hi.prod hj).exists_isMinOn hne hcont
  have hdistne : {r : ℝ | ∃ a ∈ P.node i, ∃ b ∈ P.node j, dist a b = r}.Nonempty :=
    ⟨dist p.1 p.2, p.1, hp.1, p.2, hp.2, rfl⟩
  have hlower : dist p.1 p.2 ≤ nodeSeparation P i j := by
    apply le_csInf hdistne
    rintro r ⟨a, ha, b, hb, rfl⟩
    exact (isMinOn_iff.mp hmin) (a,b) ⟨ha,hb⟩
  have hupper : nodeSeparation P i j ≤ dist p.1 p.2 :=
    diameter_separation_le P hp.1 hp.2
  exact ⟨p.1, hp.1, p.2, hp.2, le_antisymm hlower hupper⟩

lemma count_neighbor_containment {N : ℕ}
    (P : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)))
    (D r : ℝ) (hcompact : ∀ i, IsCompact (P.node i))
    (hdiam : ∀ i, ∀ x ∈ P.node i, ∀ y ∈ P.node i, dist x y ≤ D)
    (i : Fin N) {x0 : EuclideanSpace ℝ (Fin 2)} (hx0 : x0 ∈ P.node i)
    {j : Fin N} (hj : j ∈ ball (nodeSeparation P) i r) :
    P.node j ⊆ Metric.closedBall x0 (r+2*D) := by
  have hsep : nodeSeparation P i j ≤ r := (Finset.mem_filter.mp hj).2
  obtain ⟨a, ha, b, hb, hab⟩ :=
    count_separation_attained P i j (hcompact i) (hcompact j)
  intro y hy
  apply Metric.mem_closedBall.mpr
  have h1 : dist x0 a ≤ D := hdiam i x0 hx0 a ha
  have h2 : dist a b ≤ r := hab.le.trans hsep
  have h3 : dist b y ≤ D := hdiam j b hb y hy
  have ht1 := dist_triangle x0 a y
  have ht2 := dist_triangle a b y
  rw [dist_comm y x0]
  linarith

theorem polygon_count_bound_proof {N : ℕ} (P : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)))
    (a D r : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hpoly : ∀ i, Polygonal (P.node i))
    (hdis : Pairwise (fun i j => Disjoint (interior (P.node i)) (interior (P.node j))))
    (harea : ∀ i, ENNReal.ofReal a ≤ volume (P.node i))
    (hdiam : ∀ i, ∀ x ∈ P.node i, ∀ y ∈ P.node i, dist x y ≤ D) :
    ∀ i, ((ball (nodeSeparation P) i r).card : ℝ) ≤ Real.pi*(r+2*D)^2/a := by
  intro i
  let J : Finset (Fin N) := ball (nodeSeparation P) i r
  let R : ℝ := r+2*D
  obtain ⟨x0, hx0⟩ := P.node_nonempty i
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcompact : ∀ j, IsCompact (P.node j) := fun j => count_polygon_compact (hpoly j)
  have hinterior : ∀ j, volume (interior (P.node j)) = volume (P.node j) :=
    fun j => count_polygon_area_interior (hpoly j)
  have hsub : (⋃ j ∈ J, interior (P.node j)) ⊆ Metric.closedBall x0 R := by
    intro y hy
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
    exact count_neighbor_containment P D r hcompact hdiam i hx0 hj
      (interior_subset hyj)
  have hpair : Set.PairwiseDisjoint (↑J : Set (Fin N))
      (fun j => interior (P.node j)) := by
    intro j hj k hk hjk
    exact hdis hjk
  have hunion : volume (⋃ j ∈ J, interior (P.node j)) =
      ∑ j ∈ J, volume (interior (P.node j)) :=
    measure_biUnion_finset hpair (fun j hj => isOpen_interior.measurableSet)
  have hsum : (∑ j ∈ J, ENNReal.ofReal a) ≤
      volume (Metric.closedBall x0 R) := by
    calc
      (∑ j ∈ J, ENNReal.ofReal a) ≤ ∑ j ∈ J, volume (interior (P.node j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [hinterior j]
        exact harea j
      _ = volume (⋃ j ∈ J, interior (P.node j)) := hunion.symm
      _ ≤ volume (Metric.closedBall x0 R) := measure_mono hsub
  have hleft : (∑ j ∈ J, ENNReal.ofReal a) = ENNReal.ofReal ((J.card : ℝ)*a) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj => ha.le)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hdisk : volume (Metric.closedBall x0 R) = ENNReal.ofReal (Real.pi*R^2) := by
    rw [EuclideanSpace.volume_closedBall_fin_two, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hR]
    exact mul_comm _ _
  rw [hleft, hdisk] at hsum
  have hnum : (J.card : ℝ)*a ≤ Real.pi*R^2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum
  change (J.card : ℝ) ≤ Real.pi*(r+2*D)^2/a
  apply (le_div_iff₀ ha).mpr
  exact hnum

end
end AronowAudit.P004.Wave1
