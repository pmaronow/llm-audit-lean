import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellSurvival

/-! Direct finite-sample formulas for marked donor avoidance.

Distinguished labels remain in the multinomial population, outside the forbidden
set.  Their occupancies and the central retention event are kept explicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellFiniteAvoidance (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Avoidance of a finite set of original labels. -/
def markedAvoids {N : ℕ} (D : Finset (Fin N)) (a : Fin N → Fin N) : Prop :=
  ∀ t, a t ∉ D

theorem marked_occupancy_positive_iff {N : ℕ} (a : Fin N → Fin N) (j : Fin N) :
    0 < reuseOccupancy a j ↔ ∃ t, a t = j := by
  simp only [reuseOccupancy,Nat.cast_pos,Finset.card_pos,Finset.filter_nonempty_iff,
    Finset.mem_univ,true_and]

/-- A prescribed finite set of draws, together with avoidance on all draws. -/
theorem marked_forced_avoidance {N k : ℕ} (hN : 0 < N)
    (D : Finset (Fin N)) (e : Fin k ↪ Fin N) (v : Fin k → Fin N)
    (hv : ∀ i, v i ∉ D) :
    mean (UniformResampling N) (fun a =>
      if markedAvoids D a ∧ (∀ i, a (e i) = v i) then 1 else 0) =
      (N : ℝ)⁻¹^k * (1-(D.card : ℝ)/(N : ℝ))^(N-k) := by
  haveI instNonzeroMarkedForced : NeZero N := ⟨hN.ne'⟩
  let S : Finset (Fin N) := Finset.univ.map e
  let f : Fin N → Fin N → ℝ := fun t x =>
    if x ∉ D ∧ (∀ i, e i = t → x = v i) then 1 else 0
  have heq (a : Fin N → Fin N) :
      (if markedAvoids D a ∧ (∀ i, a (e i) = v i) then (1 : ℝ) else 0) =
        ∏ t, f t (a t) := by
    have hi : (markedAvoids D a ∧ (∀ i, a (e i) = v i)) ↔
        ∀ t, a t ∉ D ∧ (∀ i, e i = t → a t = v i) := by
      constructor
      · rintro ⟨hA,hV⟩ t
        exact ⟨hA t,fun i hi => hi ▸ hV i⟩
      · intro h
        exact ⟨fun t => (h t).1,fun i => (h (e i)).2 i rfl⟩
    simp only [hi, f, Fintype.prod_ite_zero, Finset.prod_const_one]
  have hcoord (t : Fin N) :
      (∫ x, f t x ∂(PMF.uniformOfFintype (Fin N)).toMeasure) =
        if t ∈ S then (N : ℝ)⁻¹ else 1-(D.card : ℝ)/(N : ℝ) := by
    rw [uniform_index_integral]
    by_cases ht : t ∈ S
    · obtain ⟨i,_,hi⟩ := Finset.mem_map.mp ht
      have hf (x : Fin N) : f t x = if x = v i then 1 else 0 := by
        dsimp only [f]
        apply if_congr
        · constructor
          · exact fun h => h.2 i hi
          · intro h
            refine ⟨h ▸ hv i,?_⟩
            intro j hj
            have hji : j = i := e.injective (hj.trans hi.symm)
            simpa only [hji] using h
        · rfl
        · rfl
      simp only [hf,Finset.sum_ite_eq',Finset.mem_univ,ite_true,if_pos ht,one_div]
    · have hf (x : Fin N) : f t x = if x ∉ D then 1 else 0 := by
        have hnone : ∀ i, e i ≠ t := by
          intro i hit
          exact ht (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,hit⟩)
        simp only [f,hnone,IsEmpty.forall_iff,forall_true_iff,and_true]
      simp only [hf,if_neg ht]
      have hfilter : (Finset.univ.filter (fun x : Fin N => x ∉ D)) = Dᶜ := by
        ext x
        simp
      have hc : D.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ D
      rw [Finset.sum_boole,hfilter,Finset.card_compl,Fintype.card_fin,Nat.cast_sub hc]
      have hn0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      field_simp
  simp only [heq,mean,uniform_resampling_eq_uniform_pi hN,
    integral_fintype_prod_eq_prod,hcoord]
  have hcard : S.card = k := by simp only [S,Finset.card_map,Finset.card_univ,Fintype.card_fin]
  have hcomp : (Finset.univ.filter (fun t : Fin N => t ∉ S)).card = N-k := by
    have hf : (Finset.univ.filter (fun t : Fin N => t ∉ S)) = Sᶜ := by ext t; simp
    rw [hf,Finset.card_compl,Fintype.card_fin,hcard]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const,Finset.filter_mem_eq_inter,Finset.univ_inter,hcard,hcomp]

/-- An occupancy in a resample that avoids `D`. -/
theorem marked_occupancy_avoidance {N : ℕ} (hN : 0 < N)
    (D : Finset (Fin N)) (i : Fin N) (hi : i ∉ D) :
    mean (UniformResampling N) (fun a =>
      if markedAvoids D a then reuseOccupancy a i else 0) =
      (1-(D.card : ℝ)/(N : ℝ))^(N-1) := by
  have hp (a : Fin N → Fin N) :
      (if markedAvoids D a then reuseOccupancy a i else 0) =
        ∑ t, if markedAvoids D a ∧ a t = i then (1 : ℝ) else 0 := by
    by_cases ha : markedAvoids D a
    · simp [ha,reuseOccupancy,Finset.sum_boole]
    · simp [ha]
  have hc (t : Fin N) :
      mean (UniformResampling N) (fun a =>
        if markedAvoids D a ∧ a t = i then 1 else 0) =
          (N : ℝ)⁻¹ * (1-(D.card : ℝ)/(N : ℝ))^(N-1) := by
    let e : Fin 1 ↪ Fin N := ⟨fun _ => t,fun x y _ => Subsingleton.elim x y⟩
    have he (l : Fin 1) : e l = t := rfl
    simpa only [Fin.forall_fin_one,he,pow_one] using
      marked_forced_avoidance hN D e (fun _ => i) (fun _ => hi)
  simp only [hp,mean]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [show ∀ t, (∫ a, (if markedAvoids D a ∧ a t = i then (1 : ℝ) else 0)
    ∂UniformResampling N) = _ from hc,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  have hn0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

/-- Two occupancies, including the extra diagonal draw when the labels agree. -/
theorem marked_occupancy_product_avoidance {N : ℕ} (hN : 0 < N)
    (D : Finset (Fin N)) (i j : Fin N) (hi : i ∉ D) (hj : j ∉ D) :
    mean (UniformResampling N) (fun a =>
      if markedAvoids D a then reuseOccupancy a i*reuseOccupancy a j else 0) =
      (if i = j then (1-(D.card : ℝ)/(N : ℝ))^(N-1) else 0) +
        ((N-1 : ℕ) : ℝ)/(N : ℝ) * (1-(D.card : ℝ)/(N : ℝ))^(N-2) := by
  let A := 1-(D.card : ℝ)/(N : ℝ)
  have hp (a : Fin N → Fin N) :
      (if markedAvoids D a then reuseOccupancy a i*reuseOccupancy a j else 0) =
        ∑ t, ∑ u, if markedAvoids D a ∧ a t = i ∧ a u = j then (1 : ℝ) else 0 := by
    by_cases ha : markedAvoids D a
    · simp only [ha,true_and,ite_true,reuseOccupancy,Finset.card_filter,Nat.cast_sum,
        Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      by_cases ht : a t = i <;> by_cases hu : a u = j <;> simp [ht,hu]
    · simp [ha]
  have hc (t u : Fin N) :
      mean (UniformResampling N) (fun a =>
        if markedAvoids D a ∧ a t = i ∧ a u = j then 1 else 0) =
        if t = u then (if i = j then (N : ℝ)⁻¹*A^(N-1) else 0)
          else (N : ℝ)⁻¹^2*A^(N-2) := by
    by_cases htu : t = u
    · subst u
      rw [if_pos rfl]
      by_cases hij : i = j
      · subst j
        simp only [and_self,ite_true]
        let e : Fin 1 ↪ Fin N := ⟨fun _ => t,fun x y _ => Subsingleton.elim x y⟩
        have he (l : Fin 1) : e l = t := rfl
        simpa only [Fin.forall_fin_one,he,pow_one,A]
          using marked_forced_avoidance hN D e (fun _ => i) (fun _ => hi)
      · rw [if_neg hij]
        have hz (a : Fin N → Fin N) :
            (if markedAvoids D a ∧ a t = i ∧ a t = j then (1 : ℝ) else 0) = 0 := by
          apply if_neg
          intro h
          exact hij (h.2.1.symm.trans h.2.2)
        simp only [hz,mean,integral_zero]
    · rw [if_neg htu]
      let e : Fin 2 ↪ Fin N := ⟨![t,u],by
        intro x y h
        fin_cases x <;> fin_cases y
        · rfl
        · exact False.elim (htu h)
        · exact False.elim (htu h.symm)
        · rfl⟩
      have hlabel (l : Fin 2) : (![i,j] : Fin 2 → Fin N) l ∉ D := by
        fin_cases l
        · exact hi
        · exact hj
      have he0 : e 0 = t := rfl
      have he1 : e 1 = u := rfl
      simpa only [Fin.forall_fin_two,he0,he1,
        Matrix.cons_val_zero,Matrix.cons_val_one,A] using
        marked_forced_avoidance hN D e ![i,j] hlabel
  have hsum (t : Fin N) :
      (∑ u : Fin N, if t = u then
        (if i = j then (N : ℝ)⁻¹*A^(N-1) else 0)
        else (N : ℝ)⁻¹^2*A^(N-2)) =
      (if i = j then (N : ℝ)⁻¹*A^(N-1) else 0) +
        ((N-1 : ℕ) : ℝ)*((N : ℝ)⁻¹^2*A^(N-2)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    simp only [ite_true]
    congr 1
    have hh : ∀ u ∈ (Finset.univ : Finset (Fin N)).erase t, t ≠ u := by
      intro u hu
      exact Ne.symm (Finset.ne_of_mem_erase hu)
    simp only [Finset.sum_congr rfl (fun u hu => if_neg (hh u hu)),
      Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ t),
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [hp,mean]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  change (∑ t, ∑ u, mean (UniformResampling N)
    (fun a => if markedAvoids D a ∧ a t = i ∧ a u = j then 1 else 0)) = _
  simp only [hc,hsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  change (N : ℝ)*((if i = j then (N : ℝ)⁻¹*A^(N-1) else 0) +
    ((N-1 : ℕ) : ℝ)*((N : ℝ)⁻¹^2*A^(N-2))) = _
  by_cases hij : i = j <;> simp only [hij,ite_true,ite_false,A] <;> field_simp <;> ring

/-- Excluding one further distinguished label exactly imposes its zero mark. -/
theorem marked_central_retention_difference {N : ℕ} (D : Finset (Fin N))
    (j : Fin N) (f : (Fin N → Fin N) → ℝ) :
    mean (UniformResampling N) (fun a =>
      if markedAvoids D a ∧ 0 < reuseOccupancy a j then f a else 0) =
      mean (UniformResampling N) (fun a => if markedAvoids D a then f a else 0) -
        mean (UniformResampling N) (fun a =>
          if markedAvoids (insert j D) a then f a else 0) := by
  have heq (a : Fin N → Fin N) :
      (if markedAvoids D a ∧ 0 < reuseOccupancy a j then f a else 0) =
        (if markedAvoids D a then f a else 0) -
          (if markedAvoids (insert j D) a then f a else 0) := by
    have he : markedAvoids (insert j D) a ↔
        markedAvoids D a ∧ ¬0 < reuseOccupancy a j := by
      simp only [markedAvoids,marked_occupancy_positive_iff,not_exists,
        Finset.mem_insert,not_or]
      aesop
    rw [he]
    by_cases ha : markedAvoids D a <;>
      by_cases hj : 0 < reuseOccupancy a j <;> simp [ha,hj]
  simp only [heq,mean]
  exact integral_sub Integrable.of_finite Integrable.of_finite

/-- Exact central retention times one recipient occupancy. -/
theorem marked_central_recipient_avoidance {N : ℕ} (hN : 0 < N)
    (D : Finset (Fin N)) (j i : Fin N) (hj : j ∉ D) (hi : i ∉ D) (hij : i ≠ j) :
    mean (UniformResampling N) (fun a =>
      if markedAvoids D a ∧ 0 < reuseOccupancy a j then reuseOccupancy a i else 0) =
      (1-(D.card : ℝ)/(N : ℝ))^(N-1) -
        (1-((D.card : ℝ)+1)/(N : ℝ))^(N-1) := by
  rw [marked_central_retention_difference,
    marked_occupancy_avoidance hN D i hi,
    marked_occupancy_avoidance hN (insert j D) i (by simp [hi,hij]),
    Finset.card_insert_of_notMem hj,Nat.cast_add,Nat.cast_one]

/-- Exact central retention times a recipient product, with a separate
same-recipient term.  It also covers the square of one recipient multiplicity. -/
theorem marked_central_recipient_product_avoidance {N : ℕ} (hN : 0 < N)
    (D : Finset (Fin N)) (c i j : Fin N) (hc : c ∉ D) (hi : i ∉ D) (hj : j ∉ D)
    (hic : i ≠ c) (hjc : j ≠ c) :
    mean (UniformResampling N) (fun a =>
      if markedAvoids D a ∧ 0 < reuseOccupancy a c then
        reuseOccupancy a i*reuseOccupancy a j else 0) =
      (if i = j then (1-(D.card : ℝ)/(N : ℝ))^(N-1) -
        (1-((D.card : ℝ)+1)/(N : ℝ))^(N-1) else 0) +
      ((N-1 : ℕ) : ℝ)/(N : ℝ) *
        ((1-(D.card : ℝ)/(N : ℝ))^(N-2) -
          (1-((D.card : ℝ)+1)/(N : ℝ))^(N-2)) := by
  rw [marked_central_retention_difference,
    marked_occupancy_product_avoidance hN D i j hi hj,
    marked_occupancy_product_avoidance hN (insert c D) i j
      (by simp [hi,hic]) (by simp [hj,hjc]),
    Finset.card_insert_of_notMem hc,Nat.cast_add,Nat.cast_one]
  by_cases hij : i = j <;> simp only [hij,ite_true,ite_false] <;> ring

end AronowAudit.P001.TailA
