import AronowAudit.P001.Wave1.Lib.TailA.MatchingEndpointBase

/-! Exchangeability and donor-score disintegration of the three actual moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA

local instance instDecidableMatchingExchangeability (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

def matchingEndpointCell {n : ℕ} (z : Fin n → MatchUnit) (j i : Fin n) : Prop :=
  (z j).2.1 = true ∧ ∀ l, (z l).2.1 = true → |(z j).1-(z i).1| ≤ |(z l).1-(z i).1|

theorem matching_endpoint_cell_equiv {n : ℕ} (z : Fin n → MatchUnit)
    (e : Fin n ≃ Fin n) (j i : Fin n) :
    matchingEndpointCell (z ∘ e) j i ↔ matchingEndpointCell z (e j) (e i) := by
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,fun l hl => ?_⟩
    simpa only [Function.comp_apply,e.apply_symm_apply] using
      h (e.symm l) (by simpa only [Function.comp_apply,e.apply_symm_apply] using hl)
  · rintro ⟨hr,h⟩
    exact ⟨hr,fun l hl => h (e l) hl⟩

theorem matching_endpoint_W_cell {n : ℕ} (z : Fin n → MatchUnit) (j : Fin n)
    (hz : ∀ i l v : Fin n, l ≠ v → |(z l).1-(z i).1| ≠ |(z v).1-(z i).1|) :
    W z j = ∑ i, if (z i).2.1 then (if i = j then 1 else 0)
      else if matchingEndpointCell z j i then 1 else 0 := by
  have hh := marked_aggregated_weight (fun i => (z i).1) (fun i => (z i).2.1) id j hz
  rw [reuse_identity] at hh
  have ho (i : Fin n) : reuseOccupancy (id : Fin n → Fin n) i = 1 := by
    have hf : Finset.univ.filter (fun t : Fin n => id t = i) = {i} := by ext t; simp
    simp only [reuseOccupancy,hf,Finset.card_singleton,Nat.cast_one]
  change donorReuseWeight (fun i => (z i).1) (fun i => (z i).2.1) j = _
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  rw [ho,one_mul]
  have hcell : markedCellContains (fun i => (z i).1) (fun i => (z i).2.1) id j i ↔
      matchingEndpointCell z j i := by
    constructor
    · rintro ⟨⟨hr,_⟩,h⟩
      exact ⟨hr,fun l hl => h l ⟨hl,l,rfl⟩⟩
    · rintro ⟨hr,h⟩
      exact ⟨⟨hr,j,rfl⟩,fun l hl => h l hl.1⟩
  by_cases hri : (z i).2.1 = true
  · simp only [if_pos hri]
  · by_cases hc : matchingEndpointCell z j i
    · simp only [if_neg hri,if_pos (hcell.mpr hc),if_pos hc]
    · simp only [if_neg hri,if_neg (fun h => hc (hcell.mp h)),if_neg hc]

theorem matching_endpoint_W_equiv {n : ℕ} (z : Fin n → MatchUnit)
    (e : Fin n ≃ Fin n) (j : Fin n)
    (hz : ∀ i l v : Fin n, l ≠ v → |(z l).1-(z i).1| ≠ |(z v).1-(z i).1|) :
    W (z ∘ e) j = W z (e j) := by
  have he : ∀ i l v : Fin n, l ≠ v →
      |((z ∘ e) l).1-((z ∘ e) i).1| ≠ |((z ∘ e) v).1-((z ∘ e) i).1| :=
    fun i l v hlv => hz (e i) (e l) (e v) (fun h => hlv (e.injective h))
  rw [matching_endpoint_W_cell _ _ he,matching_endpoint_W_cell _ _ hz]
  calc
    _ = ∑ i, if (z (e i)).2.1 then (if e i = e j then (1 : ℝ) else 0)
        else if matchingEndpointCell z (e j) (e i) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply,matching_endpoint_cell_equiv,e.injective.eq_iff]
    _ = _ := e.sum_comp (fun i => if (z i).2.1 then (if i = e j then (1 : ℝ) else 0)
      else if matchingEndpointCell z (e j) i then 1 else 0)

/-- Relabeling originals leaves bootstrap positions fixed, so this identity
does not require any exclusion of ties between copies. -/
theorem matching_endpoint_U_equiv {n : ℕ} (z : Fin n → MatchUnit)
    (e : Fin n ≃ Fin n) (a : Fin n → Fin n) (j : Fin n) :
    U (z ∘ e) a j = U z (e ∘ a) (e j) := by
  unfold U bootstrapOriginalReuse
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply,e.injective.eq_iff,Function.comp_def]

theorem matching_endpoint_resampling_relabel (n : ℕ) (e : Fin n ≃ Fin n)
    (f : (Fin n → Fin n) → ℝ) :
    mean (UniformResampling n) (fun a => f (e ∘ a)) = mean (UniformResampling n) f := by
  rw [uniform_resampling_mean,uniform_resampling_mean]
  congr 1
  exact (Equiv.piCongrRight (fun _ : Fin n => e)).sum_comp f

/-- Index 0 is the original square, 1 the one-replica square, and 2 the
two-replica product, with the same original configuration in both replicas. -/
def matchingEndpointMoment (k : Fin 3) {n : ℕ} (z : Fin n → MatchUnit) (j : Fin n) : ℝ :=
  match k.val with
  | 0 => (W z j)^2
  | 1 => mean (UniformResampling n) (fun a => (U z a j)^2)
  | _ => mean (UniformResampling n) (fun a => mean (UniformResampling n)
      (fun b => U z a j*U z b j))

theorem matching_endpoint_average_integrable {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (n : ℕ) (f : (Fin n → Fin n) → E → ℝ)
    (hf : ∀ a, Integrable (f a) μ) :
    Integrable (fun z => mean (UniformResampling n) (fun a => f a z)) μ := by
  simp only [uniform_resampling_mean]
  exact (integrable_finsetSum _ (fun a _ => hf a)).div_const _

theorem matching_endpoint_moment_measurable (k : Fin 3) {n : ℕ} (j : Fin n) :
    Measurable (fun z => matchingEndpointMoment k z j) := by
  fin_cases k
  · exact (matching_W_measurable j).pow_const 2
  · exact marked_resampling_average_measurable n _
      (fun a => (matching_U_measurable a j).pow_const 2)
  · exact marked_resampling_average_measurable n _ (fun a =>
      marked_resampling_average_measurable n _ (fun b =>
        (matching_U_measurable a j).mul (matching_U_measurable b j)))

theorem matching_endpoint_moment_integrable (k : Fin 3) {n : ℕ}
    (μ : Measure (Fin n → MatchUnit)) [IsFiniteMeasure μ] (j : Fin n) :
    Integrable (fun z => matchingEndpointMoment k z j) μ := by
  fin_cases k
  · exact (matching_W_memLp μ j 2).integrable_sq
  · exact matching_endpoint_average_integrable μ n _ (fun a =>
      (matching_U_memLp μ a j 2).integrable_sq)
  · exact matching_endpoint_average_integrable μ n _ (fun a =>
      matching_endpoint_average_integrable μ n _ (fun b =>
        (matching_U_memLp μ a j 2).integrable_mul (matching_U_memLp μ b j 2)))

theorem matching_endpoint_moment_equiv (k : Fin 3) {n : ℕ}
    (z : Fin n → MatchUnit) (e : Fin n ≃ Fin n) (j : Fin n)
    (hz : ∀ i l v : Fin n, l ≠ v → |(z l).1-(z i).1| ≠ |(z v).1-(z i).1|) :
    matchingEndpointMoment k (z ∘ e) j = matchingEndpointMoment k z (e j) := by
  fin_cases k
  · change (W (z ∘ e) j)^2 = (W z (e j))^2
    rw [matching_endpoint_W_equiv _ _ _ hz]
  · change mean (UniformResampling n) (fun a => (U (z ∘ e) a j)^2) = _
    simp_rw [matching_endpoint_U_equiv]
    exact matching_endpoint_resampling_relabel n e (fun a => (U z a (e j))^2)
  · change mean (UniformResampling n) (fun a => mean (UniformResampling n)
        (fun b => U (z ∘ e) a j*U (z ∘ e) b j)) = _
    simp_rw [matching_endpoint_U_equiv]
    calc
      _ = mean (UniformResampling n) (fun a => mean (UniformResampling n)
          (fun b => U z (e ∘ a) (e j)*U z b (e j))) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun a => matching_endpoint_resampling_relabel n e
          (fun b => U z (e ∘ a) (e j)*U z b (e j)))
      _ = _ := matching_endpoint_resampling_relabel n e (fun a =>
        mean (UniformResampling n) (fun b => U z a (e j)*U z b (e j)))

theorem matching_endpoint_moment_exchangeable (k : Fin 3) {n : ℕ} (i j : Fin n) :
    mean (MatchProduct n) (fun z => matchingEndpointMoment k z i) =
      mean (MatchProduct n) (fun z => matchingEndpointMoment k z j) := by
  let e : Fin n ≃ Fin n := Equiv.swap i j
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => matchingUnitLaw) e
  have hh := hp.integral_comp' (fun z => matchingEndpointMoment k z i)
  have heq : (fun z => matchingEndpointMoment k
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => MatchUnit) e) z) i) =ᵐ[MatchProduct n]
      (fun z => matchingEndpointMoment k z j) := by
    filter_upwards [matching_original_distances_unique n] with z hz
    have hmap : ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => MatchUnit) e) z) =
        z ∘ e.symm := by
      funext v
      simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,cast_eq,
        Function.comp_apply]
    rw [hmap,matching_endpoint_moment_equiv k z e.symm i hz]
    simp only [e,Equiv.symm_swap,Equiv.swap_apply_left]
  exact hh.symm.trans (integral_congr_ae heq)

theorem matching_endpoint_W_congr {n : ℕ} {z v : Fin n → MatchUnit}
    (hs : ∀ i, (z i).1 = (v i).1) (hr : ∀ i, (z i).2.1 = (v i).2.1) (j : Fin n) :
    W z j = W v j := by
  unfold W
  rw [show (fun i => (z i).1) = (fun i => (v i).1) from funext hs,
    show (fun i => (z i).2.1) = (fun i => (v i).2.1) from funext hr]

theorem matching_endpoint_U_congr {n : ℕ} {z v : Fin n → MatchUnit}
    (hs : ∀ i, (z i).1 = (v i).1) (hr : ∀ i, (z i).2.1 = (v i).2.1)
    (a : Fin n → Fin n) (j : Fin n) : U z a j = U v a j := by
  unfold U
  rw [show (fun i => (z i).1) = (fun i => (v i).1) from funext hs,
    show (fun i => (z i).2.1) = (fun i => (v i).2.1) from funext hr]

theorem matching_endpoint_moment_congr (k : Fin 3) {n : ℕ} {z v : Fin n → MatchUnit}
    (hs : ∀ i, (z i).1 = (v i).1) (hr : ∀ i, (z i).2.1 = (v i).2.1) (j : Fin n) :
    matchingEndpointMoment k z j = matchingEndpointMoment k v j := by
  fin_cases k <;> simp only [matchingEndpointMoment,
    matching_endpoint_W_congr hs hr,matching_endpoint_U_congr hs hr]

theorem matching_endpoint_U_nondonor {n : ℕ} (z : Fin n → MatchUnit)
    (j : Fin n) (hj : (z j).2.1 = false) (a : Fin n → Fin n) : U z a j = 0 := by
  unfold U bootstrapOriginalReuse
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : a i = j
  · simp only [hi,ite_true,donorReuseWeight,Function.comp_apply,hj,Bool.false_eq_true,ite_false]
  · simp only [hi,ite_false]

theorem matching_endpoint_moment_nondonor (k : Fin 3) {n : ℕ} (z : Fin n → MatchUnit)
    (j : Fin n) (hj : (z j).2.1 = false) : matchingEndpointMoment k z j = 0 := by
  have hw : W z j = 0 := by simp only [W,donorReuseWeight,hj,Bool.false_eq_true,ite_false]
  fin_cases k <;> simp only [matchingEndpointMoment,hw,matching_endpoint_U_nondonor z j hj,
    zero_pow (by decide : 2 ≠ 0),zero_mul,mean,integral_zero]

theorem matching_endpoint_moment_cons (k : Fin 3) (n : ℕ) (u : MatchUnit)
    (z : Fin n → MatchUnit) :
    matchingEndpointMoment k (Fin.cons u z) 0 =
      if u.2.1 = true then matchingEndpointMoment k (pin n u.1 z) 0 else 0 := by
  cases hr : u.2.1 with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    exact matching_endpoint_moment_nondonor k _ _ (by simpa only [Fin.cons_zero] using hr)
  | true =>
    simp only [ite_true]
    apply matching_endpoint_moment_congr
    · intro i
      exact Fin.cases rfl (fun _ => rfl) i
    · intro i
      exact Fin.cases hr (fun _ => rfl) i

theorem matching_endpoint_pinned_measurable (k : Fin 3) (n : ℕ) :
    Measurable (fun p => mean (MatchProduct n)
      (fun z => matchingEndpointMoment k (pin n p z) 0)) :=
  matching_pinned_integral_measurable n (matching_endpoint_moment_measurable k 0)

/-- Pinning a donor is literal product disintegration, with the exact density 2p. -/
theorem matching_endpoint_disintegration (k : Fin 3) (n : ℕ) :
    mean (MatchProduct (n+1)) (fun z => matchingEndpointMoment k z 0) =
      ∫ p in Set.Icc (1/4 : ℝ) (3/4), 2*p*mean (MatchProduct n)
        (fun z => matchingEndpointMoment k (pin n p z) 0) := by
  have hm := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => matchingUnitLaw) 0).symm
  have hh := hm.integral_comp' (fun z => matchingEndpointMoment k z 0)
  have hcomp (y : MatchUnit × (Fin n → MatchUnit)) :
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => MatchUnit) 0).symm y =
        Fin.cons y.1 y.2 := by
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Fin.insertNth_zero,Equiv.coe_fn_mk,cast_eq]
  have hi := (hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr
    (matching_endpoint_moment_integrable k (MatchProduct (n+1)) 0)
  simp only [Function.comp_def,hcomp] at hi hh
  change (∫ z, matchingEndpointMoment k z 0 ∂Measure.pi (fun _ : Fin (n+1) => matchingUnitLaw)) = _
  rw [← hh,integral_prod _ hi]
  have he (u : MatchUnit) :
      (∫ z, matchingEndpointMoment k (Fin.cons u z) 0 ∂MatchProduct n) =
        if u.2.1 = true then mean (MatchProduct n)
          (fun z => matchingEndpointMoment k (pin n u.1 z) 0) else 0 := by
    simp only [matching_endpoint_moment_cons]
    split_ifs <;> simp only [mean,integral_zero]
  change (∫ u, (∫ z, matchingEndpointMoment k (Fin.cons u z) 0 ∂MatchProduct n)
    ∂matchingUnitLaw) = _
  simp_rw [he]
  exact marked_type_score_integral true _ (matching_endpoint_pinned_measurable k n)

end AronowAudit.P001.TailA
