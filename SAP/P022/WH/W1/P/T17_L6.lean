import SAP.P022.WH.W1.Leaves
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T17_L6

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def empiricalLaw (u : ℕ → ℝ × ℝ) (q : ℕ) : JointLaw := by
  let N := q + 4
  let μ : Measure (ℝ × ℝ) := Measure.sum (fun i : Fin N =>
    ENNReal.ofReal (1 / (N : ℝ)) • Measure.dirac (u i.val))
  have hN : 0 < N := by dsimp [N]; omega
  have hc : ∀ i : Fin N, 0 ≤ (1 / (N : ℝ)) := fun _ => by positivity
  have hsum : (∑ i : Fin N, (1 / (N : ℝ))) = 1 := by
    simp [Finset.sum_const, Fintype.card_fin, hN.ne']
  have hs : HasSum (fun _ : Fin N => (1 / (N : ℝ))) 1 := by
    simpa only [hsum] using
      (hasSum_fintype (fun _ : Fin N => (1 / (N : ℝ))) :
        HasSum (fun _ : Fin N => (1 / (N : ℝ))) (∑ i : Fin N, (1 / (N : ℝ))))
  exact ⟨μ, hs.isProbabilityMeasure_sum_dirac hc⟩

theorem empiricalLaw_measureReal (u : ℕ → ℝ × ℝ) (q : ℕ)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    (empiricalLaw u q : Measure (ℝ × ℝ)).real s =
      finiteMean (fun i : Fin (q + 4) => if u i.val ∈ s then (1 : ℝ) else 0) := by
  classical
  let N := q + 4
  have hN : 0 < N := by dsimp [N]; omega
  rw [measureReal_def]
  simp only [empiricalLaw, ProbabilityMeasure.coe_mk]
  change (Measure.sum (fun i : Fin N =>
    ENNReal.ofReal (1 / (N : ℝ)) • Measure.dirac (u i.val)) s).toReal = _
  rw [Measure.sum_apply _ hs]
  simp only [tsum_fintype, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator_apply]
  change (∑ i : Fin N, ENNReal.ofReal (1 / (N : ℝ)) *
      (if u i.val ∈ s then (1 : ENNReal) else 0)).toReal = _
  have hfin : ∀ i : Fin N, (ENNReal.ofReal (1 / (N : ℝ)) *
      (if u i.val ∈ s then 1 else 0)) ≠ ∞ := by
    intro i
    apply ENNReal.mul_ne_top
    · exact ENNReal.ofReal_ne_top
    · split_ifs <;> simp
  have hfin' : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      ENNReal.ofReal (1 / (N : ℝ)) * (if u i.val ∈ s then 1 else 0) ≠ ∞ := by
    intro i hi
    exact hfin i
  rw [ENNReal.toReal_sum hfin']
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / (N : ℝ)))]
  simp only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  rw [← Finset.mul_sum]
  simp only [N]
  ring_nf
  apply congrArg (fun z : ℝ => ((↑(4 + q : ℕ) : ℝ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : u i.val ∈ s <;> simp [h]

theorem empiricalLaw_integral (u : ℕ → ℝ × ℝ) (q : ℕ)
    (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) :
    (∫ p, f p ∂(empiricalLaw u q : Measure (ℝ × ℝ))) =
      finiteMean (fun i : Fin (q + 4) => f (u i.val)) := by
  classical
  let N := q + 4
  have hN : 0 < N := by dsimp [N]; omega
  have hc : ∀ i : Fin N, ENNReal.ofReal (1 / (N : ℝ)) ≠ ∞ := by
    intro i
    simp
  change (∫ p, f p ∂Measure.sum (fun i : Fin N =>
    ENNReal.ofReal (1 / (N : ℝ)) • Measure.dirac (u i.val))) = _
  rw [integral_sum_dirac hc]
  rw [tsum_fintype]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / (N : ℝ)))]
  simp only [smul_eq_mul]
  simp only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  rw [← Finset.mul_sum]
  ring

def rationalBox (a b c d : ℚ) : Set (ℝ × ℝ) :=
  Set.Ioo (a : ℝ) b ×ˢ Set.Ioo (c : ℝ) d

def rationalBoxBasis : Set (Set (ℝ × ℝ)) :=
  Set.range (fun v : ℚ × (ℚ × (ℚ × ℚ)) =>
    rationalBox v.1 v.2.1 v.2.2.1 v.2.2.2) ∪ {∅}

theorem rationalBox_inter (a b c d a' b' c' d' : ℚ) :
    rationalBox a b c d ∩ rationalBox a' b' c' d' =
      rationalBox (max a a') (min b b') (max c c') (min d d') := by
  simp [rationalBox, Set.prod_inter_prod, Set.Ioo_inter_Ioo,
    Rat.cast_max, Rat.cast_min]

theorem rationalBoxBasis_countable : rationalBoxBasis.Countable := by
  unfold rationalBoxBasis
  exact (Set.countable_range _).union (Set.countable_singleton _)

theorem rationalBoxBasis_pi : IsPiSystem rationalBoxBasis := by
  intro s hs t ht hne
  simp only [rationalBoxBasis, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hs ht
  rcases hs with ⟨v, rfl⟩ | hs
  · rcases ht with ⟨w, rfl⟩ | ht
    · rw [rationalBox_inter]
      exact Or.inl ⟨(max v.1 w.1, (min v.2.1 w.2.1,
        (max v.2.2.1 w.2.2.1, min v.2.2.2 w.2.2.2))), rfl⟩
    · simp_all
  · simp_all

theorem rationalBoxBasis_measurable :
    ∀ s ∈ rationalBoxBasis, MeasurableSet s := by
  intro s hs
  simp only [rationalBoxBasis, Set.mem_union, Set.mem_range,
    Set.mem_singleton_iff] at hs
  rcases hs with ⟨v, rfl⟩ | hs
  · simp only [rationalBox, measurableSet_prod]
    exact Or.inl ⟨measurableSet_Ioo, measurableSet_Ioo⟩
  · subst s
    exact MeasurableSet.empty

theorem rationalBoxBasis_neighborhoods :
    ∀ (u : Set (ℝ × ℝ)), IsOpen u → ∀ x ∈ u,
      ∃ s ∈ rationalBoxBasis, s ∈ 𝓝 x ∧ s ⊆ u := by
  intro u hu x hx
  rcases mem_nhds_prod_iff.mp (hu.mem_nhds hx) with
    ⟨u₁, hu₁, u₂, hu₂, hprod⟩
  rcases (nhds_basis_Ioo x.1).mem_iff.mp hu₁ with ⟨⟨l₁, r₁⟩, ⟨hl₁, hr₁⟩, hsub₁⟩
  rcases (nhds_basis_Ioo x.2).mem_iff.mp hu₂ with ⟨⟨l₂, r₂⟩, ⟨hl₂, hr₂⟩, hsub₂⟩
  obtain ⟨a, hla, hax⟩ := exists_rat_btwn hl₁
  obtain ⟨b, hxb, hbr⟩ := exists_rat_btwn hr₁
  obtain ⟨c, hlc, hcx⟩ := exists_rat_btwn hl₂
  obtain ⟨d, hxd, hdr⟩ := exists_rat_btwn hr₂
  let s := rationalBox a b c d
  have hsub₁' : Set.Ioo (a : ℝ) b ⊆ u₁ := by
    intro y hy
    apply hsub₁
    exact ⟨lt_trans hla hy.1, lt_trans hy.2 hbr⟩
  have hsub₂' : Set.Ioo (c : ℝ) d ⊆ u₂ := by
    intro y hy
    apply hsub₂
    exact ⟨lt_trans hlc hy.1, lt_trans hy.2 hdr⟩
  have hmem₁ : Set.Ioo (a : ℝ) b ∈ 𝓝 x.1 :=
    (nhds_basis_Ioo x.1).mem_iff.mpr ⟨(a, b), ⟨hax, hxb⟩, subset_rfl⟩
  have hmem₂ : Set.Ioo (c : ℝ) d ∈ 𝓝 x.2 :=
    (nhds_basis_Ioo x.2).mem_iff.mpr ⟨(c, d), ⟨hcx, hxd⟩, subset_rfl⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · apply Set.mem_union_left
    exact ⟨(a, (b, (c, d))), rfl⟩
  · simpa [s, rationalBox] using prod_mem_nhds hmem₁ hmem₂
  · intro p hp
    exact hprod ⟨hsub₁' hp.1, hsub₂' hp.2⟩

def atomHalfspace (t : Bool) (x : ℝ) : Set (ℝ × ℝ) :=
  {p | (if t then p.1 else p.2) ≤ x}

def marginalDiscontinuities (J : JointLaw) (t : Bool) : Set ℝ :=
  {x | ¬ContinuousAt (lawCDF J t) x}

theorem lawCDF_monotone (J : JointLaw) (t : Bool) :
    Monotone (lawCDF J t) := by
  intro x y hxy
  unfold lawCDF
  exact measureReal_mono (by
    intro p hp
    exact hp.trans hxy) (by finiteness)

def atomicHalfspaces (J : JointLaw) : Set (Set (ℝ × ℝ)) :=
  ⋃ t : Bool, atomHalfspace t '' marginalDiscontinuities J t

def samplingSets (J : JointLaw) : Set (Set (ℝ × ℝ)) :=
  rationalBoxBasis ∪ atomicHalfspaces J

theorem samplingSets_countable (J : JointLaw) :
    (samplingSets J).Countable := by
  have hAtoms : (atomicHalfspaces J).Countable := by
    apply Set.countable_iUnion
    intro t
    exact (lawCDF_monotone J t).countable_not_continuousAt.image (atomHalfspace t)
  exact rationalBoxBasis_countable.union hAtoms

theorem atomHalfspace_measurable (t : Bool) (x : ℝ) :
    MeasurableSet (atomHalfspace t x) := by
  cases t <;> simp only [atomHalfspace, Bool.false_eq_true, ite_false, ite_true]
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_le (by fun_prop) measurable_const

theorem samplingSets_measurable (J : JointLaw) :
    ∀ s ∈ samplingSets J, MeasurableSet s := by
  intro s hs
  simp only [samplingSets, Set.mem_union] at hs
  rcases hs with hs | hs
  · exact rationalBoxBasis_measurable s hs
  · simp only [atomicHalfspaces, Set.mem_iUnion, Set.mem_image] at hs
    rcases hs with ⟨t, x, hx, rfl⟩
    exact atomHalfspace_measurable t x

def armCount (a : ℝ) (q : ℕ) : ℕ :=
  Nat.floor (a * (q : ℝ)) + 2

def makeDesign (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (q : ℕ) : Design := by
  have hsumR : (armCount a q : ℝ) + armCount b q ≤ (q : ℝ) + 4 := by
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have hfloorA := Nat.floor_le (mul_nonneg ha hq)
    have hfloorB := Nat.floor_le (mul_nonneg hb hq)
    have habq : a * (q : ℝ) + b * (q : ℝ) ≤ (q : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hab hq]
    simp only [armCount, Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  refine ⟨q + 4, armCount a q, armCount b q, by omega, ?_, ?_, ?_⟩
  · dsimp [armCount]
    omega
  · dsimp [armCount]
    omega
  · exact_mod_cast hsumR

theorem armFraction_tendsto (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun q => (armCount a q : ℝ) / ((q : ℝ) + 4)) atTop (𝓝 a) := by
  have hN : Tendsto (fun q : ℕ => (q : ℝ) + 4) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds :
        Tendsto (fun q : ℕ => (q : ℝ) + 4) atTop atTop)
  have h4 : Tendsto (fun q : ℕ => (4 : ℝ) / ((q : ℝ) + 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have h2 : Tendsto (fun q : ℕ => (2 : ℝ) / ((q : ℝ) + 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hlo : Tendsto (fun q : ℕ => a - 4 / ((q : ℝ) + 4)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub h4
  have hhi : Tendsto (fun q : ℕ => a + 2 / ((q : ℝ) + 4)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro q
    change a - 4 / ((q : ℝ) + 4) ≤ (armCount a q : ℝ) / ((q : ℝ) + 4)
    have hn : 0 < (q : ℝ) + 4 := by positivity
    have hfloor := Nat.lt_floor_add_one (a * (q : ℝ))
    have hlowN : a * ((q : ℝ) + 4) - 4 ≤ (armCount a q : ℝ) := by
      simp only [armCount, Nat.cast_add, Nat.cast_ofNat]
      nlinarith [hfloor, mul_le_mul_of_nonneg_right ha1.le (by norm_num : (0 : ℝ) ≤ 4)]
    have hrewrite : a - 4 / ((q : ℝ) + 4) =
        (a * ((q : ℝ) + 4) - 4) / ((q : ℝ) + 4) := by field_simp
    rw [hrewrite]
    exact (div_le_div_iff_of_pos_right hn).2 hlowN
  · intro q
    change (armCount a q : ℝ) / ((q : ℝ) + 4) ≤ a + 2 / ((q : ℝ) + 4)
    have hn : 0 < (q : ℝ) + 4 := by positivity
    have hfloor := Nat.floor_le (mul_nonneg ha.le (Nat.cast_nonneg q))
    have hhighN : (armCount a q : ℝ) ≤ a * ((q : ℝ) + 4) + 2 := by
      simp only [armCount, Nat.cast_add, Nat.cast_ofNat]
      nlinarith [hfloor, mul_nonneg ha.le (by norm_num : (0 : ℝ) ≤ 4)]
    have hrewrite : a + 2 / ((q : ℝ) + 4) =
        (a * ((q : ℝ) + 4) + 2) / ((q : ℝ) + 4) := by field_simp
    rw [hrewrite]
    exact (div_le_div_iff_of_pos_right hn).2 hhighN

end
end SAP.P022.WH.W1.P.T17_L6


open SAP.P022 Filter MeasureTheory
open SAP.P022.WH.W1.P.T17_L6
open scoped BigOperators Topology ENNReal NNReal

set_option maxHeartbeats 800000 in
theorem SAP.P022.WH.W1.T17_L6_proof : SAP.P022.WH.W1.T17_L6 := by
  classical
  intro h5 J θ ρ hθ hθ1 hρ hρ1 hthird
  let a : ℝ := θ * ρ
  let b : ℝ := θ * (1 - ρ)
  have ha : 0 < a := mul_pos hθ hρ
  have hb : 0 < b := mul_pos hθ (by linarith)
  have ha1 : a < 1 := by
    dsimp [a]
    calc
      θ * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hθ1 hρ.le
      _ < 1 := by simpa using hρ1
  have hb1 : b < 1 := by
    dsimp [b]
    calc
      θ * (1 - ρ) ≤ 1 * (1 - ρ) :=
        mul_le_mul_of_nonneg_right hθ1 (by linarith)
      _ < 1 := by nlinarith
  have habEq : a + b = θ := by
    dsimp [a, b]
    ring
  have hab : a + b ≤ 1 := by
    rw [habEq]
    exact hθ1
  let C := samplingSets J
  let F : Fin 2 → (ℝ × ℝ) → ℝ := fun i p =>
    if i.val = 0 then |p.1| ^ 3 else |p.2| ^ 3
  have hF : ∀ i : Fin 2, Integrable (F i) (J : Measure (ℝ × ℝ)) := by
    intro i
    fin_cases i
    · simpa [F] using hthird true
    · simpa [F] using hthird false
  obtain ⟨u, hu_sets, hu_F⟩ :=
    h5 J C (samplingSets_countable J) (samplingSets_measurable J) F hF
  let S : ExperimentSequence :=
    { design := fun q => makeDesign a b ha.le hb.le hab q
      size := by intro q; rfl
      y1 := fun i => (u i).1
      y0 := fun i => (u i).2 }
  have hA : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N)
      atTop (𝓝 a) := by
    simpa [S, makeDesign] using armFraction_tendsto a ha ha1
  have hB : Tendsto (fun q => ((S.design q).k : ℝ) / (S.design q).N)
      atTop (𝓝 b) := by
    simpa [S, makeDesign] using armFraction_tendsto b hb hb1
  have hAlloc : Tendsto
      (fun q => (((S.design q).m : ℝ) + (S.design q).k) / (S.design q).N)
      atTop (𝓝 θ) := by
    have hsum := hA.add hB
    have hsum' : Tendsto
        (fun q => (((S.design q).m : ℝ) + (S.design q).k) / (S.design q).N)
        atTop (𝓝 (a + b)) := by
      simpa [add_div] using hsum
    simpa [habEq] using hsum'
  have hRect : ∀ s ∈ rationalBoxBasis,
      Tendsto (fun q => empiricalLaw u q s) atTop (𝓝 (J s)) := by
    intro s hs
    have havg := hu_sets s (Set.mem_union_left _ hs)
    have hsetMeas := rationalBoxBasis_measurable s hs
    have heq (q : ℕ) :
        (((empiricalLaw u q) s : ℝ≥0) : ℝ) =
          finiteMean (fun i : Fin (q + 4) => if u i.val ∈ s then (1 : ℝ) else 0) := by
      rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
      exact empiricalLaw_measureReal u q s hsetMeas
    have hcoe : Tendsto
        (fun q => (((empiricalLaw u q) s : ℝ≥0) : ℝ)) atTop
        (𝓝 (((J s : ℝ≥0) : ℝ))) := by
      have htarget : ((J : Measure (ℝ × ℝ)) s).toReal =
          (((J s : ℝ≥0) : ℝ)) := by
        simpa only [measureReal_def] using
          (ProbabilityMeasure.measureReal_eq_coe_coeFn J s)
      have havg' : Tendsto
          (fun q => finiteMean (fun i : Fin (q + 4) =>
            if u i.val ∈ s then (1 : ℝ) else 0)) atTop
          (𝓝 (((J s : ℝ≥0) : ℝ))) := by
        rw [← htarget]
        exact havg
      exact (tendsto_congr' (Filter.Eventually.of_forall fun q => (heq q).symm)).1 havg'
    exact NNReal.tendsto_coe.mp hcoe
  have hPM : Tendsto (fun q => empiricalLaw u q) atTop (𝓝 J) :=
    rationalBoxBasis_pi.tendsto_probabilityMeasure_of_tendsto_of_mem
      rationalBoxBasis_measurable rationalBoxBasis_neighborhoods hRect
  have hWeak : weakPopulationConvergence S J := by
    intro f
    have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hPM) f
    have hEq (q : ℕ) :
        finiteMean (fun i : Fin (q + 4) => f (u i.val)) =
          finiteMean (fun i : Fin (S.design q).N =>
            f (S.y1 i.val, S.y0 i.val)) := by
      congr 1
    have h' := (tendsto_congr' (Filter.Eventually.of_forall hEq)).2
      ((tendsto_congr' (Filter.Eventually.of_forall fun q =>
        (empiricalLaw_integral u q f).symm)).2 hf)
    exact h'
  have hAtoms : ∀ t x, ¬ContinuousAt (lawCDF J t) x →
      Tendsto (fun q => empiricalCDF (rowOutcomes S t q) x) atTop
        (𝓝 (lawCDF J t x)) := by
    intro t x hx
    have hs : atomHalfspace t x ∈ C := by
      apply Set.mem_union_right
      apply Set.mem_iUnion.mpr ⟨t, ?_⟩
      exact Set.mem_image_of_mem (atomHalfspace t) hx
    have hconv := hu_sets (atomHalfspace t x) hs
    have hseq : (fun q => empiricalCDF (rowOutcomes S t q) x) =
        (fun q => finiteMean (fun i : Fin (q + 4) =>
          if (if t then (u i.val).1 else (u i.val).2) ≤ x then (1 : ℝ) else 0)) := by
      funext q
      simp [empiricalCDF, rowOutcomes, S, ite_apply]
      rfl
    rw [hseq]
    change Tendsto (fun q => finiteMean (fun i : Fin (q + 4) =>
      if u i.val ∈ atomHalfspace t x then (1 : ℝ) else 0)) atTop
      (𝓝 ((J : Measure (ℝ × ℝ)).real (atomHalfspace t x)))
    exact hconv
  have hConditions : Conditions123 S J θ ρ := by
    refine ⟨hθ, hθ1, hρ, hρ1, ?_, hAlloc, hWeak, hAtoms⟩
    simpa [a] using hA
  have hThirdBound : BoundedThirdMoments S := by
    have hconv (t : Bool) : Tendsto
        (fun q => finiteMean (fun i : Fin (q + 4) =>
          |if t then (u i.val).1 else (u i.val).2| ^ 3)) atTop
        (𝓝 (∫ p, |if t then p.1 else p.2| ^ 3 ∂(J : Measure (ℝ × ℝ)))) := by
      cases t
      · simpa [F] using hu_F ⟨1, by omega⟩
      · simpa [F] using hu_F ⟨0, by omega⟩
    have hbound (t : Bool) : ∃ M : ℝ, ∀ q,
        finiteMean (fun i : Fin (q + 4) =>
          |if t then (u i.val).1 else (u i.val).2| ^ 3) ≤ M := by
      rcases (hconv t).bddAbove_range with ⟨M, hM⟩
      refine ⟨M, fun q => ?_⟩
      exact hM (Set.mem_range_self q)
    obtain ⟨Mt, hMt⟩ := hbound true
    obtain ⟨Mc, hMc⟩ := hbound false
    refine ⟨max Mt Mc, ?_⟩
    intro q t
    cases t
    · change finiteMean (fun i : Fin (q + 4) => |(u i.val).2| ^ 3) ≤ max Mt Mc
      exact le_trans (hMc q) (le_max_right Mt Mc)
    · change finiteMean (fun i : Fin (q + 4) => |(u i.val).1| ^ 3) ≤ max Mt Mc
      exact le_trans (hMt q) (le_max_left Mt Mc)
  exact ⟨S, hConditions, hThirdBound⟩
