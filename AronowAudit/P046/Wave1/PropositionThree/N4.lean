import AronowAudit.P046.Wave1.PropositionThreeBlueprint

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

/-- Choose the low positions, then the treated positions within the low positions. -/
private theorem category_vector_card (N k s : ℕ) :
    (univ.filter (fun b : Fin N → Fin 3 =>
      (univ.filter (fun i => b i ≠ 2)).card = k ∧
      (univ.filter (fun i => b i = 0)).card = s)).card = N.choose k * k.choose s := by
  classical
  let L (b : Fin N → Fin 3) : Finset (Fin N) := univ.filter (fun i => b i ≠ 2)
  let T (b : Fin N → Fin 3) : Finset (Fin N) := univ.filter (fun i => b i = 0)
  let C : Finset (Fin N → Fin 3) := univ.filter (fun b => (L b).card = k ∧ (T b).card = s)
  let D : Finset (Sigma (fun _ : Finset (Fin N) => Finset (Fin N))) :=
    (univ.powersetCard k).sigma (fun l => l.powersetCard s)
  have hsub (b : Fin N → Fin 3) : T b ⊆ L b := by
    intro i hi
    simp only [T, L, mem_filter, mem_univ, true_and] at hi ⊢
    rw [hi]
    decide
  have hcard : C.card = D.card := by
    apply card_bij (fun b _ => (⟨L b, T b⟩ : Sigma (fun _ : Finset (Fin N) => Finset (Fin N))))
    · intro b hb
      have hb' : (L b).card = k ∧ (T b).card = s := (mem_filter.1 hb).2
      exact mem_sigma.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hb'.1⟩,
        mem_powersetCard.2 ⟨hsub b, hb'.2⟩⟩
    · intro b hb b' hb' he
      have hl : L b = L b' := congrArg
        (fun d : Sigma (fun _ : Finset (Fin N) => Finset (Fin N)) => d.1) he
      have ht : T b = T b' := congrArg
        (fun d : Sigma (fun _ : Finset (Fin N) => Finset (Fin N)) => d.2) he
      funext i
      have hiL : (b i ≠ 2) ↔ (b' i ≠ 2) := by
        simpa only [L, mem_filter, mem_univ, true_and] using
          (show i ∈ L b ↔ i ∈ L b' from by rw [hl])
      have hiT : (b i = 0) ↔ (b' i = 0) := by
        simpa only [T, mem_filter, mem_univ, true_and] using
          (show i ∈ T b ↔ i ∈ T b' from by rw [ht])
      generalize hbi : b i = j at hiL hiT ⊢
      generalize hbi' : b' i = j' at hiL hiT ⊢
      fin_cases j <;> fin_cases j' <;> simp_all
    · intro d hd
      have hd' := mem_sigma.1 hd
      have hl := mem_powersetCard.1 hd'.1
      have ht := mem_powersetCard.1 hd'.2
      let b : Fin N → Fin 3 := fun i => if i ∈ d.2 then 0 else if i ∈ d.1 then 1 else 2
      have hLb : L b = d.1 := by
        ext i
        by_cases hiT : i ∈ d.2
        · have hiL := ht.1 hiT
          simp [L, b, hiT, hiL]
        · by_cases hiL : i ∈ d.1 <;> simp [L, b, hiT, hiL]
      have hTb : T b = d.2 := by
        ext i
        by_cases hiT : i ∈ d.2 <;> by_cases hiL : i ∈ d.1 <;>
          simp [T, b, hiT, hiL]
      have hb : b ∈ C := by
        simp only [C, mem_filter, mem_univ, true_and, hLb, hTb]
        exact ⟨hl.2, ht.2⟩
      refine ⟨b, hb, ?_⟩
      rcases d with ⟨l, t⟩
      change (⟨L b, T b⟩ : Sigma (fun _ : Finset (Fin N) => Finset (Fin N))) = ⟨l, t⟩
      dsimp only at hLb hTb
      rw [hLb, hTb]
  have hD : D.card = N.choose k * k.choose s := by
    simp only [D]
    rw [card_sigma]
    calc
      (∑ l ∈ (univ : Finset (Fin N)).powersetCard k, (l.powersetCard s).card) =
          ∑ _ ∈ (univ : Finset (Fin N)).powersetCard k, k.choose s := by
        apply sum_congr rfl
        intro l hl
        rw [card_powersetCard, (mem_powersetCard.1 hl).2]
      _ = _ := by simp
  exact hcard.trans hD

/-- Every vector with these counts has the same product weight. -/
private theorem category_vector_weight (N k s : ℕ) (p : Fin 3 → ℝ)
    (b : Fin N → Fin 3)
    (hb : (univ.filter (fun i => b i ≠ 2)).card = k ∧
      (univ.filter (fun i => b i = 0)).card = s) :
    (∏ i, p (b i)) = p 0 ^ s * p 1 ^ (k - s) * p 2 ^ (N - k) := by
  classical
  have h01 : (univ.filter (fun i : Fin N => b i = 0)).card +
      (univ.filter (fun i : Fin N => b i = 1)).card = k := by
    have hh := card_filter_add_card_filter_not
      (s := univ.filter (fun i : Fin N => b i ≠ 2)) (fun i => b i = 0)
    have he0 : (univ.filter (fun i : Fin N => b i ≠ 2)).filter (fun i => b i = 0) =
        univ.filter (fun i => b i = 0) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      generalize b i = j
      fin_cases j <;> simp
    have he1 : (univ.filter (fun i : Fin N => b i ≠ 2)).filter (fun i => ¬ b i = 0) =
        univ.filter (fun i => b i = 1) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      generalize b i = j
      fin_cases j <;> simp
    simpa only [he0, he1, hb.1] using hh
  have h1 : (univ.filter (fun i : Fin N => b i = 1)).card = k - s := by
    rw [hb.2] at h01
    omega
  have h2 : (univ.filter (fun i : Fin N => b i = 2)).card = N - k := by
    have hh := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin N))) (fun i => b i ≠ 2)
    simp only [not_not, hb.1, card_univ, Fintype.card_fin] at hh
    omega
  calc
    (∏ i, p (b i)) = ∏ j : Fin 3, p j ^ (univ.filter (fun i => b i = j)).card := by
      simpa only [prod_const] using (prod_fiberwise' (univ : Finset (Fin N)) b p).symm
    _ = _ := by simp [Fin.prod_univ_succ, hb.2, h1, h2, mul_assoc]

theorem n4_proof : N4 := by
  classical
  intro α _ ν _ c hc p hp hmass N k s _hs _hk
  let C : Finset (Fin N → Fin 3) := univ.filter (fun b =>
    (univ.filter (fun i => b i ≠ 2)).card = k ∧
    (univ.filter (fun i => b i = 0)).card = s)
  let f : (Fin N → α) → (Fin N → Fin 3) := fun a i => c (a i)
  have mf : Measurable f := measurable_pi_lambda (fun i => hc.comp (measurable_pi_apply i))
  have hpush : (Measure.pi (fun _ : Fin N => ν)).map f =
      Measure.pi (fun _ : Fin N => ν.map c) :=
    Measure.pi_map_pi (fun _ => hc.aemeasurable)
  have hpre : {a : Fin N → α |
      (univ.filter (fun i => c (a i) ≠ 2)).card = k ∧
      (univ.filter (fun i => c (a i) = 0)).card = s} = f ⁻¹' (C : Set (Fin N → Fin 3)) := by
    ext a
    simp [C, f]
  have hsingle (b : Fin N → Fin 3) (hb : b ∈ C) :
      (Measure.pi (fun _ : Fin N => ν.map c)) {b} =
        ENNReal.ofReal (p 0 ^ s * p 1 ^ (k - s) * p 2 ^ (N - k)) := by
    have hb' := (mem_filter.1 hb).2
    rw [Measure.pi_singleton]
    have hj (j : Fin 3) : ν.map c {j} = ENNReal.ofReal (p j) := by
      rw [Measure.map_apply hc (measurableSet_singleton j)]
      exact hmass j
    simp_rw [hj]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hp (b i)),
      category_vector_weight N k s p b hb']
  rw [hpre, ← Measure.map_apply mf C.finite_toSet.measurableSet, hpush,
    ← sum_measure_singleton]
  calc
    (∑ b ∈ C, (Measure.pi (fun _ : Fin N => ν.map c)) {b}) =
        ∑ _ ∈ C, ENNReal.ofReal (p 0 ^ s * p 1 ^ (k - s) * p 2 ^ (N - k)) :=
      sum_congr rfl hsingle
    _ = ENNReal.ofReal ((N.choose k : ℝ) * (k.choose s : ℝ) *
        p 0 ^ s * p 1 ^ (k - s) * p 2 ^ (N - k)) := by
      rw [sum_const, nsmul_eq_mul]
      have hC : C.card = N.choose k * k.choose s := category_vector_card N k s
      rw [hC]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

end

end AronowAudit.P046.Wave1.PropositionThree
