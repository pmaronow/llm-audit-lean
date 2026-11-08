import SAP.P009b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

open SAP.P009b

attribute [local instance] Classical.propDecidable

theorem SAP.P009b.WH.W1.T27_L1_proof : SAP.P009b.WH.W1.T27_L1 := by
  intro n E k hk hBER hMarg b hb a
  let E' : AronowAudit.P009.Experiment n := SAP.P009b.Bridge.toExperiment E
  let G : Finset (Fin n) := Finset.univ.filter fun i => i.val < b
  let a' : Assignment n := fun i =>
    if hi : i.val < b then a ⟨i.val, hi⟩ else false
  have hBER' : AronowAudit.P009.Bernoulli E' := by
    change AronowAudit.P009.Bernoulli (SAP.P009b.Bridge.toExperiment E)
    exact hBER
  have hMarg' : ∀ i, k⁻¹ ≤ AronowAudit.P009.marginal E' i true ∧
      AronowAudit.P009.marginal E' i true ≤ 1-k⁻¹ := by
    intro i
    change k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹
    exact hMarg i
  have hpart (i : Fin n) :
      AronowAudit.P009.marginal E' i true +
        AronowAudit.P009.marginal E' i false = 1 :=
    AronowAudit.P009.marginal_partition E' i
  have hMargFalse : ∀ i, k⁻¹ ≤ AronowAudit.P009.marginal E' i false ∧
      AronowAudit.P009.marginal E' i false ≤ 1-k⁻¹ := by
    intro i
    have ht := hMarg' i
    constructor
    · have hp := hpart i
      linarith
    · have hp := hpart i
      linarith
  have hMargA : ∀ i, k⁻¹ ≤ AronowAudit.P009.marginal E' i (a' i) ∧
      AronowAudit.P009.marginal E' i (a' i) ≤ 1-k⁻¹ := by
    intro i
    cases ha : a' i
    · simpa [ha] using hMargFalse i
    · simpa [ha] using hMarg' i
  have hcard : G.card = b := by
    simp [G, Fin.card_filter_val_lt, Nat.min_eq_right hb]
  have hprodLower :
      (k⁻¹)^b ≤ ∏ i ∈ G, AronowAudit.P009.marginal E' i (a' i) := by
    calc
      (k⁻¹)^b = ∏ i ∈ G, (k⁻¹ : ℝ) := by rw [← hcard]; simp
      _ ≤ ∏ i ∈ G, AronowAudit.P009.marginal E' i (a' i) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (inv_pos.mpr hk).le
        · intro i hi
          exact (hMargA i).1
  have hprodUpper :
      ∏ i ∈ G, AronowAudit.P009.marginal E' i (a' i) ≤ (1-k⁻¹)^b := by
    calc
      ∏ i ∈ G, AronowAudit.P009.marginal E' i (a' i) ≤
          ∏ i ∈ G, (1-k⁻¹ : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (inv_pos.mpr hk).le.trans (hMargA i).1
        · intro i hi
          exact (hMargA i).2
      _ = (1-k⁻¹)^b := by rw [← hcard]; simp
  have hevent (z : Assignment n) :
      (∀ i ∈ G, z i = a' i) ↔ wholePrefix hb z = a := by
    constructor
    · intro hz
      funext j
      have hmem : (⟨j.val, lt_of_lt_of_le j.isLt hb⟩ : Fin n) ∈ G := by
        simp [G]
      have hval := hz _ hmem
      simpa [a', wholePrefix] using hval
    · intro hz i hi
      have hiLt : i.val < b := (Finset.mem_filter.mp hi).2
      let j : Fin b := ⟨i.val, hiLt⟩
      have hval := congrFun hz j
      change z i = a' i
      simpa [j, wholePrefix, a', hiLt] using hval
  have hfix :
      prob E.design (fun z => wholePrefix hb z = a) =
        AronowAudit.P009.prob E'.design (fun z => ∀ i ∈ G, z i = a' i) := by
    congr 1
    funext z
    exact propext (hevent z).symm
  have hfixed := AronowAudit.P009.BernoulliCompletion.probability_fixed_coordinates
    E' hBER' G a'
  have hprob :
      prob E.design (fun z => wholePrefix hb z = a) =
        ∏ i ∈ G, AronowAudit.P009.marginal E' i (a' i) := by
    rw [hfix, hfixed]
  rw [hprob]
  exact ⟨hprodLower, hprodUpper⟩
