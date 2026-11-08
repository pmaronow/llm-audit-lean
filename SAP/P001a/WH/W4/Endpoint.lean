import SAP.P001a.WH.W4.Model

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Matrix

noncomputable section

namespace SAP.P001a.WH.W4

open AronowAudit.P001.Wave1.SieveRate
open AronowAudit.P001.Wave1.TailBSieveEscape

theorem gaussian_tail_half (v : ℝ≥0) (hv : (1 : ℝ) / 2 ≤ (v : ℝ)) :
    1 / 2 ≤ ((gaussianReal 0 v) {z : ℝ | 1 / 4 < |z|}).toReal := by
  have hvpos : 0 < v := by exact_mod_cast (by linarith : (0 : ℝ) < (v : ℝ))
  have hd : 1 ≤ 2 * Real.pi * (v : ℝ) := by nlinarith [Real.pi_gt_three]
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    simpa using Real.sqrt_le_sqrt hd
  have hsmall : ((gaussianReal 0 v) (Set.Icc (-(1 / 4)) (1 / 4))).toReal ≤ 1 / 2 := by
    refine (AronowAudit.Shared.MapTailB.TailB_gaussian_small_ball v hvpos (1 / 4)
      (by norm_num)).trans ?_
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)))).2
    nlinarith
  have hcomp : {z : ℝ | 1 / 4 < |z|} = (Set.Icc (-(1 / 4)) (1 / 4))ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
  rw [hcomp, ← measureReal_def, probReal_compl_eq_one_sub measurableSet_Icc]
  change (gaussianReal 0 v).real (Set.Icc (-(1 / 4)) (1 / 4)) ≤ 1 / 2 at hsmall
  linarith

theorem ols_endpoint (n d : ℕ) (x y : Fin n → ℝ) :
    (olsPoly d x y).eval 1 =
      AronowAudit.P001.olsCoef (vand d x) y ⬝ᵥ (fun _ : Fin (d + 1) => (1 : ℝ)) := by
  simp only [olsPoly, coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, dotProduct]

theorem measurable_ols_endpoint (n d : ℕ) :
    Measurable (fun z : SieveDataW4 n => (olsPoly d z.1 z.2).eval 1) := by
  simp_rw [ols_endpoint, dotProduct, mul_one]
  exact Finset.measurable_sum Finset.univ fun k _ =>
    (measurable_pi_apply k).comp (tb02_meas_ols n d)

theorem fixed_endpoint_tail (n d : ℕ) (x : Fin n → ℝ) (hcols : d + 1 ≤ n)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ d) (hq1 : q.eval 1 = 1)
    (hx : x ∈ goodDesign n q) :
    1 / 2 ≤ prob (gaussVec n) {y | 1 / 4 < |(olsPoly d x y).eval 1|} := by
  classical
  have hunit := n5_proof n d x hcols hx.1
  let c : Fin (d + 1) → ℝ := fun k => q.coeff (k : ℕ)
  let w : Fin (d + 1) → ℝ := fun _ => 1
  let v : ℝ := w ⬝ᵥ (((vand d x).transpose * vand d x)⁻¹).mulVec w
  have hpoly : coeffPoly c = q := (polynomial_of_coefficients q hq).symm
  have hcw : c ⬝ᵥ w = 1 := by
    have he : (coeffPoly c).eval 1 = c ⬝ᵥ w := by
      simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one,
        dotProduct, w]
    rw [hpoly, hq1] at he
    exact he.symm
  have hS : ∑ i : Fin n, ((vand d x).mulVec c i) ^ 2 ≤ 2 := by
    simpa only [n8_proof.2, hpoly] using hx.2
  have hcs : 1 ≤ (∑ i : Fin n, ((vand d x).mulVec c i) ^ 2) * v := by
    have h := n9_proof n (d + 1) (vand d x) hunit c w
    simpa only [hcw, one_pow] using h
  have hv0 : 0 ≤ v := by
    by_contra h
    have hS0 : 0 ≤ ∑ i : Fin n, ((vand d x).mulVec c i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have hv : (1 : ℝ) / 2 ≤ v := by nlinarith
  have htail := gaussian_tail_half v.toNNReal (by
    simpa only [Real.coe_toNNReal _ hv0] using hv)
  have hlaw := n13_proof n (d + 1) (vand d x) hunit w
  have hm : Measurable (fun y : Fin n → ℝ => AronowAudit.P001.olsCoef (vand d x) y ⬝ᵥ w) := by
    simpa only [ols_endpoint, w, Function.comp_def, id_eq] using
      (measurable_ols_endpoint n d).comp (measurable_const.prodMk measurable_id)
  have hTail : MeasurableSet {z : ℝ | 1 / 4 < |z|} := by measurability
  rw [← hlaw, Measure.map_apply hm hTail] at htail
  simpa only [prob, ols_endpoint, w, Set.preimage_setOf_eq] using htail

/-- The finite product experiment already has the endpoint bound; no coupling across
sample sizes occurs in this calculation. -/
theorem product_endpoint_tail (n d : ℕ) (hcols : d + 1 ≤ n)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ d) (hq1 : q.eval 1 = 1)
    (hmass : 1 / 2 ≤ prob (unifVec n) (goodDesign n q)) :
    1 / 4 ≤ prob ((unifVec n).prod (gaussVec n))
      {z | z.1 ∈ goodDesign n q ∧ 1 / 4 < |(olsPoly d z.1 z.2).eval 1|} := by
  classical
  letI : IsProbabilityMeasure (unifVec n) := by unfold unifVec; infer_instance
  letI : IsProbabilityMeasure (gaussVec n) := by unfold gaussVec; infer_instance
  let E : Set (SieveDataW4 n) :=
    {z | z.1 ∈ goodDesign n q ∧ 1 / 4 < |(olsPoly d z.1 z.2).eval 1|}
  have hE : MeasurableSet E :=
    ((measurable_goodDesign n q).preimage measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_ols_endpoint n d).abs)
  have hpoint (x : Fin n → ℝ) (hx : x ∈ goodDesign n q) :
      ENNReal.ofReal ((1 : ℝ) / 2) ≤ (gaussVec n) (Prod.mk x ⁻¹' E) := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
    have hsection : Prod.mk x ⁻¹' E = {y | 1 / 4 < |(olsPoly d x y).eval 1|} := by
      ext y
      simp only [E, Set.mem_preimage, Set.mem_setOf_eq, hx, true_and]
    rw [hsection]
    exact fixed_endpoint_tail n d x hcols q hq hq1 hx
  have hfubini : ENNReal.ofReal ((1 : ℝ) / 2) * (unifVec n) (goodDesign n q) ≤
      ((unifVec n).prod (gaussVec n)) E := by
    rw [Measure.prod_apply hE]
    rw [← lintegral_indicator_const (measurable_goodDesign n q)]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ goodDesign n q
    · rw [Set.indicator_of_mem hx]
      exact hpoint x hx
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hprod : 1 / 4 ≤ (((unifVec n).prod (gaussVec n)) E).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1
    have hd : ENNReal.ofReal ((1 : ℝ) / 2) ≤ (unifVec n) (goodDesign n q) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hmass
    calc
      ENNReal.ofReal ((1 : ℝ) / 4) =
          ENNReal.ofReal ((1 : ℝ) / 2) * ENNReal.ofReal ((1 : ℝ) / 2) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            congr 1
            norm_num
      _ ≤ ENNReal.ofReal ((1 : ℝ) / 2) * (unifVec n) (goodDesign n q) := by gcongr
      _ ≤ _ := hfubini
  exact hprod

/-- Integrate the fixed-design half-probability bound over a design event of mass at
least one half. Full rank then transfers OLS to every least-squares minimizer. -/
theorem sample_endpoint_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
      (uniformLaw 0 1).prod (gaussianReal 0 1))
    (J : ℕ → ℕ) (fit : ℕ → Ω → Polynomial ℝ) (hfit : IsSieveLS X Y J fit)
    (n d : ℕ) (hJ : J n = d) (hcols : d + 1 ≤ n)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ d) (hq1 : q.eval 1 = 1)
    (hmass : 1 / 2 ≤ prob (unifVec n) (goodDesign n q)) :
    1 / 4 ≤ prob μ {ω | 1 / 4 < |(fit n ω).eval 1|} := by
  classical
  let E : Set (SieveDataW4 n) :=
    {z | z.1 ∈ goodDesign n q ∧ 1 / 4 < |(olsPoly d z.1 z.2).eval 1|}
  have hE : MeasurableSet E :=
    ((measurable_goodDesign n q).preimage measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_ols_endpoint n d).abs)
  have hprod := product_endpoint_tail n d hcols q hq hq1 hmass
  let F : Ω → SieveDataW4 n :=
    fun ω => ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω))
  have hF : Measurable F :=
    (Measurable.of_eval (fun i : Fin n => (hiid.1 i).fst)).prodMk
      (Measurable.of_eval (fun i : Fin n => (hiid.1 i).snd))
  have hlawF : μ.map F = (unifVec n).prod (gaussVec n) :=
    tb02_first_law μ X Y hiid hlaw n
  have heq : μ (F ⁻¹' E) = ((unifVec n).prod (gaussVec n)) E := by
    rw [← Measure.map_apply hF hE, hlawF]
  have hsub : F ⁻¹' E ⊆ {ω | 1 / 4 < |(fit n ω).eval 1|} := by
    intro ω hω
    obtain ⟨hx, htail⟩ := hω
    have hf := hfit n ω
    rw [hJ] at hf
    have hfEq : fit n ω = olsPoly d (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω) :=
      n6_proof n5_proof n d (fun i => X i ω) (fun i => Y i ω)
        (fit n ω) hcols hx.1 hf.1 hf.2
    change 1 / 4 < |(fit n ω).eval 1|
    rw [hfEq]
    exact htail
  calc
    1 / 4 ≤ (μ (F ⁻¹' E)).toReal := by rw [heq]; exact hprod
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

/-- A finite sample with the product law suffices, on any probability space. -/
theorem finite_endpoint_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n d : ℕ) (Z : Ω → SieveDataW4 n)
    (hZ : Measurable Z) (hlaw : μ.map Z = finiteSampleLawW4 n)
    (fit : Ω → Polynomial ℝ) (hdeg : ∀ ω, (fit ω).natDegree ≤ d)
    (hmin : ∀ ω : Ω, ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      (∑ i : Fin n, ((Z ω).2 i - (fit ω).eval ((Z ω).1 i)) ^ 2) ≤
        ∑ i : Fin n, ((Z ω).2 i - p.eval ((Z ω).1 i)) ^ 2)
    (hcols : d + 1 ≤ n) (q : Polynomial ℝ) (hq : q.natDegree ≤ d) (hq1 : q.eval 1 = 1)
    (hmass : 1 / 2 ≤ prob (unifVec n) (goodDesign n q)) :
    1 / 4 ≤ prob μ {ω | 1 / 4 < |(fit ω).eval 1|} := by
  classical
  let E : Set (SieveDataW4 n) :=
    {z | z.1 ∈ goodDesign n q ∧ 1 / 4 < |(olsPoly d z.1 z.2).eval 1|}
  have hE : MeasurableSet E :=
    ((measurable_goodDesign n q).preimage measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_ols_endpoint n d).abs)
  have hprod := product_endpoint_tail n d hcols q hq hq1 hmass
  have heq : μ (Z ⁻¹' E) = ((unifVec n).prod (gaussVec n)) E := by
    rw [← Measure.map_apply hZ hE, hlaw]
    rfl
  have hsub : Z ⁻¹' E ⊆ {ω | 1 / 4 < |(fit ω).eval 1|} := by
    intro ω hω
    obtain ⟨hx, htail⟩ := hω
    let x : ℕ → ℝ := fun i => if h : i < n then (Z ω).1 ⟨i, h⟩ else 0
    let y : ℕ → ℝ := fun i => if h : i < n then (Z ω).2 ⟨i, h⟩ else 0
    have hxf : (fun i : Fin n => x i) = (Z ω).1 := by
      funext i
      exact dif_pos i.isLt
    have hyf : (fun i : Fin n => y i) = (Z ω).2 := by
      funext i
      exact dif_pos i.isLt
    have hmin' (p : Polynomial ℝ) (hp : p.natDegree ≤ d) :
        (∑ i ∈ Finset.range n, (y i - (fit ω).eval (x i)) ^ 2) ≤
          ∑ i ∈ Finset.range n, (y i - p.eval (x i)) ^ 2 := by
      have h := hmin ω p hp
      rw [← hxf, ← hyf] at h
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (y i - (fit ω).eval (x i)) ^ 2) n,
        Fin.sum_univ_eq_sum_range (fun i : ℕ => (y i - p.eval (x i)) ^ 2) n] at h
      exact h
    have hfEq := n6_proof n5_proof n d x y (fit ω) hcols (hxf.symm ▸ hx.1) (hdeg ω) hmin'
    rw [hxf, hyf] at hfEq
    change 1 / 4 < |(fit ω).eval 1|
    rw [hfEq]
    exact htail
  calc
    1 / 4 ≤ (μ (Z ⁻¹' E)).toReal := by rw [heq]; exact hprod
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

end SAP.P001a.WH.W4
