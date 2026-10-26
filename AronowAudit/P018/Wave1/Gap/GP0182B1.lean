import AronowAudit.P018.P018_Audit
import Mathlib.Probability.HasLaw

/-!
Finite two-atom laws, shared-endpoint dyad counts, Gaussian moments,
and incidence covariance identities.
-/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! P018-T3: a finite two-atom probability law. -/

private lemma spike_weights (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (N : ℝ)⁻¹ ∧ 0 ≤ 1 - (N : ℝ)⁻¹ := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact ⟨inv_nonneg.mpr (by positivity), sub_nonneg.mpr (inv_le_one_of_one_le₀ hn)⟩

private lemma spike_probability (N : ℕ) (hN : 1 ≤ N) :
    IsProbabilityMeasure (inverseSpikeLaw N) := by
  obtain ⟨hp, hq⟩ := spike_weights N hN
  have hw : ENNReal.ofReal ((N : ℝ)⁻¹) +
      ENNReal.ofReal (1 - (N : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_add hp hq]
    norm_num
  constructor
  simpa [inverseSpikeLaw, Measure.add_apply, Measure.smul_apply] using hw

-- Every real-valued function is integrable against this finite-support law.
private lemma spike_integrable (N : ℕ) (f : ℝ → ℝ) :
    Integrable f (inverseSpikeLaw N) := by
  have hleft : Integrable f (Measure.dirac (N : ℝ)) := integrable_dirac (by simp)
  have hright : Integrable f (Measure.dirac (1 : ℝ)) := integrable_dirac (by simp)
  exact integrable_add_measure.mpr
    ⟨hleft.smul_measure ENNReal.ofReal_ne_top,
      hright.smul_measure ENNReal.ofReal_ne_top⟩

private lemma spike_integral (N : ℕ) (hN : 1 ≤ N) (f : ℝ → ℝ) :
    (∫ x, f x ∂inverseSpikeLaw N) =
      (N : ℝ)⁻¹ * f N + (1 - (N : ℝ)⁻¹) * f 1 := by
  obtain ⟨hp, hq⟩ := spike_weights N hN
  have hleft : Integrable f (Measure.dirac (N : ℝ)) := integrable_dirac (by simp)
  have hright : Integrable f (Measure.dirac (1 : ℝ)) := integrable_dirac (by simp)
  rw [inverseSpikeLaw, integral_add_measure
    (hleft.smul_measure ENNReal.ofReal_ne_top)
    (hright.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, smul_eq_mul]

private lemma spike_moments (N : ℕ) (hN : 1 ≤ N) :
    (∫ x, x ∂inverseSpikeLaw N) = 2 - (N : ℝ)⁻¹ ∧
    ProbabilityTheory.variance id (inverseSpikeLaw N) =
      (N : ℝ) - 3 + 3 / (N : ℝ) - 1 / (N : ℝ)^2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  letI : IsProbabilityMeasure (inverseSpikeLaw N) := spike_probability N hN
  have hm : (∫ x, x ∂inverseSpikeLaw N) = 2 - (N : ℝ)⁻¹ := by
    rw [spike_integral N hN]
    field_simp [hn0]
    <;> ring
  have hs : (∫ x, x^2 ∂inverseSpikeLaw N) = (N : ℝ) + 1 - (N : ℝ)⁻¹ := by
    rw [spike_integral N hN]
    field_simp [hn0]
    <;> ring
  have hLp : MemLp (id : ℝ → ℝ) 2 (inverseSpikeLaw N) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr
      (spike_integrable N (fun x => x^2))
  refine ⟨hm, ?_⟩
  rw [ProbabilityTheory.variance_eq_sub hLp]
  change (∫ x, x^2 ∂inverseSpikeLaw N) - (∫ x, x ∂inverseSpikeLaw N)^2 = _
  rw [hm, hs]
  field_simp [hn0]
  <;> ring

private lemma spike_tail_bound (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    (inverseSpikeLaw N {x | ε ≤ ‖x - 1‖}).toReal ≤ (N : ℝ)⁻¹ := by
  have hp := (spike_weights N hN).1
  have h1 : (1 : ℝ) ∉ {x : ℝ | ε ≤ ‖x - 1‖} := by simp [not_le.mpr hε]
  have hbound : inverseSpikeLaw N {x | ε ≤ ‖x - 1‖} ≤
      ENNReal.ofReal ((N : ℝ)⁻¹) := by
    unfold inverseSpikeLaw
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> simp_all
  simpa only [ENNReal.toReal_ofReal hp] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

private lemma spike_variance_ge (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) - 3 ≤ ProbabilityTheory.variance id (inverseSpikeLaw N) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hr : 3 / (N : ℝ) - 1 / (N : ℝ)^2 =
      (3 * (N : ℝ) - 1) / (N : ℝ)^2 := by field_simp [hn0] <;> ring
  have hpos : 0 ≤ (3 * (N : ℝ) - 1) / (N : ℝ)^2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  rw [(spike_moments N hN).2]
  linarith [hr]

theorem inverse_spike_counterexample_proof :
    (∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (inverseSpikeLaw N)) ∧
    inProbability inverseSpikeLaw (fun _ x => x-1) ∧
    (∀ N : ℕ, 1 ≤ N → (∫ x, x ∂ inverseSpikeLaw N) = 2-(N : ℝ)⁻¹ ∧
      ProbabilityTheory.variance id (inverseSpikeLaw N) =
        (N : ℝ)-3+3/(N : ℝ)-1/(N : ℝ)^2) ∧
    Tendsto (fun N : ℕ => ∫ x, x ∂ inverseSpikeLaw N) atTop (𝓝 2) ∧
    Tendsto (fun N : ℕ => ProbabilityTheory.variance id (inverseSpikeLaw N)) atTop atTop := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine ⟨spike_probability, ?_, spike_moments, ?_, ?_⟩
  · intro ε hε
    apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact spike_tail_bound N hN ε hε
    · exact hinv
  · have hlim : Tendsto (fun N : ℕ => 2 - (N : ℝ)⁻¹) atTop (𝓝 2) := by
      simpa using tendsto_const_nhds.sub hinv
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (spike_moments N hN).1.symm
  · apply tendsto_atTop.2
    intro b
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, hcast.eventually (eventually_ge_atTop (b + 3))]
      with N hN hb
    exact le_trans (by linarith : b ≤ (N : ℝ) - 3) (spike_variance_ge N hN)

/-! P018-T4: neighbors as one shared and one outside endpoint. -/

private def counts_pair {N : ℕ} (u v : Fin N) (huv : u ≠ v) : Dyad N :=
  ⟨{u, v}, by simp [dyads, Finset.mem_powersetCard, huv]⟩

private lemma counts_pair_members {N : ℕ} (u v : Fin N) (huv : u ≠ v) :
    members (counts_pair u v huv) = {u, v} := rfl

private lemma counts_other_endpoint {N : ℕ} (d f : Dyad N) (hfd : f ≠ d)
    (u : Fin N) (hud : u ∈ members d) (huf : u ∈ members f) :
    ∃ v : Fin N, v ∉ members d ∧ members f = {u, v} := by
  classical
  obtain ⟨x, y, hxy, hf⟩ := Finset.card_eq_two.mp (members_card f)
  have hup : u = x ∨ u = y := by simpa only [hf, mem_insert, mem_singleton] using huf
  have hout (v : Fin N) (hpair : members f = {u, v}) : v ∉ members d := by
    intro hv
    have hsub : members f ⊆ members d := by
      intro z hz
      rcases (show z = u ∨ z = v by simpa only [hpair, mem_insert, mem_singleton] using hz) with hz | hz
      · simpa only [hz] using hud
      · simpa only [hz] using hv
    have heq : members f = members d :=
      Finset.eq_of_subset_of_card_le hsub (by rw [members_card, members_card])
    exact hfd (Subtype.ext heq)
  rcases hup with hux | huy
  · have hpair : members f = {u, y} := by simpa only [hux] using hf
    exact ⟨y, hout y hpair, hpair⟩
  · have hpair : members f = {u, x} := by
      simpa only [huy] using hf.trans (Finset.pair_comm _ _)
    exact ⟨x, hout x hpair, hpair⟩

private def counts_neighborMap {N : ℕ} (d : Dyad N)
    (p : ↥(members d) × ↥(univ \ members d)) : ↥(neighbors d) := by
  classical
  have hu : p.1.val ∈ members d := p.1.property
  have hv : p.2.val ∉ members d := (mem_sdiff.mp p.2.property).2
  have huv : p.1.val ≠ p.2.val := by intro h; exact hv (h ▸ hu)
  let f := counts_pair p.1.val p.2.val huv
  refine ⟨f, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩⟩
  · intro hfd
    apply hv
    have hmem : p.2.val ∈ members f := by simp [f, counts_pair_members]
    simpa only [hfd] using hmem
  · exact ⟨p.1.val, mem_inter.mpr ⟨hu, by simp [f, counts_pair_members]⟩⟩

private lemma counts_neighborMap_bijective {N : ℕ} (d : Dyad N) :
    Function.Bijective (counts_neighborMap d) := by
  classical
  constructor
  · intro p q hpq
    have hu : p.1.val ∈ members d := p.1.property
    have hv : p.2.val ∉ members d := (mem_sdiff.mp p.2.property).2
    have hqu : q.1.val ∈ members d := q.1.property
    have hqv : q.2.val ∉ members d := (mem_sdiff.mp q.2.property).2
    have heq : ({p.1.val, p.2.val} : Finset (Fin N)) = {q.1.val, q.2.val} :=
      congrArg (fun f : ↥(neighbors d) => members f.val) hpq
    have hpu : p.1.val = q.1.val := by
      have hm : p.1.val ∈ ({q.1.val, q.2.val} : Finset (Fin N)) :=
        heq ▸ (by simp)
      rcases (show p.1.val = q.1.val ∨ p.1.val = q.2.val by simpa using hm) with h | h
      · exact h
      · exact False.elim (hqv (h ▸ hu))
    have hpv : p.2.val = q.2.val := by
      have hm : p.2.val ∈ ({q.1.val, q.2.val} : Finset (Fin N)) :=
        heq ▸ (by simp)
      rcases (show p.2.val = q.1.val ∨ p.2.val = q.2.val by simpa using hm) with h | h
      · exact False.elim (hv (h.symm ▸ hqu))
      · exact h
    exact Prod.ext (Subtype.ext hpu) (Subtype.ext hpv)
  · intro f
    have hf : f.val ≠ d ∧ (members d ∩ members f.val).Nonempty :=
      (mem_filter.mp f.property).2
    obtain ⟨u, hu⟩ := hf.2
    obtain ⟨v, hv, hpair⟩ :=
      counts_other_endpoint d f.val hf.1 u (mem_inter.mp hu).1 (mem_inter.mp hu).2
    let p : ↥(members d) × ↥(univ \ members d) :=
      (⟨u, (mem_inter.mp hu).1⟩, ⟨v, mem_sdiff.mpr ⟨mem_univ _, hv⟩⟩)
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hpair.symm

private lemma counts_neighbors {N : ℕ} (d : Dyad N) :
    (neighbors d).card = 2 * (N - 2) := by
  classical
  have hc := Fintype.card_of_bijective (counts_neighborMap_bijective d)
  simpa only [Fintype.card_prod, Fintype.card_coe,
    Finset.card_sdiff_of_subset (subset_univ (members d)),
    Finset.card_univ, Fintype.card_fin, members_card] using hc.symm

private lemma counts_overlap_fiber (N : ℕ) (hN : 2 ≤ N) (d : Dyad N) :
    (univ.filter (fun f : Dyad N => overlap d f)).card = 2 * N - 3 := by
  classical
  have hself : overlap d d := by
    simpa only [overlap, inter_self] using
      (Finset.card_pos.mp (by rw [members_card]; omega) : (members d).Nonempty)
  have heq : univ.filter (fun f : Dyad N => overlap d f) = insert d (neighbors d) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_insert, neighbors]
    change overlap d f ↔ f = d ∨ (f ≠ d ∧ overlap d f)
    by_cases hfd : f = d <;> simp_all
  have hnot : d ∉ neighbors d := by simp [neighbors]
  rw [heq, card_insert_of_notMem hnot, counts_neighbors]
  omega

private lemma counts_choose_twice (N : ℕ) : N.choose 2 * 2 = N * (N - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose N 2
  simpa [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.mul_comm] using h.symm

theorem dyad_counts_proof (N : ℕ) (hN : 2 ≤ N) :
    Fintype.card (Dyad N) = N.choose 2 ∧
    (∀ d : Dyad N, (neighbors d).card = 2*(N-2)) ∧
    (∑ d : Dyad N, (neighbors d).card) = N*(N-1)*(N-2) ∧
    (univ.filter (fun p : Dyad N × Dyad N => overlap p.1 p.2)).card =
      N.choose 2 * (2*N-3) := by
  classical
  refine ⟨number_of_dyads N, counts_neighbors, ?_, ?_⟩
  · simp_rw [counts_neighbors]
    simp only [sum_const, card_univ, smul_eq_mul, number_of_dyads]
    rw [← Nat.mul_assoc, counts_choose_twice]
  · calc
      (univ.filter (fun p : Dyad N × Dyad N => overlap p.1 p.2)).card =
          ∑ p : Dyad N × Dyad N, if overlap p.1 p.2 then 1 else 0 := by
            rw [Finset.card_filter]
      _ = ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then 1 else 0 := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ d : Dyad N, (univ.filter (fun f : Dyad N => overlap d f)).card := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.card_filter]
      _ = N.choose 2 * (2 * N - 3) := by
            simp only [counts_overlap_fiber N hN, sum_const, card_univ, number_of_dyads,
              smul_eq_mul]

/-! P018-T5: Gaussian coordinate moments and independent translation noise. -/

private lemma intercept_coordinate_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (a : Fin N → Ω → ℝ)
    (hlaw : ∀ i, HasLaw (a i) (gaussianReal 0 1) μ) :
    (∀ i, MemLp (a i) 2 μ) ∧ (∀ i, ProbabilityTheory.variance (a i) μ = 1) := by
  constructor
  · intro i
    exact (hlaw i).memLp (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  · intro i
    simpa only [variance_id_gaussianReal, NNReal.coe_one] using (hlaw i).variance_eq

private lemma intercept_shift_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N)
    (a : Fin N → Ω → ℝ) (ha : iIndepFun a μ)
    (hlaw : ∀ i, HasLaw (a i) (gaussianReal 0 1) μ) :
    MemLp (fun ω => 2 * (∑ i, a i ω) / (N : ℝ)) 2 μ ∧
    ProbabilityTheory.variance (fun ω => 2 * (∑ i, a i ω) / (N : ℝ)) μ = 4 / (N : ℝ) := by
  classical
  obtain ⟨hLp, hv⟩ := intercept_coordinate_moments μ N a hlaw
  have hsumLp : MemLp (fun ω => ∑ i, a i ω) 2 μ := by
    exact memLp_finsetSum univ (fun i _ => hLp i)
  have hsumV : ProbabilityTheory.variance (fun ω => ∑ i, a i ω) μ = (N : ℝ) := by
    have hpair : Set.Pairwise (↑(univ : Finset (Fin N)))
        (fun i j => IndepFun (a i) (a j) μ) := by
      intro i hi j hj hij
      exact ha.indepFun hij
    have hs := ProbabilityTheory.IndepFun.variance_sum (s := univ)
      (fun i _ => hLp i) hpair
    have hsumfun : (∑ i : Fin N, a i) = (fun ω => ∑ i, a i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hsumfun] at hs
    simpa [hv] using hs
  have hfun : (fun ω => 2 * (∑ i, a i ω) / (N : ℝ)) =
      (fun ω => (2 / (N : ℝ)) * (∑ i, a i ω)) := by
    funext ω
    ring
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  constructor
  · rw [hfun]
    exact hsumLp.const_mul (2 / (N : ℝ))
  · rw [hfun, ProbabilityTheory.variance_const_mul, hsumV]
    field_simp [hn0]
    <;> ring

theorem random_intercept_lower_bound_proof {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N)
    (a : Fin N → Ω → ℝ) (ha : iIndepFun a μ)
    (hlaw : ∀ i, HasLaw (a i) (gaussianReal 0 1) μ)
    {D : ℕ} (yc : Ω → Vec D) (estimate : Vec D → ℝ)
    (htranslate : ∀ y c, estimate (y+c • (fun _ => 1)) = estimate y+c)
    (hind : IndepFun yc (fun ω => (∑ i, a i ω)/(N : ℝ)) μ)
    (hmeas : Measurable estimate)
    (hL2c : MemLp (fun ω => estimate (yc ω)) 2 μ)
    (hL2 : MemLp (fun ω => estimate (yc ω+(2*(∑ i,a i ω)/(N : ℝ)) • (fun _ => 1))) 2 μ) :
    ProbabilityTheory.variance
      (fun ω => estimate (yc ω+(2*(∑ i,a i ω)/(N : ℝ)) • (fun _ => 1))) μ =
        ProbabilityTheory.variance (fun ω => estimate (yc ω)) μ + 4/(N : ℝ) ∧
    4/(N : ℝ) ≤ ProbabilityTheory.variance
      (fun ω => estimate (yc ω+(2*(∑ i,a i ω)/(N : ℝ)) • (fun _ => 1))) μ := by
  obtain ⟨hshiftLp, hshiftV⟩ := intercept_shift_moments μ N hN a ha hlaw
  have hshift : (fun ω => 2 * (∑ i, a i ω) / (N : ℝ)) =
      (fun x : ℝ => 2 * x) ∘ (fun ω => (∑ i, a i ω) / (N : ℝ)) := by
    funext ω
    dsimp only [Function.comp_def]
    ring
  have hi : IndepFun (fun ω => estimate (yc ω))
      (fun ω => 2 * (∑ i, a i ω) / (N : ℝ)) μ := by
    rw [hshift]
    exact hind.comp hmeas (measurable_const.mul measurable_id)
  have hv : ProbabilityTheory.variance
      (fun ω => estimate (yc ω) + 2 * (∑ i, a i ω) / (N : ℝ)) μ =
      ProbabilityTheory.variance (fun ω => estimate (yc ω)) μ + 4 / (N : ℝ) := by
    rw [hi.variance_fun_add hL2c hshiftLp, hshiftV]
  have heq : (fun ω => estimate (yc ω + (2 * (∑ i, a i ω) / (N : ℝ)) •
      (fun _ => 1))) = (fun ω => estimate (yc ω) + 2 * (∑ i, a i ω) / (N : ℝ)) := by
    funext ω
    exact htranslate _ _
  rw [heq]
  refine ⟨hv, ?_⟩
  rw [hv]
  exact le_add_of_nonneg_left (ProbabilityTheory.variance_nonneg _ _)

/-! P018-T6: incidence products and the cross-role covariance witness. -/

private lemma benchmark_endpoints {N : ℕ} (d : Dyad N) :
    firstUnit d < secondUnit d ∧ members d = {firstUnit d, secondUnit d} := by
  classical
  obtain ⟨u, v, huv, hd⟩ := Finset.card_eq_two.mp (members_card d)
  have hfirst : firstUnit d = min u v := by
    simp only [firstUnit, hd, Finset.min'_pair]
  have hsecond : secondUnit d = max u v := by
    simp only [secondUnit, hd, Finset.max'_pair]
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · rw [hfirst, hsecond, min_eq_left hlt.le, max_eq_right hlt.le]
    exact ⟨hlt, hd⟩
  · rw [hfirst, hsecond, min_eq_right hgt.le, max_eq_left hgt.le]
    exact ⟨hgt, hd.trans (Finset.pair_comm _ _)⟩

private lemma benchmark_pair_endpoints {N : ℕ} (u v : Fin N) (huv : u < v) :
    firstUnit (counts_pair u v huv.ne) = u ∧
    secondUnit (counts_pair u v huv.ne) = v := by
  constructor
  · simp only [firstUnit, counts_pair_members, Finset.min'_pair, min_eq_left huv.le]
  · simp only [secondUnit, counts_pair_members, Finset.max'_pair, max_eq_right huv.le]

private lemma benchmark_indicator_product {N : ℕ} (a b : Fin N) :
    (∑ i : Fin N, (if a = i then (1 : ℝ) else 0) * (if b = i then 1 else 0)) =
      (if a = b then 1 else 0) := by
  classical
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, if_true]
  simp only [eq_comm]

private lemma benchmark_role_products {N : ℕ} (d f : Dyad N) :
    (endpointZ1 N * (endpointZ1 N).transpose) d f = (if firstUnit d = firstUnit f then 1 else 0) ∧
    (endpointZ2 N * (endpointZ2 N).transpose) d f = (if secondUnit d = secondUnit f then 1 else 0) ∧
    (endpointZ1 N * (endpointZ2 N).transpose) d f = (if firstUnit d = secondUnit f then 1 else 0) ∧
    (endpointZ2 N * (endpointZ1 N).transpose) d f = (if secondUnit d = firstUnit f then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.mul_apply, Matrix.transpose_apply, endpointZ1] using
      benchmark_indicator_product (firstUnit d) (firstUnit f)
  · simpa only [Matrix.mul_apply, Matrix.transpose_apply, endpointZ2] using
      benchmark_indicator_product (secondUnit d) (secondUnit f)
  · simpa only [Matrix.mul_apply, Matrix.transpose_apply, endpointZ1, endpointZ2] using
      benchmark_indicator_product (firstUnit d) (secondUnit f)
  · simpa only [Matrix.mul_apply, Matrix.transpose_apply, endpointZ1, endpointZ2] using
      benchmark_indicator_product (secondUnit d) (firstUnit f)

private lemma benchmark_incidence_row {N : ℕ} (d : Dyad N) (i : Fin N) :
    (endpointZ1 N + endpointZ2 N) d i = if i ∈ members d then 1 else 0 := by
  classical
  obtain ⟨hlt, hpair⟩ := benchmark_endpoints d
  have hne : firstUnit d ≠ secondUnit d := hlt.ne
  simp only [Matrix.add_apply, endpointZ1, endpointZ2, hpair, mem_insert, mem_singleton]
  by_cases h1 : firstUnit d = i <;> by_cases h2 : secondUnit d = i <;>
    simp_all [eq_comm]

private lemma benchmark_shared_product {N : ℕ} (d f : Dyad N) :
    ((endpointZ1 N + endpointZ2 N) * (endpointZ1 N + endpointZ2 N).transpose) d f =
      ((members d ∩ members f).card : ℝ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, benchmark_incidence_row]
  have hterm (i : Fin N) :
      (if i ∈ members d then (1 : ℝ) else 0) * (if i ∈ members f then 1 else 0) =
      (if i ∈ members d ∩ members f then 1 else 0) := by
    by_cases hd : i ∈ members d <;> by_cases hf : i ∈ members f <;> simp [hd, hf]
  simp_rw [hterm]
  have hfilter : univ.filter (fun i => i ∈ members d ∩ members f) = members d ∩ members f := by
    ext i
    simp
  rw [← Finset.sum_filter, hfilter]
  simp

private lemma benchmark_expansion (N : ℕ) (τ σ : ℝ) : sharedCov N τ σ =
    τ • (endpointZ1 N * (endpointZ1 N).transpose + endpointZ2 N * (endpointZ2 N).transpose +
      endpointZ1 N * (endpointZ2 N).transpose + endpointZ2 N * (endpointZ1 N).transpose) + σ • 1 := by
  unfold sharedCov
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  congr 2
  abel

private lemma benchmark_no_match (N : ℕ) (hN : 3 ≤ N) (τ σ : ℝ) (hτ : 0 < τ)
    (t1 t2 s : ℝ) : sharedCov N τ σ ≠ twoRoleCov N t1 t2 s := by
  classical
  let u : Fin N := ⟨0, by omega⟩
  let v : Fin N := ⟨1, by omega⟩
  let w : Fin N := ⟨2, by omega⟩
  have huv : u < v := by change (0 : ℕ) < 1; omega
  have hvw : v < w := by change (1 : ℕ) < 2; omega
  let d : Dyad N := counts_pair u v huv.ne
  let f : Dyad N := counts_pair v w hvw.ne
  have hd1 : firstUnit d = u := (benchmark_pair_endpoints u v huv).1
  have hd2 : secondUnit d = v := (benchmark_pair_endpoints u v huv).2
  have hf1 : firstUnit f = v := (benchmark_pair_endpoints v w hvw).1
  have hf2 : secondUnit f = w := (benchmark_pair_endpoints v w hvw).2
  have hdf : d ≠ f := by
    intro h
    apply huv.ne
    simpa only [hd1, hf1] using congrArg (fun q : Dyad N => firstUnit q) h
  have hov : (members d ∩ members f).Nonempty := by
    refine ⟨v, mem_inter.mpr ⟨?_, ?_⟩⟩ <;> simp [d, f, counts_pair_members]
  have hinter : ((members d ∩ members f).card : ℝ) = 1 := by
    have hinj : Function.Injective (members : Dyad N → Finset (Fin N)) := by
      intro x y h
      exact Subtype.ext h
    simpa only [hov, if_true, hdf, if_false, add_zero] using
      intersection_count members members_card hinj d f
  have hshared : sharedCov N τ σ d f = τ := by
    simp only [sharedCov, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      benchmark_shared_product, hinter, Matrix.one_apply, hdf, if_false,
      mul_one, mul_zero, add_zero]
  have htwo : twoRoleCov N t1 t2 s d f = 0 := by
    obtain ⟨h11, h22, h12, h21⟩ := benchmark_role_products d f
    simp only [twoRoleCov, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      h11, h22, hd1, hd2, hf1, hf2, huv.ne, hvw.ne, if_false,
      Matrix.one_apply, hdf, mul_zero, add_zero]
  intro h
  have he := congrArg (fun M : Matrix (Dyad N) (Dyad N) ℝ => M d f) h
  rw [hshared, htwo] at he
  linarith

theorem benchmark_covariance_correction_proof (N : ℕ) (hN : 2 ≤ N) :
    (∀ d f : Dyad N,
      (endpointZ1 N * (endpointZ1 N).transpose) d f = (if firstUnit d = firstUnit f then 1 else 0) ∧
      (endpointZ2 N * (endpointZ2 N).transpose) d f = (if secondUnit d = secondUnit f then 1 else 0) ∧
      (endpointZ1 N * (endpointZ2 N).transpose) d f = (if firstUnit d = secondUnit f then 1 else 0) ∧
      (endpointZ2 N * (endpointZ1 N).transpose) d f = (if secondUnit d = firstUnit f then 1 else 0) ∧
      ((endpointZ1 N + endpointZ2 N) * (endpointZ1 N + endpointZ2 N).transpose) d f =
        ((members d ∩ members f).card : ℝ)) ∧
    (∀ τ σ : ℝ, sharedCov N τ σ =
      τ • (endpointZ1 N * (endpointZ1 N).transpose + endpointZ2 N * (endpointZ2 N).transpose +
        endpointZ1 N * (endpointZ2 N).transpose + endpointZ2 N * (endpointZ1 N).transpose) + σ • 1) ∧
    (3 ≤ N → ∀ τ σ : ℝ, 0 < τ → ∀ t1 t2 s : ℝ, sharedCov N τ σ ≠ twoRoleCov N t1 t2 s) := by
  refine ⟨?_, benchmark_expansion N, ?_⟩
  · intro d f
    obtain ⟨h11, h22, h12, h21⟩ := benchmark_role_products d f
    exact ⟨h11, h22, h12, h21, benchmark_shared_product d f⟩
  · intro hthree τ σ hτ t1 t2 s
    exact benchmark_no_match N hthree τ σ hτ t1 t2 s

end AronowAudit.P018.Wave1
