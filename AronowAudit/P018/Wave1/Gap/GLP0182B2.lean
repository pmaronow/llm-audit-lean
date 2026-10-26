import AronowAudit.P018.Wave1.Gap.GP0182B2b

/-!
P018-T4: finite population-residual variance bounds and corrected sandwich
consistency.
-/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! Sharp finite support counts. -/

private def population_meat_mkDyad {N : ℕ} (i j : Fin N) (hij : i ≠ j) : Dyad N :=
  ⟨{i, j}, by simp [dyads, Finset.mem_powersetCard, hij]⟩

lemma population_meat_incident_count {N : ℕ} (i : Fin N) :
    (∑ d : Dyad N, if i ∈ members d then (1 : ℝ) else 0) = (N : ℝ) - 1 := by
  classical
  let s : Finset (Dyad N) := univ.filter (fun d => i ∈ members d)
  let f (j : Fin N) (hj : j ∈ univ.erase i) : Dyad N :=
    population_meat_mkDyad i j (ne_of_mem_erase hj).symm
  have hcard : (univ.erase i).card = s.card := by
    apply Finset.card_bij f
    · intro j hj
      apply mem_filter.mpr
      exact ⟨mem_univ _, by change i ∈ ({i, j} : Finset (Fin N)); simp⟩
    · intro j hj j' hj' heq
      have he : ({i, j} : Finset (Fin N)) = {i, j'} :=
        congrArg members heq
      have hm : j ∈ ({i, j'} : Finset (Fin N)) := he ▸ (by simp)
      have hh := (Finset.mem_insert.mp hm).resolve_left (ne_of_mem_erase hj)
      simpa only [Finset.mem_singleton] using hh
    · intro d hd
      have hi : i ∈ members d := (mem_filter.mp hd).2
      obtain ⟨x, y, hxy, hmem⟩ := Finset.card_eq_two.mp (members_card d)
      have hixy : i = x ∨ i = y := by simpa [hmem] using hi
      rcases hixy with hx | hy
      · subst x
        refine ⟨y, by simp [hxy.symm], ?_⟩
        apply Subtype.ext
        exact hmem.symm
      · subst y
        refine ⟨x, by simp [hxy], ?_⟩
        apply Subtype.ext
        exact (Finset.pair_comm i x).trans hmem.symm
  have hn : 1 ≤ N := by have := i.isLt; omega
  have hs : s.card = N - 1 := by
    rw [← hcard]
    simp
  calc
    _ = (s.card : ℝ) := by simp [s, ← Finset.sum_filter]
    _ = (N : ℝ) - 1 := by rw [hs, Nat.cast_sub hn]; norm_num

lemma population_meat_overlap_row {N : ℕ} (hN : 2 ≤ N) (d : Dyad N) :
    (∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) = 2 * (N : ℝ) - 3 := by
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
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, heq,
    card_insert_of_notMem hnot, (dyad_counts_proof N hN).2.1 d]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN]
  norm_num
  ring

lemma population_meat_overlap_total {N : ℕ} (hN : 2 ≤ N) :
    (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) =
      Dreal N * (2 * (N : ℝ) - 3) := by
  simp only [population_meat_overlap_row hN, Finset.sum_const, card_univ,
    nsmul_eq_mul, printed_card_real]

/-- Inclusion-exclusion avoids an orientation-dependent count of triples. -/
lemma population_meat_pair_through_unit {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    (∑ P : Dyad N × Dyad N,
      if i ∈ WeightedConsistency.pairSupport P then (1 : ℝ) else 0) =
        ((N : ℝ) - 1) * (3 * (N : ℝ) - 5) := by
  classical
  have hsymm (d f : Dyad N) : overlap d f ↔ overlap f d := by
    unfold overlap
    rw [inter_comm]
  have hterm (d f : Dyad N) :
      (if i ∈ WeightedConsistency.pairSupport (d, f) then (1 : ℝ) else 0) =
        (if i ∈ members d then (if overlap d f then 1 else 0) else 0) +
        (if i ∈ members f then (if overlap f d then 1 else 0) else 0) -
        (if i ∈ members d then (if i ∈ members f then 1 else 0) else 0) := by
    have hboth : i ∈ members d → i ∈ members f → overlap d f :=
      fun hd hf => ⟨i, mem_inter.mpr ⟨hd, hf⟩⟩
    simp only [WeightedConsistency.pairSupport, ← hsymm]
    split_ifs <;> simp_all
  have hfirst : (∑ d : Dyad N, ∑ f : Dyad N,
      if i ∈ members d then (if overlap d f then (1 : ℝ) else 0) else 0) =
      ((N : ℝ) - 1) * (2 * (N : ℝ) - 3) := by
    calc
      _ = ∑ d : Dyad N, (if i ∈ members d then 1 else 0) *
          (∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> simp
      _ = _ := by simp_rw [population_meat_overlap_row hN]
                  rw [← Finset.sum_mul, population_meat_incident_count]
  have hsecond : (∑ d : Dyad N, ∑ f : Dyad N,
      if i ∈ members f then (if overlap f d then (1 : ℝ) else 0) else 0) =
      ((N : ℝ) - 1) * (2 * (N : ℝ) - 3) := by
    rw [Finset.sum_comm]
    exact hfirst
  have hboth : (∑ d : Dyad N, ∑ f : Dyad N,
      if i ∈ members d then (if i ∈ members f then (1 : ℝ) else 0) else 0) =
      ((N : ℝ) - 1)^2 := by
    calc
      _ = ∑ d : Dyad N, (if i ∈ members d then 1 else 0) *
          (∑ f : Dyad N, if i ∈ members f then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> simp
      _ = _ := by rw [population_meat_incident_count, ← Finset.sum_mul,
                       population_meat_incident_count, pow_two]
  rw [Fintype.sum_prod_type]
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hfirst, hsecond, hboth]
  ring

lemma population_meat_pair_dependency_count {N : ℕ} (hN : 2 ≤ N) :
    (∑ P : Dyad N × Dyad N, ((univ.filter (fun Q : Dyad N × Dyad N =>
      (WeightedConsistency.pairSupport P ∩ WeightedConsistency.pairSupport Q).Nonempty)).card : ℝ)) ≤
      (Dreal N * (2 * (N : ℝ) - 3)) *
        (3 * ((N : ℝ) - 1) * (3 * (N : ℝ) - 5)) := by
  classical
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnon : 0 ≤ ((N : ℝ) - 1) * (3 * (N : ℝ) - 5) :=
    mul_nonneg (by linarith) (by linarith)
  have hrow (P : Dyad N × Dyad N) :
      (∑ Q : Dyad N × Dyad N,
        if (WeightedConsistency.pairSupport P ∩ WeightedConsistency.pairSupport Q).Nonempty
          then (1 : ℝ) else 0) ≤
      if overlap P.1 P.2 then 3 * (((N : ℝ) - 1) * (3 * (N : ℝ) - 5)) else 0 := by
    by_cases hP : overlap P.1 P.2
    · rw [if_pos hP]
      calc
        _ ≤ (WeightedConsistency.pairSupport P).card *
            (((N : ℝ) - 1) * (3 * (N : ℝ) - 5)) :=
          WeightedConsistency.support_overlap_row_bound WeightedConsistency.pairSupport
            (WeightedConsistency.pairSupport P) _
            (fun x _ => le_of_eq (population_meat_pair_through_unit hN x))
        _ ≤ 3 * (((N : ℝ) - 1) * (3 * (N : ℝ) - 5)) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast WeightedConsistency.pairSupport_card_le P) hnon
    · simp [WeightedConsistency.pairSupport, hP]
  have hsum := Finset.sum_le_sum (s := univ) (fun P _ => hrow P)
  have hrhs : (∑ P : Dyad N × Dyad N,
      if overlap P.1 P.2 then 3 * (((N : ℝ) - 1) * (3 * (N : ℝ) - 5)) else 0) =
      (3 * (((N : ℝ) - 1) * (3 * (N : ℝ) - 5))) *
        (Dreal N * (2 * (N : ℝ) - 3)) := by
    rw [← population_meat_overlap_total hN, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    split_ifs <;> simp
  rw [hrhs] at hsum
  convert hsum using 1
  · simp only [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
  · ring

lemma population_meat_coordinate_bound {k : ℕ} (x : Vec k) (C : ℝ) (hC : 0 ≤ C)
    (hx : euclideanSq x ≤ C^2) (a : Fin k) : |x a| ≤ C := by
  apply (sq_le_sq₀ (abs_nonneg _) hC).mp
  rw [sq_abs]
  exact (Finset.single_le_sum (fun b _ => sq_nonneg (x b)) (mem_univ a)).trans hx

lemma population_meat_sample_bounds {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] (CX Ce : ℝ) (hCX : 0 ≤ CX)
    (hX : ∀ᵐ uv ∂ K.μ.prod K.μ, euclideanSq (K.X uv.1 uv.2) ≤ CX^2)
    (he : ∀ᵐ uv ∂ K.μ.prod K.μ, |populationResidual K uv.1 uv.2| ≤ Ce)
    (d : Dyad N) :
    ∀ᵐ ω ∂unitSampleLaw K N, (∀ a, |design K ω d a| ≤ CX) ∧ |epsilon K ω d| ≤ Ce := by
  have hall : ∀ᵐ uv ∂K.μ.prod K.μ,
      (∀ a, |K.X uv.1 uv.2 a| ≤ CX) ∧ |populationResidual K uv.1 uv.2| ≤ Ce := by
    filter_upwards [hX, he] with uv hx he
    exact ⟨fun a => population_meat_coordinate_bound _ _ hCX hx a, he⟩
  rw [← (corrected_pair_preserving K d).map_eq] at hall
  exact ae_of_ae_map (corrected_pair_preserving K d).measurable.aemeasurable hall

theorem population_meat_variance_bounds_proof {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) (CX Ce : ℝ)
    (hCX : 0 ≤ CX) (hCe : 0 ≤ Ce)
    (hX : ∀ᵐ uv ∂ K.μ.prod K.μ, euclideanSq (K.X uv.1 uv.2) ≤ CX^2)
    (he : ∀ᵐ uv ∂ K.μ.prod K.μ, |populationResidual K uv.1 uv.2| ≤ Ce) :
    (∀ a b, ProbabilityTheory.variance (fun ω =>
      (((Dreal N)⁻¹ • sampleGram (design K ω)) a b)) (unitSampleLaw K N) ≤
        2*CX^4*(2*(N : ℝ)-3)/Dreal N) ∧
    (∀ a b, ProbabilityTheory.variance (fun ω => scaledMeat K (epsilon K) ω a b)
      (unitSampleLaw K N) ≤ (N : ℝ)^2/(Dreal N)^4 *
        (2*(CX^2*Ce^2)^2)*(Dreal N*(2*(N : ℝ)-3)) *
          (3*((N : ℝ)-1)*(3*(N : ℝ)-5))) := by
  classical
  letI population_meat_unitProbability : IsProbabilityMeasure K.μ := hK.1
  letI population_meat_sampleProbability : IsProbabilityMeasure (unitSampleLaw K N) := by
    unfold unitSampleLaw
    infer_instance
  have hD : Dreal N ≠ 0 := (printed_Dpos hN).ne'
  have hb := population_meat_sample_bounds (N := N) K CX Ce hCX hX he
  have hXm (d : Dyad N) : Measurable (fun ω : Fin N → U => design K ω d) := by
    have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    simpa only [Function.comp_def, design] using hK.2.1.comp hp
  have hYm (d : Dyad N) : Measurable (fun ω : Fin N → U => response K ω d) := by
    have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    simpa only [Function.comp_def, response] using hK.2.2.1.comp hp
  have hem (d : Dyad N) : Measurable (fun ω : Fin N → U => epsilon K ω d) := by
    change Measurable (fun ω => response K ω d - dot (design K ω d) (populationBeta K))
    simp only [dot]
    fun_prop
  have hsm (d : Dyad N) (a : Fin k) :
      Measurable (fun ω : Fin N → U => score (design K ω d) (epsilon K ω d) a) :=
    (hem d).mul ((measurable_pi_apply a).comp (hXm d))
  have hsb (d : Dyad N) (a : Fin k) :
      ∀ᵐ ω ∂unitSampleLaw K N, |score (design K ω d) (epsilon K ω d) a| ≤ Ce * CX := by
    filter_upwards [hb d] with ω hω
    change |epsilon K ω d * design K ω d a| ≤ _
    rw [abs_mul]
    exact mul_le_mul hω.2 (hω.1 a) (abs_nonneg _) hCe
  have hcount : (∑ d : Dyad N, ((univ.filter (fun f : Dyad N =>
      (members d ∩ members f).Nonempty)).card : ℝ)) = Dreal N * (2 * (N : ℝ) - 3) := by
    convert population_meat_overlap_total hN using 1
    simp only [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rfl
  constructor
  · intro a b
    let Z : Dyad N → (Fin N → U) → ℝ := fun d ω => design K ω d a * design K ω d b
    have hZm (d : Dyad N) : Measurable (Z d) :=
      ((measurable_pi_apply a).comp (hXm d)).mul ((measurable_pi_apply b).comp (hXm d))
    have hZs (d : Dyad N) (ω ω' : Fin N → U)
        (h : ∀ i ∈ members d, ω i = ω' i) : Z d ω = Z d ω' := by
      simp only [Z, design, h _ (WeightedConsistency.firstUnit_mem d),
        h _ (WeightedConsistency.secondUnit_mem d)]
    have hZb (d : Dyad N) : ∀ᵐ ω ∂unitSampleLaw K N, |Z d ω| ≤ CX^2 := by
      filter_upwards [hb d] with ω hω
      dsimp [Z]
      rw [abs_mul, pow_two]
      exact mul_le_mul (hω.1 a) (hω.1 b) (abs_nonneg _) hCX
    have hv := WeightedConsistency.g3_proof K.μ members Z (CX^2) hZm hZs hZb
    rw [hcount] at hv
    have hentry (ω : Fin N → U) :
        ((Dreal N)⁻¹ • sampleGram (design K ω)) a b = (Dreal N)⁻¹ * ∑ d, Z d ω := by
      simp only [sampleGram, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, outer, Z]
    simp_rw [hentry]
    rw [variance_const_mul]
    calc
      _ ≤ ((Dreal N)⁻¹)^2 * (2 * (CX^2)^2 * (Dreal N * (2 * (N : ℝ) - 3))) :=
        mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ = _ := by field_simp [hD] <;> ring
  · intro a b
    let Z : (Dyad N × Dyad N) → (Fin N → U) → ℝ := fun P ω =>
      if overlap P.1 P.2 then score (design K ω P.1) (epsilon K ω P.1) a *
        score (design K ω P.2) (epsilon K ω P.2) b else 0
    have hZm (P : Dyad N × Dyad N) : Measurable (Z P) := by
      dsimp [Z]
      split_ifs
      · exact (hsm P.1 a).mul (hsm P.2 b)
      · exact measurable_const
    have hZs (P : Dyad N × Dyad N) (ω ω' : Fin N → U)
        (h : ∀ i ∈ WeightedConsistency.pairSupport P, ω i = ω' i) : Z P ω = Z P ω' := by
      dsimp [Z]
      split_ifs with hP
      · have hd : ∀ i ∈ members P.1, ω i = ω' i :=
          fun i hi => h i (by simp [WeightedConsistency.pairSupport, hP, hi])
        have hf : ∀ i ∈ members P.2, ω i = ω' i :=
          fun i hi => h i (by simp [WeightedConsistency.pairSupport, hP, hi])
        simp only [score, design, epsilon, hd _ (WeightedConsistency.firstUnit_mem P.1),
          hd _ (WeightedConsistency.secondUnit_mem P.1), hf _ (WeightedConsistency.firstUnit_mem P.2),
          hf _ (WeightedConsistency.secondUnit_mem P.2)]
      · rfl
    have hZb (P : Dyad N × Dyad N) :
        ∀ᵐ ω ∂unitSampleLaw K N, |Z P ω| ≤ CX^2 * Ce^2 := by
      filter_upwards [hsb P.1 a, hsb P.2 b] with ω hd hf
      dsimp [Z]
      split_ifs
      · rw [abs_mul]
        calc
          _ ≤ (Ce * CX) * (Ce * CX) :=
            mul_le_mul hd hf (abs_nonneg _) (mul_nonneg hCe hCX)
          _ = _ := by ring
      · simp [mul_nonneg (sq_nonneg CX) (sq_nonneg Ce)]
    have hv := WeightedConsistency.g3_proof K.μ WeightedConsistency.pairSupport
      Z (CX^2 * Ce^2) hZm hZs hZb
    have hdep := population_meat_pair_dependency_count hN
    have hentry (ω : Fin N → U) :
        scaledMeat K (epsilon K) ω a b = ((N : ℝ) / (Dreal N)^2) * ∑ P, Z P ω := by
      simp only [scaledMeat, meat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Fintype.sum_prod_type, Z, overlap, matrix_ite_apply, outer, Matrix.zero_apply]
      rfl
    simp_rw [hentry]
    rw [variance_const_mul]
    calc
      _ ≤ ((N : ℝ) / (Dreal N)^2)^2 *
          (2 * (CX^2 * Ce^2)^2 * ((Dreal N * (2 * (N : ℝ) - 3)) *
            (3 * ((N : ℝ) - 1) * (3 * (N : ℝ) - 5)))) :=
        mul_le_mul_of_nonneg_left
          (hv.trans (mul_le_mul_of_nonneg_left hdep (by positivity))) (sq_nonneg _)
      _ = _ := by ring

/-! Specialization of common-directed-kernel consistency to single records
and unit weights, using positive definiteness of the population Gram and
eventual equality with the unconditional target under `Standing`.
-/

theorem variance_consistency_corrected_proof {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N) := by
  exact GP0182B2b_variance_consistency K hK

end AronowAudit.P018.Wave1
