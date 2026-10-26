import AronowAudit.P011.P011_OracleCompletion
import AronowAudit.P011.P011_SpectralCompletion


namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open Causalean.Mathlib.Probability.SteinMethod
open scoped BigOperators Topology Classical Matrix NNReal ENNReal ProbabilityTheory
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

local instance : ENNReal.HolderTriple (4 : ENNReal) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

/-! Deterministically shifted weighted coordinates. These need no mean model. -/
def msr_shift {n : ℕ} (m : Model n) (a : Fin n → ℝ) (i : Fin n)
    (y : Fin n → ℝ) : ℝ := weighted m y i - a i

def msr_Q {n : ℕ} (m : Model n) (a : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  quadratic (oracleMatrix m.G) (fun i => msr_shift m a i y)

lemma msr_shift_measurable {n : ℕ} (m : Model n) (a : Fin n → ℝ) (i : Fin n) :
    Measurable (msr_shift m a i) :=
  (ProbabilityCompletion.weighted_measurable m i).sub measurable_const

lemma msr_shift_memLp {n : ℕ} (m : Model n) (a : Fin n → ℝ) (B : ℝ)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |msr_shift m a i y| ≤ B)
    (q : ENNReal) (i : Fin n) : MemLp (msr_shift m a i) q m.law := by
  let : IsProbabilityMeasure m.law := m.probability
  exact MemLp.of_bound (msr_shift_measurable m a i).aestronglyMeasurable B
    (hb.mono fun y hy => by simpa only [Real.norm_eq_abs] using hy i)

lemma msr_shift_mean {n : ℕ} (m : Model n) (a : Fin n → ℝ)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (i : Fin n) :
    expectation m (msr_shift m a i) = expectation m (fun y => weighted m y i) - a i := by
  let : IsProbabilityMeasure m.law := m.probability
  unfold expectation msr_shift
  rw [integral_sub ((hL2 i).integrable (by norm_num)) (integrable_const _)]
  simp

lemma msr_shift_pair {n : ℕ} (m : Model n) (a : Fin n → ℝ)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (i j : Fin n) :
    expectation m (fun y => msr_shift m a i y * msr_shift m a j y) =
      covariance m i j +
        (expectation m (fun y => weighted m y i) - a i) *
        (expectation m (fun y => weighted m y j) - a j) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hz (i : Fin n) : MemLp (msr_shift m a i) 2 m.law := by
    exact (hL2 i).sub (memLp_const (a i))
  have hc : cov[msr_shift m a i, msr_shift m a j; m.law] = covariance m i j := by
    unfold msr_shift
    rw [ProbabilityTheory.covariance_sub_const_left ((hL2 i).integrable (by norm_num)),
      ProbabilityTheory.covariance_sub_const_right ((hL2 j).integrable (by norm_num))]
    rfl
  have hp := ProbabilityTheory.covariance_eq_sub (hz i) (hz j)
  change cov[msr_shift m a i, msr_shift m a j; m.law] =
    expectation m (fun y => msr_shift m a i y * msr_shift m a j y) -
    expectation m (msr_shift m a i) * expectation m (msr_shift m a j) at hp
  rw [hc, msr_shift_mean m a hL2, msr_shift_mean m a hL2] at hp
  linarith

lemma msr_Q_expectation {n : ℕ} (m : Model n) (a : Fin n → ℝ)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    expectation m (msr_Q m a) = Matrix.trace (oracleMatrix m.G * covariance m) +
      quadratic (oracleMatrix m.G)
        (fun i => expectation m (fun y => weighted m y i) - a i) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hz (i : Fin n) : MemLp (msr_shift m a i) 2 m.law :=
    (hL2 i).sub (memLp_const _)
  have hi (i j : Fin n) : Integrable
      (fun y => oracleMatrix m.G i j * msr_shift m a i y * msr_shift m a j y) m.law := by
    exact ((hz i).integrable_mul (hz j) |>.const_mul _).congr
      (Eventually.of_forall fun y => by dsimp only [Pi.mul_apply]; ring)
  have ho (i : Fin n) : Integrable
      (fun y => ∑ j, oracleMatrix m.G i j * msr_shift m a i y * msr_shift m a j y) m.law :=
    integrable_finsetSum Finset.univ (fun j _ => hi i j)
  calc
    _ = ∑ i, ∑ j, ∫ y,
        oracleMatrix m.G i j * msr_shift m a i y * msr_shift m a j y ∂m.law := by
      unfold expectation msr_Q quadratic
      rw [integral_finsetSum Finset.univ (fun i _ => ho i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    _ = ∑ i, ∑ j, oracleMatrix m.G i j * (covariance m i j +
        (expectation m (fun y => weighted m y i) - a i) *
        (expectation m (fun y => weighted m y j) - a j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = oracleMatrix m.G i j *
            expectation m (fun y => msr_shift m a i y * msr_shift m a j y) := by
          simpa only [mul_assoc, expectation] using
            integral_const_mul (oracleMatrix m.G i j)
              (fun y => msr_shift m a i y * msr_shift m a j y)
        _ = _ := by rw [msr_shift_pair m a hL2]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc]
      rw [← QuadraticCompletion.trace_prod_symm _ _ (QuadraticCompletion.covariance_symm m)]
      rfl

lemma msr_normalized_expectation {n : ℕ} (hn : 0 < n) (m : Model n)
    (a : Fin n → ℝ) (hd : Dependency m)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    expectation m (fun y => msr_Q m a y / (n : ℝ)) =
      (n : ℝ) * var m (betaHat m) + quadratic (oracleMatrix m.G)
        (fun i => expectation m (fun y => weighted m y i) - a i) / (n : ℝ) := by
  rw [expectation, integral_div]
  change expectation m (msr_Q m a) / (n : ℝ) = _
  rw [msr_Q_expectation m a hL2, OracleCompletion.oracle_trace m hd hL2,
    QuadraticCompletion.beta_variance m hL2]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0]
  <;> ring

/-- The full tuple dependency graph survives arbitrary deterministic coordinate shifts. -/
def msr_dep {n : ℕ} (m : Model n) (hd : Dependency m) (a : Fin n → ℝ) :
    DepGraph (msr_shift m a) m.law := by
  classical
  let : IsProbabilityMeasure m.law := m.probability
  exact {
    G := fun i j => i = j ∨ m.G.val i j = true
    decG := inferInstance
    refl := fun i => Or.inl rfl
    symm := by
      intro i j hij
      rcases hij with hij | hij
      · exact Or.inl hij.symm
      · exact Or.inr ((m.G.property.1 j i).trans hij)
    meas := msr_shift_measurable m a
    indep := by
      intro S T hsep
      have hdis : Disjoint S T := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        exact hsep i hi i hj (Or.inl rfl)
      have hf : ∀ i ∈ S, ∀ j ∈ T, m.G.val i j = false := by
        intro i hi j hj
        cases he : m.G.val i j
        · rfl
        · exact False.elim (hsep i hi j hj (Or.inr he))
      simpa only [msr_shift, div_one] using
        ProbabilityCompletion.centred_dependency m hd a 1 S T hdis hf }

lemma msr_dep_degree {n : ℕ} (m : Model n) (hd : Dependency m)
    (a : Fin n → ℝ) (i : Fin n) :
    ((msr_dep m hd a).nbhd i).card = degree m.G i + 1 := by
  have he : (msr_dep m hd a).nbhd i = (ProbabilityCompletion.modelDep m hd).nbhd i := by
    ext j
    rw [DepGraph.mem_nbhd_iff, DepGraph.mem_nbhd_iff]
    rfl
  rw [he, ProbabilityCompletion.modelDep_degree]

lemma msr_Q_nbhd {n : ℕ} (m : Model n) (hd : Dependency m)
    (a : Fin n → ℝ) (y : Fin n → ℝ) :
    (∑ i, msr_shift m a i y * ∑ j ∈ (msr_dep m hd a).nbhd i, msr_shift m a j y) =
      msr_Q m a y := by
  classical
  have hs (i : Fin n) : (msr_dep m hd a).nbhd i =
      Finset.univ.filter (fun j => i = j ∨ m.G.val i j = true) := by
    ext j
    simp only [DepGraph.mem_nbhd_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  unfold msr_Q quadratic
  apply Finset.sum_congr rfl
  intro i _
  rw [hs, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [CliqueCompletion.oracle_apply]
  by_cases hij : i = j ∨ m.G.val i j = true <;> simp [hij] <;> ring

lemma msr_Q_memLp2 {n : ℕ} (m : Model n) (a : Fin n → ℝ) (B : ℝ)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |msr_shift m a i y| ≤ B) :
    MemLp (msr_Q m a) 2 m.law := by
  have hz := msr_shift_memLp m a B hb 4
  have ht (i j : Fin n) : MemLp
      (fun y => oracleMatrix m.G i j * msr_shift m a i y * msr_shift m a j y) 2 m.law := by
    have hp : MemLp (fun y => msr_shift m a i y * msr_shift m a j y) 2 m.law :=
      (hz i).mul (hz j)
    exact (memLp_congr_ae (Eventually.of_forall fun y => by ring)).mp (hp.const_mul _)
  have hi (i : Fin n) : MemLp
      (fun y => ∑ j, oracleMatrix m.G i j * msr_shift m a i y * msr_shift m a j y) 2 m.law :=
    by simpa using memLp_finsetSum Finset.univ (fun j _ => ht i j)
  unfold msr_Q quadratic
  exact memLp_finsetSum Finset.univ (fun i _ => hi i)

lemma msr_normalized_variance {n : ℕ} (hn : 0 < n) (m : Model n)
    (a : Fin n → ℝ) (hd : Dependency m) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |msr_shift m a i y| ≤ B)
    (d : ℕ) (hdeg : ∀ i, degree m.G i + 1 ≤ d) :
    ProbabilityTheory.variance (fun y => msr_Q m a y / (n : ℝ)) m.law ≤
      2 * (d : ℝ)^5 * B^4 / (n : ℝ) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hv := (msr_dep m hd a).var_nbhd_prod_le_ae hB
    (fun i => hb.mono fun y hy => hy i)
    (fun i => by rw [msr_dep_degree]; exact hdeg i)
  simp only [msr_Q_nbhd, Fintype.card_fin] at hv
  have he : (fun y => msr_Q m a y / (n : ℝ)) =
      fun y => (n : ℝ)⁻¹ * msr_Q m a y := by funext y; ring
  rw [he, ProbabilityTheory.variance_const_mul]
  calc
    _ ≤ ((n : ℝ)⁻¹)^2 * (2 * (d : ℝ)^5 * (n : ℝ) * B^4) :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp [hn0]
      <;> ring

lemma msr_quadratic_concentration (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (a : ∀ k, Fin (F.size k) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |msr_shift (F.model k) (a k) i y| ≤ B) :
    InProbability F (fun k y => msr_Q (F.model k) (a k) y / (F.size k : ℝ))
      (fun k => scaledTrue F k + quadratic (oracleMatrix (F.model k).G)
        (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i) - a k i) /
          (F.size k : ℝ)) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  rcases h with ⟨hNest, hc1, hc2, hc3, hc4, hDep, hBound, hDeg, hVar, hTheta⟩
  let d : ℕ := ⌈c2⌉₊ + 1
  have hdeg (k : ℕ) (i : Fin (F.size k)) : degree (F.model k).G i + 1 ≤ d := by
    dsimp [d]
    exact Nat.add_le_add_right
      (by exact_mod_cast (hDeg k i).trans (Nat.le_ceil c2)) 1
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    ProbabilityCompletion.weighted_memLp (F.model k) c1 (hBound k) i
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  have hQ2 (k : ℕ) : MemLp
      (fun y => msr_Q (F.model k) (a k) y / (F.size k : ℝ)) 2 (F.model k).law := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (msr_Q_memLp2 (F.model k) (a k) B (hb k)).const_mul ((F.size k : ℝ)⁻¹)
  have hv : Tendsto (fun k => ProbabilityTheory.variance
      (fun y => msr_Q (F.model k) (a k) y / (F.size k : ℝ)) (F.model k).law)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => ProbabilityTheory.variance_nonneg _ _)
      (fun k => msr_normalized_variance (F.positive k) (F.model k) (a k) (hDep k)
        B hB (hb k) d (hdeg k))
    exact hN.const_div_atTop _
  have hcp := OracleCompletion.rowCP_of_variance (fun k => (F.model k).law)
    (fun k y => msr_Q (F.model k) (a k) y / (F.size k : ℝ)) hQ2 hv
  have he (k : ℕ) : (∫ y, msr_Q (F.model k) (a k) y / (F.size k : ℝ)
      ∂(F.model k).law) = scaledTrue F k + quadratic (oracleMatrix (F.model k).G)
        (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i) - a k i) /
          (F.size k : ℝ) :=
    msr_normalized_expectation (F.positive k) (F.model k) (a k) (hDep k) (hL2 k)
  simpa only [InProbability, probability, he] using hcp

/-- Normalized perturbation; only the true graph degree is bounded. -/
lemma msr_prediction_bound {n : ℕ} (hn : 0 < n) (G : Graph n)
    (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hd : ∀ i, (degree G i : ℝ) ≤ c) (r z : Fin n → ℝ)
    (hz : ∀ i, |z i| ≤ B) :
    |(n : ℝ) * VResidual G r - quadratic (oracleMatrix G) z / (n : ℝ)| ≤
      (1 + c) * (l2 (r-z) / Real.sqrt (n : ℝ)) *
        (2 * B + l2 (r-z) / Real.sqrt (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hs2 : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := hs.ne'
  have hL : 0 ≤ l2 (r-z) := DenseCompletion.l2_nonneg _
  have hZ : 0 ≤ l2 z := DenseCompletion.l2_nonneg _
  have hop : operatorNorm (oracleMatrix G) ≤ 1 + c := by
    apply SpectralConfidence.operatorNorm_le_abs_row_sum _
      (SpectralConfidence.oracle_symmetric G) _ (by linarith)
    intro i
    simp_rw [abs_of_nonneg (OracleCompletion.oracle_nonneg G i _)]
    rw [OracleCompletion.oracle_row_sum]
    linarith [hd i]
  have hz2 : l2 z ≤ Real.sqrt (n : ℝ) * B := DenseCompletion.l2_abs_bound z B hB hz
  have he : (n : ℝ) * VResidual G r - quadratic (oracleMatrix G) z / (n : ℝ) =
      (quadratic (oracleMatrix G) r - quadratic (oracleMatrix G) z) / (n : ℝ) := by
    unfold VResidual
    field_simp [hn0]
    <;> ring
  rw [he, abs_div, abs_of_pos hnR]
  calc
    _ ≤ operatorNorm (oracleMatrix G) * l2 (r-z) * (2*l2 z+l2 (r-z)) / (n : ℝ) :=
      div_le_div_of_nonneg_right
        (residual_perturbation _ (SpectralConfidence.oracle_symmetric G) r z) hnR.le
    _ ≤ (1+c) * l2 (r-z) * (2*(Real.sqrt (n : ℝ)*B)+l2 (r-z)) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      exact mul_le_mul (mul_le_mul_of_nonneg_right hop hL)
        (by linarith [hz2]) (by positivity) (by positivity)
    _ = (1+c) * l2 (r-z) * (2*(Real.sqrt (n : ℝ)*B)+l2 (r-z)) /
        (Real.sqrt (n : ℝ))^2 := by rw [hs2]
    _ = _ := by
      field_simp [hs0]
      <;> ring

/-- Oracle prediction transfer, deliberately independent of Valid or a maximizer. -/
lemma msr_prediction_transfer (F : Family) (c : ℝ) (hc : 0 ≤ c)
    (hd : ∀ k i, (degree (F.model k).G i : ℝ) ≤ c)
    (r z : ∀ k, (Fin (F.size k) → ℝ) → (Fin (F.size k) → ℝ))
    (B : ℝ) (hB : 0 ≤ B)
    (hz : ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |z k y i| ≤ B)
    (herr : InProbability F (fun k y => l2 (r k y-z k y) / Real.sqrt (F.size k : ℝ))
      (fun _ => 0)) :
    CoverageCompletion.RowCP (fun k => (F.model k).law)
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G (r k y) -
        quadratic (oracleMatrix (F.model k).G) (z k y) / (F.size k : ℝ)) 0 := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let e := fun k y => l2 (r k y-z k y) / Real.sqrt (F.size k : ℝ)
  have he : CoverageCompletion.RowCP (fun k => (F.model k).law) e 0 := herr
  let f : ℝ × ℝ → ℝ := fun t => (1+c)*t.1*(2*B+t.1)
  have hpoly : CoverageCompletion.RowCP (fun k => (F.model k).law)
      (fun k y => (1+c)*e k y*(2*B+e k y)) 0 := by
    have hh := CoverageCompletion.rowCP_continuous_pair (fun k => (F.model k).law)
      e (fun _ _ => (0 : ℝ)) 0 0 he
      (CoverageCompletion.rowCP_det _ (fun _ => (0 : ℝ)) 0 tendsto_const_nhds)
      f (by dsimp [f]; fun_prop)
    simpa only [f, mul_zero, zero_mul] using hh
  apply OracleCompletion.rowCP_dominated _ _ _ hpoly
  intro k
  filter_upwards [hz k] with y hy
  exact msr_prediction_bound (F.positive k) (F.model k).G c B hc hB (hd k) _ _ hy

theorem misspecified_residual_limit_proof (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γstar : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γstar y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γstar y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0)) :
    InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)-scaledTrue F k)
      (fun k => quadratic (oracleMatrix (F.model k).G)
        (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i)
          -(F.model k).theta i*(D k *ᵥ γstar) i) / (F.size k : ℝ)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let a : ∀ k, Fin (F.size k) → ℝ :=
    fun k i => (F.model k).theta i * (D k *ᵥ γstar) i
  have hshift (k : ℕ) (y : Fin (F.size k) → ℝ) :
      (fun i => msr_shift (F.model k) (a k) i y) =
        trueResidual (F.model k) (D k) γstar y := by
    funext i
    dsimp [msr_shift, a, weighted, trueResidual]
    ring
  obtain ⟨B₀, hB₀⟩ := hz
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hzB (k : ℕ) : ∀ᵐ y ∂(F.model k).law,
      ∀ i, |trueResidual (F.model k) (D k) γstar y i| ≤ B :=
    (hB₀ k).mono fun y hy i => (hy i).trans (le_max_left _ _)
  have hb (k : ℕ) : ∀ᵐ y ∂(F.model k).law,
      ∀ i, |msr_shift (F.model k) (a k) i y| ≤ B := by
    filter_upwards [hzB k] with y hy
    simpa only [← hshift k y] using hy
  have hQ := msr_quadratic_concentration F c1 c2 c3 c4 h a B hB hb
  let b : ℕ → ℝ := fun k => quadratic (oracleMatrix (F.model k).G)
    (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i) - a k i) /
      (F.size k : ℝ)
  have hQ' : ∀ ε > (0 : ℝ), Tendsto (fun k => (F.model k).law.real
      {y | |quadratic (oracleMatrix (F.model k).G)
        (trueResidual (F.model k) (D k) γstar y) / (F.size k : ℝ) -
          (scaledTrue F k + b k)| > ε}) atTop (𝓝 0) := by
    simpa only [InProbability, probability, msr_Q, hshift, b] using hQ
  have hdeg : ∀ k i, (degree (F.model k).G i : ℝ) ≤ c2 := h.2.2.2.2.2.2.2.1
  have hE := msr_prediction_transfer F c2 (le_of_lt h.2.2.1) hdeg
    (fun k y => fittedResidual (F.model k) (D k) (γhat k) y)
    (fun k y => trueResidual (F.model k) (D k) γstar y) B hB hzB herr
  have hfit := OracleCompletion.row_moving_add_error (fun k => (F.model k).law)
    (fun k y => quadratic (oracleMatrix (F.model k).G)
      (trueResidual (F.model k) (D k) γstar y) / (F.size k : ℝ))
    (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y))
    (fun k => scaledTrue F k + b k) hQ' hE
  intro ε hε
  have hh := hfit ε hε
  change Tendsto (fun k => probability (F.model k) {y |
    |((F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y) - scaledTrue F k) - b k| > ε})
    atTop (𝓝 0)
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      ((F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y) - scaledTrue F k) - b k =
      (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y) - (scaledTrue F k + b k) := by ring
  simpa only [probability, he] using hh

/-! Correct specification eliminates the moving mean quadratic. -/
lemma rps_weighted_mean {n p : ℕ} (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ)
    (hm : MeanModel m D γ) (i : Fin n) :
    expectation m (fun y => weighted m y i) = m.theta i * (D *ᵥ γ) i := by
  unfold expectation weighted
  rw [integral_const_mul]
  change m.theta i * expectation m (fun y => y i) = _
  rw [hm.2 i]

lemma rps_true_eq {n p : ℕ} (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ)
    (hm : MeanModel m D γ) (y : Fin n → ℝ) (i : Fin n) :
    trueResidual m D γ y i =
      weighted m y i - expectation m (fun y => weighted m y i) := by
  rw [rps_weighted_mean m D γ hm]
  dsimp [trueResidual, weighted]
  ring

/-- This oracle component carries no feasibility or selection premises. -/
lemma rps_oracle (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law,
      ∀ i, |trueResidual (F.model k) (D k) γ y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y -
        trueResidual (F.model k) (D k) γ y) / Real.sqrt (F.size k : ℝ)) (fun _ => 0)) :
    InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) := by
  have hm := misspecified_residual_limit_proof F c1 c2 c3 c4 h p D γ γhat hmeas hz herr
  have hb (k : ℕ) (i : Fin (F.size k)) : expectation (F.model k)
      (fun y => weighted (F.model k) y i) - (F.model k).theta i*(D k *ᵥ γ) i = 0 := by
    rw [rps_weighted_mean (F.model k) (D k) γ (hmean k) i]
    simp
  intro ε hε
  have hh := hm ε hε
  simpa only [hb, quadratic, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_div, sub_zero] using hh

lemma rps_maximum_conservative (F : Family)
    (r : ∀ k, (Fin (F.size k) → ℝ) → (Fin (F.size k) → ℝ))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun G => VResidual G (r k y)) (A k y))
    (ho : InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G (r k y))
      (scaledTrue F)) : Conservative F (fun k y => VResidual (A k y) (r k y)) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  intro ε hε
  apply squeeze_zero (fun k => measureReal_nonneg) (fun k => ?_) (ho ε hε)
  apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
  intro y hy
  have hmax : VResidual (F.model k).G (r k y) ≤ VResidual (A k y) (r k y) :=
    (hm k y).2 (F.model k).G (hv k)
  have hn : 0 ≤ (F.size k : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hmax hn
  change ε < (F.size k : ℝ) *
    (var (F.model k) (betaHat (F.model k)) - VResidual (A k y) (r k y)) at hy
  change ε < |(F.size k : ℝ)*VResidual (F.model k).G (r k y) - scaledTrue F k|
  change ε < |(F.size k : ℝ)*VResidual (F.model k).G (r k y) -
    (F.size k : ℝ) * var (F.model k) (betaHat (F.model k))|
  have h2 : ε < (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) -
      (F.size k : ℝ)*VResidual (F.model k).G (r k y) := by nlinarith
  rw [abs_sub_comm]
  exact lt_of_lt_of_le h2 (le_abs_self _)

theorem residual_prediction_stability_proof (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γ y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)) :
    InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y) (fittedResidual (F.model k) (D k) (γhat k) y)) := by
  have ho := rps_oracle F c1 c2 c3 c4 h p D γ γhat hmeas hmean hz herr
  exact ⟨ho, rps_maximum_conservative F
    (fun k y => fittedResidual (F.model k) (D k) (γhat k) y) A hv hm ho⟩

/-! Norm and probability-tail helpers for root-n estimation. -/
lemma rrn_probability_mono_ae {n : ℕ} (m : Model n)
    (E H : Set (Fin n → ℝ)) (hEH : ∀ᵐ y ∂m.law, y ∈ E → y ∈ H) :
    probability m E ≤ probability m H := by
  let : IsProbabilityMeasure m.law := m.probability
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  exact measure_mono_ae hEH

lemma rrn_tight_dominated (F : Family)
    (S T : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hS : Tight F S)
    (hb : ∀ k, ∀ᵐ y ∂(F.model k).law, |T k y| ≤ C*|S k y|) : Tight F T := by
  intro ε hε
  obtain ⟨b, hbpos, k0, hk0⟩ := hS ε hε
  refine ⟨C*b+1, by positivity, k0, ?_⟩
  intro k hk
  apply le_trans (rrn_probability_mono_ae (F.model k) _ _ ?_) (hk0 k hk)
  filter_upwards [hb k] with y hy
  intro hbad
  change C*b+1 < |T k y| at hbad
  change b < |S k y|
  by_contra hnot
  have hsmall : |S k y| ≤ b := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hsmall hC
  linarith

lemma rrn_tight_ae_bound (F : Family)
    (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, ∀ᵐ y ∂(F.model k).law, |T k y| ≤ C) : Tight F T := by
  intro ε hε
  refine ⟨C+1, by linarith, 0, ?_⟩
  intro k hk
  have hp : probability (F.model k) {y | |T k y| > C+1} ≤
      probability (F.model k) ∅ := by
    apply rrn_probability_mono_ae
    filter_upwards [hb k] with y hy
    intro hbad
    change C+1 < |T k y| at hbad
    exact False.elim (by linarith)
  have hp0 : probability (F.model k) {y | |T k y| > C+1} ≤ 0 := by
    simpa only [probability, measureReal_empty] using hp
  exact hp0.trans hε.le

/-- Eventual Tightness on changing row spaces suffices for division by sqrt(n). -/
lemma rrn_tight_div_sqrt (F : Family)
    (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (ht : Tight F T) :
    InProbability F (fun k y => T k y / Real.sqrt (F.size k : ℝ)) (fun _ => 0) := by
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  have hs : Tendsto (fun k => Real.sqrt (F.size k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  intro δ hδ
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun k => lt_of_lt_of_le ha measureReal_nonneg
  · intro b hb
    obtain ⟨M, hM, k0, hk0⟩ := ht (b/2) (by linarith)
    have hlarge : ∀ᶠ k in atTop, M/δ < Real.sqrt (F.size k : ℝ) :=
      hs.eventually_gt_atTop (M/δ)
    filter_upwards [hlarge, eventually_ge_atTop k0] with k hlarge hk
    have hspos : 0 < Real.sqrt (F.size k : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast F.positive k)
    have hscale : M < δ*Real.sqrt (F.size k : ℝ) := by
      have hh := (div_lt_iff₀ hδ).mp hlarge
      nlinarith
    have hp : probability (F.model k)
        {y | |T k y / Real.sqrt (F.size k : ℝ) - 0| > δ} ≤
          probability (F.model k) {y | |T k y| > M} := by
      let : IsProbabilityMeasure (F.model k).law := (F.model k).probability
      apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
      intro y hy
      change δ < |T k y / Real.sqrt (F.size k : ℝ) - 0| at hy
      rw [sub_zero, abs_div, abs_of_pos hspos] at hy
      have hh := (lt_div_iff₀ hspos).mp hy
      change M < |T k y|
      exact hscale.trans hh
    have hp' := hp.trans (hk0 k hk)
    change probability (F.model k)
      {y | |T k y / Real.sqrt (F.size k : ℝ) - 0| > δ} < b
    linarith

lemma rrn_l2_div_bound {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i, |x i| ≤ B) :
    l2 x / Real.sqrt (n : ℝ) ≤ B := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_iff₀ hs).mpr
  simpa only [mul_comm] using DenseCompletion.l2_abs_bound x B hB hb

lemma rrn_maxAbs_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ maxAbs x := by
  unfold maxAbs
  exact NNReal.coe_nonneg _

lemma rrn_maxAbs_le {n : ℕ} (x : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ i, |x i| ≤ B) : maxAbs x ≤ B := by
  have hs : Finset.univ.sup (fun i => (⟨|x i|, abs_nonneg (x i)⟩ : ℝ≥0)) ≤
      (⟨B, hB⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i hi
    exact hb i
  exact hs

lemma rrn_dot_bound {p : ℕ} (x v : Fin p → ℝ) :
    |∑ j, x j*v j| ≤ l2 x*l2 v := by
  have hi : (∑ j, x j*v j) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 v) := by
    simp [EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]
  rw [hi, ← Real.norm_eq_abs]
  simpa only [DenseCompletion.l2_norm] using
    norm_inner_le_norm (WithLp.toLp 2 x) (WithLp.toLp 2 v)

lemma rrn_error_coordinate {n p : ℕ} (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : (Fin n → ℝ) → (Fin p → ℝ)) (c B : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (ht : ∀ i, |m.theta i| ≤ c)
    (hD : ∀ i, l2 (D i) ≤ B) (y : Fin n → ℝ) (i : Fin n) :
    |(fittedResidual m D γhat y - trueResidual m D γ y) i| ≤
      (c*B)*l2 (γhat y-γ) := by
  have he : (fittedResidual m D γhat y - trueResidual m D γ y) i =
      -(m.theta i * (D *ᵥ (γhat y-γ)) i) := by
    simp only [Pi.sub_apply, fittedResidual, trueResidual, Matrix.mulVec_sub]
    ring
  rw [he, abs_neg, abs_mul]
  have hdot : |(D *ᵥ (γhat y-γ)) i| ≤ l2 (D i)*l2 (γhat y-γ) :=
    rrn_dot_bound (D i) (γhat y-γ)
  calc
    _ ≤ c * (l2 (D i)*l2 (γhat y-γ)) :=
      mul_le_mul (ht i) hdot (abs_nonneg _) hc
    _ ≤ c * (B*l2 (γhat y-γ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hD i) (DenseCompletion.l2_nonneg _)) hc
    _ = _ := by ring

lemma rrn_error_norm_bounds {n p : ℕ} (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : (Fin n → ℝ) → (Fin p → ℝ)) (c B : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (ht : ∀ i, |m.theta i| ≤ c)
    (hD : ∀ i, l2 (D i) ≤ B) (y : Fin n → ℝ) :
    Real.sqrt (n : ℝ)*maxAbs (fittedResidual m D γhat y - trueResidual m D γ y) ≤
        (c*B)*(Real.sqrt (n : ℝ)*l2 (γhat y-γ)) ∧
    l2 (fittedResidual m D γhat y - trueResidual m D γ y) ≤
        (c*B)*(Real.sqrt (n : ℝ)*l2 (γhat y-γ)) := by
  have hcB : 0 ≤ (c*B)*l2 (γhat y-γ) :=
    mul_nonneg (mul_nonneg hc hB) (DenseCompletion.l2_nonneg _)
  have hcoord := rrn_error_coordinate m D γ γhat c B hc hB ht hD y
  constructor
  · calc
      _ ≤ Real.sqrt (n : ℝ)*((c*B)*l2 (γhat y-γ)) :=
        mul_le_mul_of_nonneg_left (rrn_maxAbs_le _ _ hcB hcoord) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ Real.sqrt (n : ℝ)*((c*B)*l2 (γhat y-γ)) :=
        DenseCompletion.l2_abs_bound _ _ hcB hcoord
      _ = _ := by ring

lemma rrn_residual_moments {n p : ℕ} (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ)
    (hm : MeanModel m D γ)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    (∀ i, expectation m (fun y => trueResidual m D γ y i) = 0) ∧
    (∀ i j, expectation m (fun y => trueResidual m D γ y i * trueResidual m D γ y j) =
      covariance m i j) := by
  let : IsProbabilityMeasure m.law := m.probability
  constructor
  · intro i
    simp_rw [rps_true_eq m D γ hm]
    unfold expectation
    rw [integral_sub ((hL2 i).integrable (by norm_num)) (integrable_const _)]
    simp [expectation]
  · intro i j
    simp_rw [rps_true_eq m D γ hm]
    rfl

theorem residual_root_n_proof (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hbound : ∃ B : ℝ, ∀ k i, l2 (D k i) ≤ B)
    (hrate : Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (γhat k y-γ)))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)) :
    (∀ k i, expectation (F.model k) (fun y => trueResidual (F.model k) (D k) γ y i) = 0) ∧
    (∀ k i j, expectation (F.model k) (fun y =>
      trueResidual (F.model k) (D k) γ y i*trueResidual (F.model k) (D k) γ y j) =
      covariance (F.model k) i j) ∧
    Tight F (fun k y => Real.sqrt (F.size k : ℝ)*maxAbs
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2 (trueResidual (F.model k) (D k) γ y)/Real.sqrt (F.size k : ℝ)) ∧
    InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y)
      (fittedResidual (F.model k) (D k) (γhat k) y)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hcopy := h
  obtain ⟨hNest, hc1, hc2, hc3, hc4, hDep, hBound, hDeg, hVar, hTheta⟩ := hcopy
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    ProbabilityCompletion.weighted_memLp (F.model k) c1 (hBound k) i
  have hmom (k : ℕ) := rrn_residual_moments (F.model k) (D k) γ (hmean k) (hL2 k)
  have hz (k : ℕ) : ∀ᵐ y ∂(F.model k).law,
      ∀ i, |trueResidual (F.model k) (D k) γ y i| ≤ 2*c1 := by
    have hb := ProbabilityCompletion.own_centred_bound (F.model k) c1 (hL2 k) (hBound k)
    simpa only [rps_true_eq (F.model k) (D k) γ (hmean k)] using hb
  obtain ⟨B₀, hB₀⟩ := hbound
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hD (k : ℕ) (i : Fin (F.size k)) : l2 (D k i) ≤ B :=
    (hB₀ k i).trans (le_max_left _ _)
  let S : ∀ k, (Fin (F.size k) → ℝ) → ℝ :=
    fun k y => Real.sqrt (F.size k : ℝ)*l2 (γhat k y-γ)
  let E : ∀ k, (Fin (F.size k) → ℝ) → (Fin (F.size k) → ℝ) :=
    fun k y => fittedResidual (F.model k) (D k) (γhat k) y -
      trueResidual (F.model k) (D k) γ y
  have hS : Tight F S := hrate
  have hSpos (k : ℕ) (y : Fin (F.size k) → ℝ) : 0 ≤ S k y :=
    mul_nonneg (Real.sqrt_nonneg _) (DenseCompletion.l2_nonneg _)
  have hfinite (k : ℕ) (y : Fin (F.size k) → ℝ) :
      Real.sqrt (F.size k : ℝ)*maxAbs (E k y) ≤ (c4*B)*S k y ∧
        l2 (E k y) ≤ (c4*B)*S k y :=
    rrn_error_norm_bounds (F.model k) (D k) γ (γhat k) c4 B hc4.le hB
      (fun i => (hTheta k i).le) (hD k) y
  have hmax : Tight F (fun k y => Real.sqrt (F.size k : ℝ)*maxAbs (E k y)) := by
    apply rrn_tight_dominated F S _ (c4*B) (mul_nonneg hc4.le hB) hS
    intro k
    exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (rrn_maxAbs_nonneg _)),
        abs_of_nonneg (hSpos k y)]
      exact (hfinite k y).1
  have hnorm : Tight F (fun k y => l2 (E k y)) := by
    apply rrn_tight_dominated F S _ (c4*B) (mul_nonneg hc4.le hB) hS
    intro k
    exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (DenseCompletion.l2_nonneg _), abs_of_nonneg (hSpos k y)]
      exact (hfinite k y).2
  have htrue : Tight F (fun k y =>
      l2 (trueResidual (F.model k) (D k) γ y) / Real.sqrt (F.size k : ℝ)) := by
    apply rrn_tight_ae_bound F _ (2*c1) (by positivity)
    intro k
    filter_upwards [hz k] with y hy
    rw [abs_of_nonneg (div_nonneg (DenseCompletion.l2_nonneg _) (Real.sqrt_nonneg _))]
    exact rrn_l2_div_bound (F.positive k) _ (2*c1) (by positivity) hy
  have herr : InProbability F (fun k y => l2 (E k y) / Real.sqrt (F.size k : ℝ))
      (fun _ => 0) := rrn_tight_div_sqrt F _ hnorm
  have hlast := residual_prediction_stability_proof F c1 c2 c3 c4 h p D γ γhat
    hmeas hmean ⟨2*c1, hz⟩ herr A hv hm
  exact ⟨(fun k i => (hmom k).1 i), (fun k i j => (hmom k).2 i j),
    hmax, hnorm, htrue, hlast.1, hlast.2⟩

end
end AronowAudit.P011.Wave1
