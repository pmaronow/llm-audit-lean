/- P011 T3(ii): finite expectation bound with exact constant 3(1+c2)^2*c1^2/n. The proof derives weighted covariance bounds and true-graph support without a common-mean premise. -/
import AronowAudit.P011.P011_OracleCompletion

namespace AronowAudit.P011.ExpectationCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open OracleCompletion
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma weighted_variance_le {n : ℕ} (m : Model n) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) (i : Fin n) :
    ProbabilityTheory.variance (fun y => weighted m y i) m.law ≤ c^2 := by
  let : IsProbabilityMeasure m.law := m.probability
  have hu : MemLp (OracleCompletion.U m i) 2 m.law := U_memLp m c hb 2 i
  have hs : (∫ y, OracleCompletion.U m i y^2 ∂m.law) ≤ c^2 := by
    calc
      _ ≤ ∫ _, c^2 ∂m.law := integral_mono_ae hu.integrable_sq (integrable_const _) (by
        filter_upwards [hb] with y hy
        have hi := hy i
        change |OracleCompletion.U m i y| ≤ c at hi
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (OracleCompletion.U m i y)) hc).mpr hi)
      _ = _ := by simp
  have hv := ProbabilityTheory.variance_eq_sub hu
  have he : ProbabilityTheory.variance (OracleCompletion.U m i) m.law =
      ProbabilityTheory.variance (fun y => weighted m y i) m.law := by
    exact ProbabilityTheory.variance_sub_const
      (ProbabilityCompletion.weighted_measurable m i).aestronglyMeasurable (beta m)
  rw [he] at hv
  simp only [Pi.pow_apply] at hv
  linarith [sq_nonneg (∫ y, OracleCompletion.U m i y ∂m.law)]

lemma covariance_abs_le {n : ℕ} (m : Model n) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) (i j : Fin n) :
    |covariance m i j| ≤ c^2 := by
  let : IsProbabilityMeasure m.law := m.probability
  have hL2 := ProbabilityCompletion.weighted_memLp m c hb
  have hi := weighted_variance_le m c hc hb i
  have hj := weighted_variance_le m c hc hb j
  have hp := ProbabilityTheory.variance_nonneg (fun y => weighted m y i+weighted m y j) m.law
  have hn := ProbabilityTheory.variance_nonneg (fun y => weighted m y i-weighted m y j) m.law
  rw [ProbabilityTheory.variance_fun_add (hL2 i) (hL2 j)] at hp
  rw [ProbabilityTheory.variance_fun_sub (hL2 i) (hL2 j)] at hn
  rw [QuadraticCompletion.covariance_eq_mathlib]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma row_covariance_bound {n : ℕ} (m : Model n) (c D : ℝ) (hc : 0 ≤ c)
    (hdep : Dependency m) (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c)
    (hD : ∀ i, (degree m.G i:ℝ)+1 ≤ D) (i : Fin n) :
    |∑ j, covariance m i j| ≤ D*c^2 := by
  classical
  have hL2 := ProbabilityCompletion.weighted_memLp m c hb
  have ht (j : Fin n) : |covariance m i j| ≤ oracleMatrix m.G i j*c^2 := by
    rw [CliqueCompletion.oracle_apply]
    by_cases h : i=j ∨ m.G.val i j=true
    · simpa only [if_pos h,one_mul] using covariance_abs_le m c hc hb i j
    · have hij : i≠j := fun he => h (Or.inl he)
      have hg : m.G.val i j=false := by cases he : m.G.val i j <;> simp_all
      rw [if_neg h,covariance_support m hdep hL2 i j hij hg]
      simp
  calc
    _ ≤ ∑ j, |covariance m i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, oracleMatrix m.G i j*c^2 := Finset.sum_le_sum (fun j _ => ht j)
    _ = ((degree m.G i:ℝ)+1)*c^2 := by rw [←Finset.sum_mul,oracle_row_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _)

lemma total_covariance_bound {n : ℕ} (m : Model n) (c D : ℝ) (hc : 0 ≤ c)
    (hdep : Dependency m) (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c)
    (hD : ∀ i, (degree m.G i:ℝ)+1 ≤ D) :
    |QuadraticCompletion.total (covariance m)| ≤ (n:ℝ)*D*c^2 := by
  calc
    _ ≤ ∑ i, |∑ j, covariance m i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, D*c^2 := Finset.sum_le_sum (fun i _ => row_covariance_bound m c D hc hdep hb hD i)
    _ = _ := by simp;ring

lemma total_product_bound {n : ℕ} (m : Model n) (c D : ℝ) (hc : 0 ≤ c) (hD0 : 0 ≤ D)
    (hdep : Dependency m) (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c)
    (hD : ∀ i, (degree m.G i:ℝ)+1 ≤ D) :
    |QuadraticCompletion.total (oracleMatrix m.G*covariance m)| ≤ (n:ℝ)*D^2*c^2 := by
  rw [←QuadraticCompletion.row_total_right]
  calc
    _ ≤ ∑ i, |∑ j, oracleMatrix m.G i j*(∑ k, covariance m j k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, D^2*c^2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j, |oracleMatrix m.G i j*(∑ k, covariance m j k)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, oracleMatrix m.G i j*|∑ k, covariance m j k| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul,abs_of_nonneg (oracle_nonneg m.G i j)]
        _ ≤ ∑ j, oracleMatrix m.G i j*(D*c^2) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (row_covariance_bound m c D hc hdep hb hD j)
            (oracle_nonneg m.G i j)
        _ = ((degree m.G i:ℝ)+1)*(D*c^2) := by rw [←Finset.sum_mul,oracle_row_sum]
        _ ≤ D*(D*c^2) := mul_le_mul_of_nonneg_right (hD i) (by positivity)
        _ = _ := by ring
    _ = _ := by simp;ring

lemma beta_variance_bound {n : ℕ} (hn : 0<n) (m : Model n) (c D : ℝ) (hc : 0 ≤ c)
    (hdep : Dependency m) (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c)
    (hD : ∀ i, (degree m.G i:ℝ)+1 ≤ D) : var m (betaHat m) ≤ D*c^2/(n:ℝ) := by
  rw [QuadraticCompletion.beta_variance _ (ProbabilityCompletion.weighted_memLp m c hb)]
  calc
    _ ≤ ((n:ℝ)*D*c^2)/(n:ℝ)^2 := div_le_div_of_nonneg_right
      ((le_abs_self _).trans (total_covariance_bound m c D hc hdep hb hD)) (sq_nonneg _)
    _ = _ := by
      have hn0 : (n:ℝ)≠0 := by positivity
      field_simp <;> ring

lemma oracle_symmetric {n : ℕ} (G : Graph n) (i j : Fin n) : oracleMatrix G i j=oracleMatrix G j i := by
  simp only [oracleMatrix,Matrix.add_apply,Matrix.one_apply,adjacency]
  rw [G.property.1 i j]
  simp only [eq_comm]

lemma oracle_expectation_error {n : ℕ} (hn : 0<n) (m : Model n)
    (hdep : Dependency m) (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) :
    expectation m (fun y => (n:ℝ)*V1 m.G (weighted m y))-
      (n:ℝ)*var m (betaHat m)-meanBias m =
      -(2/(n:ℝ)^2)*QuadraticCompletion.total (oracleMatrix m.G*covariance m)+
        (QuadraticCompletion.total (oracleMatrix m.G)/(n:ℝ))*var m (betaHat m) := by
  have hn0 : (n:ℝ)≠0 := by positivity
  have he : (fun y => (n:ℝ)*V1 m.G (weighted m y))=
      fun y => quadratic (oracleMatrix m.G) (centered (weighted m y))/(n:ℝ) := by
    funext y
    rw [←variance_form_oracle,varianceForm]
    field_simp <;> ring
  have hq := (quadratic_expectation hn m hL2 (oracleMatrix m.G) (oracle_symmetric m.G)).2
  have hones : quadratic (oracleMatrix m.G) (fun _ => 1)=QuadraticCompletion.total (oracleMatrix m.G) :=
    by simp [quadratic,QuadraticCompletion.total]
  rw [he,expectation,integral_div]
  change expectation m (fun y => quadratic (oracleMatrix m.G) (centered (weighted m y)))/(n:ℝ)-
    (n:ℝ)*var m (betaHat m)-meanBias m=_
  rw [hq,oracle_trace m hdep hL2,hones,QuadraticCompletion.beta_variance m hL2]
  unfold meanBias QuadraticCompletion.total
  field_simp <;> ring

lemma finite_oracle_expectation_bound {n : ℕ} (hn : 0<n) (m : Model n) (c D : ℝ)
    (hc : 0 ≤ c) (hD0 : 0 ≤ D) (hdep : Dependency m)
    (hb : ∀ᵐ y ∂m.law,∀ i,|weighted m y i-beta m| ≤ c)
    (hD : ∀ i,(degree m.G i:ℝ)+1 ≤ D) :
    |expectation m (fun y => (n:ℝ)*V1 m.G (weighted m y))-
      (n:ℝ)*var m (betaHat m)-meanBias m| ≤ 3*D^2*c^2/(n:ℝ) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hnR : 0<(n:ℝ) := by positivity
  have hn0 : (n:ℝ)≠0 := ne_of_gt hnR
  have ht0 : 0≤QuadraticCompletion.total (oracleMatrix m.G) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => oracle_nonneg m.G i j))
  have hv0 : 0≤var m (betaHat m) := integral_nonneg (fun y => sq_nonneg _)
  have htotal := oracle_total_bound m.G D hD
  have hvar := beta_variance_bound hn m c D hc hdep hb hD
  rw [oracle_expectation_error hn m hdep (ProbabilityCompletion.weighted_memLp m c hb)]
  calc
    _ ≤ |-(2/(n:ℝ)^2)*QuadraticCompletion.total (oracleMatrix m.G*covariance m)| +
        |(QuadraticCompletion.total (oracleMatrix m.G)/(n:ℝ))*var m (betaHat m)| := abs_add_le _ _
    _ = (2/(n:ℝ)^2)*|QuadraticCompletion.total (oracleMatrix m.G*covariance m)| +
        (QuadraticCompletion.total (oracleMatrix m.G)/(n:ℝ))*var m (betaHat m) := by
      rw [abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤(2/(n:ℝ)^2)),
        abs_of_nonneg (mul_nonneg (div_nonneg ht0 hnR.le) hv0)]
    _ ≤ (2/(n:ℝ)^2)*((n:ℝ)*D^2*c^2)+D*(D*c^2/(n:ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (total_product_bound m c D hc hD0 hdep hb hD) (by positivity)
      · apply mul_le_mul (by apply (div_le_iff₀ hnR).mpr;simpa only [QuadraticCompletion.total,mul_comm] using htotal) hvar hv0 hD0
    _ = _ := by field_simp <;> ring

lemma revised_oracle_expectation_completed (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (k : ℕ) :
    |expectation (F.model k) (scaledOracle F k) - scaledTrue F k - meanBias (F.model k)|
      ≤ 3*(1+c2)^2*c1^2/(F.size k : ℝ) := by
  rcases h with ⟨hNested,hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  exact finite_oracle_expectation_bound (F.positive k) (F.model k) c1 (1+c2) hc1.le
    (by linarith) (hDep k) (hBound k) (fun i => by linarith [hDeg k i])

end
end AronowAudit.P011.ExpectationCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem revised_oracle_expectation (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (k : ℕ) :
    |expectation (F.model k) (scaledOracle F k) - scaledTrue F k - meanBias (F.model k)|
      ≤ 3*(1+c2)^2*c1^2/(F.size k : ℝ) := by
  exact ExpectationCompletion.revised_oracle_expectation_completed F c1 c2 c3 c4 h k
end AronowAudit.P011

