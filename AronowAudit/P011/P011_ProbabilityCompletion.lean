/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
 P011 T38: dependency-graph central limit theorem.
This file applies the dependency CLT imported from CausalSmith;
see NOTICE at the repository root. -/
import AronowAudit.P011.P011_FiniteCompletion
import AronowAudit.External.Causalean.Mathlib.Probability.SteinMethod.AlmostEverywhereDepGraphCLT

namespace AronowAudit.P011.ProbabilityCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
noncomputable section
attribute [-simp] Finset.sum_boole
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

lemma weighted_measurable {n : ℕ} (m : Model n) (i : Fin n) :
    Measurable (fun y => weighted m y i) := by
  exact measurable_const.mul (measurable_pi_apply i)

lemma betaHat_measurable {n : ℕ} (m : Model n) : Measurable (betaHat m) := by
  unfold betaHat average
  exact (Finset.measurable_sum Finset.univ fun i _ => weighted_measurable m i).div_const _

lemma weighted_memLp {n : ℕ} (m : Model n) (c : ℝ)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) (i : Fin n) :
    MemLp (fun y => weighted m y i) 2 m.law := by
  let : IsProbabilityMeasure m.law := m.probability
  apply MemLp.of_bound (weighted_measurable m i).aestronglyMeasurable (c+|beta m|)
  filter_upwards [hb] with y hy
  simpa only [Real.norm_eq_abs] using
    (calc |weighted m y i| = |(weighted m y i-beta m)+beta m| := by ring_nf
          _ ≤ |weighted m y i-beta m|+|beta m| := abs_add_le _ _
          _ ≤ c+|beta m| := by linarith [hy i])

lemma betaHat_memLp {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    MemLp (betaHat m) 2 m.law := by
  have hsum : MemLp (fun y => ∑ i, weighted m y i) 2 m.law :=
    by simpa using memLp_finsetSum Finset.univ (fun i _ => hL2 i)
  change MemLp (fun y => (∑ i, weighted m y i)/(n:ℝ)) 2 m.law
  simpa only [div_eq_mul_inv, mul_comm] using hsum.const_mul (n:ℝ)⁻¹

lemma own_mean_bound {n : ℕ} (m : Model n) (c : ℝ)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) (i : Fin n) :
    |expectation m (fun y => weighted m y i)-beta m| ≤ c := by
  let : IsProbabilityMeasure m.law := m.probability
  have hi := (hL2 i).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hdiff : Integrable (fun y => weighted m y i-beta m) m.law :=
    hi.sub (integrable_const _)
  have hid : expectation m (fun y => weighted m y i)-beta m =
      ∫ y, (weighted m y i-beta m) ∂m.law := by
    rw [integral_sub hi (integrable_const _)]
    simp [expectation]
  rw [hid]
  calc
    _ ≤ ∫ y, |weighted m y i-beta m| ∂m.law := abs_integral_le_integral_abs
    _ ≤ ∫ _, c ∂m.law := integral_mono_ae hdiff.abs (integrable_const _) (hb.mono fun y hy => hy i)
    _ = c := by simp

lemma own_centred_bound {n : ℕ} (m : Model n) (c : ℝ)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (hb : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) :
    ∀ᵐ y ∂m.law, ∀ i,
      |weighted m y i-expectation m (fun z => weighted m z i)| ≤ 2*c := by
  filter_upwards [hb] with y hy i
  calc
    _ = |(weighted m y i-beta m)-(expectation m (fun z => weighted m z i)-beta m)| := by ring_nf
    _ ≤ |weighted m y i-beta m|+|expectation m (fun z => weighted m z i)-beta m| := abs_sub _ _
    _ ≤ c+c := add_le_add (hy i) (own_mean_bound m c hL2 hb i)
    _ = _ := by ring

lemma sum_own_centred {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (y : Fin n → ℝ) :
    (∑ i, (weighted m y i-expectation m (fun z => weighted m z i))) =
      (n:ℝ)*(betaHat m y-beta m) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hL1 := fun i => (hL2 i).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hb : beta m = (∑ i, expectation m (fun z => weighted m z i))/(n:ℝ) := by
    unfold beta expectation betaHat average
    rw [integral_div, integral_finsetSum Finset.univ (fun i _ => hL1 i)]
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, hb]
  unfold betaHat average
  field_simp

lemma centred_dependency {n : ℕ} (m : Model n) (hdep : Dependency m)
    (b : Fin n → ℝ) (c : ℝ) :
    VariableDependency m.law m.G (fun i y => (weighted m y i-b i)/c) := by
  intro S T hdis hsep
  have hi := hdep S T hdis hsep
  have hm (S : Finset (Fin n)) : Measurable
      (fun z : ({i // i∈S} → ℝ) => fun i : {i // i∈S} => (m.theta i.val*z i-b i.val)/c) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul (measurable_pi_apply i) |>.sub measurable_const).div_const _
  exact hi.comp (hm S) (hm T)


lemma sum_zeta {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (y : Fin n → ℝ) :
    (∑ i, zeta m i y) = standardized m y := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  simp only [zeta, ← Finset.sum_div]
  rw [sum_own_centred hn m hL2]
  simpa only [standardized] using
    mul_div_mul_left (betaHat m y-beta m) (Real.sqrt (var m (betaHat m))) hn0

lemma mean_zeta {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (i : Fin n) :
    expectation m (zeta m i) = 0 := by
  let : IsProbabilityMeasure m.law := m.probability
  unfold expectation zeta
  rw [integral_div, integral_sub ((hL2 i).integrable (by norm_num)) (integrable_const _)]
  simp [expectation]

lemma standardized_var {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (hv : 0 < var m (betaHat m)) : var m (standardized m) = 1 := by
  let : IsProbabilityMeasure m.law := m.probability
  have hb := (betaHat_memLp m hL2).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hm : expectation m (standardized m) = 0 := by
    unfold expectation standardized
    rw [integral_div, integral_sub hb (integrable_const _)]
    simp [beta, expectation]
  unfold var
  rw [hm]
  simp only [sub_zero]
  unfold expectation standardized
  simp only [div_pow, integral_div]
  rw [Real.sq_sqrt hv.le]
  exact div_self hv.ne'

lemma clt_finite_normalization_completed {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (hv : 0 < var m (betaHat m)) (c : ℝ)
    (hbound : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) :
    (∀ y, ∑ i, zeta m i y=standardized m y) ∧
    (∀ i, expectation m (zeta m i)=0) ∧
    var m (fun y => ∑ i, zeta m i y)=1 ∧
    (∀ᵐ y ∂m.law, ∀ i, |zeta m i y| ≤ 2*c/((n : ℝ)*Real.sqrt (var m (betaHat m)))) ∧
    (Dependency m → VariableDependency m.law m.G (zeta m)) := by
  refine ⟨sum_zeta hn m hL2, mean_zeta m hL2, ?_, ?_, ?_⟩
  · have he : (fun y => ∑ i, zeta m i y) = standardized m := funext (sum_zeta hn m hL2)
    rw [he]
    exact standardized_var m hL2 hv
  · have hc := own_centred_bound m c hL2 hbound
    have hd : 0 < (n:ℝ)*Real.sqrt (var m (betaHat m)) :=
      mul_pos (by positivity) (Real.sqrt_pos.mpr hv)
    filter_upwards [hc] with y hy i
    rw [zeta, abs_div, abs_of_pos hd]
    exact div_le_div_of_nonneg_right (hy i) hd.le
  · intro hdep
    exact centred_dependency m hdep (fun i => expectation m (fun y => weighted m y i)) _


open Causalean.Mathlib.Probability.SteinMethod

def modelDep {n : ℕ} (m : Model n) (hdep : Dependency m) :
    DepGraph (fun i y => weighted m y i-expectation m (fun z => weighted m z i)) m.law := by
  classical
  let : IsProbabilityMeasure m.law := m.probability
  exact {
    G := fun i j => i=j ∨ m.G.val i j=true
    decG := inferInstance
    refl := fun i => Or.inl rfl
    symm := by
      intro i j hij
      rcases hij with h | h
      · exact Or.inl h.symm
      · exact Or.inr ((m.G.property.1 j i).trans h)
    meas := fun i => (weighted_measurable m i).sub measurable_const
    indep := by
      intro S T hsep
      have hd : Disjoint S T := by
        apply Finset.disjoint_left.mpr
        intro i hiS hiT
        exact hsep i hiS i hiT (Or.inl rfl)
      have hfalse : ∀ i∈S, ∀ j∈T, m.G.val i j=false := by
        intro i hi j hj
        cases he : m.G.val i j
        · rfl
        · exact False.elim (hsep i hi j hj (Or.inr he))
      simpa only [div_one] using
        centred_dependency m hdep (fun i => expectation m (fun z => weighted m z i)) 1 S T hd hfalse }

lemma modelDep_degree {n : ℕ} (m : Model n) (hdep : Dependency m) (i : Fin n) :
    ((modelDep m hdep).nbhd i).card = degree m.G i+1 := by
  classical
  have hi : i ∉ Finset.univ.filter (fun j => m.G.val i j=true) := by
    simp [m.G.property.2]
  have hs : (modelDep m hdep).nbhd i =
      insert i (Finset.univ.filter (fun j => m.G.val i j=true)) := by
    ext j
    rw [DepGraph.mem_nbhd_iff]
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    change (i=j ∨ m.G.val i j=true) ↔ (j=i ∨ m.G.val i j=true)
    exact or_congr eq_comm Iff.rfl
  rw [hs, Finset.card_insert_of_notMem hi]
  congr 1
  simp [Finset.card_filter, degree]

lemma sum_variance {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    (∫ y, (depSum (fun i y => weighted m y i-expectation m (fun z => weighted m z i)) y)^2 ∂m.law) =
      (n:ℝ)^2*var m (betaHat m) := by
  simp only [depSum, sum_own_centred hn m hL2, mul_pow]
  exact integral_const_mul _ _

lemma depSum_standardized {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (y : Fin n → ℝ) :
    depSum (fun i y => weighted m y i-expectation m (fun z => weighted m z i)) y /
      Real.sqrt ((n:ℝ)^2*var m (betaHat m)) = standardized m y := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  rw [depSum, sum_own_centred hn m hL2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  exact mul_div_mul_left _ _ hn0

lemma dependency_graph_clt_completed (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4) :
    ∀ t : ℝ, Tendsto (fun k => probability (F.model k) {y | standardized (F.model k) y ≤ t})
      atTop (𝓝 (Phi t)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  rcases h with ⟨hNested,hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  have hL2 (k : ℕ) (i : Fin (F.size k)) := weighted_memLp (F.model k) c1 (hBound k) i
  let X : ∀ k, Fin (F.size k) → (Fin (F.size k) → ℝ) → ℝ :=
    fun k i y => weighted (F.model k) y i-expectation (F.model k) (fun z => weighted (F.model k) z i)
  let D := fun k => modelDep (F.model k) (hDep k)
  have hdeg (k : ℕ) (i : Fin (F.size k)) : ((D k).nbhd i).card ≤ ⌈c2⌉₊+1 := by
    rw [modelDep_degree]
    have hh : degree (F.model k).G i ≤ ⌈c2⌉₊ := by
      exact_mod_cast (hDeg k i).trans (Nat.le_ceil c2)
    omega
  have hb (k : ℕ) (i : Fin (F.size k)) : ∀ᵐ y ∂(F.model k).law, |X k i y| ≤ 2*c1 :=
    (own_centred_bound (F.model k) c1 (hL2 k) (hBound k)).mono (fun y hy => hy i)
  have hm (k : ℕ) (i : Fin (F.size k)) : ∫ y, X k i y ∂(F.model k).law = 0 := by
    dsimp [X]
    rw [integral_sub ((hL2 k i).integrable (by norm_num)) (integrable_const _)]
    simp [expectation]
  let v := fun k => (F.size k:ℝ)^2*var (F.model k) (betaHat (F.model k))
  have hv (k : ℕ) : ∫ y, (depSum (X k) y)^2 ∂(F.model k).law = v k :=
    sum_variance (F.positive k) (F.model k) (hL2 k)
  have hvc : ∀ᶠ k in atTop, (c3/2)*(Fintype.card (Fin (F.size k)):ℝ) ≤ v k := by
    have hev : ∀ᶠ k in atTop, c3/2 < (F.size k:ℝ)*var (F.model k) (betaHat (F.model k)) :=
      hVar.eventually (Ioi_mem_nhds (show c3/2<c3 by linarith))
    filter_upwards [hev] with k hk
    dsimp [v]
    simp only [Fintype.card_fin]
    have hn : 0 < (F.size k:ℝ) := by exact_mod_cast F.positive k
    nlinarith
  intro t
  have hh := bounded_degree_dependency_clt_ae (fun k => (F.model k).law) X D
    (⌈c2⌉₊+1) hdeg (2*c1) hb hm v hv (c3/2) (by linarith) hvc
    (by simpa only [Fintype.card_fin] using F.grows) t
  have hid (k : ℕ) : (fun y => depSum (X k) y/Real.sqrt (v k)) = standardized (F.model k) :=
    funext (depSum_standardized (F.positive k) (F.model k) (hL2 k))
  simp only [hid] at hh
  have hPhi : (gaussianReal 0 1).real (Set.Iic t) = Phi t :=
    (ProbabilityTheory.cdf_eq_real (gaussianReal 0 1) t).symm
  rw [hPhi] at hh
  convert hh using 1
  funext k
  have hstd : Measurable (standardized (F.model k)) := by
    exact ((betaHat_measurable (F.model k)).sub measurable_const).div_const _
  symm
  simpa [probability, Set.preimage, Set.Iic] using
    map_measureReal_apply hstd measurableSet_Iic

end
end AronowAudit.P011.ProbabilityCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem dependency_graph_clt (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4) :
    ∀ t : ℝ, Tendsto (fun k => probability (F.model k) {y | standardized (F.model k) y ≤ t})
      atTop (𝓝 (Phi t)) := by
  exact ProbabilityCompletion.dependency_graph_clt_completed F c1 c2 c3 c4 h

theorem clt_finite_normalization {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (hv : 0 < var m (betaHat m)) (c : ℝ)
    (hbound : ∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) :
    (∀ y, ∑ i, zeta m i y=standardized m y) ∧
    (∀ i, expectation m (zeta m i)=0) ∧
    var m (fun y => ∑ i, zeta m i y)=1 ∧
    (∀ᵐ y ∂m.law, ∀ i, |zeta m i y| ≤ 2*c/((n : ℝ)*Real.sqrt (var m (betaHat m)))) ∧
    (Dependency m → VariableDependency m.law m.G (zeta m)) := by
  exact ProbabilityCompletion.clt_finite_normalization_completed hn m hL2 hv c hbound

end AronowAudit.P011

