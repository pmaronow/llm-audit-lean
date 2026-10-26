/- P011 T3(i): oracle concentration with a moving mean term.
The neighborhood-product variance bound is adapted from CausalSmith
(Apache-2.0); see NOTICE at the repository root. -/
import AronowAudit.P011.P011_CoverageCompletion
import AronowAudit.P011.P011_QuadraticCompletion
import AronowAudit.External.Causalean.Mathlib.Probability.SteinMethod.AlmostEverywhereDepGraphVariance

namespace AronowAudit.P011.OracleCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open Causalean.Mathlib.Probability.SteinMethod
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
local instance : ENNReal.HolderTriple (4:ENNReal) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

def U {n : ℕ} (m : Model n) (i : Fin n) (y : Fin n → ℝ) : ℝ := weighted m y i-beta m

def Q {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ := quadratic (oracleMatrix m.G) (fun i => U m i y)

def betaDep {n : ℕ} (m : Model n) (hdep : Dependency m) : DepGraph (U m) m.law := by
  classical
  let : IsProbabilityMeasure m.law := m.probability
  exact {
    G := fun i j => i=j ∨ m.G.val i j=true
    decG := inferInstance
    refl := fun i => Or.inl rfl
    symm := by
      intro i j h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr ((m.G.property.1 j i).trans h)
    meas := fun i => (ProbabilityCompletion.weighted_measurable m i).sub measurable_const
    indep := by
      intro S T hsep
      have hd : Disjoint S T := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        exact hsep i hi i hj (Or.inl rfl)
      have hfalse : ∀ i∈S,∀ j∈T,m.G.val i j=false := by
        intro i hi j hj
        cases he : m.G.val i j
        · rfl
        · exact False.elim (hsep i hi j hj (Or.inr he))
      simpa only [div_one,U] using
        ProbabilityCompletion.centred_dependency m hdep (fun _ => beta m) 1 S T hd hfalse }

lemma betaDep_degree {n : ℕ} (m : Model n) (hdep : Dependency m) (i : Fin n) :
    ((betaDep m hdep).nbhd i).card=degree m.G i+1 := by
  have hs : (betaDep m hdep).nbhd i=(ProbabilityCompletion.modelDep m hdep).nbhd i := by
    ext j
    rw [DepGraph.mem_nbhd_iff,DepGraph.mem_nbhd_iff]
    rfl
  rw [hs,ProbabilityCompletion.modelDep_degree]

lemma Q_nbhd {n : ℕ} (m : Model n) (hdep : Dependency m) (y : Fin n → ℝ) :
    (∑ i,U m i y*∑ j∈(betaDep m hdep).nbhd i,U m j y)=Q m y := by
  classical
  have hs (i : Fin n) : (betaDep m hdep).nbhd i=
      Finset.univ.filter (fun j => i=j ∨ m.G.val i j=true) := by
    ext j
    simp only [DepGraph.mem_nbhd_iff,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  unfold Q quadratic
  apply Finset.sum_congr rfl
  intro i _
  rw [hs,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [CliqueCompletion.oracle_apply]
  by_cases h : i=j ∨ m.G.val i j=true <;> simp [h] <;> ring

lemma U_memLp {n : ℕ} (m : Model n) (c : ℝ)
    (hbound : ∀ᵐ y ∂m.law,∀ i,|weighted m y i-beta m| ≤ c)
    (p : ENNReal) (i : Fin n) : MemLp (U m i) p m.law := by
  let : IsProbabilityMeasure m.law := m.probability
  apply MemLp.of_bound ((ProbabilityCompletion.weighted_measurable m i).sub measurable_const).aestronglyMeasurable c
  exact hbound.mono (fun y hy => by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hy i)

lemma Q_memLp2 {n : ℕ} (m : Model n) (c : ℝ)
    (hbound : ∀ᵐ y ∂m.law,∀ i,|weighted m y i-beta m| ≤ c) : MemLp (Q m) 2 m.law := by
  have hu := U_memLp m c hbound 4
  have hterm (i j : Fin n) : MemLp (fun y => oracleMatrix m.G i j*U m i y*U m j y) 2 m.law := by
    have hp : MemLp (fun y => U m i y*U m j y) 2 m.law := (hu i).mul (hu j)
    exact (memLp_congr_ae (Eventually.of_forall fun y => by ring)).mp (hp.const_mul _)
  have hinner (i : Fin n) : MemLp (fun y => ∑ j,oracleMatrix m.G i j*U m i y*U m j y) 2 m.law :=
    by simpa using memLp_finsetSum Finset.univ (fun j _ => hterm i j)
  unfold Q quadratic
  exact memLp_finsetSum Finset.univ (fun i _ => hinner i)

lemma covariance_support {n : ℕ} (m : Model n) (hdep : Dependency m)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law)
    (i j : Fin n) (hij : i≠j) (hG : m.G.val i j=false) : covariance m i j=0 := by
  classical
  have hv := ProbabilityCompletion.centred_dependency m hdep (fun _ => 0) 1
    {i} {j} (by simpa using hij) (by simpa using hG)
  have hi : IndepFun (fun y => weighted m y i) (fun y => weighted m y j) m.law := by
    simpa only [sub_zero,div_one,Function.comp_def] using hv.comp
      (measurable_pi_apply ⟨i,by simp⟩) (measurable_pi_apply ⟨j,by simp⟩)
  rw [QuadraticCompletion.covariance_eq_mathlib]
  exact hi.covariance_eq_zero (hL2 i) (hL2 j)

lemma oracle_trace {n : ℕ} (m : Model n) (hdep : Dependency m)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) :
    Matrix.trace (oracleMatrix m.G*covariance m)=QuadraticCompletion.total (covariance m) := by
  classical
  rw [QuadraticCompletion.trace_prod_symm _ _ (QuadraticCompletion.covariance_symm m)]
  unfold QuadraticCompletion.total
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [CliqueCompletion.oracle_apply]
  by_cases h : i=j ∨ m.G.val i j=true
  · simp [h]
  · have hij : i≠j := fun he => h (Or.inl he)
    have hG : m.G.val i j=false := by cases he : m.G.val i j <;> simp_all
    rw [covariance_support m hdep hL2 i j hij hG]
    simp

lemma U_pair_mean {n : ℕ} (m : Model n)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) (i j : Fin n) :
    expectation m (fun y => U m i y*U m j y)=covariance m i j+delta m i*delta m j := by
  let : IsProbabilityMeasure m.law := m.probability
  have hi (i : Fin n) : MemLp (U m i) 2 m.law :=
    (memLp_congr_ae (Eventually.of_forall fun y => rfl)).mp ((hL2 i).sub (memLp_const _))
  have hm (i : Fin n) : expectation m (U m i)=delta m i := by
    unfold expectation U
    rw [integral_sub ((hL2 i).integrable (by norm_num)) (integrable_const _)]
    simp [delta,expectation]
  have hc : cov[U m i,U m j;m.law]=covariance m i j := by
    unfold U
    rw [ProbabilityTheory.covariance_sub_const_left ((hL2 i).integrable (by norm_num)),
      ProbabilityTheory.covariance_sub_const_right ((hL2 j).integrable (by norm_num))]
    rfl
  have hp := ProbabilityTheory.covariance_eq_sub (hi i) (hi j)
  change cov[U m i,U m j;m.law]=expectation m (fun y => U m i y*U m j y)-
    expectation m (U m i)*expectation m (U m j) at hp
  rw [hc,hm,hm] at hp
  linarith

lemma Q_expectation {n : ℕ} (m : Model n)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) :
    expectation m (Q m)=Matrix.trace (oracleMatrix m.G*covariance m)+
      quadratic (oracleMatrix m.G) (delta m) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hu (i : Fin n) : MemLp (U m i) 2 m.law :=
    (memLp_congr_ae (Eventually.of_forall fun y => rfl)).mp ((hL2 i).sub (memLp_const _))
  have hInt (i j : Fin n) : Integrable (fun y => oracleMatrix m.G i j*U m i y*U m j y) m.law :=
    ((hu i).integrable_mul (hu j) |>.const_mul _).congr
      (Eventually.of_forall fun y => by dsimp only [Pi.mul_apply]; ring)
  have houter (i : Fin n) : Integrable (fun y => ∑ j,oracleMatrix m.G i j*U m i y*U m j y) m.law :=
    integrable_finsetSum Finset.univ (fun j _ => hInt i j)
  calc
    _ = ∑ i,∑ j,∫ y,oracleMatrix m.G i j*U m i y*U m j y ∂m.law := by
      unfold expectation Q quadratic
      rw [integral_finsetSum Finset.univ (fun i _ => houter i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hInt i j)]
    _ = ∑ i,∑ j,oracleMatrix m.G i j*(covariance m i j+delta m i*delta m j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = oracleMatrix m.G i j*expectation m (fun y => U m i y*U m j y) := by
          simpa only [mul_assoc,expectation] using integral_const_mul (oracleMatrix m.G i j) (fun y => U m i y*U m j y)
        _ = _ := by rw [U_pair_mean m hL2]
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,←mul_assoc]
      rw [←QuadraticCompletion.trace_prod_symm _ _ (QuadraticCompletion.covariance_symm m)]
      rfl

lemma normalized_Q_expectation {n : ℕ} (hn : 0 < n) (m : Model n) (hdep : Dependency m)
    (hL2 : ∀ i,MemLp (fun y => weighted m y i) 2 m.law) :
    expectation m (fun y => Q m y/(n:ℝ))=(n:ℝ)*var m (betaHat m)+meanBias m := by
  rw [expectation,integral_div]
  change expectation m (Q m)/(n:ℝ)=_
  rw [Q_expectation m hL2,oracle_trace m hdep hL2,QuadraticCompletion.beta_variance m hL2]
  unfold meanBias
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  field_simp <;> ring

lemma oracle_nonneg {n : ℕ} (G : Graph n) (i j : Fin n) : 0≤oracleMatrix G i j := by
  classical
  rw [CliqueCompletion.oracle_apply]
  split_ifs <;> norm_num

lemma oracle_row_sum {n : ℕ} (G : Graph n) (i : Fin n) :
    (∑ j,oracleMatrix G i j)=(degree G i:ℝ)+1 := by
  classical
  unfold oracleMatrix adjacency degree
  simp only [Matrix.add_apply,Matrix.one_apply,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  push_cast
  ring

lemma quadratic_shift_bound {n : ℕ} (G : Graph n) (u : Fin n→ℝ) (a c : ℝ)
    (hu : ∀ i,|u i| ≤c) :
    |quadratic (oracleMatrix G) (fun i=>u i-a)-quadratic (oracleMatrix G) u| ≤
      (∑ i,∑ j,oracleMatrix G i j)*(2*c*|a| +a^2) := by
  classical
  unfold quadratic
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i,|(∑ j,oracleMatrix G i j*(u i-a)*(u j-a))-
        ∑ j,oracleMatrix G i j*u i*u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,∑ j,oracleMatrix G i j*(2*c*|a| +a^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [←Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ j,|oracleMatrix G i j*(u i-a)*(u j-a)-oracleMatrix G i j*u i*u j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          have hp : |(u i-a)*(u j-a)-u i*u j| ≤2*c*|a| +a^2 := by
            calc
              _ = |(-u i*a-u j*a)+a^2| := by congr 1;ring
              _ ≤ |-u i*a-u j*a| +|a^2| := abs_add_le _ _
              _ ≤ |-u i*a| +|u j*a| +a^2 := by
                rw [abs_of_nonneg (sq_nonneg a)]
                linarith [abs_sub (-u i*a) (u j*a)]
              _ ≤ c*|a| +c*|a| +a^2 := by
                simp only [abs_mul,abs_neg]
                gcongr
                exact hu i
                exact hu j
              _ = _ := by ring
          calc
            _ = oracleMatrix G i j*|(u i-a)*(u j-a)-u i*u j| := by
              calc
                _ = |oracleMatrix G i j*((u i-a)*(u j-a)-u i*u j)| := by congr 1;ring
                _ = |oracleMatrix G i j| *|(u i-a)*(u j-a)-u i*u j| := abs_mul _ _
                _ = _ := by rw [abs_of_nonneg (oracle_nonneg G i j)]
            _ ≤ _ := mul_le_mul_of_nonneg_left hp (oracle_nonneg G i j)
    _ = _ := by simp only [←Finset.sum_mul]

lemma oracle_total_bound {n : ℕ} (G : Graph n) (D : ℝ)
    (hD : ∀ i,(degree G i:ℝ)+1≤D) :
    (∑ i,∑ j,oracleMatrix G i j)≤(n:ℝ)*D := by
  simp_rw [oracle_row_sum]
  simpa using Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>hD i)

lemma sample_centering_bound {n : ℕ} (hn : 0<n) (m : Model n) (c D : ℝ)
    (hD : ∀ i,(degree m.G i:ℝ)+1≤D) (y : Fin n→ℝ)
    (hu : ∀ i,|weighted m y i-beta m| ≤c) :
    |(n:ℝ)*V1 m.G (weighted m y)-Q m y/(n:ℝ)| ≤
      D*(2*c*|betaHat m y-beta m| +(betaHat m y-beta m)^2) := by
  classical
  have hnR : 0<(n:ℝ) := by positivity
  have hc : 0≤c := le_trans (abs_nonneg _) (hu ⟨0,hn⟩)
  let a := betaHat m y-beta m
  have hid : centered (weighted m y)=fun i=>U m i y-a := by
    funext i
    dsimp [centered,U,a,betaHat]
    ring
  rw [←variance_form_oracle,varianceForm,hid]
  have he : (n:ℝ)* (quadratic (oracleMatrix m.G) (fun i=>U m i y-a)/(n:ℝ)^2)-Q m y/(n:ℝ)=
      (quadratic (oracleMatrix m.G) (fun i=>U m i y-a)-Q m y)/(n:ℝ) := by field_simp <;> ring
  rw [he,abs_div,abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ (∑ i,∑ j,oracleMatrix m.G i j)*(2*c*|a| +a^2) :=
      quadratic_shift_bound m.G (fun i=>U m i y) a c hu
    _ ≤ ((n:ℝ)*D)*(2*c*|a| +a^2) := by
      apply mul_le_mul_of_nonneg_right (oracle_total_bound m.G D hD)
      positivity
    _ = _ := by dsimp [a];ring

lemma chebyshev_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω→ℝ) (hX : MemLp X 2 μ) (ε : ℝ) (hε : 0<ε) :
    μ.real {ω | |X ω-∫ z,X z ∂μ| > ε} ≤ ProbabilityTheory.variance X μ/ε^2 := by
  have hb := meas_ge_le_variance_div_sq hX hε
  have hne : ENNReal.ofReal (ProbabilityTheory.variance X μ/ε^2)≠⊤ := ENNReal.ofReal_ne_top
  have hsub : {ω | |X ω-(∫ z, X z ∂μ)| > ε}⊆{ω | ε≤ |X ω-(∫ z, X z ∂μ)|} := by
    intro ω hω
    change ε < |X ω-(∫ z, X z ∂μ)| at hω
    change ε ≤ |X ω-(∫ z, X z ∂μ)|
    exact hω.le
  refine le_trans (measureReal_mono (μ:=μ) hsub (measure_ne_top _ _)) ?_
  change (μ {ω|ε≤ |X ω-∫ z,X z ∂μ|}).toReal≤_
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) hne).mpr hb |>.trans_eq
    (ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (sq_nonneg _)))

lemma rowCP_of_variance {Ω : ℕ→Type*} [∀k,MeasurableSpace (Ω k)]
    (μ : ∀k,Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)]
    (X : ∀k,Ω k→ℝ) (hX : ∀k,MemLp (X k) 2 (μ k))
    (hv : Tendsto (fun k=>ProbabilityTheory.variance (X k) (μ k)) atTop (𝓝 0)) :
    ∀ ε>0,Tendsto (fun k=>(μ k).real {ω| |X k ω-∫z,X k z∂μ k| > ε}) atTop (𝓝 0) := by
  intro ε hε
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>chebyshev_real (μ k) (X k) (hX k) ε hε)
  simpa using hv.div_const (ε^2)

lemma normalized_Q_variance {n : ℕ} (hn : 0<n) (m : Model n) (c : ℝ)
    (hc : 0≤c) (hdep : Dependency m)
    (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m| ≤c)
    (D : ℕ) (hd : ∀i,degree m.G i+1≤D) :
    ProbabilityTheory.variance (fun y=>Q m y/(n:ℝ)) m.law≤2*(D:ℝ)^5*c^4/(n:ℝ) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hq := (betaDep m hdep).var_nbhd_prod_le_ae hc
    (fun i=>hb.mono (fun y hy=>hy i)) (fun i=>by rw [betaDep_degree];exact hd i)
  simp only [Q_nbhd,Fintype.card_fin] at hq
  have he : (fun y=>Q m y/(n:ℝ))=fun y=>(n:ℝ)⁻¹*Q m y := by funext y;ring
  rw [he,ProbabilityTheory.variance_const_mul]
  calc
    _ ≤ ((n:ℝ)⁻¹)^2*(2*(D:ℝ)^5*(n:ℝ)*c^4) :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    _ = _ := by
      have hn0 : (n:ℝ)≠0 := by positivity
      field_simp <;> ring

lemma rowCP_dominated {Ω : ℕ→Type*} [∀k,MeasurableSpace (Ω k)]
    (μ : ∀k,Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)]
    (X B : ∀k,Ω k→ℝ) (hB : CoverageCompletion.RowCP μ B 0)
    (hbound : ∀k,∀ᵐω∂μ k,|X k ω| ≤B k ω) : CoverageCompletion.RowCP μ X 0 := by
  intro ε hε
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>?_) (hB ε hε)
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  apply measure_mono_ae
  filter_upwards [hbound k] with ω hω
  intro hbad
  change ε< |X k ω-0| at hbad
  change ε< |B k ω-0|
  rw [sub_zero] at hbad ⊢
  exact lt_of_lt_of_le (lt_of_lt_of_le hbad hω) (le_abs_self _)

lemma row_moving_add_error {Ω : ℕ→Type*} [∀k,MeasurableSpace (Ω k)]
    (μ : ∀k,Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)]
    (X T : ∀k,Ω k→ℝ) (a : ℕ→ℝ)
    (hX : ∀ε>0,Tendsto (fun k=>(μ k).real {ω | |X k ω-a k| > ε}) atTop (𝓝 0))
    (hE : CoverageCompletion.RowCP μ (fun k ω=>T k ω-X k ω) 0) :
    ∀ε>0,Tendsto (fun k=>(μ k).real {ω | |T k ω-a k| > ε}) atTop (𝓝 0) := by
  intro ε hε
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>?_)
    (by simpa using (hX (ε/2) (by linarith)).add (hE (ε/2) (by linarith)))
  calc
    _ ≤ (μ k).real ({ω | |X k ω-a k| > ε/2}∪{ω | |T k ω-X k ω-0| > ε/2}) := by
      apply measureReal_mono (μ:=μ k) ?_ (measure_ne_top _ _)
      intro ω hbad
      by_contra he
      simp only [Set.mem_union,Set.mem_setOf_eq,not_or,not_lt,sub_zero] at he
      have ht : |T k ω-a k| ≤ |T k ω-X k ω| +|X k ω-a k| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (T k ω-X k ω) (X k ω-a k)
      change ε< |T k ω-a k| at hbad
      linarith
    _ ≤ (μ k).real {ω | |X k ω-a k| > ε/2}+(μ k).real {ω | |T k ω-X k ω-0| > ε/2} :=
      measureReal_union_le _ _
    _ = _ := by simp only [sub_zero]

lemma revised_oracle_convergence_completed (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    InProbability F
      (fun k y => (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y))
      (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) + meanBias (F.model k)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  rcases h with ⟨hNested,hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  let D : ℕ := ⌈c2⌉₊+1
  have hD (k : ℕ) (i : Fin (F.size k)) : degree (F.model k).G i+1≤D := by
    dsimp [D]
    exact Nat.add_le_add_right (by exact_mod_cast (hDeg k i).trans (Nat.le_ceil c2)) 1
  have hDR (k : ℕ) (i : Fin (F.size k)) : (degree (F.model k).G i:ℝ)+1≤(D:ℝ) :=
    by exact_mod_cast hD k i
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    ProbabilityCompletion.weighted_memLp (F.model k) c1 (hBound k) i
  have hN : Tendsto (fun k=>(F.size k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  have hQ2 (k : ℕ) : MemLp (fun y=>Q (F.model k) y/(F.size k:ℝ)) 2 (F.model k).law := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (Q_memLp2 (F.model k) c1 (hBound k)).const_mul ((F.size k:ℝ)⁻¹)
  have hQV : Tendsto (fun k=>ProbabilityTheory.variance
      (fun y=>Q (F.model k) y/(F.size k:ℝ)) (F.model k).law) atTop (𝓝 0) := by
    apply squeeze_zero (fun k=>ProbabilityTheory.variance_nonneg _ _)
      (fun k=>normalized_Q_variance (F.positive k) (F.model k) c1 hc1.le
        (hDep k) (hBound k) D (hD k))
    exact hN.const_div_atTop _
  have hQ := rowCP_of_variance (fun k=>(F.model k).law)
    (fun k y=>Q (F.model k) y/(F.size k:ℝ)) hQ2 hQV
  have hQB : ∀ε>0,Tendsto (fun k=>probability (F.model k)
      {y | |Q (F.model k) y/(F.size k:ℝ)-
        ((F.size k:ℝ)*var (F.model k) (betaHat (F.model k))+meanBias (F.model k))| > ε})
        atTop (𝓝 0) := by
    have hE (k : ℕ) : (∫y,Q (F.model k) y/(F.size k:ℝ)∂(F.model k).law)=
        (F.size k:ℝ)*var (F.model k) (betaHat (F.model k))+meanBias (F.model k) :=
      normalized_Q_expectation (F.positive k) (F.model k) (hDep k) (hL2 k)
    simpa only [probability,hE] using hQ
  have hBV : Tendsto (fun k=>ProbabilityTheory.variance (betaHat (F.model k)) (F.model k).law)
      atTop (𝓝 0) := by
    have hv := hVar.div_atTop hN
    have he (k : ℕ) : ((F.size k:ℝ)*var (F.model k) (betaHat (F.model k)))/(F.size k:ℝ)=
        ProbabilityTheory.variance (betaHat (F.model k)) (F.model k).law := by
      rw [ProbabilityTheory.variance_eq_integral (ProbabilityCompletion.betaHat_measurable _).aemeasurable]
      change _=var (F.model k) (betaHat (F.model k))
      have hn0 : (F.size k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (F.positive k)
      field_simp
    simpa only [he] using hv
  have hBC : CoverageCompletion.RowCP (fun k=>(F.model k).law)
      (fun k y=>betaHat (F.model k) y-beta (F.model k)) 0 := by
    simpa only [CoverageCompletion.RowCP,sub_zero,beta,expectation] using
      rowCP_of_variance (fun k=>(F.model k).law) (fun k=>betaHat (F.model k))
        (fun k=>ProbabilityCompletion.betaHat_memLp _ (hL2 k)) hBV
  let B : ℝ→ℝ := fun a=>(D:ℝ)*(2*c1*|a| +a^2)
  have hBC' : CoverageCompletion.RowCP (fun k=>(F.model k).law)
      (fun k y=>B (betaHat (F.model k) y-beta (F.model k))) 0 := by
    have hh := CoverageCompletion.rowCP_continuous_pair (fun k=>(F.model k).law)
      (fun k y=>betaHat (F.model k) y-beta (F.model k)) (fun _ _=>(0:ℝ)) 0 0 hBC
      (CoverageCompletion.rowCP_det _ (fun _=>(0:ℝ)) 0 tendsto_const_nhds)
      (fun p:ℝ×ℝ=>B p.1) (by dsimp [B];fun_prop)
    simpa only [B,abs_zero,mul_zero,zero_pow (by decide:2≠0),add_zero] using hh
  have hE : CoverageCompletion.RowCP (fun k=>(F.model k).law)
      (fun k y=>(F.size k:ℝ)*V1 (F.model k).G (weighted (F.model k) y)-Q (F.model k) y/(F.size k:ℝ)) 0 := by
    apply rowCP_dominated _ _ (fun k y=>B (betaHat (F.model k) y-beta (F.model k))) hBC'
    intro k
    filter_upwards [hBound k] with y hy
    exact sample_centering_bound (F.positive k) (F.model k) c1 D (hDR k) y hy
  exact row_moving_add_error (fun k=>(F.model k).law) _ _ _ hQB hE

end
end AronowAudit.P011.OracleCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem revised_oracle_convergence (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    InProbability F
      (fun k y => (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y))
      (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) + meanBias (F.model k)) := by
  exact OracleCompletion.revised_oracle_convergence_completed F c1 c2 c3 c4 h
end AronowAudit.P011

