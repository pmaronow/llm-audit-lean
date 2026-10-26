/- P011 T3(iv),(v): exact necessary and sufficient mean-bias conditions for oracle consistency and conservativeness under Scaling, with common-mean and PSD consequences. Neither equivalence concerns consistency of the data-selected maximum. -/
import AronowAudit.P011.P011_HomoskedasticCompletion

namespace AronowAudit.P011.MeanCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma quadratic_bound {n : ℕ} (G : Graph n) (c d : ℝ) (hc : 0≤c)
    (hd : ∀i,(degree G i:ℝ)+1≤d) (u : Fin n→ℝ) (hu : ∀i,|u i| ≤c) :
    |quadratic (oracleMatrix G) u| ≤(n:ℝ)*d*c^2 := by
  classical
  calc
    _ ≤ ∑i,|∑j,oracleMatrix G i j*u i*u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑i,∑j,oracleMatrix G i j*c^2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑j,|oracleMatrix G i j*u i*u j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul,abs_mul,abs_of_nonneg (OracleCompletion.oracle_nonneg G i j)]
          calc
            _ ≤ oracleMatrix G i j*c*c := by
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left (hu i) (OracleCompletion.oracle_nonneg G i j))
                (hu j) (abs_nonneg _) (mul_nonneg (OracleCompletion.oracle_nonneg G i j) hc)
            _ = _ := by ring
    _ = (∑i,∑j,oracleMatrix G i j)*c^2 := by simp only [←Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (OracleCompletion.oracle_total_bound G d hd) (sq_nonneg _)

lemma bias_bound (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4) (k : ℕ) :
    |meanBias (F.model k)| ≤(1+c2)*c1^2 := by
  rcases h with ⟨_,hc1,_,_,_,hDep,hBound,hDeg,_,_⟩
  have hL2 := ProbabilityCompletion.weighted_memLp (F.model k) c1 (hBound k)
  have hu (i : Fin (F.size k)) : |delta (F.model k) i| ≤c1 :=
    ProbabilityCompletion.own_mean_bound (F.model k) c1 hL2 (hBound k) i
  have hq := quadratic_bound (F.model k).G c1 (1+c2) hc1.le
    (fun i=>by linarith [hDeg k i]) (delta (F.model k)) hu
  have hnR : 0<(F.size k:ℝ) := by exact_mod_cast F.positive k
  unfold meanBias
  rw [abs_div,abs_of_pos hnR]
  exact (div_le_iff₀ hnR).mpr (by nlinarith [hq])

lemma probability_one_union {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A B : Set Ω) (h : Set.univ⊆A∪B) : 1≤μ.real A+μ.real B := by
  have hm := measureReal_mono (μ:=μ) h (measure_ne_top _ _)
  have hu := measureReal_union_le (μ:=μ) A B
  simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using hm.trans hu

lemma deterministic_centres {Ω : ℕ→Type*} [∀k,MeasurableSpace (Ω k)]
    (μ : ∀k,Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)]
    (X : ∀k,Ω k→ℝ) (b : ℕ→ℝ) (hX : CoverageCompletion.RowCP μ X 0)
    (hE : CoverageCompletion.RowCP μ (fun k ω=>X k ω-b k) 0) : Tendsto b atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hp := (hX (ε/4) (by linarith)).add (hE (ε/4) (by linarith))
  have he := hp.eventually (Iio_mem_nhds (show (0:ℝ)+0<1 by norm_num))
  filter_upwards [he] with k hk
  rw [Real.dist_eq,sub_zero]
  by_contra hb
  have hlarge : ε≤|b k| := le_of_not_gt hb
  have hall : Set.univ⊆{ω | |X k ω-0| >ε/4}∪{ω | |X k ω-b k-0| >ε/4} := by
    intro ω _
    by_contra hn
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,sub_zero] at hn
    have ht : |b k| ≤|X k ω|+|X k ω-b k| := by
      have hh := abs_sub (X k ω) (X k ω-b k)
      ring_nf at hh ⊢
      exact hh
    linarith
  have hprob := probability_one_union (μ k) _ _ hall
  linarith

lemma conservative_centres {Ω : ℕ→Type*} [∀k,MeasurableSpace (Ω k)]
    (μ : ∀k,Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)]
    (X : ∀k,Ω k→ℝ) (b : ℕ→ℝ)
    (hE : CoverageCompletion.RowCP μ (fun k ω=>X k ω-b k) 0)
    (hBelow : IsBoundedUnder (·≥·) atTop b) (hAbove : IsBoundedUnder (·≤·) atTop b) :
    (∀ε>0,Tendsto (fun k=>(μ k).real {ω | -X k ω>ε}) atTop (𝓝 0))↔0≤liminf b atTop := by
  constructor
  · intro hC
    apply (le_liminf_iff hAbove.isCoboundedUnder_ge hBelow).mpr
    intro y hy
    have hd : 0< -y/4 := by linarith
    have hp := (hC (-y/4) hd).add (hE (-y/4) hd)
    have he := hp.eventually (Iio_mem_nhds (show (0:ℝ)+0<1 by norm_num))
    filter_upwards [he] with k hk
    by_contra hb
    have hlarge : b k≤y := le_of_not_gt hb
    have hall : Set.univ⊆{ω | -X k ω> -y/4}∪{ω | |X k ω-b k-0| > -y/4} := by
      intro ω _
      by_contra hn
      simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,sub_zero] at hn
      have hlow := (abs_le.mp hn.2).2
      linarith
    have hprob := probability_one_union (μ k) _ _ hall
    linarith
  · intro hL ε hε
    have he := eventually_lt_of_lt_liminf (lt_of_lt_of_le (show -ε/2<0 by linarith) hL) hBelow
    apply squeeze_zero' (Eventually.of_forall fun k=>measureReal_nonneg) ?_ (hE (ε/2) (by linarith))
    filter_upwards [he] with k hk
    apply measureReal_mono (μ:=μ k) ?_ (measure_ne_top _ _)
    intro ω hω
    change ε< -X k ω at hω
    change ε/2< |X k ω-b k-0|
    rw [sub_zero]
    have hlow := neg_le_abs (X k ω-b k)
    linarith

lemma oracle_mean_conditions_completed (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    (InProbability F (scaledOracle F) (scaledTrue F) ↔
      Tendsto (fun k => meanBias (F.model k)) atTop (𝓝 0)) ∧
    (Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)) ↔
      0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop) ∧
    ((∀ k i, delta (F.model k) i = 0) →
      InProbability F (scaledOracle F) (scaledTrue F)) ∧
    ((∀ k, PSD (oracleMatrix (F.model k).G)) →
      Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y))) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let μ := fun k=>(F.model k).law
  let X := fun k y=>scaledOracle F k y-scaledTrue F k
  let b := fun k=>meanBias (F.model k)
  have hE : CoverageCompletion.RowCP μ (fun k y=>X k y-b k) 0 := by
    intro ε hε
    have hh := revised_oracle_convergence F c1 c2 c3 c4 h ε hε
    have he (k : ℕ) (y : Fin (F.size k)→ℝ) : X k y-b k-0=
        (F.size k:ℝ)*V1 (F.model k).G (weighted (F.model k) y)-
          ((F.size k:ℝ)*var (F.model k) (betaHat (F.model k))+meanBias (F.model k)) := by
      dsimp [X,b,scaledOracle,scaledTrue]
      ring
    simpa only [he,μ,probability] using hh
  have hBound (k : ℕ) : |b k| ≤(1+c2)*c1^2 := bias_bound F c1 c2 c3 c4 h k
  have hBelow : IsBoundedUnder (·≥·) atTop b := by
    refine ⟨-((1+c2)*c1^2),?_⟩
    change ∀ᶠ k : ℕ in atTop,-((1+c2)*c1^2)≤b k
    exact Eventually.of_forall fun k=>(abs_le.mp (hBound k)).1
  have hAbove : IsBoundedUnder (·≤·) atTop b := by
    refine ⟨(1+c2)*c1^2,?_⟩
    change ∀ᶠ k : ℕ in atTop,b k≤(1+c2)*c1^2
    exact Eventually.of_forall fun k=>(abs_le.mp (hBound k)).2
  have hIff : InProbability F (scaledOracle F) (scaledTrue F)↔Tendsto b atTop (𝓝 0) := by
    constructor
    · intro hx
      have hx' : CoverageCompletion.RowCP μ X 0 := by simpa only [CoverageCompletion.RowCP,InProbability,probability,μ,X,sub_zero] using hx
      exact deterministic_centres μ X b hx' hE
    · intro hb
      have hx := CoverageCompletion.rowCP_moving_center μ X b 0
        (by simpa only [CoverageCompletion.RowCP,sub_zero] using hE) hb
      simpa only [CoverageCompletion.RowCP,InProbability,probability,μ,X,sub_zero] using hx
  have hCiff : Conservative F (fun k y=>V1 (F.model k).G (weighted (F.model k) y))↔0≤liminf b atTop := by
    have hh := conservative_centres μ X b hE hBelow hAbove
    have he (k : ℕ) (y : Fin (F.size k)→ℝ) :
        (F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-V1 (F.model k).G (weighted (F.model k) y))= -X k y := by
      dsimp [X,scaledOracle,scaledTrue]
      ring
    simpa only [Conservative,probability,μ,he] using hh
  refine ⟨hIff,hCiff,?_,?_⟩
  · intro hδ
    apply hIff.mpr
    have he : b=fun _=>(0:ℝ) := by
      funext k
      simp [b,meanBias,quadratic,hδ k]
    rw [he]
    exact tendsto_const_nhds
  · intro hPSD
    apply hCiff.mpr
    apply (le_liminf_iff hAbove.isCoboundedUnder_ge hBelow).mpr
    intro y hy
    filter_upwards [] with k
    have hb : 0≤b k := div_nonneg ((hPSD k).2 (delta (F.model k))) (Nat.cast_nonneg _)
    linarith

end
end AronowAudit.P011.MeanCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem oracle_mean_conditions (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    (InProbability F (scaledOracle F) (scaledTrue F) ↔
      Tendsto (fun k => meanBias (F.model k)) atTop (𝓝 0)) ∧
    (Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)) ↔
      0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop) ∧
    ((∀ k i, delta (F.model k) i = 0) →
      InProbability F (scaledOracle F) (scaledTrue F)) ∧
    ((∀ k, PSD (oracleMatrix (F.model k).G)) →
      Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y))) := by
  exact MeanCompletion.oracle_mean_conditions_completed F c1 c2 c3 c4 h
end AronowAudit.P011

