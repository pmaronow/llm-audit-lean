import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Instances.Matrix
namespace AronowAudit.P015.ConvergenceCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- A continuous map at a deterministic finite-dimensional limit preserves actual
convergence in probability. Coordinate bad events are bounded by their finite union. -/
lemma finite_cmt {Ω I E : Type*} [MeasurableSpace Ω] [Fintype I] [PseudoMetricSpace E]
    (P : Measure Ω) (f : ℕ → Ω → I → ℝ) (a : I → ℝ) (g : (I → ℝ) → E)
    (hf : ∀ i, TendstoInMeasure P (fun n s=>f n s i) atTop (fun _=>a i))
    (hg : ContinuousAt g a) :
    TendstoInMeasure P (fun n s=>g (f n s)) atTop (fun _=>g a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩:=Metric.continuousAt_iff.mp hg ε hε
  have hsub(n:ℕ):{s|ε≤dist (g (f n s)) (g a)}⊆⋃i,{s|δ≤dist (f n s i) (a i)}:=by
    intro s hs
    by_contra hn
    have hn' : ∀ i,dist (f n s i) (a i)<δ:=by
      simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hn
    exact not_lt_of_ge hs (hcont ((dist_pi_lt_iff hδ).mpr hn'))
  have hlim:Tendsto (fun n=>∑i,P {s|δ≤dist (f n s i) (a i)}) atTop (𝓝 0):=by
    have h:=tendsto_finsetSum Finset.univ (fun i _=>(tendstoInMeasure_iff_dist.mp (hf i)) δ hδ)
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _=>zero_le)
  intro n
  exact (measure_mono (hsub n)).trans (measure_iUnion_fintype_le _ _)

lemma constant_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (a : ℝ) :
    TendstoInMeasure P (fun (_:ℕ) (_:Ω)=>a) atTop (fun _=>a) := by
  intro ε hε
  have he : {s:Ω|ε≤edist a a}=∅:=by
    ext s
    simp only [edist_self,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    exact not_le.mpr hε
  simp only [he,measure_empty]
  exact tendsto_const_nhds

lemma pair_cmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : ℕ → Ω → ℝ) (a b : ℝ) (F : ℝ×ℝ → ℝ)
    (hf:TendstoInMeasure P f atTop (fun _=>a))
    (hg:TendstoInMeasure P g atTop (fun _=>b)) (hF:ContinuousAt F (a,b)) :
    TendstoInMeasure P (fun n s=>F (f n s,g n s)) atTop (fun _=>F (a,b)) := by
  let H : Bool → ℝ:=fun t=>if t then b else a
  let X : ℕ → Ω → Bool → ℝ:=fun n s t=>if t then g n s else f n s
  have hx : ∀ t,TendstoInMeasure P (fun n s=>X n s t) atTop (fun _=>H t):=by
    intro t
    cases t
    · simpa [X,H] using hf
    · simpa [X,H] using hg
  have hcont : ContinuousAt (fun v:Bool→ℝ=>F (v false,v true)) H:=by
    exact hF.comp₂_of_eq (continuous_apply false).continuousAt (continuous_apply true).continuousAt (by simp [H])
  exact finite_cmt P X H _ hx hcont

lemma add_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf:TendstoInMeasure P f atTop (fun _=>a)) (hg:TendstoInMeasure P g atTop (fun _=>b)) :
    TendstoInMeasure P (fun n s=>f n s+g n s) atTop (fun _=>a+b) :=
  pair_cmt P f g a b (fun z=>z.1+z.2) hf hg (by fun_prop)

lemma sub_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf:TendstoInMeasure P f atTop (fun _=>a)) (hg:TendstoInMeasure P g atTop (fun _=>b)) :
    TendstoInMeasure P (fun n s=>f n s-g n s) atTop (fun _=>a-b) :=
  pair_cmt P f g a b (fun z=>z.1-z.2) hf hg (by fun_prop)

lemma mul_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf:TendstoInMeasure P f atTop (fun _=>a)) (hg:TendstoInMeasure P g atTop (fun _=>b)) :
    TendstoInMeasure P (fun n s=>f n s*g n s) atTop (fun _=>a*b) :=
  pair_cmt P f g a b (fun z=>z.1*z.2) hf hg (by fun_prop)

lemma div_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf:TendstoInMeasure P f atTop (fun _=>a)) (hg:TendstoInMeasure P g atTop (fun _=>b)) (hb:b≠0) :
    TendstoInMeasure P (fun n s=>f n s/g n s) atTop (fun _=>a/b) :=
  pair_cmt P f g a b (fun z=>z.1/z.2) hf hg (continuousAt_fst.div continuousAt_snd hb)

lemma sum_limit {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] (P : Measure Ω)
    (f : I → ℕ → Ω → ℝ) (a : I → ℝ)
    (hf : ∀i,TendstoInMeasure P (f i) atTop (fun _=>a i)) :
    TendstoInMeasure P (fun n s=>∑i,f i n s) atTop (fun _=>∑i,a i) :=
  finite_cmt P (fun n s i=>f i n s) a (fun v=>∑i,v i) hf (by fun_prop)

lemma inverse_smul_real {Q : Type*} [Fintype Q] [DecidableEq Q]
    (A : Matrix Q Q ℝ) (c : ℝ) (hc : c≠0) : (c • A)⁻¹=c⁻¹ • A⁻¹ := by
  by_cases ha : IsUnit A.det
  · letI : Invertible c:=invertibleOfNonzero hc
    simpa only [invOf_eq_inv] using Matrix.inv_smul A c ha
  · have ha0 : A.det=0:=by simpa only [isUnit_iff_ne_zero,not_not] using ha
    have hca : ¬IsUnit (c • A).det:=by simp [ha0,isUnit_iff_ne_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hca,Matrix.nonsing_inv_apply_not_isUnit _ ha,smul_zero]

end
end AronowAudit.P015.ConvergenceCompletion
