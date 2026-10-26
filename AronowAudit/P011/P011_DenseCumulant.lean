import AronowAudit.P011.P011_MeanCompletion
import AronowAudit.P011.P011_DenseTreeCount
namespace AronowAudit.P011.DenseCumulant
open MeasureTheory ProbabilityTheory Filter Finset
open Causalean.Mathlib.Probability.SteinMethod
open scoped BigOperators ENNReal ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency true

variable {Ω ι : Type*} [MeasurableSpace Ω]

def pairMean (μ : Measure Ω) (Z : ι→Ω→ℝ) (i j:ι) : ℝ := ∫ω,Z i ω*Z j ω∂μ

def cumulant4 (μ : Measure Ω) (Z : ι→Ω→ℝ) (i j k l:ι) : ℝ :=
  (∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)-pairMean μ Z i j*pairMean μ Z k l-
    pairMean μ Z i k*pairMean μ Z j l-pairMean μ Z i l*pairMean μ Z j k

lemma pairMean_symm (μ : Measure Ω) (Z : ι→Ω→ℝ) (i j:ι) : pairMean μ Z i j=pairMean μ Z j i := by
  unfold pairMean
  apply integral_congr_ae
  exact Eventually.of_forall fun ω=>mul_comm _ _

lemma cumulant_swap01 (μ : Measure Ω) (Z : ι→Ω→ℝ) (i j k l:ι) :
    cumulant4 μ Z i j k l=cumulant4 μ Z j i k l := by
  unfold cumulant4
  have h4 : (∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)=(∫ω,Z j ω*Z i ω*Z k ω*Z l ω∂μ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω=>by ring
  rw [h4,pairMean_symm μ Z i j]
  ring

lemma cumulant_swap12 (μ : Measure Ω) (Z : ι→Ω→ℝ) (i j k l:ι) :
    cumulant4 μ Z i j k l=cumulant4 μ Z i k j l := by
  unfold cumulant4
  have h4 : (∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)=(∫ω,Z i ω*Z k ω*Z j ω*Z l ω∂μ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω=>by ring
  rw [h4,pairMean_symm μ Z j k]
  ring

lemma cumulant_swap23 (μ : Measure Ω) (Z : ι→Ω→ℝ) (i j k l:ι) :
    cumulant4 μ Z i j k l=cumulant4 μ Z i j l k := by
  unfold cumulant4
  have h4 : (∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)=(∫ω,Z i ω*Z j ω*Z l ω*Z k ω∂μ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω=>by ring
  rw [h4,pairMean_symm μ Z k l]
  ring

variable [Fintype ι] [DecidableEq ι]

lemma pairMean_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ι→Ω→ℝ)
    (D : DepGraph Z μ) (hz : ∀i,∫ω,Z i ω∂μ=0) (i j:ι) (hij:¬D.G i j) : pairMean μ Z i j=0 := by
  classical
  have hsep : ∀a∈({i}:Finset ι),∀b∈({j}:Finset ι),¬D.G a b := by simpa using hij
  have hI : IndepFun (Z i) (Z j) μ := by
    simpa only [Function.comp_def] using (D.indep {i} {j} hsep).comp
      (measurable_pi_apply ⟨i,by simp⟩) (measurable_pi_apply ⟨j,by simp⟩)
  simpa only [pairMean,hz,mul_zero,zero_mul] using
    hI.integral_fun_mul_eq_mul_integral (D.meas i).aestronglyMeasurable (D.meas j).aestronglyMeasurable

lemma cumulant_isolated (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ι→Ω→ℝ)
    (D : DepGraph Z μ) (hz : ∀i,∫ω,Z i ω∂μ=0) (i j k l:ι)
    (hij:¬D.G i j) (hik:¬D.G i k) (hil:¬D.G i l) : cumulant4 μ Z i j k l=0 := by
  classical
  let T : Finset ι:={j,k,l}
  have hsep : ∀a∈({i}:Finset ι),∀b∈T,¬D.G a b := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha
    subst a
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl <;> assumption
  have hm (a:T) : Measurable (fun v:T→ℝ=>v a) := measurable_pi_apply a
  have hProd : Measurable (fun v : T→ℝ=>v ⟨j,by simp[T]⟩*v ⟨k,by simp[T]⟩*v ⟨l,by simp[T]⟩) :=
    ((hm ⟨j,by simp[T]⟩).mul (hm ⟨k,by simp[T]⟩)).mul (hm ⟨l,by simp[T]⟩)
  have hI : IndepFun (Z i) (fun ω=>Z j ω*Z k ω*Z l ω) μ := by
    simpa only [Function.comp_def] using (D.indep {i} T hsep).comp
      (measurable_pi_apply ⟨i,by simp⟩) hProd
  have h4 : (∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)=0 := by
    calc
      _ = ∫ω,Z i ω*(Z j ω*Z k ω*Z l ω)∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω=>by ring
      _ = _ := by rw [hI.integral_fun_mul_eq_mul_integral (D.meas i).aestronglyMeasurable
        (((D.meas j).mul (D.meas k)).mul (D.meas l)).aestronglyMeasurable,hz,zero_mul]
  unfold cumulant4
  rw [h4,pairMean_zero μ Z D hz i j hij,pairMean_zero μ Z D hz i k hik,
    pairMean_zero μ Z D hz i l hil]
  ring

lemma cumulant_pair_cut (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ι→Ω→ℝ)
    (D : DepGraph Z μ) (hz : ∀i,∫ω,Z i ω∂μ=0) (i j k l:ι)
    (hik:¬D.G i k) (hil:¬D.G i l) (hjk:¬D.G j k) (hjl:¬D.G j l) : cumulant4 μ Z i j k l=0 := by
  classical
  let S : Finset ι:={i,j}
  let T : Finset ι:={k,l}
  have hsep : ∀a∈S,∀b∈T,¬D.G a b := by
    intro a ha b hb
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at ha
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> assumption
  have hmS (a:S) : Measurable (fun v:S→ℝ=>v a) := measurable_pi_apply a
  have hmT (a:T) : Measurable (fun v:T→ℝ=>v a) := measurable_pi_apply a
  have hP : Measurable (fun v:S→ℝ=>v ⟨i,by simp[S]⟩*v ⟨j,by simp[S]⟩) :=
    (hmS ⟨i,by simp[S]⟩).mul (hmS ⟨j,by simp[S]⟩)
  have hQ : Measurable (fun v:T→ℝ=>v ⟨k,by simp[T]⟩*v ⟨l,by simp[T]⟩) :=
    (hmT ⟨k,by simp[T]⟩).mul (hmT ⟨l,by simp[T]⟩)
  have hI : IndepFun (fun ω=>Z i ω*Z j ω) (fun ω=>Z k ω*Z l ω) μ := by
    simpa only [Function.comp_def] using (D.indep S T hsep).comp hP hQ
  have h4 : (∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)=pairMean μ Z i j*pairMean μ Z k l := by
    calc
      _ = ∫ω,(Z i ω*Z j ω)*(Z k ω*Z l ω)∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω=>by ring
      _ = _ := hI.integral_fun_mul_eq_mul_integral ((D.meas i).mul (D.meas j)).aestronglyMeasurable
        ((D.meas k).mul (D.meas l)).aestronglyMeasurable
  unfold cumulant4
  rw [h4,pairMean_zero μ Z D hz i k hik,pairMean_zero μ Z D hz i l hil]
  ring

def FourCut (G:ι→ι→Prop) (i j k l:ι) : Prop :=
  (¬G i j ∧ ¬G i k ∧ ¬G i l) ∨
  (¬G i j ∧ ¬G j k ∧ ¬G j l) ∨
  (¬G i k ∧ ¬G j k ∧ ¬G k l) ∨
  (¬G i l ∧ ¬G j l ∧ ¬G k l) ∨
  (¬G i k ∧ ¬G i l ∧ ¬G j k ∧ ¬G j l) ∨
  (¬G i j ∧ ¬G i l ∧ ¬G j k ∧ ¬G k l) ∨
  (¬G i j ∧ ¬G i k ∧ ¬G j l ∧ ¬G k l)

lemma cumulant_of_cut (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ)
    (D:DepGraph Z μ) (hz:∀i,∫ω,Z i ω∂μ=0) (i j k l:ι)
    (h:FourCut D.G i j k l) : cumulant4 μ Z i j k l=0 := by
  have hs {a b:ι} (h:¬D.G a b) : ¬D.G b a := fun h' => h (D.symm b a h')
  rcases h with h|h|h|h|h|h|h
  · exact cumulant_isolated μ Z D hz i j k l h.1 h.2.1 h.2.2
  · rw [cumulant_swap01]
    exact cumulant_isolated μ Z D hz j i k l (hs h.1) h.2.1 h.2.2
  · rw [cumulant_swap12,cumulant_swap01]
    exact cumulant_isolated μ Z D hz k i j l (hs h.1) (hs h.2.1) h.2.2
  · rw [cumulant_swap23,cumulant_swap12,cumulant_swap01]
    exact cumulant_isolated μ Z D hz l i j k (hs h.1) (hs h.2.1) (hs h.2.2)
  · exact cumulant_pair_cut μ Z D hz i j k l h.1 h.2.1 h.2.2.1 h.2.2.2
  · rw [cumulant_swap12]
    exact cumulant_pair_cut μ Z D hz i k j l h.1 h.2.1 (hs h.2.2.1) h.2.2.2
  · rw [cumulant_swap23,cumulant_swap12]
    exact cumulant_pair_cut μ Z D hz i l j k h.1 h.2.1 (hs h.2.2.1) (hs h.2.2.2)

lemma integral_abs_bound (μ:Measure Ω) [IsProbabilityMeasure μ] (f:Ω→ℝ) (B:ℝ)
    (hb:∀ᵐω∂μ,|f ω|≤B) : |∫ω,f ω∂μ|≤B := by
  have hn:=norm_integral_le_of_norm_le_const (μ:=μ) (f:=f) (C:=B)
    (hb.mono fun ω hω=>by simpa only [Real.norm_eq_abs] using hω)
  simpa [Real.norm_eq_abs,measureReal_def] using hn

lemma pair_abs_bound (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ) (B:ℝ)
    (hB:0≤B) (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j:ι) : |pairMean μ Z i j|≤B^2 := by
  apply integral_abs_bound
  filter_upwards [hb i,hb j] with ω hi hj
  rw [abs_mul]
  nlinarith [abs_nonneg (Z i ω),abs_nonneg (Z j ω)]

lemma four_abs_bound (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ) (B:ℝ)
    (hB:0≤B) (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j k l:ι) :
    |∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ|≤B^4 := by
  apply integral_abs_bound
  filter_upwards [hb i,hb j,hb k,hb l] with ω hi hj hk hl
  have hp : |Z i ω*Z j ω|≤B^2 := by rw [abs_mul];nlinarith [abs_nonneg (Z i ω),abs_nonneg (Z j ω)]
  have hq : |Z k ω*Z l ω|≤B^2 := by rw [abs_mul];nlinarith [abs_nonneg (Z k ω),abs_nonneg (Z l ω)]
  rw [show Z i ω*Z j ω*Z k ω*Z l ω=(Z i ω*Z j ω)*(Z k ω*Z l ω) by ring,abs_mul]
  nlinarith [abs_nonneg (Z i ω*Z j ω),abs_nonneg (Z k ω*Z l ω)]

lemma cumulant_abs_bound (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ) (B:ℝ)
    (hB:0≤B) (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j k l:ι) : |cumulant4 μ Z i j k l|≤4*B^4 := by
  have hp (a b c d:ι) : |pairMean μ Z a b*pairMean μ Z c d|≤B^4 := by
    rw [abs_mul]
    nlinarith [pair_abs_bound μ Z B hB hb a b,pair_abs_bound μ Z B hB hb c d,
      abs_nonneg (pairMean μ Z a b),abs_nonneg (pairMean μ Z c d),sq_nonneg B]
  have h4:=four_abs_bound μ Z B hB hb i j k l
  unfold cumulant4
  calc
    _ ≤ |(∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)-pairMean μ Z i j*pairMean μ Z k l-
        pairMean μ Z i k*pairMean μ Z j l| +|pairMean μ Z i l*pairMean μ Z j k| := abs_sub _ _
    _ ≤ (|(∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ)-pairMean μ Z i j*pairMean μ Z k l| +
        |pairMean μ Z i k*pairMean μ Z j l|)+|pairMean μ Z i l*pairMean μ Z j k| :=
      add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ ((|∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ| +|pairMean μ Z i j*pairMean μ Z k l|)+
        |pairMean μ Z i k*pairMean μ Z j l|)+|pairMean μ Z i l*pairMean μ Z j k| := by
      gcongr
      exact abs_sub _ _
    _ ≤ _ := by linarith [hp i j k l,hp i k j l,hp i l j k]

lemma cut_or_connected (G:ι→ι→Prop) (hG:∀⦃i j⦄,G i j→G j i) (i j k l:ι) :
    FourCut G i j k l ∨ DenseTreeCount.Connected4 G i j k l := by
  have hji : G j i↔G i j := ⟨fun h=>hG h,fun h=>hG h⟩
  have hki : G k i↔G i k := ⟨fun h=>hG h,fun h=>hG h⟩
  have hli : G l i↔G i l := ⟨fun h=>hG h,fun h=>hG h⟩
  have hkj : G k j↔G j k := ⟨fun h=>hG h,fun h=>hG h⟩
  have hlj : G l j↔G j l := ⟨fun h=>hG h,fun h=>hG h⟩
  have hlk : G l k↔G k l := ⟨fun h=>hG h,fun h=>hG h⟩
  simp only [FourCut,DenseTreeCount.Connected4,DenseTreeCount.Grow4,hji,hki,hli,hkj,hlj,hlk]
  by_cases h1:G i j <;> by_cases h2:G i k <;> by_cases h3:G i l <;>
    by_cases h4:G j k <;> by_cases h5:G j l <;> by_cases h6:G k l <;> simp_all

lemma cumulant_connected_bound (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ)
    (D:DepGraph Z μ) (hz:∀i,∫ω,Z i ω∂μ=0) (B:ℝ) (hB:0≤B)
    (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j k l:ι) :
    |cumulant4 μ Z i j k l| ≤4*B^4*(if DenseTreeCount.Connected4 D.G i j k l then 1 else 0) := by
  classical
  by_cases hc:DenseTreeCount.Connected4 D.G i j k l
  · simpa [hc] using cumulant_abs_bound μ Z B hB hb i j k l
  · have hcut:FourCut D.G i j k l :=
      (cut_or_connected D.G (fun {i j} h=>D.symm i j h) i j k l).resolve_right hc
    simp [hc,cumulant_of_cut μ Z D hz i j k l hcut]

lemma pair_graph_bound (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ)
    (D:DepGraph Z μ) (hz:∀i,∫ω,Z i ω∂μ=0) (B:ℝ) (hB:0≤B)
    (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j:ι) :
    |pairMean μ Z i j| ≤B^2*(if D.G i j then 1 else 0) := by
  classical
  by_cases hg:D.G i j
  · simpa [hg] using pair_abs_bound μ Z B hB hb i j
  · simp [hg,pairMean_zero μ Z D hz i j hg]

lemma pair_bound_ae (μ:Measure Ω) (Z:ι→Ω→ℝ) (B:ℝ) (hB:0≤B)
    (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j:ι) : ∀ᵐω∂μ,|Z i ω*Z j ω|≤B^2 := by
  filter_upwards [hb i,hb j] with ω hi hj
  rw [abs_mul]
  nlinarith [abs_nonneg (Z i ω),abs_nonneg (Z j ω)]

lemma pair_memLp (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ)
    (hmeas:∀i,Measurable (Z i)) (B:ℝ) (hB:0≤B) (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j:ι) :
    MemLp (fun ω=>Z i ω*Z j ω) 2 μ :=
  SampleCompletion.bounded_memLp μ _ ((hmeas i).mul (hmeas j)) (B^2) (pair_bound_ae μ Z B hB hb i j) 2

lemma covariance_pair_decomposition (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ)
    (hmeas:∀i,Measurable (Z i)) (B:ℝ) (hB:0≤B) (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B) (i j k l:ι) :
    ProbabilityTheory.covariance (fun ω=>Z i ω*Z j ω) (fun ω=>Z k ω*Z l ω) μ=
      cumulant4 μ Z i j k l+pairMean μ Z i k*pairMean μ Z j l+pairMean μ Z i l*pairMean μ Z j k := by
  rw [ProbabilityTheory.covariance_eq_sub (pair_memLp μ Z hmeas B hB hb i j)
    (pair_memLp μ Z hmeas B hB hb k l)]
  have he : (∫ω,(Z i ω*Z j ω)*(Z k ω*Z l ω)∂μ)=(∫ω,Z i ω*Z j ω*Z k ω*Z l ω∂μ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω=>by ring
  change (∫ω,(Z i ω*Z j ω)*(Z k ω*Z l ω)∂μ)-pairMean μ Z i j*pairMean μ Z k l=_
  rw [he]
  unfold cumulant4
  ring

lemma variance_expansion (μ:Measure Ω) [IsProbabilityMeasure μ] (Z:ι→Ω→ℝ)
    (hmeas:∀i,Measurable (Z i)) (B:ℝ) (hB:0≤B) (hb:∀i,∀ᵐω∂μ,|Z i ω|≤B)
    (A:ι→ι→ℝ) :
    ProbabilityTheory.variance (fun ω=>∑i,∑j,A i j*Z i ω*Z j ω) μ=
      ∑i,∑j,∑k,∑l,A i j*A k l*(cumulant4 μ Z i j k l+
        pairMean μ Z i k*pairMean μ Z j l+pairMean μ Z i l*pairMean μ Z j k) := by
  classical
  let Y (p:ι×ι) (ω:Ω) := A p.1 p.2*(Z p.1 ω*Z p.2 ω)
  have hY (p:ι×ι) : MemLp (Y p) 2 μ := (pair_memLp μ Z hmeas B hB hb p.1 p.2).const_mul _
  have he : (fun ω=>∑i,∑j,A i j*Z i ω*Z j ω)=(fun ω=>∑p:ι×ι,Y p ω) := by
    funext ω
    simp only [Fintype.sum_prod_type,Y]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,ProbabilityTheory.variance_fun_sum hY]
  simp only [Fintype.sum_prod_type,Y]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [ProbabilityTheory.covariance_const_mul_left,ProbabilityTheory.covariance_const_mul_right,
    covariance_pair_decomposition μ Z hmeas B hB hb i j k l]
  ring

end
end AronowAudit.P011.DenseCumulant

