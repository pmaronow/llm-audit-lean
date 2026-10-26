/-
Local file of llm-audit-lean, not taken from Causalean; it builds on the vendored Causalean code in this directory tree.
-/
import AronowAudit.External.Causalean.Mathlib.Probability.SteinMethod.DepGraphCLT

/-! Local a.e.-bounded adapter for the licensed CausalSmith neighborhood-product variance
bound. Coordinatewise clipping preserves the entire graph independence and statistic a.e. -/
namespace Causalean.Mathlib.Probability.SteinMethod
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 500000

theorem DepGraph.var_nbhd_prod_le_ae
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} (D : DepGraph X μ)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i,∀ᵐ ω ∂μ,|X i ω|≤B)
    {m : ℕ} (hdeg : ∀ i,(D.nbhd i).card≤m) :
    variance (fun ω=>∑ i,X i ω*∑ k∈D.nbhd i,X k ω) μ≤
      2*(m:ℝ)^5*(Fintype.card ι:ℝ)*B^4 := by
  classical
  let Y : ι→Ω→ℝ := fun i ω=>max (-B) (min (X i ω) B)
  have hYbound (i : ι) (ω : Ω) : |Y i ω|≤B := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _,max_le (by linarith) (min_le_right _ _)⟩
  have hYae (i : ι) : Y i=ᵐ[μ]X i := by
    filter_upwards [hbound i] with ω hω
    dsimp [Y]
    rw [min_eq_left (abs_le.mp hω).2,max_eq_right (abs_le.mp hω).1]
  let DY : DepGraph Y μ := {
    G:=D.G
    decG:=D.decG
    refl:=D.refl
    symm:=D.symm
    meas:=fun i=>measurable_const.max ((D.meas i).min measurable_const)
    indep:=by
      intro A C hAC
      apply (D.indep A C hAC).congr
      · filter_upwards [ae_all_iff.2 (fun i:A=>(hYae i).symm)] with ω hω
        exact funext hω
      · filter_upwards [ae_all_iff.2 (fun i:C=>(hYae i).symm)] with ω hω
        exact funext hω }
  have hs : (fun ω=>∑ i,Y i ω*∑ k∈DY.nbhd i,Y k ω)=ᵐ[μ]
      (fun ω=>∑ i,X i ω*∑ k∈D.nbhd i,X k ω) := by
    filter_upwards [ae_all_iff.2 hYae] with ω hω
    apply Finset.sum_congr rfl
    intro i _
    rw [hω i]
    congr 1
    exact Finset.sum_congr rfl (fun k _=>hω k)
  rw [←variance_congr hs]
  exact DY.var_nbhd_prod_le hB hYbound hdeg

end
end Causalean.Mathlib.Probability.SteinMethod
