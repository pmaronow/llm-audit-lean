/-
Local file of llm-audit-lean, not taken from Causalean; it builds on the vendored Causalean code in this directory tree.
-/
import AronowAudit.External.Causalean.Mathlib.Probability.SteinMethod.StandardizedDepGraphCLT

/-!
An almost-everywhere bounded form of the licensed CausalSmith dependency-graph CLT.
A common a.e. bound is converted to a pointwise bound by coordinatewise clipping;
the original means, second moments, joint independence and laws are preserved
a.e.
-/

namespace Causalean.Mathlib.Probability.SteinMethod
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 500000

/-- The bounded-degree CLT with the usual common almost-everywhere summand
bound. The graph retains independence of every two separated finite families. -/
theorem bounded_degree_dependency_clt_ae
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (Dep : ∀ n, DepGraph (X n) (μ n))
    (Dmax : ℕ) (hdeg : ∀ n i, ((Dep n).nbhd i).card ≤ Dmax)
    (M : ℝ) (hbound : ∀ n i, ∀ᵐ ω ∂μ n, |X n i ω| ≤ M)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = v n)
    (c : ℝ) (hc : 0 < c)
    (hvc : ∀ᶠ n in atTop, c * (Fintype.card (ι n) : ℝ) ≤ v n)
    (hcard : Tendsto (fun n => Fintype.card (ι n)) atTop atTop)
    (s : ℝ) :
    Tendsto (fun n =>
        ((μ n).map (fun ω => depSum (X n) ω / Real.sqrt (v n))).real (Set.Iic s))
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  let R := max |M| 1
  have hR : 0 ≤ R := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  let Y : ∀ n, ι n → Ω n → ℝ := fun n i ω => max (-R) (min (X n i ω) R)
  have hYbound (n : ℕ) (i : ι n) (ω : Ω n) : |Y n i ω| ≤ R := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _,max_le (by linarith) (min_le_right _ _)⟩
  have hYae (n : ℕ) (i : ι n) : Y n i =ᵐ[μ n] X n i := by
    filter_upwards [hbound n i] with ω hω
    have hω' : |X n i ω| ≤ R := hω.trans ((le_abs_self M).trans (le_max_left _ _))
    dsimp [Y]
    rw [min_eq_left (abs_le.mp hω').2,max_eq_right (abs_le.mp hω').1]
  have hsum (n : ℕ) : depSum (Y n) =ᵐ[μ n] depSum (X n) := by
    filter_upwards [ae_all_iff.2 (hYae n)] with ω hω
    exact Finset.sum_congr rfl (fun i _ => hω i)
  let DepY : ∀ n, DepGraph (Y n) (μ n) := fun n => {
    G := (Dep n).G
    decG := (Dep n).decG
    refl := (Dep n).refl
    symm := (Dep n).symm
    meas := fun i => measurable_const.max (((Dep n).meas i).min measurable_const)
    indep := by
      intro A B hAB
      apply ((Dep n).indep A B hAB).congr
      · filter_upwards [ae_all_iff.2 (fun i : A => (hYae n i).symm)] with ω hω
        exact funext hω
      · filter_upwards [ae_all_iff.2 (fun i : B => (hYae n i).symm)] with ω hω
        exact funext hω }
  have hdegY (n : ℕ) (i : ι n) : ((DepY n).nbhd i).card ≤ Dmax := hdeg n i
  have hmeanY (n : ℕ) (i : ι n) : ∫ ω, Y n i ω ∂(μ n) = 0 :=
    (integral_congr_ae (hYae n i)).trans (hmean n i)
  have hvY (n : ℕ) : ∫ ω, (depSum (Y n) ω)^2 ∂(μ n) = v n :=
    (integral_congr_ae ((hsum n).mono (fun _ h => congrArg (fun x : ℝ => x^2) h))).trans (hv n)
  have hlim := bounded_degree_dependency_clt μ Y DepY Dmax hdegY R hR hYbound hmeanY v hvY
    c hc hvc hcard s
  exact hlim.congr (fun n => congrArg (fun ν : Measure ℝ => ν.real (Set.Iic s))
    (Measure.map_congr ((hsum n).mono (fun _ h => congrArg (fun x : ℝ => x/Real.sqrt (v n)) h))))

end
end Causalean.Mathlib.Probability.SteinMethod
