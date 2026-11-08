import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: refutation of `AronowAudit.P001.printed_finite_variance_mean_hadamard` (P001-T118)

Record 17 of group P001a: P001-T118 / `AronowAudit.P001.printed_finite_variance_mean_hadamard`;
resolution `refute`. Frozen contract (P001_Foundations.lean:6993): for every probability law
`ν` on `ℝ` with `id ∈ L²(ν)`, the mean functional `cdfMeanFunctional` is Hadamard
differentiable (`HadamardAt`, :421) at the embedded CDF of `ν` in `KolmogorovSpace` (sup
norm), on the domain of finite-second-moment CDFs, with all bounded tangent directions.

`Target` is the negation of exactly that contract; the `example` checks by `Iff.rfl` that it
is the negation of the frozen declaration's type.

Witness (paper proof, record 17): `ν₀ = (δ₀ + δ₂)/2` (mean `1`, variance `1`). For
`r_n = n + 2`, `a_n = r_n⁻³`, `t_n = r_n⁻²`, the finite-support contamination
`ν_n = (1 - a_n) ν₀ + a_n δ_{r_n + 1}` has mean `1 + t_n`, and its CDF differs from that of
`ν₀` by at most `a_n` in sup norm. The directions `h_n = t_n⁻¹ (F_n - F)` have norm
`≤ 1/r_n → 0`, `F + t_n h_n = F_n` lies in the domain, and every difference quotient of the
mean equals `1`; a Hadamard derivative would force the limit `L 0 = 0`.
The sorry-bearing `geometric_mean_perturbation` (:1043) is not used.

Nodes: `N1` (the functional evaluates the mean of the actual law; CDF uniqueness), `N2` (the
contamination laws), `N3` (the sup-norm bound). The assembly is fully proved.
Writers prove `theorem nk_proof : Nk` in `AronowAudit/P001/Wave1/MeanHadamard/Nk.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MeanHadamard

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_finite_variance_mean_hadamard`. -/
def Target : Prop :=
  ¬ ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    ∃ L : KolmogorovSpace →L[ℝ] ℝ,
      HadamardAt {F | finiteSecondCDF F} Set.univ cdfMeanFunctional
        (kolmogorovEmbed (cdf ν id)) L

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P001.printed_finite_variance_mean_hadamard) :=
  Iff.rfl

/-- The base law `ν₀ = (δ₀ + δ₂)/2`. -/
def baseLaw : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (2 : ℝ)

/-- `r_n = n + 2`. -/
def contR (n : ℕ) : ℝ := (n : ℝ) + 2

/-- The contamination weight `a_n = r_n⁻³`. -/
def contA (n : ℕ) : ℝ := (contR n)⁻¹ ^ 3

/-- The scale `t_n = r_n⁻²`. -/
def contT (n : ℕ) : ℝ := (contR n)⁻¹ ^ 2

/-- The contaminated law `ν_n = (1 - a_n) ν₀ + a_n δ_{r_n + 1}`. -/
def contam (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - contA n) • baseLaw + ENNReal.ofReal (contA n) • Measure.dirac (contR n + 1)

/-- The embedded base CDF `F`. -/
def baseCDF : KolmogorovSpace := kolmogorovEmbed (cdf baseLaw id)

/-- The embedded contaminated CDF `F_n`. -/
def contCDF (n : ℕ) : KolmogorovSpace := kolmogorovEmbed (cdf (contam n) id)

/-- The tangent directions `h_n = t_n⁻¹ (F_n - F)`. -/
def dirSeq (n : ℕ) : KolmogorovSpace := (contT n)⁻¹ • (contCDF n - baseCDF)

/-- **Node N1** (paper proof, record 17, third paragraph: "A probability law on ℝ is
determined by its CDF ... Hence the law chosen inside cdfMeanFunctional at each embedded
CDF must equal its actual law ... with no ambiguity from Classical.choose"). For every
probability law with finite second moment, its embedded CDF is in the domain and the
functional returns its mean.
Suggested route: the witness `ν` itself for `finiteSecondCDF`, with the proved
`kolmogorov_embedding_preserves_cdf_supporting` (:6775); for the value, unfold
`cdfMeanFunctional` (`dif_pos`), take `h.choose_spec`, show
`ProbabilityTheory.cdf h.choose = ProbabilityTheory.cdf ν` (`StieltjesFunction.ext`,
`ProbabilityTheory.cdf_eq_real`/`cdf_eq_toReal`, `prob`, `Set.Iic`) and conclude with
`MeasureTheory.Measure.eq_of_cdf`. -/
def N1 : Prop :=
  ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    finiteSecondCDF (kolmogorovEmbed (cdf ν id)) ∧
      cdfMeanFunctional (kolmogorovEmbed (cdf ν id)) = mean ν id

/-- **Node N2** (paper proof, record 17, first two paragraphs: "Its nonnegative masses sum
to one, so it is a probability law. E_ν[X]=(0+2)/2=1, E_ν[X²]=(0+4)/2=2 ... Since r_n≥2,
0<a_n≤1/8<1. Thus ν_n is a probability measure on the three finite points 0,2,r_n+1; all
its second moments are finite. Its mean is (1-a_n)·1+a_n(r_n+1)=1+a_nr_n=1+t_n").
Suggested route: `Measure.add_apply`, `Measure.smul_apply`, `measure_univ` of Dirac masses,
`ENNReal.ofReal_add` (`0 ≤ a_n ≤ 1`); `MemLp` on a finite sum of Diracs
(`memLp_add_measure`/`MemLp.smul_measure`, `memLp_dirac`-type lemmas or
`MemLp.of_bound` on the a.s. bounded identity); `integral_add_measure`,
`integral_smul_measure`, `integral_dirac`; field arithmetic `(1 - r⁻³) + r⁻³ (r + 1) = 1 + r⁻²`. -/
def N2 : Prop :=
  IsProbabilityMeasure baseLaw ∧ MemLp id 2 baseLaw ∧ mean baseLaw id = 1 ∧
    ∀ n : ℕ, IsProbabilityMeasure (contam n) ∧ MemLp id 2 (contam n) ∧
      mean (contam n) id = 1 + contT n

/-- **Node N3** (paper proof, record 17, second paragraph: "Its CDF is
F_n=(1-a_n)F+a_nH_{r_n+1} ... Therefore |F_n(x)-F(x)|≤a_n for every x, because both CDF
values in the difference H_z-F lie in [0,1] ... ‖h_n‖∞≤a_n/t_n=1/r_n"). Under `N2`, the
directions have sup norm at most `1/r_n`.
Suggested route: `kolmogorov_embedding_preserves_cdf_supporting` for both probability laws;
pointwise `cdf (contam n) id x - cdf baseLaw id x = a_n (1_{r_n+1 ≤ x} - cdf baseLaw id x)`
(`Measure.add_apply`, `Measure.smul_apply`, `ENNReal.toReal_add`, `ENNReal.toReal_ofReal`);
`lp.norm_le_of_forall_le` (`0 ≤ a_n`), `norm_smul`, `contA n / contT n = (contR n)⁻¹`. -/
def N3 : Prop :=
  N2 → ∀ n : ℕ, ‖dirSeq n‖ ≤ (contR n)⁻¹

theorem contR_pos (n : ℕ) : 0 < contR n := by unfold contR; positivity

theorem contT_pos (n : ℕ) : 0 < contT n := by
  unfold contT; have := contR_pos n; positivity

theorem tendsto_contR_inv : Tendsto (fun n : ℕ => (contR n)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => contR n) atTop atTop := by
    unfold contR
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

theorem tendsto_contT : Tendsto contT atTop (𝓝 0) := by
  have h := tendsto_contR_inv.pow 2
  rw [zero_pow two_ne_zero] at h
  exact h

/-- `F + t_n h_n = F_n`. -/
theorem base_add_dir (n : ℕ) : baseCDF + contT n • dirSeq n = contCDF n := by
  simp only [dirSeq, smul_smul, mul_inv_cancel₀ (contT_pos n).ne', one_smul,
    add_sub_cancel]

/-- The nodes suffice: at the zero tangent, the admissible sequence `t_n`, `h_n` has every
mean difference quotient equal to `1`, while `HadamardAt` forces the limit `L 0 = 0`. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) : Target := by
  intro H
  have hp0 : IsProbabilityMeasure baseLaw := h2.1
  obtain ⟨L, hL⟩ := H baseLaw h2.2.1
  have hh : Tendsto dirSeq atTop (𝓝 0) :=
    squeeze_zero_norm (h3 h2) tendsto_contR_inv
  have hmem : ∀ n, baseCDF + contT n • dirSeq n ∈ {F | finiteSecondCDF F} := by
    intro n
    rw [base_add_dir]
    have := (h2.2.2.2 n).1
    exact (h1 (contam n) (h2.2.2.2 n).2.1).1
  have key := hL 0 (Set.mem_univ _) contT dirSeq contT_pos tendsto_contT hh hmem
  have hq : ∀ n : ℕ, (cdfMeanFunctional (baseCDF + contT n • dirSeq n) -
      cdfMeanFunctional baseCDF) / contT n = 1 := by
    intro n
    rw [base_add_dir]
    have := (h2.2.2.2 n).1
    have e1 : cdfMeanFunctional (contCDF n) = 1 + contT n :=
      ((h1 (contam n) (h2.2.2.2 n).2.1).2).trans (h2.2.2.2 n).2.2
    have e0 : cdfMeanFunctional baseCDF = 1 :=
      ((h1 baseLaw h2.2.1).2).trans h2.2.2.1
    rw [e1, e0, add_sub_cancel_left, div_self (contT_pos n).ne']
  have key' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (L 0)) := Tendsto.congr hq key
  rw [map_zero] at key'
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds key')

/-- Nonvacuity record: the base law satisfies the contract's hypotheses (probability law
with finite second moment), with positive variance (mean `1`, second moment `2`). -/
example (h2 : N2) : IsProbabilityMeasure baseLaw ∧ MemLp id 2 baseLaw ∧ mean baseLaw id = 1 :=
  ⟨h2.1, h2.2.1, h2.2.2.1⟩

end

end AronowAudit.P001.Wave1.MeanHadamard
