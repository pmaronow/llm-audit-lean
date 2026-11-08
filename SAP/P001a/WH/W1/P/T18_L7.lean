import SAP.P001a.WH.W1.Leaves
import AronowAudit.P015.P015_ConvergenceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

universe u v

namespace SAP.P001a.WH.W1.P.T18_L7

lemma cp_iff_eventually_small {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (f : ℕ → Ω → E) (c : E) :
    CP μ f c ↔ ∀ ε > 0, ∀ δ > 0, ∀ᶠ n in atTop,
      prob μ {ω | ε ≤ dist (f n ω) c} < δ := by
  simp only [CP]
  constructor
  · intro h ε hε δ hδ
    exact (tendsto_order.1 (h ε hε)).2 δ hδ
  · intro h ε hε
    apply tendsto_order.2
    constructor
    · intro a ha
      refine Eventually.of_forall ?_
      intro n
      have hp : 0 ≤ prob μ {ω | ε ≤ dist (f n ω) c} := by
        simp [prob]
      exact lt_of_lt_of_le ha hp
    · intro δ hδ
      exact h ε hε δ hδ

lemma prob_union_le {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Set Ω) : prob μ (A ∪ B) ≤ prob μ A + prob μ B := by
  simpa [prob, Measure.real] using (measureReal_union_le (μ := μ) A B)

lemma prob_mono {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {A B : Set Ω} (h : A ⊆ B) : prob μ A ≤ prob μ B := by
  simpa [prob, Measure.real] using (measureReal_mono h (measure_ne_top μ B))

lemma cp_matrix_entry {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (M : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ)
    [IsFiniteMeasure μ] (A : Matrix (Fin p) (Fin p) ℝ) (hM : CP μ M A) (j k : Fin p) :
    CP μ (fun n ω => M n ω j k) (A j k) := by
  apply (cp_iff_eventually_small μ _ _).2
  intro ε hε δ hδ
  have h := (cp_iff_eventually_small μ M A).1 hM ε hε δ hδ
  filter_upwards [h] with n hn
  have hsub : {ω | ε ≤ dist (M n ω j k) (A j k)} ⊆
      {ω | ε ≤ dist (M n ω) A} := by
    intro ω hω
    have hc : dist (M n ω j k) (A j k) ≤ dist (M n ω) A := by
      exact (dist_le_pi_dist ((M n ω) j) (A j) k).trans
        (dist_le_pi_dist (M n ω) A j)
    exact le_trans hω hc
  have hm := prob_mono μ hsub
  exact lt_of_le_of_lt hm hn

lemma cp_real_to_tendstoInMeasure {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (c : ℝ)
    (h : CP μ f c) : TendstoInMeasure μ f atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  simpa [prob, Measure.real] using h ε hε

lemma tendstoInMeasure_to_cp_real {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (c : ℝ)
    (h : TendstoInMeasure μ f atTop (fun _ => c)) : CP μ f c := by
  apply (cp_iff_eventually_small μ f c).2
  intro ε hε δ hδ
  have h' := (tendstoInMeasure_iff_measureReal_dist.mp h) ε hε
  exact (tendsto_order.1 h').2 δ hδ

lemma tight_mul_cp_zero {Ω : Type u} {E : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → E) (y : ℕ → Ω → ℝ)
    (ht : WholeTight μ x) (hy : CP μ y 0) (hyn : ∀ n ω, 0 ≤ y n ω) :
    CP μ (fun n ω => ‖x n ω‖ ^ 2 * y n ω) 0 := by
  apply (cp_iff_eventually_small μ _ 0).2
  intro ε hε δ hδ
  obtain ⟨C, hC, htail⟩ := ht (δ / 2) (by positivity)
  have hyt := (cp_iff_eventually_small μ y 0).1 hy
      (ε / C ^ 2) (by positivity) (δ / 2) (by positivity)
  have hsub (n : ℕ) :
      {ω | ε ≤ dist (‖x n ω‖ ^ 2 * y n ω) 0} ⊆
        {ω | C < ‖x n ω‖} ∪ {ω | ε / C ^ 2 ≤ dist (y n ω) 0} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le] at hn
    have hx : ‖x n ω‖ ≤ C := hn.1
    have hy' : dist (y n ω) 0 < ε / C ^ 2 := hn.2
    have hprod : 0 ≤ ‖x n ω‖ ^ 2 * y n ω := mul_nonneg (sq_nonneg _) (hyn n ω)
    have hω' : ε ≤ ‖x n ω‖ ^ 2 * y n ω := by
      simpa [Real.dist_eq, abs_of_nonneg hprod, abs_of_nonneg (hyn n ω)] using hω
    have hya : |y n ω| < ε / C ^ 2 := by simpa [Real.dist_eq] using hy'
    have hlt : ‖x n ω‖ ^ 2 * y n ω < ε := by
      calc
        _ ≤ C ^ 2 * |y n ω| := by
          rw [abs_of_nonneg (hyn n ω)]
          exact mul_le_mul_of_nonneg_right
            ((sq_le_sq₀ (norm_nonneg _) (le_of_lt hC)).2 hx) (hyn n ω)
        _ < ε := by
          have hC2 : 0 < C ^ 2 := sq_pos_of_pos hC
          calc
            C ^ 2 * |y n ω| < C ^ 2 * (ε / C ^ 2) := mul_lt_mul_of_pos_left hya hC2
            _ = ε := by field_simp
    exact (not_lt_of_ge hω') hlt
  filter_upwards [htail, hyt] with n hn ht2
  have hprob : prob μ {ω | ε ≤ dist (‖x n ω‖ ^ 2 * y n ω) 0} ≤
      prob μ {ω | C < ‖x n ω‖} + prob μ {ω | ε / C ^ 2 ≤ dist (y n ω) 0} :=
    (prob_mono μ (hsub n)).trans (prob_union_le μ _ _)
  have hsum : prob μ {ω | C < ‖x n ω‖} +
      prob μ {ω | ε / C ^ 2 ≤ dist (y n ω) 0} < δ := by linarith
  exact lt_of_le_of_lt hprob hsum

lemma pi_norm_sq_le_sum_sq {p : ℕ} (x : Fin p → ℝ) :
    ‖x‖ ^ 2 ≤ ∑ j, (x j) ^ 2 := by
  let s := ∑ j : Fin p, (x j) ^ 2
  have hs : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
  have hcoord (j : Fin p) : |x j| ≤ Real.sqrt s := by
    apply Real.le_sqrt_of_sq_le
    have hsingle := Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
    simpa [sq_abs] using hsingle
  have hnorm : ‖x‖ ≤ Real.sqrt s := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg s)).2
    intro j
    simpa [Real.norm_eq_abs] using hcoord j
  have hsq := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg s)).2 hnorm
  simpa [s, Real.sq_sqrt hs] using hsq

lemma coord_abs_le_norm {p : ℕ} (x : Fin p → ℝ) (j : Fin p) :
    |x j| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm x j

lemma dotProduct_abs_le_pi {p : ℕ} (x y : Fin p → ℝ) :
    |x ⬝ᵥ y| ≤ (p : ℝ) * ‖x‖ * ‖y‖ := by
  rw [dotProduct]
  calc
    |∑ j, x j * y j| ≤ ∑ j, |x j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin p, ‖x‖ * ‖y‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (coord_abs_le_norm x j) (coord_abs_le_norm y j)
        (abs_nonneg _) (norm_nonneg _)
    _ = (p : ℝ) * ‖x‖ * ‖y‖ := by simp [Finset.sum_const, Fintype.card_fin, mul_assoc]

lemma normalized_cauchy {I : Type u} (s : Finset I)
    (f g : I → ℝ) (t : ℝ) (ht : 0 < t) :
    ((∑ i ∈ s, f i * g i) / t) ^ 2 ≤
      ((∑ i ∈ s, f i ^ 2) / t) * ((∑ i ∈ s, g i ^ 2) / t) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s f g
  rw [div_pow]
  calc
    (∑ i ∈ s, f i * g i) ^ 2 / t ^ 2 ≤
        ((∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2) / t ^ 2 :=
      div_le_div_of_nonneg_right hc (sq_nonneg t)
    _ = ((∑ i ∈ s, f i ^ 2) / t) * ((∑ i ∈ s, g i ^ 2) / t) := by
      field_simp [ne_of_gt ht]

def gramTraceEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := ∑ j, wholeEmpiricalQ Z n ω j j

def gramTracePop {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) : ℝ := ∑ j, wholeQ μ (Z 0) j j

def trueMeatTraceEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j, wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω j j

def trueMeatTracePop {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) : ℝ :=
  ∑ j, wholeOmega μ (Z 0) (D 0) b j j

def rowNormEnergyEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, ‖Z i ω‖ ^ 2) / (n : ℝ)

def betaDiff {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) : Fin p → ℝ :=
  wholeBetaHat Z D n ω - b

def fitDelta {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
  Z i ω ⬝ᵥ betaDiff Z D b n ω

def perturbEnergyEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n,
    (fitDelta Z D b n ω i) ^ 2 * ‖Z i ω‖ ^ 2) / (n : ℝ)

def trueMeatDiagEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) (j : Fin p) : ℝ :=
  (∑ i ∈ Finset.range n,
    (wholeResidual (Z i) (D i) b ω) ^ 2 * (Z i ω j) ^ 2) / (n : ℝ)

def quadMeatDiagEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) (j : Fin p) : ℝ :=
  (∑ i ∈ Finset.range n,
    (fitDelta Z D b n ω i) ^ 2 * (Z i ω j) ^ 2) / (n : ℝ)

def crossMeatEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω)
    (j k : Fin p) : ℝ :=
  (∑ i ∈ Finset.range n,
    wholeResidual (Z i) (D i) b ω * fitDelta Z D b n ω i *
      Z i ω j * Z i ω k) / (n : ℝ)

def quadMeatEmp {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω)
    (j k : Fin p) : ℝ :=
  (∑ i ∈ Finset.range n,
    (fitDelta Z D b n ω i) ^ 2 * Z i ω j * Z i ω k) / (n : ℝ)

lemma gramTrace_eq_coordSum {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (n : ℕ) (ω : Ω) :
    gramTraceEmp Z n ω =
      (∑ i ∈ Finset.range n, ∑ j : Fin p, (Z i ω j) ^ 2) / (n : ℝ) := by
  unfold gramTraceEmp wholeEmpiricalQ
  simp_rw [pow_two]
  calc
    (∑ j, (∑ i ∈ Finset.range n, Z i ω j * Z i ω j) / (n : ℝ)) =
        (∑ j, ∑ i ∈ Finset.range n, Z i ω j * Z i ω j) / (n : ℝ) := by
      rw [← Finset.sum_div]
    _ = (∑ i ∈ Finset.range n, ∑ j, Z i ω j * Z i ω j) / (n : ℝ) := by
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_div]

lemma gramTrace_cp {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (hgram : WholeGramLimits μ Z D b) :
    CP μ (gramTraceEmp Z) (gramTracePop μ Z) := by
  have hentry : ∀ j : Fin p,
      TendstoInMeasure μ (fun n ω => wholeEmpiricalQ Z n ω j j) atTop
        (fun _ => wholeQ μ (Z 0) j j) := by
    intro j
    exact cp_real_to_tendstoInMeasure μ _ _
      (cp_matrix_entry μ (wholeEmpiricalQ Z) (wholeQ μ (Z 0)) hgram.gram j j)
  apply tendstoInMeasure_to_cp_real μ _ _
  change TendstoInMeasure μ (fun n ω => ∑ j, wholeEmpiricalQ Z n ω j j) atTop
    (fun _ => ∑ j, wholeQ μ (Z 0) j j)
  exact AronowAudit.P015.ConvergenceCompletion.sum_limit μ
      (fun j n ω => wholeEmpiricalQ Z n ω j j)
      (fun j => wholeQ μ (Z 0) j j) hentry

lemma trueMeatTrace_cp {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (hgram : WholeGramLimits μ Z D b) :
    CP μ (trueMeatTraceEmp Z D b) (trueMeatTracePop μ Z D b) := by
  have hentry : ∀ j : Fin p,
      TendstoInMeasure μ
        (fun n ω => wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω j j)
        atTop (fun _ => wholeOmega μ (Z 0) (D 0) b j j) := by
    intro j
    exact cp_real_to_tendstoInMeasure μ _ _
      (cp_matrix_entry μ _ _ hgram.trueMeat j j)
  apply tendstoInMeasure_to_cp_real μ _ _
  change TendstoInMeasure μ
    (fun n ω => ∑ j, wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω j j) atTop
    (fun _ => ∑ j, wholeOmega μ (Z 0) (D 0) b j j)
  exact AronowAudit.P015.ConvergenceCompletion.sum_limit μ
      (fun j n ω => wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω j j)
      (fun j => wholeOmega μ (Z 0) (D 0) b j j) hentry

lemma rowNormEnergy_le_gramTrace {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (n : ℕ) (ω : Ω) (hn : 0 < n) :
    rowNormEnergyEmp Z n ω ≤ gramTraceEmp Z n ω := by
  have hsum : (∑ i ∈ Finset.range n, ‖Z i ω‖ ^ 2) ≤
      ∑ i ∈ Finset.range n, ∑ j : Fin p, (Z i ω j) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact pi_norm_sq_le_sum_sq (Z i ω)
  rw [rowNormEnergyEmp, gramTrace_eq_coordSum]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n)

lemma rowNormSq_le_n_maxRow {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (n : ℕ) (ω : Ω) (hn : 0 < n)
    (i : ℕ) (hi : i ∈ Finset.range n) :
    ‖Z i ω‖ ^ 2 ≤ (n : ℝ) * wholeMaxRow Z n ω := by
  have hs := Finset.le_sup' (fun i => ‖Z i ω‖ ^ 2) hi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [wholeMaxRow, dif_pos hn]
  calc
    ‖Z i ω‖ ^ 2 ≤ (Finset.range n).sup' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
        (fun i => ‖Z i ω‖ ^ 2) := hs
    _ = (n : ℝ) * ((Finset.range n).sup'
        (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
        (fun i => ‖Z i ω‖ ^ 2) / (n : ℝ)) := by field_simp

lemma betaDiff_root_sq {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) :
    ‖wholeRootError Z D b n ω‖ ^ 2 =
      (n : ℝ) * ‖betaDiff Z D b n ω‖ ^ 2 := by
  have hnrm : ‖wholeRootError Z D b n ω‖ =
      Real.sqrt n * ‖betaDiff Z D b n ω‖ := by
    simp [wholeRootError, betaDiff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    ‖wholeRootError Z D b n ω‖ ^ 2 =
        (Real.sqrt n * ‖betaDiff Z D b n ω‖) ^ 2 := by rw [hnrm]
    _ = (Real.sqrt n) ^ 2 * ‖betaDiff Z D b n ω‖ ^ 2 := by ring
    _ = (n : ℝ) * ‖betaDiff Z D b n ω‖ ^ 2 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma wholeMaxRow_nonneg {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ wholeMaxRow Z n ω := by
  by_cases hn : 0 < n
  · simp only [wholeMaxRow, dif_pos hn]
    apply div_nonneg
    · have hzmem : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
      exact le_trans (sq_nonneg ‖Z 0 ω‖)
        (Finset.le_sup' (fun i => ‖Z i ω‖ ^ 2) hzmem)
    · positivity
  · simp [wholeMaxRow, hn]

lemma perturbEnergy_le_root_bound {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (hn : 0 < n) :
    perturbEnergyEmp Z D b n ω ≤
      (p : ℝ) ^ 2 * ‖wholeRootError Z D b n ω‖ ^ 2 *
        wholeMaxRow Z n ω * gramTraceEmp Z n ω := by
  let d := betaDiff Z D b n ω
  let M := wholeMaxRow Z n ω
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 ≤ M := wholeMaxRow_nonneg Z n ω
  have hG : rowNormEnergyEmp Z n ω ≤ gramTraceEmp Z n ω :=
    rowNormEnergy_le_gramTrace Z n ω hn
  have hterms (i : ℕ) (hi : i ∈ Finset.range n) :
      (fitDelta Z D b n ω i) ^ 2 * ‖Z i ω‖ ^ 2 ≤
        (p : ℝ) ^ 2 * ‖d‖ ^ 2 * ((n : ℝ) * M) * ‖Z i ω‖ ^ 2 := by
    have hdot := dotProduct_abs_le_pi (Z i ω) d
    have hdotAbsSq : |Z i ω ⬝ᵥ d| ^ 2 ≤ ((p : ℝ) * ‖Z i ω‖ * ‖d‖) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdot
    have hdotSq : (fitDelta Z D b n ω i) ^ 2 ≤
        ((p : ℝ) * ‖Z i ω‖ * ‖d‖) ^ 2 := by
      simpa only [fitDelta, betaDiff, d, sq_abs] using hdotAbsSq
    have hrow := rowNormSq_le_n_maxRow Z n ω hn i hi
    have hcoef : 0 ≤ (p : ℝ) ^ 2 * ‖d‖ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc
      _ ≤ ((p : ℝ) * ‖Z i ω‖ * ‖d‖) ^ 2 * ‖Z i ω‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hdotSq (sq_nonneg _)
      _ = (p : ℝ) ^ 2 * ‖d‖ ^ 2 * ‖Z i ω‖ ^ 2 * ‖Z i ω‖ ^ 2 := by ring
      _ ≤ (p : ℝ) ^ 2 * ‖d‖ ^ 2 * ((n : ℝ) * M) * ‖Z i ω‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hrow (sq_nonneg (‖Z i ω‖))
        calc
          _ = ((p : ℝ) ^ 2 * ‖d‖ ^ 2) * (‖Z i ω‖ ^ 2 * ‖Z i ω‖ ^ 2) := by ring
          _ ≤ ((p : ℝ) ^ 2 * ‖d‖ ^ 2) * (((n : ℝ) * M) * ‖Z i ω‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hmul hcoef
          _ = _ := by ring
  have hsum := Finset.sum_le_sum fun i hi => hterms i hi
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  rw [perturbEnergyEmp]
  have hfactor :
      (∑ i ∈ Finset.range n,
        (p : ℝ) ^ 2 * ‖d‖ ^ 2 * ((n : ℝ) * M) * ‖Z i ω‖ ^ 2) / (n : ℝ) =
        (p : ℝ) ^ 2 * ‖d‖ ^ 2 * (n : ℝ) * M * rowNormEnergyEmp Z n ω := by
    rw [rowNormEnergyEmp]
    simp_rw [← Finset.mul_sum]
    field_simp [ne_of_gt hnR]
  rw [hfactor] at hdiv
  have hroot := betaDiff_root_sq Z D b n ω
  have hcoefM : 0 ≤ (p : ℝ) ^ 2 * ((n : ℝ) * ‖d‖ ^ 2) * M := by
    positivity
  calc
    perturbEnergyEmp Z D b n ω ≤
        (p : ℝ) ^ 2 * ‖d‖ ^ 2 * (n : ℝ) * M * rowNormEnergyEmp Z n ω := hdiv
    _ ≤ (p : ℝ) ^ 2 * ((n : ℝ) * ‖d‖ ^ 2) * M * gramTraceEmp Z n ω := by
      have hh := mul_le_mul_of_nonneg_left hG hcoefM
      nlinarith [hh]
    _ = (p : ℝ) ^ 2 * ‖wholeRootError Z D b n ω‖ ^ 2 * M * gramTraceEmp Z n ω := by
      rw [hroot]

lemma gramTraceEmp_nonneg {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ gramTraceEmp Z n ω := by
  by_cases hn : 0 < n
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold gramTraceEmp wholeEmpiricalQ
    apply Finset.sum_nonneg
    intro j hj
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      nlinarith [sq_nonneg (Z i ω j)]
    · positivity
  · have hn0 : n = 0 := by omega
    subst n
    simp [gramTraceEmp, wholeEmpiricalQ]

lemma perturbEnergy_nonneg {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) : 0 ≤ perturbEnergyEmp Z D b n ω := by
  by_cases hn : 0 < n
  · unfold perturbEnergyEmp
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      positivity
    · positivity
  · have hn0 : n = 0 := by omega
    subst n
    simp [perturbEnergyEmp]

lemma trueMeatDiag_eq {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (j : Fin p) :
    trueMeatDiagEmp Z D b n ω j =
      wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω j j := by
  simp [trueMeatDiagEmp, wholeMeat, pow_two, mul_assoc]

lemma trueMeatTrace_eq_diagSum {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) :
    trueMeatTraceEmp Z D b n ω =
      ∑ j, trueMeatDiagEmp Z D b n ω j := by
  simp [trueMeatTraceEmp, trueMeatDiagEmp, wholeMeat, pow_two, mul_assoc]

lemma trueMeatDiag_nonneg {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (j : Fin p) (hn : 0 < n) :
    0 ≤ trueMeatDiagEmp Z D b n ω j := by
  unfold trueMeatDiagEmp
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    positivity
  · positivity

lemma trueMeatTrace_nonneg {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (hn : 0 < n) : 0 ≤ trueMeatTraceEmp Z D b n ω := by
  rw [trueMeatTrace_eq_diagSum]
  apply Finset.sum_nonneg
  intro j hj
  exact trueMeatDiag_nonneg Z D b n ω j hn

lemma trueMeatDiag_le_trace {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (j : Fin p) (hn : 0 < n) :
    trueMeatDiagEmp Z D b n ω j ≤ trueMeatTraceEmp Z D b n ω := by
  rw [trueMeatTrace_eq_diagSum]
  exact Finset.single_le_sum
    (fun k hk => trueMeatDiag_nonneg Z D b n ω k hn) (Finset.mem_univ j)

lemma quadMeatDiag_le_perturbEnergy {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (j : Fin p) (hn : 0 < n) :
    quadMeatDiagEmp Z D b n ω j ≤ perturbEnergyEmp Z D b n ω := by
  have hsum : (∑ i ∈ Finset.range n,
      (fitDelta Z D b n ω i) ^ 2 * (Z i ω j) ^ 2) ≤
      ∑ i ∈ Finset.range n, (fitDelta Z D b n ω i) ^ 2 * ‖Z i ω‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hc := coord_abs_le_norm (Z i ω) j
    have hc2 : |Z i ω j| ^ 2 ≤ ‖Z i ω‖ ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hc
    have hc2' : (Z i ω j) ^ 2 = |Z i ω j| ^ 2 := by simp
    rw [hc2']
    exact mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
  unfold quadMeatDiagEmp perturbEnergyEmp
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n)

lemma crossMeat_sq_le {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (j k : Fin p) (hn : 0 < n) :
    (crossMeatEmp Z D b n ω j k) ^ 2 ≤
      trueMeatTraceEmp Z D b n ω * perturbEnergyEmp Z D b n ω := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := normalized_cauchy (Finset.range n)
    (fun i => wholeResidual (Z i) (D i) b ω * Z i ω j)
    (fun i => fitDelta Z D b n ω i * Z i ω k) (n : ℝ) hnR
  have hdiag := trueMeatDiag_le_trace Z D b n ω j hn
  have hquad := quadMeatDiag_le_perturbEnergy Z D b n ω k hn
  have htrace0 := trueMeatTrace_nonneg Z D b n ω hn
  have hquad0 : 0 ≤ quadMeatDiagEmp Z D b n ω k := by
    unfold quadMeatDiagEmp
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      positivity
    · positivity
  have hcross : (crossMeatEmp Z D b n ω j k) ^ 2 ≤
      trueMeatDiagEmp Z D b n ω j * quadMeatDiagEmp Z D b n ω k := by
    simpa [crossMeatEmp, trueMeatDiagEmp, quadMeatDiagEmp,
      pow_two, mul_assoc, mul_left_comm, mul_comm] using hc
  have hprod : trueMeatDiagEmp Z D b n ω j * quadMeatDiagEmp Z D b n ω k ≤
      trueMeatTraceEmp Z D b n ω * perturbEnergyEmp Z D b n ω := by
    calc
      _ ≤ trueMeatTraceEmp Z D b n ω * quadMeatDiagEmp Z D b n ω k :=
        mul_le_mul_of_nonneg_right hdiag hquad0
      _ ≤ trueMeatTraceEmp Z D b n ω * perturbEnergyEmp Z D b n ω :=
        mul_le_mul_of_nonneg_left hquad htrace0
  exact hcross.trans hprod

lemma quadMeat_abs_le {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (j k : Fin p) (hn : 0 < n) :
    |quadMeatEmp Z D b n ω j k| ≤ perturbEnergyEmp Z D b n ω := by
  have hterm (i : ℕ) :
      |(fitDelta Z D b n ω i) ^ 2 * Z i ω j * Z i ω k| ≤
        (fitDelta Z D b n ω i) ^ 2 * ‖Z i ω‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hj := coord_abs_le_norm (Z i ω) j
    have hk := coord_abs_le_norm (Z i ω) k
    have hprod : |Z i ω j| * |Z i ω k| ≤ ‖Z i ω‖ * ‖Z i ω‖ :=
      mul_le_mul hj hk (abs_nonneg _) (norm_nonneg _)
    nlinarith [sq_nonneg (fitDelta Z D b n ω i), norm_nonneg (Z i ω)]
  have hsum := Finset.abs_sum_le_sum_abs
    (fun i => (fitDelta Z D b n ω i) ^ 2 * Z i ω j * Z i ω k) (Finset.range n)
  have hsum' : ∑ i ∈ Finset.range n,
      |(fitDelta Z D b n ω i) ^ 2 * Z i ω j * Z i ω k| ≤
      ∑ i ∈ Finset.range n, (fitDelta Z D b n ω i) ^ 2 * ‖Z i ω‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact hterm i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold quadMeatEmp perturbEnergyEmp
  rw [abs_div, abs_of_nonneg hnR.le]
  exact div_le_div_of_nonneg_right (hsum.trans hsum') (Nat.cast_nonneg n)

lemma fittedResidual_eq_true_sub_delta {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n i : ℕ) (ω : Ω) :
    D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω =
      wholeResidual (Z i) (D i) b ω - fitDelta Z D b n ω i := by
  change D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω =
    (D i ω - Z i ω ⬝ᵥ b) - Z i ω ⬝ᵥ (wholeBetaHat Z D n ω - b)
  have hs : Z i ω ⬝ᵥ wholeBetaHat Z D n ω =
      Z i ω ⬝ᵥ b + Z i ω ⬝ᵥ (wholeBetaHat Z D n ω - b) := by
    change (∑ l : Fin p, Z i ω l * wholeBetaHat Z D n ω l) =
      (∑ l : Fin p, Z i ω l * b l) +
        ∑ l : Fin p, Z i ω l * (wholeBetaHat Z D n ω l - b l)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hs]
  ring

lemma fittedMeat_entry_expansion {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (j k : Fin p) :
    wholeFittedMeat Z D n ω j k -
        wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω j k =
      -2 * crossMeatEmp Z D b n ω j k + quadMeatEmp Z D b n ω j k := by
  have hsum :
      (∑ i ∈ Finset.range n,
        (D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω) ^ 2 * Z i ω j * Z i ω k) =
      (∑ i ∈ Finset.range n,
        (wholeResidual (Z i) (D i) b ω) ^ 2 * Z i ω j * Z i ω k) -
        2 * (∑ i ∈ Finset.range n,
          (wholeResidual (Z i) (D i) b ω) * fitDelta Z D b n ω i * Z i ω j * Z i ω k) +
        (∑ i ∈ Finset.range n,
          (fitDelta Z D b n ω i) ^ 2 * Z i ω j * Z i ω k) := by
    calc
      _ = ∑ i ∈ Finset.range n,
          ((wholeResidual (Z i) (D i) b ω) ^ 2 * Z i ω j * Z i ω k -
            2 * ((wholeResidual (Z i) (D i) b ω) * fitDelta Z D b n ω i *
              Z i ω j * Z i ω k) +
            (fitDelta Z D b n ω i) ^ 2 * Z i ω j * Z i ω k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [fittedResidual_eq_true_sub_delta]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold wholeFittedMeat wholeMeat
  rw [hsum]
  simp only [crossMeatEmp, quadMeatEmp]
  ring

lemma perturbEnergy_le_root_bound_all {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) :
    perturbEnergyEmp Z D b n ω ≤
      (p : ℝ) ^ 2 * ‖wholeRootError Z D b n ω‖ ^ 2 *
        wholeMaxRow Z n ω * gramTraceEmp Z n ω := by
  by_cases hn : 0 < n
  · exact perturbEnergy_le_root_bound Z D b n ω hn
  · have hn0 : n = 0 := by omega
    subst n
    simp [perturbEnergyEmp, wholeMaxRow, gramTraceEmp, wholeEmpiricalQ,
      wholeRootError]

lemma matrixDiff_norm_le_energy {Ω : Type*} {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (n : ℕ) (ω : Ω) (hn : 0 < n) :
    ‖wholeFittedMeat Z D n ω -
      wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω‖ ≤
      2 * Real.sqrt (trueMeatTraceEmp Z D b n ω * perturbEnergyEmp Z D b n ω) +
        perturbEnergyEmp Z D b n ω := by
  let B := trueMeatTraceEmp Z D b n ω
  let Q := perturbEnergyEmp Z D b n ω
  let E := 2 * Real.sqrt (B * Q) + Q
  have hB : 0 ≤ B := trueMeatTrace_nonneg Z D b n ω hn
  have hQ : 0 ≤ Q := perturbEnergy_nonneg Z D b n ω
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hprod : 0 ≤ B * Q := mul_nonneg hB hQ
  have hcoord (j k : Fin p) :
      |wholeFittedMeat Z D n ω j k -
        wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω j k| ≤ E := by
    have hc := crossMeat_sq_le Z D b n ω j k hn
    have hcabs : |crossMeatEmp Z D b n ω j k| ≤ Real.sqrt (B * Q) := by
      apply Real.le_sqrt_of_sq_le
      simpa [B, Q, sq_abs] using hc
    have hqabs := quadMeat_abs_le Z D b n ω j k hn
    rw [fittedMeat_entry_expansion]
    calc
      |(-2) * crossMeatEmp Z D b n ω j k + quadMeatEmp Z D b n ω j k| ≤
          |(-2) * crossMeatEmp Z D b n ω j k| +
            |quadMeatEmp Z D b n ω j k| := abs_add_le _ _
      _ = 2 * |crossMeatEmp Z D b n ω j k| +
            |quadMeatEmp Z D b n ω j k| := by simp
      _ ≤ 2 * Real.sqrt (B * Q) + Q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hcabs (by norm_num)) hqabs
  have hrow (j : Fin p) :
      ‖(wholeFittedMeat Z D n ω -
        wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω) j‖ ≤ E := by
    apply (pi_norm_le_iff_of_nonneg hE).2
    intro k
    simpa [Real.norm_eq_abs, Matrix.sub_apply] using hcoord j k
  have hmat := (pi_norm_le_iff_of_nonneg hE).2 hrow
  exact hmat

lemma perturbEnergy_cp_zero {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (hgram : WholeGramLimits μ Z D b) (htight : WholeTight μ (wholeRootError Z D b))
    (hmax : CP μ (wholeMaxRow Z) 0) :
    CP μ (perturbEnergyEmp Z D b) 0 := by
  have hGram := gramTrace_cp μ Z D b hgram
  have hMGti := AronowAudit.P015.ConvergenceCompletion.mul_limit μ
    (cp_real_to_tendstoInMeasure μ _ _ hmax)
    (cp_real_to_tendstoInMeasure μ _ _ hGram)
  have hMGti' : TendstoInMeasure μ
      (fun n ω => wholeMaxRow Z n ω * gramTraceEmp Z n ω) atTop (fun _ => 0) := by
    simpa using hMGti
  have hMG : CP μ (fun n ω => wholeMaxRow Z n ω * gramTraceEmp Z n ω) 0 :=
    tendstoInMeasure_to_cp_real μ _ _ hMGti'
  have hMGnonneg : ∀ n ω, 0 ≤ wholeMaxRow Z n ω * gramTraceEmp Z n ω := by
    intro n ω
    exact mul_nonneg (wholeMaxRow_nonneg Z n ω) (gramTraceEmp_nonneg Z n ω)
  have hRoot : CP μ
      (fun n ω => ‖wholeRootError Z D b n ω‖ ^ 2 *
        (wholeMaxRow Z n ω * gramTraceEmp Z n ω)) 0 :=
    tight_mul_cp_zero μ (wholeRootError Z D b) _ htight hMG hMGnonneg
  have hUpperTi := AronowAudit.P015.ConvergenceCompletion.mul_limit μ
    (AronowAudit.P015.ConvergenceCompletion.constant_limit μ ((p : ℝ) ^ 2))
    (cp_real_to_tendstoInMeasure μ _ _ hRoot)
  have hUpper : CP μ
      (fun n ω => (p : ℝ) ^ 2 * ‖wholeRootError Z D b n ω‖ ^ 2 *
        wholeMaxRow Z n ω * gramTraceEmp Z n ω) 0 := by
    apply tendstoInMeasure_to_cp_real μ _ _
    simpa [mul_assoc] using hUpperTi
  apply (cp_iff_eventually_small μ _ 0).2
  intro ε hε δ hδ
  have hu := (cp_iff_eventually_small μ _ 0).1 hUpper ε hε δ hδ
  have hsub (n : ℕ) :
      {ω | ε ≤ dist (perturbEnergyEmp Z D b n ω) 0} ⊆
        {ω | ε ≤ dist ((p : ℝ) ^ 2 * ‖wholeRootError Z D b n ω‖ ^ 2 *
          wholeMaxRow Z n ω * gramTraceEmp Z n ω) 0} := by
    intro ω hω
    have hQ := perturbEnergy_nonneg Z D b n ω
    have hle := perturbEnergy_le_root_bound_all Z D b n ω
    have hω' : ε ≤ perturbEnergyEmp Z D b n ω := by
      simpa [Real.dist_eq, abs_of_nonneg hQ] using hω
    have hU := le_trans hω' hle
    have hUnonneg : 0 ≤ (p : ℝ) ^ 2 * ‖wholeRootError Z D b n ω‖ ^ 2 *
        wholeMaxRow Z n ω * gramTraceEmp Z n ω :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (wholeMaxRow_nonneg Z n ω)) (gramTraceEmp_nonneg Z n ω)
    change ε ≤ dist ((p : ℝ) ^ 2 * ‖wholeRootError Z D b n ω‖ ^ 2 *
      wholeMaxRow Z n ω * gramTraceEmp Z n ω) 0
    simpa [Real.dist_eq, sub_zero, abs_mul,
      abs_of_nonneg (sq_nonneg (p : ℝ)),
      abs_of_nonneg (sq_nonneg (‖wholeRootError Z D b n ω‖)),
      abs_of_nonneg (wholeMaxRow_nonneg Z n ω),
      abs_of_nonneg (gramTraceEmp_nonneg Z n ω)] using hU
  filter_upwards [hu] with n hn
  exact lt_of_le_of_lt (prob_mono μ (hsub n)) hn

lemma fittedMeat_perturbation_cp_zero {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ)
    (hgram : WholeGramLimits μ Z D b) (htight : WholeTight μ (wholeRootError Z D b))
    (hmax : CP μ (wholeMaxRow Z) 0) :
    CP μ (fun n ω => ‖wholeFittedMeat Z D n ω -
      wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω‖) 0 := by
  have hB := trueMeatTrace_cp μ Z D b hgram
  have hQ := perturbEnergy_cp_zero μ Z D b hgram htight hmax
  have hBti := cp_real_to_tendstoInMeasure μ _ _ hB
  have hQti := cp_real_to_tendstoInMeasure μ _ _ hQ
  have hE : CP μ
      (fun n ω => 2 * Real.sqrt (trueMeatTraceEmp Z D b n ω *
        perturbEnergyEmp Z D b n ω) + perturbEnergyEmp Z D b n ω) 0 := by
    apply tendstoInMeasure_to_cp_real μ _ _
    have hpair := AronowAudit.P015.ConvergenceCompletion.pair_cmt μ
      (trueMeatTraceEmp Z D b) (perturbEnergyEmp Z D b)
      (trueMeatTracePop μ Z D b) 0
      (fun z : ℝ × ℝ => 2 * Real.sqrt (z.1 * z.2) + z.2)
      hBti hQti (by fun_prop)
    simpa using hpair
  apply (cp_iff_eventually_small μ _ 0).2
  intro ε hε δ hδ
  have he := (cp_iff_eventually_small μ _ 0).1 hE ε hε δ hδ
  have hsub (n : ℕ) :
      {ω | ε ≤ dist (‖wholeFittedMeat Z D n ω -
        wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω‖) 0} ⊆
        {ω | ε ≤ dist (2 * Real.sqrt (trueMeatTraceEmp Z D b n ω *
          perturbEnergyEmp Z D b n ω) + perturbEnergyEmp Z D b n ω) 0} := by
    intro ω hω
    have hbound := matrixDiff_norm_le_energy Z D b n ω
    by_cases hn : 0 < n
    · have hEω := hbound hn
      have hB0 := trueMeatTrace_nonneg Z D b n ω hn
      have hQ0 := perturbEnergy_nonneg Z D b n ω
      have hE0 : 0 ≤ 2 * Real.sqrt (trueMeatTraceEmp Z D b n ω *
          perturbEnergyEmp Z D b n ω) + perturbEnergyEmp Z D b n ω := by
        positivity
      have hω' : ε ≤ ‖wholeFittedMeat Z D n ω -
          wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω‖ := by
        simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hω
      have hU := le_trans hω' hEω
      simpa [Real.dist_eq, abs_of_nonneg hE0] using hU
    · have hn0 : n = 0 := by omega
      subst n
      have hfit0 : wholeFittedMeat Z D 0 ω = 0 := by
        ext j k
        simp [wholeFittedMeat, wholeMeat]
      have htrue0 : wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) 0 ω = 0 := by
        ext j k
        simp [wholeMeat]
      have hbad : ε ≤ 0 := by simpa [hfit0, htrue0] using hω
      have hB0 : trueMeatTraceEmp Z D b 0 ω = 0 := by
        simp [trueMeatTraceEmp, wholeMeat]
      have hQ0 : perturbEnergyEmp Z D b 0 ω = 0 := by
        simp [perturbEnergyEmp]
      change ε ≤ dist (2 * Real.sqrt
        (trueMeatTraceEmp Z D b 0 ω * perturbEnergyEmp Z D b 0 ω) +
        perturbEnergyEmp Z D b 0 ω) 0
      rw [hB0, hQ0]
      simp
      linarith
  filter_upwards [he] with n hn
  exact lt_of_le_of_lt (prob_mono μ (hsub n)) hn

end SAP.P001a.WH.W1.P.T18_L7

open SAP.P001a
theorem SAP.P001a.WH.W1.T18_L7_proof : SAP.P001a.WH.W1.T18_L7 := by
  intro Ω _ μ hμ p Z D hiid b hscore hgram htight hmax
  have hpert := SAP.P001a.WH.W1.P.T18_L7.fittedMeat_perturbation_cp_zero
    μ Z D b hgram htight hmax
  apply (SAP.P001a.WH.W1.P.T18_L7.cp_iff_eventually_small μ
    (wholeFittedMeat Z D) (wholeOmega μ (Z 0) (D 0) b)).2
  intro ε hε δ hδ
  have hleft := (SAP.P001a.WH.W1.P.T18_L7.cp_iff_eventually_small μ
      (fun n ω => ‖wholeFittedMeat Z D n ω -
        wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω‖) 0).1 hpert
      (ε / 2) (by positivity) (δ / 2) (by positivity)
  have hright := (SAP.P001a.WH.W1.P.T18_L7.cp_iff_eventually_small μ
      (wholeMeat Z (fun i => wholeResidual (Z i) (D i) b))
      (wholeOmega μ (Z 0) (D 0) b)).1 hgram.trueMeat
      (ε / 2) (by positivity) (δ / 2) (by positivity)
  filter_upwards [hleft, hright] with n hleft' hright'
  let F : Ω → Matrix (Fin p) (Fin p) ℝ := wholeFittedMeat Z D n
  let T : Ω → Matrix (Fin p) (Fin p) ℝ :=
    wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n
  have hsub : {ω | ε ≤ dist (wholeFittedMeat Z D n ω)
      (wholeOmega μ (Z 0) (D 0) b)} ⊆
      {ω | ε / 2 ≤ dist
        (‖wholeFittedMeat Z D n ω -
          wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω‖) 0} ∪
      {ω | ε / 2 ≤ dist
        (wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω)
        (wholeOmega μ (Z 0) (D 0) b)} := by
    intro ω hω
    by_contra hbad
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hbad
    have hnormdist : dist (F ω) (T ω) =
        dist (‖F ω - T ω‖) (0 : ℝ) := by
      rw [dist_eq_norm, Real.dist_eq]
      simp [abs_of_nonneg (norm_nonneg (F ω - T ω))]
    have hsmall : dist (F ω) (T ω) < ε / 2 := by
      rw [hnormdist]
      simpa [F, T] using hbad.1
    have htri : dist (wholeFittedMeat Z D n ω)
        (wholeOmega μ (Z 0) (D 0) b) ≤
          dist (F ω) (T ω) + dist (T ω) (wholeOmega μ (Z 0) (D 0) b) :=
      dist_triangle _ _ _
    have hlarge : ε ≤ dist (wholeFittedMeat Z D n ω)
        (wholeOmega μ (Z 0) (D 0) b) := hω
    linarith
  have hprob := (SAP.P001a.WH.W1.P.T18_L7.prob_mono μ hsub).trans
    (SAP.P001a.WH.W1.P.T18_L7.prob_union_le μ _ _)
  have hsum :
      prob μ {ω | ε / 2 ≤ dist
        (‖wholeFittedMeat Z D n ω -
          wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω‖) 0} +
      prob μ {ω | ε / 2 ≤ dist
        (wholeMeat Z (fun i => wholeResidual (Z i) (D i) b) n ω)
        (wholeOmega μ (Z 0) (D 0) b)} < δ := by
    linarith [add_lt_add hleft' hright']
  exact lt_of_le_of_lt hprob hsum
