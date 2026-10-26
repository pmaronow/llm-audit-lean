import AronowAudit.P011.P011_ProbabilityCompletion
import AronowAudit.P011.P011_StarCompletion
import AronowAudit.P053.P053_NormalQuantiles

/- The CDF squeeze adapts the P001 random-width interval argument to
row-specific probability spaces and closed intervals. The coverage argument
uses the P011 central limit theorem.
The adapted squeeze originates in StatLean's `SteinMethod` module
(Apache-2.0); see NOTICE at the repository root.
-/
namespace AronowAudit.P011.CoverageCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1:NNReal) ≠ 0)

def RowCP {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | |X n ω-c| > ε}) atTop (𝓝 0)

def rowCDF {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (μ n).real {ω | X n ω ≤ t}

theorem continuous_squeeze_zero {G : ℕ → ℝ} {F : ℝ → ℝ}
    (hF : ContinuousAt F 0)
    (hb : ∀ ε > (0:ℝ), ∀ᶠ n in atTop, F (-ε)-ε ≤ G n ∧ G n ≤ F ε+ε) :
    Tendsto G atTop (nhds (F 0)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ,hδ,hδF⟩ := Metric.tendsto_nhds_nhds.mp hF (η/2) (by linarith)
  let ε := min (δ/2) (η/4)
  have he : 0 < ε := lt_min (by linarith) (by linarith)
  have hed : ε ≤ δ/2 := min_le_left _ _
  have heη : ε ≤ η/4 := min_le_right _ _
  have hl := hδF (show dist (-ε) 0 < δ by rw [Real.dist_eq,sub_zero,abs_neg,abs_of_pos he]; linarith)
  have hr := hδF (show dist ε 0 < δ by rw [Real.dist_eq,sub_zero,abs_of_pos he]; linarith)
  rw [Real.dist_eq, abs_lt] at hl hr
  filter_upwards [hb ε he] with n hn
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith [hn.1,hn.2]


theorem row_random_width_interval {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Z W : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    (F : ℝ → ℝ) (hCD : ∀ t, Tendsto (fun n => rowCDF μ Z n t) atTop (𝓝 (F t)))
    (hF : Continuous F) (hFm : Monotone F)
    (w : ℝ) (hw : 0 < w) (hW : RowCP μ W w) :
    Tendsto (fun n => (μ n).real {ω | |Z n ω| ≤ W n ω}) atTop
      (𝓝 (F w-F (-w))) := by
  let Ψ := fun e => F (w+e)-F (-w-e)
  have hΨ : Continuous Ψ := by dsimp [Ψ]; fun_prop
  have hIoc (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
      (μ n).real {ω | a < Z n ω ∧ Z n ω ≤ b} = rowCDF μ Z n b-rowCDF μ Z n a := by
    have he : {ω | a < Z n ω ∧ Z n ω ≤ b} = {ω | Z n ω ≤ b} \ {ω | Z n ω ≤ a} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le, and_comm]
    rw [he]
    exact measureReal_sdiff (μ := μ n) (fun ω hω => hω.trans hab)
      ((measurableSet_Iic : MeasurableSet (Set.Iic a)).preimage (hZ n))
  have hlim (a b : ℝ) : Tendsto (fun n => rowCDF μ Z n b-rowCDF μ Z n a)
      atTop (nhds (F b-F a)) :=
    (hCD b).sub (hCD a)
  have hg : Tendsto (fun n => (μ n).real {ω | |Z n ω| ≤ W n ω}) atTop (nhds (Ψ 0)) := by
    apply continuous_squeeze_zero hΨ.continuousAt
    intro ε hε
    let Bad := fun n => {ω | ε/2 < |W n ω-w|}
    have hb : Tendsto (fun n => (μ n).real (Bad n)) atTop (nhds 0) := hW (ε/2) (by linarith)
    have hupper (n : ℕ) : (μ n).real {ω | |Z n ω| ≤ W n ω} ≤
        (rowCDF μ Z n (w+ε)-rowCDF μ Z n (-w-ε)) + (μ n).real (Bad n) := by
      have hsub : {ω | |Z n ω| ≤ W n ω} ⊆
          {ω | -w-ε < Z n ω ∧ Z n ω ≤ w+ε} ∪ Bad n := by
        intro ω hω
        by_cases hd : ε/2 < |W n ω-w|
        · exact Or.inr hd
        · apply Or.inl
          have hd' : |W n ω-w| ≤ ε/2 := le_of_not_gt hd
          rw [abs_le] at hd'
          change |Z n ω| ≤ W n ω at hω
          rw [abs_le] at hω
          change -w-ε < Z n ω ∧ Z n ω ≤ w+ε
          constructor <;> linarith [hω.1,hω.2,hd'.1,hd'.2]
      have hle := (measureReal_mono (μ := μ n) hsub).trans (measureReal_union_le _ _)
      rw [show (μ n).real {ω | -w-ε < Z n ω ∧ Z n ω ≤ w+ε} =
        rowCDF μ Z n (w+ε)-rowCDF μ Z n (-w-ε) from hIoc n _ _ (by linarith)] at hle
      exact hle
    have hlow : ∀ᶠ n in atTop, Ψ (-ε)-ε ≤ (μ n).real {ω | |Z n ω| ≤ W n ω} := by
      by_cases hsmall : ε < w
      · have hlower (n : ℕ) : rowCDF μ Z n (w-ε)-rowCDF μ Z n (-w+ε) ≤
            (μ n).real {ω | |Z n ω| ≤ W n ω} + (μ n).real (Bad n) := by
          have hsub : {ω | -w+ε < Z n ω ∧ Z n ω ≤ w-ε} ⊆
              {ω | |Z n ω| ≤ W n ω} ∪ Bad n := by
            intro ω hω
            by_cases hd : ε/2 < |W n ω-w|
            · exact Or.inr hd
            · apply Or.inl
              have hd' : |W n ω-w| ≤ ε/2 := le_of_not_gt hd
              rw [abs_le] at hd'
              change |Z n ω| ≤ W n ω
              rw [abs_le]
              change -w+ε < Z n ω ∧ Z n ω ≤ w-ε at hω
              constructor <;> linarith [hω.1,hω.2,hd'.1,hd'.2]
          have hle := (measureReal_mono (μ := μ n) hsub).trans (measureReal_union_le _ _)
          rw [show (μ n).real {ω | -w+ε < Z n ω ∧ Z n ω ≤ w-ε} =
            rowCDF μ Z n (w-ε)-rowCDF μ Z n (-w+ε) from hIoc n _ _ (by linarith)] at hle
          exact hle
        have hl := (hlim (-w+ε) (w-ε)).eventually
          (eventually_gt_nhds (show F (w-ε)-F (-w+ε)-ε/2 < F (w-ε)-F (-w+ε) by linarith))
        have hbad := hb.eventually (eventually_lt_nhds (show (0:ℝ) < ε/2 by linarith))
        filter_upwards [hl,hbad] with n hn hbn
        have hbound := hlower n
        dsimp [Ψ]
        rw [sub_neg_eq_add]
        change F (w-ε)-F (-w+ε)-ε ≤ _
        linarith
      · have hΨneg : Ψ (-ε) ≤ 0 := by
          dsimp [Ψ]
          have hm := hFm (show w + -ε ≤ -w - -ε by linarith)
          linarith
        filter_upwards [] with n
        have hnonneg : 0 ≤ (μ n).real {ω | |Z n ω| ≤ W n ω} := ENNReal.toReal_nonneg
        linarith
    have hu := (hlim (-w-ε) (w+ε)).eventually
      (eventually_lt_nhds (show F (w+ε)-F (-w-ε) < F (w+ε)-F (-w-ε)+ε/2 by linarith))
    have hbad := hb.eventually (eventually_lt_nhds (show (0:ℝ) < ε/2 by linarith))
    filter_upwards [hlow,hu,hbad] with n hln hun hbn
    refine ⟨hln,?_⟩
    have hbound := hupper n
    dsimp [Ψ]
    linarith
  simpa [Ψ] using hg


lemma rowCP_det {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (𝓝 c)) :
    RowCP μ (fun n _ => a n) c := by
  intro ε hε
  have he : ∀ᶠ n in atTop, |a n-c| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ha ε hε)
  apply tendsto_congr' (he.mono fun n hn => ?_) |>.mpr tendsto_const_nhds
  have hs : {ω : Ω n | |a n-c| > ε} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hn.le
  rw [hs]
  simp

lemma rowCP_moving_center {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (a : ℕ → ℝ) (c : ℝ)
    (hX : ∀ ε > (0:ℝ), Tendsto (fun n => (μ n).real {ω | |X n ω-a n| > ε}) atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 c)) : RowCP μ X c := by
  intro ε hε
  have he : ∀ᶠ n in atTop, |a n-c| < ε/2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ha (ε/2) (by linarith))
  apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ (hX (ε/2) (by linarith))
  filter_upwards [he] with n hn
  apply measureReal_mono (μ := μ n) ?_ (measure_ne_top _ _)
  intro ω hω
  change ε < |X n ω-c| at hω
  change ε/2 < |X n ω-a n|
  have htri : |X n ω-c| ≤ |X n ω-a n|+|a n-c| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (X n ω-a n) (a n-c)
  linarith

lemma rowCP_continuous_pair {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) (a b : ℝ) (hX : RowCP μ X a) (hY : RowCP μ Y b)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousAt f (a,b)) :
    RowCP μ (fun n ω => f (X n ω,Y n ω)) (f (a,b)) := by
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hf ε hε
  have hd : 0 < δ/2 := by positivity
  have hlim := (hX (δ/2) hd).add (hY (δ/2) hd)
  apply squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) (by simpa using hlim)
  calc
    (μ n).real {ω | |f (X n ω,Y n ω)-f (a,b)| > ε} ≤
      (μ n).real ({ω | |X n ω-a| > δ/2} ∪ {ω | |Y n ω-b| > δ/2}) := by
      apply measureReal_mono (μ := μ n) ?_ (measure_ne_top _ _)
      intro ω hω
      change ε < |f (X n ω,Y n ω)-f (a,b)| at hω
      by_contra hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hn
      have hp : dist (X n ω,Y n ω) (a,b) < δ := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt (by linarith [hn.1]) (by linarith [hn.2])
      have hh := hclose hp
      rw [Real.dist_eq] at hh
      linarith
    _ ≤ _ := measureReal_union_le _ _

lemma quantile_eq (α : ℝ) : normalQuantile α = AronowAudit.P053.normalCritical α := by
  unfold normalQuantile AronowAudit.P053.normalCritical
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, Phi,
    AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]

lemma quantile_positive (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < normalQuantile α := by
  rw [quantile_eq]
  exact AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1

lemma quantile_mass (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Phi (normalQuantile α)-Phi (-normalQuantile α) = 1-α := by
  rw [quantile_eq]
  unfold Phi
  rw [AronowAudit.P053.NormalCompletion.normal_cdf_neg,
    ← AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf,
    AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα hα1]
  ring


lemma scaled_width (n v V z : ℝ) (hn : 0 < n) :
    z*Real.sqrt (max (n*V) 0)/Real.sqrt (n*v) =
      z*Real.sqrt (max V 0)/Real.sqrt v := by
  have hmax : max (n*V) 0 = n*max V 0 := by
    by_cases hV : 0 ≤ V
    · rw [max_eq_left hV, max_eq_left (mul_nonneg hn.le hV)]
    · have hV' : V ≤ 0 := le_of_not_ge hV
      rw [max_eq_right hV', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hn.le hV')]
      simp
  rw [hmax, Real.sqrt_mul hn.le, Real.sqrt_mul hn.le]
  calc
    _ = (Real.sqrt n*(z*Real.sqrt (max V 0)))/(Real.sqrt n*Real.sqrt v) := by ring
    _ = _ := mul_div_mul_left _ _ (Real.sqrt_pos.mpr hn).ne'

lemma consistent_coverage (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (_hV : ∀ k, Measurable (V k))
    (hc : InProbability F (fun k y => (F.size k:ℝ)*V k y) (scaledTrue F)) :
    ∀ α : ℝ, 0 < α → α < 1 → Tendsto (fun k => coverage (F.model k) (V k) α)
      atTop (𝓝 (1-α)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hc3 : 0 < c3 := h.2.2.2.1
  have hscale : Tendsto (scaledTrue F) atTop (𝓝 c3) := h.2.2.2.2.2.2.2.2.1
  let μ := fun k => (F.model k).law
  have hcp : RowCP μ (fun k y => (F.size k:ℝ)*V k y) c3 :=
    rowCP_moving_center μ _ (scaledTrue F) c3 hc hscale
  have hdcp : RowCP μ (fun k _ => scaledTrue F k) c3 := rowCP_det μ _ _ hscale
  intro α hα hα1
  let z := normalQuantile α
  have hz : 0 < z := quantile_positive α hα hα1
  let f : ℝ × ℝ → ℝ := fun u => z*Real.sqrt (max u.1 0)/Real.sqrt u.2
  have hf : ContinuousAt f (c3,c3) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (Real.sqrt_pos.mpr hc3).ne'
  have hfc : f (c3,c3) = z := by
    dsimp [f]
    rw [max_eq_left hc3.le]
    exact mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hc3).ne'
  let W := fun k y => f ((F.size k:ℝ)*V k y,scaledTrue F k)
  have hW : RowCP μ W z := by
    simpa only [hfc] using rowCP_continuous_pair μ _ _ c3 c3 hcp hdcp f hf
  have hPhi : Continuous Phi := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1) t
  have hZ (k : ℕ) : Measurable (standardized (F.model k)) :=
    ((ProbabilityCompletion.betaHat_measurable (F.model k)).sub measurable_const).div_const _
  have hlim := row_random_width_interval μ (fun k => standardized (F.model k)) W hZ
    Phi (dependency_graph_clt F c1 c2 c3 c4 h) hPhi (monotone_cdf (μ := gaussianReal 0 1))
    z hz hW
  rw [quantile_mass α hα hα1] at hlim
  have hpos : ∀ᶠ k in atTop, 0 < var (F.model k) (betaHat (F.model k)) := by
    have he := hscale.eventually (Ioi_mem_nhds hc3)
    filter_upwards [he] with k hk
    change 0 < scaledTrue F k at hk
    dsimp [scaledTrue] at hk
    have hn : 0 < (F.size k:ℝ) := by exact_mod_cast F.positive k
    nlinarith
  have heq : (fun k => coverage (F.model k) (V k) α) =ᶠ[atTop]
      (fun k => (μ k).real {y | |standardized (F.model k) y| ≤ W k y}) := by
    filter_upwards [hpos] with k hk
    apply congrArg ((μ k).real)
    ext y
    change (|betaHat (F.model k) y-beta (F.model k)| ≤ z*Real.sqrt (max (V k y) 0)) ↔
      (|standardized (F.model k) y| ≤ W k y)
    dsimp [W,f,scaledTrue]
    rw [scaled_width _ _ _ _ (by exact_mod_cast F.positive k), standardized,
      abs_div, abs_of_pos (Real.sqrt_pos.mpr hk)]
    exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hk)).symm
  exact (tendsto_congr' heq).mpr hlim


lemma conservative_coverage (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (hV : ∀ k, Measurable (V k))
    (hc : Conservative F V) : ConservativeCoverage F V := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let U := fun k y => min (V k y) (var (F.model k) (betaHat (F.model k)))
  have hU : ∀ k, Measurable (U k) := fun k => (hV k).min measurable_const
  have hUc : InProbability F (fun k y => (F.size k:ℝ)*U k y) (scaledTrue F) := by
    intro ε hε
    have heq : (fun k => probability (F.model k)
        {y | |(F.size k:ℝ)*U k y-scaledTrue F k| > ε}) =
        (fun k => probability (F.model k)
          {y | (F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-V k y) > ε}) := by
      funext k
      apply congrArg (probability (F.model k))
      ext y
      dsimp [U,scaledTrue]
      rw [(truncation_identity (F.size k:ℝ) _ _ (by positivity)).1]
      have hid : (F.size k:ℝ)*var (F.model k) (betaHat (F.model k))-(F.size k:ℝ)*V k y =
          (F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-V k y) := by ring
      rw [hid]
      change (ε < max ((F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-V k y)) 0) ↔
        ε < (F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-V k y)
      rw [lt_max_iff]
      simp only [show ¬ ε<0 by linarith, or_false]
    rw [heq]
    exact hc ε hε
  have hlim := consistent_coverage F c1 c2 c3 c4 h U hU hUc
  intro α hα hα1
  have hz : 0 ≤ normalQuantile α := (quantile_positive α hα hα1).le
  have hdom (k : ℕ) : coverage (F.model k) (U k) α ≤ coverage (F.model k) (V k) α := by
    apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
    intro y hy
    exact interval_containment _ _ _ _ hz (min_le_left _ _) hy
  have hbelow : atTop.IsBoundedUnder (· ≥ ·) (fun k => coverage (F.model k) (V k) α) :=
    isBoundedUnder_of ⟨0,fun k => measureReal_nonneg⟩
  have habove : atTop.IsBoundedUnder (· ≤ ·) (fun k => coverage (F.model k) (V k) α) := by
    refine isBoundedUnder_of ⟨1,fun k => ?_⟩
    simpa only [coverage, probability, measureReal_def, measure_univ, ENNReal.toReal_one] using measureReal_mono (μ := (F.model k).law) (Set.subset_univ
      {y | |betaHat (F.model k) y-beta (F.model k)| ≤ normalQuantile α*Real.sqrt (max (V k y) 0)})
  apply (le_liminf_iff habove.isCoboundedUnder_flip hbelow).mpr
  intro y hy
  filter_upwards [(hlim α hα hα1).eventually_const_lt hy] with k hk
  exact hk.trans_le (hdom k)

lemma conditional_wald_coverage_completed (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (hV : ∀ k, Measurable (V k)) :
    (InProbability F (fun k y => (F.size k : ℝ)*V k y) (scaledTrue F) →
      ∀ α : ℝ, 0 < α → α < 1 → Tendsto (fun k => coverage (F.model k) (V k) α)
        atTop (𝓝 (1-α))) ∧
    (Conservative F V → ConservativeCoverage F V) := by
  exact ⟨consistent_coverage F c1 c2 c3 c4 h V hV, conservative_coverage F c1 c2 c3 c4 h V hV⟩

end
end AronowAudit.P011.CoverageCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem conditional_wald_coverage (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (hV : ∀ k, Measurable (V k)) :
    (InProbability F (fun k y => (F.size k : ℝ)*V k y) (scaledTrue F) →
      ∀ α : ℝ, 0 < α → α < 1 → Tendsto (fun k => coverage (F.model k) (V k) α)
        atTop (𝓝 (1-α))) ∧
    (Conservative F V → ConservativeCoverage F V) := by
  exact CoverageCompletion.conditional_wald_coverage_completed F c1 c2 c3 c4 h V hV
end AronowAudit.P011

