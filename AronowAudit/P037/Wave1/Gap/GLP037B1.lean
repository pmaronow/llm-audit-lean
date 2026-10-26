import AronowAudit.P037.P037_FiniteDesign
import AronowAudit.P053.P053_NormalQuantiles

namespace AronowAudit.P037.Wave1
open scoped BigOperators Topology
open Filter
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-! Finite probability calculus on the changing row spaces. -/

def fittedBlock_small {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (X : ∀ n, Ω n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
    designProbability (d n) (fun w => ε < |X n w|)) atTop (𝓝 0)

lemma fittedBlock_probability_union {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (E F : Ω → Prop) :
    designProbability d (fun w => E w ∨ F w) ≤
      designProbability d E + designProbability d F := by
  unfold designProbability
  rw [← designMean_add]
  unfold designMean
  apply Finset.sum_le_sum
  intro w _
  apply mul_le_mul_of_nonneg_left _ (d.nonneg w)
  dsimp
  split_ifs <;> simp_all

lemma fittedBlock_small_mono {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (X Y : ∀ n, Ω n → ℝ)
    (hX : fittedBlock_small d X) (h : ∀ n w, |Y n w| ≤ |X n w|) :
    fittedBlock_small d Y := by
  intro ε hε
  exact squeeze_zero (fun n => WitnessCompletion.probability_nonneg _ _)
    (fun n => WitnessCompletion.probability_mono _ _ _
      (fun w hw => lt_of_lt_of_le hw (h n w))) (hX ε hε)

lemma fittedBlock_small_add {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (X Y : ∀ n, Ω n → ℝ)
    (hX : fittedBlock_small d X) (hY : fittedBlock_small d Y) :
    fittedBlock_small d (fun n w => X n w + Y n w) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hb : ∀ n, designProbability (d n) (fun w => ε < |X n w + Y n w|) ≤
      designProbability (d n) (fun w => ε / 2 < |X n w|) +
      designProbability (d n) (fun w => ε / 2 < |Y n w|) := by
    intro n
    refine (WitnessCompletion.probability_mono _ _ _ ?_).trans
      (fittedBlock_probability_union _ _ _)
    intro w hw
    by_contra hn
    push_neg at hn
    have := abs_add_le (X n w) (Y n w)
    linarith [hn.1, hn.2]
  exact squeeze_zero (fun n => WitnessCompletion.probability_nonneg _ _)
    hb (by simpa using (hX _ hε2).add (hY _ hε2))

lemma fittedBlock_small_bound {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (X Y : ∀ n, Ω n → ℝ)
    (E : ∀ n, Ω n → Prop) (C : ℝ)
    (hX : fittedBlock_small d X)
    (hE : Tendsto (fun n => designProbability (d n) (E n)) atTop (𝓝 0))
    (h : ∀ n w, ¬ E n w → |Y n w| ≤ |C| * |X n w|) :
    fittedBlock_small d Y := by
  intro ε hε
  have hδ : 0 < ε / (|C| + 1) := div_pos hε (by positivity)
  have hb : ∀ n, designProbability (d n) (fun w => ε < |Y n w|) ≤
      designProbability (d n) (E n) +
      designProbability (d n) (fun w => ε / (|C| + 1) < |X n w|) := by
    intro n
    refine (WitnessCompletion.probability_mono _ _ _ ?_).trans
      (fittedBlock_probability_union _ _ _)
    intro w hw
    by_cases he : E n w
    · exact Or.inl he
    · right
      by_contra hn
      have hn' := le_of_not_gt hn
      have hmul : (|C| + 1) * |X n w| ≤ ε := by
        simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp hn'
      have hbound := h n w he
      nlinarith [abs_nonneg (X n w)]
  exact squeeze_zero (fun n => WitnessCompletion.probability_nonneg _ _)
    hb (by simpa using hE.add (hX _ hδ))


lemma fittedBlock_small_deterministic {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (a : ℕ → ℝ) (a₀ : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀)) :
    fittedBlock_small d (fun n _ => a n - a₀) := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  have he := (Metric.tendsto_atTop.mp ha) ε hε
  obtain ⟨N, hN⟩ := he
  filter_upwards [eventually_ge_atTop N] with n hn
  have hlt : |a n - a₀| < ε := by simpa only [Real.dist_eq] using hN n hn
  simp [designProbability, designMean, not_lt_of_ge hlt.le]

lemma fittedBlock_small_sum {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    {I : Type*} [Fintype I] (d : ∀ n, FiniteDesign (Ω n))
    (X : I → ∀ n, Ω n → ℝ) (hX : ∀ i, fittedBlock_small d (X i)) :
    fittedBlock_small d (fun n w => ∑ i, X i n w) := by
  have hh := WitnessCompletion.finite_continuous_map d
    (fun n w i => X i n w) (fun _ => 0) (fun a => ∑ i, a i)
    (fun i ε hε => by simpa using hX i ε hε)
    (continuous_finset_sum _ (fun i _ => continuous_apply i)).continuousAt
  simpa only [fittedBlock_small, sub_zero, Finset.sum_const_zero] using hh

/-! A scalar weighted cross-product is an oracle mean with zero prediction. -/

def fittedBlock_scalarRow {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ) : RetainedBlockRow B :=
  { r with y := t, g := fun _ _ => 0 }

def fittedBlock_HT {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r) : ℝ :=
  (∑ b, ∑ i, (if r.exposed b (w b) i then 1 else 0) / p b i * t b i) /
    retainedSize r

def fittedBlock_population {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ) : ℝ :=
  (∑ b, ∑ i, t b i) / retainedSize r

lemma fittedBlock_scalar_bounds (r : ∀ B, RetainedBlockRow (B+1))
    (t : ∀ B, (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K T : ℝ) (h : UniformBlockBounds r m c eta K)
    (hT : 0 ≤ T) (ht : ∀ B b i, |t B b i| ≤ T) :
    UniformBlockBounds (fun B => fittedBlock_scalarRow (r B) (t B)) m c eta T := by
  refine ⟨h.1, h.2.1, hT, fun B => ⟨(h.2.2.2 B).1, fun b =>
    ⟨((h.2.2.2 B).2 b).1, fun i => ?_⟩⟩⟩
  exact ⟨((h.2.2.2 B).2 b).2 i |>.1, ht B b i, by simpa [fittedBlock_scalarRow] using hT⟩

lemma fittedBlock_HT_oracle {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r) :
    fittedBlock_HT r t r.pi w = oracleRowMean (fittedBlock_scalarRow r t) w := by
  simp [fittedBlock_HT, oracleRowMean, oracleBlockTotal, fittedBlock_scalarRow,
    augmentedContribution, retainedSize]
  congr!

lemma fittedBlock_HT_consistent (r : ∀ B, RetainedBlockRow (B+1))
    (t : ∀ B, (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K T : ℝ) (h : UniformBlockBounds r m c eta K)
    (hT : 0 ≤ T) (ht : ∀ B b i, |t B b i| ≤ T) :
    fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => fittedBlock_HT (r B) (t B) (r B).pi w -
        fittedBlock_population (r B) (t B)) := by
  intro ε hε
  have hh := independent_blocks_oracle_consistent
    (fun B => fittedBlock_scalarRow (r B) (t B)) m c eta T
    (fittedBlock_scalar_bounds r t m c eta K T h hT ht) ε hε
  convert hh using 1
  funext B
  unfold designProbability designMean blockRowProbability
  dsimp only [productDesign, fittedBlock_scalarRow]
  congr 1
  funext w
  congr 1
  congr 1
  rw [fittedBlock_HT_oracle]
  rfl

lemma fittedBlock_size_pos (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K : ℝ) (h : UniformBlockBounds r m c eta K) (B : ℕ) :
    0 < (retainedSize (r B) : ℝ) := by
  have hn : 0 < c * ((B : ℝ) + 1) := mul_pos h.1 (by positivity)
  exact hn.trans_le (h.2.2.2 B).1

lemma fittedBlock_sqrt_ge_one (B : ℕ) : (1 : ℝ) ≤ Real.sqrt (B+1) := by
  apply Real.one_le_sqrt.mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg B)

lemma fittedBlock_inverse_error (eta δ p pi : ℝ) (heta : 0 < eta)
    (hδ : 0 ≤ δ) (hδe : δ ≤ eta / 2) (hpi : eta ≤ pi)
    (hp : 0 < p) (hd : |p-pi| ≤ δ) :
    |p⁻¹ - pi⁻¹| ≤ 2 * δ / eta^2 := by
  have hpi0 : 0 < pi := heta.trans_le hpi
  have hpl : eta / 2 ≤ p := by
    have := (abs_le.mp hd).1
    linarith
  have hid : p⁻¹ - pi⁻¹ = (pi-p)/(p*pi) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hp hpi0), abs_sub_comm]
  have hden : eta^2 / 2 ≤ p*pi := by nlinarith
  rw [div_le_div_iff₀ (mul_pos hp hpi0) (sq_pos_of_pos heta)]
  nlinarith

lemma fittedBlock_sum_const {B : ℕ} (r : RetainedBlockRow B) (a : ℝ) :
    (∑ b : Fin B, ∑ _ : Fin (r.students b), a) = (retainedSize r : ℝ) * a := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  simp [retainedSize]

lemma fittedBlock_sum_abs_bound {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ) (T : ℝ)
    (ht : ∀ b i, |t b i| ≤ T) :
    |∑ b, ∑ i, t b i| ≤ (retainedSize r : ℝ) * T := by
  calc
    _ ≤ ∑ b, |∑ i, t b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, ∑ i, |t b i| := Finset.sum_le_sum
      (fun b _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ b : Fin B, ∑ _ : Fin (r.students b), T := Finset.sum_le_sum
      (fun b _ => Finset.sum_le_sum (fun i _ => ht b i))
    _ = _ := fittedBlock_sum_const r T

lemma fittedBlock_HT_sub {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r) :
    fittedBlock_HT r t p w - fittedBlock_HT r t r.pi w =
      (∑ b, ∑ i, (if r.exposed b (w b) i then 1 else 0) * t b i *
        ((p b i)⁻¹ - (r.pi b i)⁻¹)) / retainedSize r := by
  unfold fittedBlock_HT
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv]
  ring

lemma fittedBlock_HT_error_bound {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r)
    (T eta δ : ℝ) (hN : 0 < (retainedSize r : ℝ))
    (hT : 0 ≤ T) (heta : 0 < eta) (hδ : 0 ≤ δ) (hδe : δ ≤ eta/2)
    (ht : ∀ b i, |t b i| ≤ T) (hp : ∀ b i, 0 < p b i)
    (hpi : ∀ b i, eta ≤ r.pi b i) (hd : ∀ b i, |p b i-r.pi b i| ≤ δ) :
    |fittedBlock_HT r t p w - fittedBlock_HT r t r.pi w| ≤ 2*T*δ/eta^2 := by
  rw [fittedBlock_HT_sub, abs_div, abs_of_pos hN]
  have hb : ∀ b i, |(if r.exposed b (w b) i then (1:ℝ) else 0) * t b i *
      ((p b i)⁻¹ - (r.pi b i)⁻¹)| ≤ 2*T*δ/eta^2 := by
    intro b i
    have hi : |(if r.exposed b (w b) i then (1:ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    have he := fittedBlock_inverse_error eta δ (p b i) (r.pi b i)
      heta hδ hδe (hpi b i) (hp b i) (hd b i)
    calc
      _ = |(if r.exposed b (w b) i then (1:ℝ) else 0)| * |t b i| *
          |(p b i)⁻¹ - (r.pi b i)⁻¹| := by rw [abs_mul, abs_mul]
      _ ≤ (1*T) * (2*δ/eta^2) := mul_le_mul
        (mul_le_mul hi (ht b i) (abs_nonneg _) (by norm_num)) he
        (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ((retainedSize r : ℝ) * (2*T*δ/eta^2)) / retainedSize r :=
      div_le_div_of_nonneg_right (fittedBlock_sum_abs_bound r _ _ hb) hN.le
    _ = _ := mul_div_cancel_left₀ _ hN.ne'

/-- The uniform simulation rate controls a weighted sum even when its bounded
summands and the estimated probabilities use the same realization. -/
lemma fittedBlock_simulation_small (r : ∀ B, RetainedBlockRow (B+1))
    (p : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (t : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K T : ℝ) (h : UniformBlockBounds r m c eta K)
    (hp : ∀ B w b i, 0 < p B w b i)
    (hSim : ∀ ε : ℝ, 0 < ε → Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ b i, ε < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|)) atTop (𝓝 0))
    (E : ∀ B, BlockSample (r B) → Prop)
    (hE : Tendsto (fun B => designProbability (productDesign (r B).law) (E B))
      atTop (𝓝 0)) (hT : 0 ≤ T)
    (ht : ∀ B w, ¬ E B w → ∀ b i, |t B w b i| ≤ T) :
    fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
      Real.sqrt (B+1) * (fittedBlock_HT (r B) (t B w) (p B w) w -
        fittedBlock_HT (r B) (t B w) (r B).pi w)) := by
  intro ε hε
  let C : ℝ := 2*T/eta^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let α : ℝ := min (eta/2) (ε/(C+1))
  have hα : 0 < α := lt_min (by have := h.2.1; positivity)
    (div_pos hε (by positivity))
  have hs : Tendsto (fun B => designProbability (productDesign (r B).law)
      (fun w => ∃ b i, α < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|))
      atTop (𝓝 0) := by
    simpa only [blockRowProbability, designProbability, designMean, productDesign]
      using hSim α hα
  have hb : ∀ B, designProbability (productDesign (r B).law) (fun w =>
      ε < |Real.sqrt (B+1) * (fittedBlock_HT (r B) (t B w) (p B w) w -
        fittedBlock_HT (r B) (t B w) (r B).pi w)|) ≤
      designProbability (productDesign (r B).law) (E B) +
      designProbability (productDesign (r B).law) (fun w =>
        ∃ b i, α < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|) := by
    intro B
    refine (WitnessCompletion.probability_mono _ _ _ ?_).trans
      (fittedBlock_probability_union _ _ _)
    intro w hw
    by_cases he : E B w
    · exact Or.inl he
    · right
      by_contra hn
      push_neg at hn
      let s : ℝ := Real.sqrt (B+1)
      have hs1 : 1 ≤ s := fittedBlock_sqrt_ge_one B
      have hsp : 0 < s := lt_of_lt_of_le zero_lt_one hs1
      have hδ : 0 ≤ α/s := div_nonneg hα.le hsp.le
      have hδe : α/s ≤ eta/2 := by
        calc
          _ ≤ α := (div_le_self hα.le hs1)
          _ ≤ eta/2 := min_le_left _ _
      have hd : ∀ b i, |p B w b i-(r B).pi b i| ≤ α/s := by
        intro b i
        apply (le_div_iff₀ hsp).mpr
        simpa only [mul_comm] using hn b i
      have hbound := fittedBlock_HT_error_bound (r B) (t B w) (p B w) w T eta (α/s)
        (fittedBlock_size_pos r m c eta K h B) hT h.2.1 hδ hδe (ht B w he)
        (hp B w) (fun b i => (((h.2.2.2 B).2 b).2 i).1) hd
      have hroot : s * |fittedBlock_HT (r B) (t B w) (p B w) w -
          fittedBlock_HT (r B) (t B w) (r B).pi w| ≤ C*α := by
        calc
          _ ≤ s * (2*T*(α/s)/eta^2) := mul_le_mul_of_nonneg_left hbound hsp.le
          _ = _ := by dsimp [C]; field_simp
      have hαε : (C+1)*α ≤ ε := by
        have hh : α ≤ ε/(C+1) := min_le_right _ _
        simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp hh
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hw
      change ε < s * _ at hw
      nlinarith
  exact squeeze_zero (fun B => WitnessCompletion.probability_nonneg _ _) hb
    (by simpa using hE.add hs)

lemma fittedBlock_unscale (r : ∀ B, RetainedBlockRow (B+1))
    (X : ∀ B, BlockSample (r B) → ℝ)
    (hX : fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => Real.sqrt (B+1)*X B w)) :
    fittedBlock_small (fun B => productDesign (r B).law) X := by
  apply fittedBlock_small_mono _ _ _ hX
  intro B w
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [fittedBlock_sqrt_ge_one B, abs_nonneg (X B w)]

lemma fittedBlock_estimated_limit (r : ∀ B, RetainedBlockRow (B+1))
    (p : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (t : ∀ B, (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K T a : ℝ) (h : UniformBlockBounds r m c eta K)
    (hT : 0 ≤ T) (ht : ∀ B b i, |t B b i| ≤ T)
    (hp : ∀ B w b i, 0 < p B w b i)
    (hSim : ∀ ε : ℝ, 0 < ε → Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ b i, ε < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|)) atTop (𝓝 0))
    (ha : Tendsto (fun B => fittedBlock_population (r B) (t B)) atTop (𝓝 a)) :
    fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => fittedBlock_HT (r B) (t B) (p B w) w - a) := by
  have hsim := fittedBlock_simulation_small r p (fun B _ => t B) m c eta K T h hp hSim
    (fun _ _ => False) (by
      simpa [designProbability, designMean] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    hT (fun B _ _ => ht B)
  have h₁ := fittedBlock_unscale r _ hsim
  have h₂ := fittedBlock_HT_consistent r t m c eta K T h hT ht
  have h₃ := fittedBlock_small_deterministic (fun B => productDesign (r B).law)
    (fun B => fittedBlock_population (r B) (t B)) a ha
  have hh := fittedBlock_small_add _ _ _ (fittedBlock_small_add _ _ _ h₁ h₂) h₃
  apply fittedBlock_small_mono _ _ _ hh
  intro B w
  apply le_of_eq
  congr 1
  ring

abbrev fittedBlock_Coordinate (q : ℕ) := Fin q × Option (Fin q)

def fittedBlock_crossproducts {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q) (p : (b : Fin B) → Fin (r.students b) → ℝ)
    (w : BlockSample r) (j : fittedBlock_Coordinate q) : ℝ :=
  match j.2 with
  | none => fittedBlock_HT r (fun b i => x b i j.1 * r.y b i) p w
  | some l => fittedBlock_HT r (fun b i => x b i j.1 * x b i l) p w

def fittedBlock_limitPoint {q : ℕ} (Q : Matrix (Fin q) (Fin q) ℝ)
    (v : Fin q → ℝ) (j : fittedBlock_Coordinate q) : ℝ :=
  match j.2 with | none => v j.1 | some l => Q j.1 l

def fittedBlock_gram {q : ℕ} (a : fittedBlock_Coordinate q → ℝ) :
    Matrix (Fin q) (Fin q) ℝ := fun k l => a (k, some l)

def fittedBlock_rhs {q : ℕ} (a : fittedBlock_Coordinate q → ℝ) : Fin q → ℝ :=
  fun k => a (k, none)

def fittedBlock_coefficient {q : ℕ} (a : fittedBlock_Coordinate q → ℝ) : Fin q → ℝ :=
  (fittedBlock_gram a)⁻¹.mulVec (fittedBlock_rhs a)

lemma fittedBlock_crossproducts_limit {q : ℕ} (r : ∀ B, RetainedBlockRow (B+1))
    (x : ∀ B, RowCovariates (r B) q)
    (p : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K L : ℝ) (Q : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ)
    (h : UniformBlockBounds r m c eta K) (hx : ∀ B b i k, |x B b i k| ≤ L)
    (hQ : ∀ k l, Tendsto (fun B => populationRowGram (r B) (x B) k l) atTop (𝓝 (Q k l)))
    (hv : ∀ k, Tendsto (fun B => populationRowRhs (r B) (x B) k) atTop (𝓝 (v k)))
    (hp : ∀ B w b i, 0 < p B w b i)
    (hSim : ∀ ε : ℝ, 0 < ε → Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ b i, ε < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|)) atTop (𝓝 0)) :
    ∀ j, fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
      fittedBlock_crossproducts (r B) (x B) (p B w) w j - fittedBlock_limitPoint Q v j) := by
  have hx' : ∀ B b i k, |x B b i k| ≤ |L| := fun B b i k =>
    (hx B b i k).trans (le_abs_self L)
  rintro ⟨k, o⟩
  cases o with
  | none =>
      apply fittedBlock_estimated_limit r p (fun B b i => x B b i k * (r B).y b i)
        m c eta K (|L| * K) (v k) h (mul_nonneg (abs_nonneg _) h.2.2.1) _ hp hSim (hv k)
      intro B b i
      rw [abs_mul]
      exact mul_le_mul (hx' B b i k) (((h.2.2.2 B).2 b).2 i).2.1
        (abs_nonneg _) (abs_nonneg _)
  | some l =>
      apply fittedBlock_estimated_limit r p (fun B b i => x B b i k * x B b i l)
        m c eta K (|L| * |L|) (Q k l) h (mul_nonneg (abs_nonneg _) (abs_nonneg _)) _ hp hSim (hQ k l)
      intro B b i
      rw [abs_mul]
      exact mul_le_mul (hx' B b i k) (hx' B b i l) (abs_nonneg _) (abs_nonneg _)

lemma fittedBlock_positive_det {q : ℕ} (Q : Matrix (Fin q) (Fin q) ℝ)
    (hQ : ∀ a : Fin q → ℝ, a ≠ 0 → 0 < ∑ k, a k*(Q.mulVec a) k) : Q.det ≠ 0 := by
  have hker : ∀ a : Fin q → ℝ, Q.mulVec a = 0 → a = 0 := by
    intro a ha
    by_contra hn
    have hh := hQ a hn
    simp only [ha, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hh
    exact lt_irrefl _ hh
  have hinj : Function.Injective Q.mulVec := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, hab, sub_self]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det Q).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

lemma fittedBlock_coefficient_continuous {q : ℕ}
    (Q : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (hQ : Q.det ≠ 0) (k : Fin q) :
    ContinuousAt (fun a => fittedBlock_coefficient a k) (fittedBlock_limitPoint Q v) := by
  have hG : Continuous (fittedBlock_gram (q := q)) :=
    continuous_pi (fun _ => continuous_pi (fun _ => continuous_apply _))
  have hR : Continuous (fittedBlock_rhs (q := q)) :=
    continuous_pi (fun _ => continuous_apply _)
  have hi : ContinuousAt (fun a => (fittedBlock_gram a)⁻¹) (fittedBlock_limitPoint Q v) := by
    apply ContinuousAt.comp (continuousAt_matrix_inv _ _) hG.continuousAt
    change ContinuousAt Ring.inverse Q.det
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hQ
  unfold fittedBlock_coefficient Matrix.mulVec dotProduct
  exact tendsto_finsetSum _ (fun j _ =>
    ((continuous_apply j).continuousAt.comp ((continuous_apply k).continuousAt.comp hi)).mul
      ((continuous_apply j).continuousAt.comp hR.continuousAt))

lemma fittedBlock_coefficient_normalized {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q) (p : (b : Fin B) → Fin (r.students b) → ℝ)
    (w : BlockSample r) (hN : (retainedSize r : ℝ) ≠ 0) :
    fittedRowCoefficient r x p w =
      fittedBlock_coefficient (fittedBlock_crossproducts r x p w) := by
  let G : Matrix (Fin q) (Fin q) ℝ := fun k l => ∑ b, ∑ i,
    (if r.exposed b (w b) i then 1 else 0)/p b i * x b i k*x b i l
  let u : Fin q → ℝ := fun k => ∑ b, ∑ i,
    (if r.exposed b (w b) i then 1 else 0)/p b i * x b i k*r.y b i
  have hG : fittedBlock_gram (fittedBlock_crossproducts r x p w) =
      (retainedSize r : ℝ)⁻¹ • G := by
    ext k l
    change fittedBlock_HT r (fun b i => x b i k * x b i l) p w =
      (retainedSize r : ℝ)⁻¹ * G k l
    simp only [fittedBlock_HT, G, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hu : fittedBlock_rhs (fittedBlock_crossproducts r x p w) =
      (retainedSize r : ℝ)⁻¹ • u := by
    ext k
    simp only [fittedBlock_rhs, fittedBlock_crossproducts, fittedBlock_HT,
      Pi.smul_apply, smul_eq_mul, u, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    ring
  change G⁻¹.mulVec u = _
  unfold fittedBlock_coefficient
  rw [hG, hu, WitnessCompletion.matrix_inv_smul G _ (inv_ne_zero hN),
    Matrix.smul_mulVec, Matrix.mulVec_smul]
  simp [smul_smul, hN]

lemma fittedBlock_coefficient_limit {q : ℕ} (r : ∀ B, RetainedBlockRow (B+1))
    (x : ∀ B, RowCovariates (r B) q)
    (p : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K L : ℝ) (Q : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ)
    (h : UniformBlockBounds r m c eta K) (hx : ∀ B b i k, |x B b i k| ≤ L)
    (hQ : ∀ k l, Tendsto (fun B => populationRowGram (r B) (x B) k l) atTop (𝓝 (Q k l)))
    (hv : ∀ k, Tendsto (fun B => populationRowRhs (r B) (x B) k) atTop (𝓝 (v k)))
    (hposQ : ∀ a : Fin q → ℝ, a ≠ 0 → 0 < ∑ k, a k*(Q.mulVec a) k)
    (hp : ∀ B w b i, 0 < p B w b i)
    (hSim : ∀ ε : ℝ, 0 < ε → Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ b i, ε < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|)) atTop (𝓝 0)) :
    ∀ k, fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
      fittedRowCoefficient (r B) (x B) (p B w) w k - (Q⁻¹.mulVec v) k) := by
  intro k
  have hh := WitnessCompletion.finite_continuous_map (fun B => productDesign (r B).law)
    (fun B w => fittedBlock_crossproducts (r B) (x B) (p B w) w)
    (fittedBlock_limitPoint Q v) (fun a => fittedBlock_coefficient a k)
    (fittedBlock_crossproducts_limit r x p m c eta K L Q v h hx hQ hv hp hSim)
    (fittedBlock_coefficient_continuous Q v (fittedBlock_positive_det Q hposQ) k)
  change fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
    fittedBlock_coefficient (fittedBlock_crossproducts (r B) (x B) (p B w) w) k -
      (Q⁻¹.mulVec v) k) at hh
  have hn : ∀ B w, fittedBlock_coefficient (fittedBlock_crossproducts (r B) (x B) (p B w) w) =
      fittedRowCoefficient (r B) (x B) (p B w) w := by
    intro B w
    exact (fittedBlock_coefficient_normalized _ _ _ _ (fittedBlock_size_pos r m c eta K h B).ne').symm
  simpa only [fittedBlock_small, hn] using hh

lemma fittedBlock_exists_small {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    {I : Type*} [Fintype I] (d : ∀ n, FiniteDesign (Ω n))
    (X : I → ∀ n, Ω n → ℝ) (hX : ∀ i, fittedBlock_small d (X i))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => designProbability (d n) (fun w => ∃ i, ε < |X i n w|)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => WitnessCompletion.probability_nonneg _ _)
    (fun n => WitnessCompletion.probability_exists_le_sum _ _)
  simpa using tendsto_finset_sum Finset.univ (fun i _ => hX i ε hε)

lemma fittedBlock_HT_tail (r : ∀ B, RetainedBlockRow (B+1))
    (t : ∀ B, (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K T : ℝ) (h : UniformBlockBounds r m c eta K)
    (hT : 0 ≤ T) (ht : ∀ B b i, |t B b i| ≤ T) (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    designProbability (productDesign (r B).law) (fun w =>
      ε < |fittedBlock_HT (r B) (t B) (r B).pi w - fittedBlock_population (r B) (t B)|) ≤
      (m:ℝ)^2*(T+2*T/eta)^2/(c^2*(B+1)*ε^2) := by
  have hh := (oracle_row_finite_bounds (fun B => fittedBlock_scalarRow (r B) (t B))
    m c eta T (fittedBlock_scalar_bounds r t m c eta K T h hT ht) B ε hε).2.2.2
  convert hh using 1
  unfold designProbability designMean blockRowProbability
  dsimp only [productDesign, fittedBlock_scalarRow]
  congr 1
  funext w
  congr 1
  congr 1
  rw [fittedBlock_HT_oracle]
  rfl

def fittedBlock_score {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r) : ℝ :=
  (∑ b, ∑ i, (1-(if r.exposed b (w b) i then 1 else 0)/r.pi b i)*t b i) /
    retainedSize r

lemma fittedBlock_score_eq {B : ℕ} (r : RetainedBlockRow B)
    (t : (b : Fin B) → Fin (r.students b) → ℝ) (w : BlockSample r) :
    fittedBlock_score r t w = fittedBlock_population r t - fittedBlock_HT r t r.pi w := by
  unfold fittedBlock_score fittedBlock_population fittedBlock_HT
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma fittedBlock_score_tail (r : ∀ B, RetainedBlockRow (B+1))
    (t : ∀ B, (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K T : ℝ) (h : UniformBlockBounds r m c eta K)
    (hT : 0 ≤ T) (ht : ∀ B b i, |t B b i| ≤ T) (M : ℝ) (hM : 0 < M) (B : ℕ) :
    designProbability (productDesign (r B).law) (fun w =>
      M < |Real.sqrt (B+1)*fittedBlock_score (r B) (t B) w|) ≤
      ((m:ℝ)^2*(T+2*T/eta)^2/c^2)/M^2 := by
  have hs : 0 < Real.sqrt (B+1) := lt_of_lt_of_le zero_lt_one (fittedBlock_sqrt_ge_one B)
  have ht' := fittedBlock_HT_tail r t m c eta K T h hT ht B
    (M/Real.sqrt (B+1)) (div_pos hM hs)
  refine (WitnessCompletion.probability_mono _ _ _ ?_).trans (ht'.trans_eq ?_)
  · intro w hw
    rw [abs_mul, abs_of_pos hs, fittedBlock_score_eq, abs_sub_comm] at hw
    apply (div_lt_iff₀ hs).mpr
    simpa only [mul_comm] using hw
  · rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (B:ℝ)+1)]
    have hn : (B:ℝ)+1 ≠ 0 := by positivity
    field_simp

/-- A uniformly Chebyshev-bounded variable times a vanishing variable vanishes;
the two variables may be dependent and may live on changing finite spaces. -/
lemma fittedBlock_small_tight_mul {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (X Y : ∀ n, Ω n → ℝ) (C : ℝ)
    (hY : fittedBlock_small d Y)
    (hX : ∀ M : ℝ, 0 < M → ∀ n,
      designProbability (d n) (fun w => M < |X n w|) ≤ C/M^2) :
    fittedBlock_small d (fun n w => X n w * Y n w) := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (WitnessCompletion.probability_nonneg _ _))
  · intro b hb
    have hb2 : 0 < b/2 := by positivity
    obtain ⟨M, hM⟩ := exists_nat_gt (max (1:ℝ) (C/(b/2)))
    have hM1 : (1:ℝ) < M := (le_max_left _ _).trans_lt hM
    have hMp : (0:ℝ) < M := zero_lt_one.trans hM1
    have hCM : C < (b/2)*(M:ℝ) := by
      have hc : C/(b/2) < M := (le_max_right _ _).trans_lt hM
      simpa only [mul_comm] using (div_lt_iff₀ hb2).mp hc
    have hMM : (M:ℝ) ≤ (M:ℝ)^2 := by nlinarith
    have htail : C/(M:ℝ)^2 < b/2 := (div_lt_iff₀ (sq_pos_of_pos hMp)).mpr
      (hCM.trans_le (mul_le_mul_of_nonneg_left hMM hb2.le))
    have hy := (hY (ε/M) (div_pos hε hMp)).eventually (eventually_lt_nhds hb2)
    filter_upwards [hy] with n hn
    have hbound : designProbability (d n) (fun w => ε < |X n w * Y n w|) ≤
        designProbability (d n) (fun w => (M:ℝ) < |X n w|) +
        designProbability (d n) (fun w => ε/M < |Y n w|) := by
      refine (WitnessCompletion.probability_mono _ _ _ ?_).trans
        (fittedBlock_probability_union _ _ _)
      intro w hw
      by_contra hh
      push_neg at hh
      have hyM : |Y n w| * (M:ℝ) ≤ ε := (le_div_iff₀ hMp).mp hh.2
      have hprod := mul_le_mul_of_nonneg_right hh.1 (abs_nonneg (Y n w))
      rw [abs_mul] at hw
      nlinarith
    have hxM := hX M hMp n
    linarith

lemma fittedBlock_oracle_eq {B q : ℕ} (r : RetainedBlockRow B)
    (x : RowCovariates r q) (β : Fin q → ℝ)
    (hg : ∀ b i, r.g b i = ∑ k, x b i k * β k) (w : BlockSample r) :
    oracleRowMean r w = fittedRowMean r x β r.pi w := by
  unfold oracleRowMean oracleBlockTotal fittedRowMean
  simp_rw [hg]

lemma fittedBlock_fitting_small {q : ℕ} (r : ∀ B, RetainedBlockRow (B+1))
    (x : ∀ B, RowCovariates (r B) q)
    (β : ∀ B, BlockSample (r B) → Fin q → ℝ) (β₀ : Fin q → ℝ)
    (m : ℕ) (c eta K L : ℝ) (h : UniformBlockBounds r m c eta K)
    (hx : ∀ B b i k, |x B b i k| ≤ L)
    (hβ : ∀ k, fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => β B w k - β₀ k))
    (hg : ∀ B b i, (r B).g b i = ∑ k, x B b i k * β₀ k) :
    fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
      Real.sqrt (B+1) * (fittedRowMean (r B) (x B) (β B w) (r B).pi w -
        oracleRowMean (r B) w)) := by
  have hp : ∀ k, fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
      (Real.sqrt (B+1) * fittedBlock_score (r B) (fun b i => x B b i k) w) *
        (β B w k - β₀ k)) := by
    intro k
    apply fittedBlock_small_tight_mul _ _ _ ((m:ℝ)^2*(|L| + 2*|L| /eta)^2/c^2) (hβ k)
    intro M hM B
    exact fittedBlock_score_tail r (fun B b i => x B b i k) m c eta K |L| h
      (abs_nonneg _) (fun B b i => (hx B b i k).trans (le_abs_self L)) M hM B
  have hh := fittedBlock_small_sum _ _ hp
  apply fittedBlock_small_mono _ _ _ hh
  intro B w
  apply le_of_eq
  congr 1
  rw [fittedBlock_oracle_eq (r B) (x B) β₀ (hg B) w,
    (fitted_mean_subtraction_identities (r B) (x B) (β B w) β₀ (r B).pi w
      (r B).pi_pos).1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold fittedBlock_score
  ring

lemma fittedBlock_weight_fitting_small {q : ℕ} (r : ∀ B, RetainedBlockRow (B+1))
    (x : ∀ B, RowCovariates (r B) q)
    (p : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (β : ∀ B, BlockSample (r B) → Fin q → ℝ) (β₀ : Fin q → ℝ)
    (m : ℕ) (c eta K L : ℝ) (h : UniformBlockBounds r m c eta K)
    (hx : ∀ B b i k, |x B b i k| ≤ L)
    (hp : ∀ B w b i, 0 < p B w b i)
    (hSim : ∀ ε : ℝ, 0 < ε → Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ b i, ε < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|)) atTop (𝓝 0))
    (hβ : ∀ k, fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => β B w k - β₀ k)) :
    fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
      Real.sqrt (B+1) * (fittedRowMean (r B) (x B) (β B w) (p B w) w -
        fittedRowMean (r B) (x B) (β B w) (r B).pi w)) := by
  let E := fun B w => ∃ k, (1:ℝ) < |β B w k - β₀ k|
  let C : ℝ := 1 + ∑ k, |β₀ k|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : Tendsto (fun B => designProbability (productDesign (r B).law) (E B))
      atTop (𝓝 0) := fittedBlock_exists_small _ _ hβ 1 zero_lt_one
  have hb : ∀ B w, ¬ E B w → ∀ k, |β B w k| ≤ C := by
    intro B w he k
    have hk : |β B w k - β₀ k| ≤ 1 := le_of_not_gt (fun hk => he ⟨k, hk⟩)
    have hsum : |β₀ k| ≤ ∑ j, |β₀ j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (β₀ j)) (Finset.mem_univ k)
    calc
      _ = |(β B w k - β₀ k) + β₀ k| := by congr 1; ring
      _ ≤ |β B w k - β₀ k| + |β₀ k| := abs_add_le _ _
      _ ≤ C := by dsimp [C]; linarith
  let T : ℝ := K + (q:ℝ)*|L| * C
  have hT : 0 ≤ T := by dsimp [T]; exact add_nonneg h.2.2.1 (by positivity)
  let t := fun B w b i => (r B).y b i - ∑ k, x B b i k * β B w k
  have ht : ∀ B w, ¬ E B w → ∀ b i, |t B w b i| ≤ T := by
    intro B w he b i
    have hsum : |∑ k, x B b i k * β B w k| ≤ (q:ℝ)*|L| * C := by
      calc
        _ ≤ ∑ k, |x B b i k * β B w k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ : Fin q, |L| * C := Finset.sum_le_sum (fun k _ => by
          rw [abs_mul]
          exact mul_le_mul ((hx B b i k).trans (le_abs_self L)) (hb B w he k)
            (abs_nonneg _) (abs_nonneg _))
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]; ring
    calc
      _ ≤ |(r B).y b i| + |∑ k, x B b i k * β B w k| := by
        simpa only [t, sub_eq_add_neg, abs_neg] using
          abs_add_le ((r B).y b i) (-(∑ k, x B b i k * β B w k))
      _ ≤ T := add_le_add (((h.2.2.2 B).2 b).2 i).2.1 hsum
  have hh := fittedBlock_simulation_small r p t m c eta K T h hp hSim E hE hT ht
  apply fittedBlock_small_mono _ _ _ hh
  intro B w
  apply le_of_eq
  congr 2
  rw [(fitted_mean_subtraction_identities (r B) (x B) (β B w) β₀ (p B w) w
    (hp B w)).2, fittedBlock_HT_sub]

lemma fittedBlock_remainder_small {q : ℕ} (r : ∀ B, RetainedBlockRow (B+1))
    (x : ∀ B, RowCovariates (r B) q)
    (p : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (β : ∀ B, BlockSample (r B) → Fin q → ℝ) (β₀ : Fin q → ℝ)
    (m : ℕ) (c eta K L : ℝ) (h : UniformBlockBounds r m c eta K)
    (hx : ∀ B b i k, |x B b i k| ≤ L)
    (hp : ∀ B w b i, 0 < p B w b i)
    (hSim : ∀ ε : ℝ, 0 < ε → Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ b i, ε < Real.sqrt (B+1)*|p B w b i-(r B).pi b i|)) atTop (𝓝 0))
    (hβ : ∀ k, fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => β B w k - β₀ k))
    (hg : ∀ B b i, (r B).g b i = ∑ k, x B b i k * β₀ k) :
    fittedBlock_small (fun B => productDesign (r B).law) (fun B w =>
      Real.sqrt (B+1) * (fittedRowMean (r B) (x B) (β B w) (p B w) w -
        oracleRowMean (r B) w)) := by
  have hf := fittedBlock_fitting_small r x β β₀ m c eta K L h hx hβ hg
  have hw := fittedBlock_weight_fitting_small r x p β β₀ m c eta K L h hx hp hSim hβ
  have hh := fittedBlock_small_add _ _ _ hw hf
  apply fittedBlock_small_mono _ _ _ hh
  intro B w
  apply le_of_eq
  congr 1
  ring

lemma fittedBlock_consistency_transfer (r : ∀ B, RetainedBlockRow (B+1))
    (μ : ∀ B, BlockSample (r B) → ℝ) (m : ℕ) (c eta K : ℝ)
    (h : UniformBlockBounds r m c eta K)
    (hμ : fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => Real.sqrt (B+1)*(μ B w-oracleRowMean (r B) w))) :
    fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => μ B w-retainedPotentialMean (r B)) := by
  have ho : fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => oracleRowMean (r B) w-retainedPotentialMean (r B)) := by
    intro ε hε
    simpa only [blockRowProbability, designProbability, designMean, productDesign]
      using independent_blocks_oracle_consistent r m c eta K h ε hε
  have hh := fittedBlock_small_add _ _ _ (fittedBlock_unscale r _ hμ) ho
  apply fittedBlock_small_mono _ _ _ hh
  intro B w
  apply le_of_eq
  congr 1
  ring

lemma fittedBlock_size_le (r : ∀ B, RetainedBlockRow (B+1))
    (m : ℕ) (c eta K : ℝ) (h : UniformBlockBounds r m c eta K) (B : ℕ) :
    (retainedSize (r B) : ℝ) ≤ (m:ℝ)*(B+1) := by
  calc
    _ = ∑ b, ((r B).students b : ℝ) := by simp [retainedSize]
    _ ≤ ∑ _ : Fin (B+1), (m:ℝ) := Finset.sum_le_sum (fun b _ => by
      exact_mod_cast ((h.2.2.2 B).2 b).1)
    _ = _ := by simp [Nat.cast_add, Nat.cast_one, mul_comm]

lemma fittedBlock_standardized_small (r : ∀ B, RetainedBlockRow (B+1))
    (X : ∀ B, BlockSample (r B) → ℝ) (m : ℕ) (c eta K σ : ℝ)
    (h : UniformBlockBounds r m c eta K) (hσ : 0 < σ)
    (hv : ∀ B, σ*(B+1) ≤ rowTotalVariance (r B))
    (hX : fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => Real.sqrt (B+1)*X B w)) :
    fittedBlock_small (fun B => productDesign (r B).law)
      (fun B w => (retainedSize (r B):ℝ)*X B w / Real.sqrt (rowTotalVariance (r B))) := by
  apply fittedBlock_small_bound _ _ _ (fun _ _ => False) ((m:ℝ)/Real.sqrt σ) hX
  · simpa [designProbability, designMean] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · intro B w _
    have hn : (0:ℝ) < (B:ℝ)+1 := by positivity
    have hsσ : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
    have hsn : 0 < Real.sqrt (B+1) := Real.sqrt_pos.mpr hn
    have hvp : 0 < rowTotalVariance (r B) := (mul_pos hσ hn).trans_le (hv B)
    have hsv : 0 < Real.sqrt (rowTotalVariance (r B)) := Real.sqrt_pos.mpr hvp
    have hlow : Real.sqrt σ * Real.sqrt (B+1) ≤ Real.sqrt (rowTotalVariance (r B)) := by
      rw [← Real.sqrt_mul hσ.le]
      exact Real.sqrt_le_sqrt (hv B)
    have hratio : (retainedSize (r B):ℝ) / Real.sqrt (rowTotalVariance (r B)) ≤
        ((m:ℝ)/Real.sqrt σ) * Real.sqrt (B+1) := by
      apply (div_le_iff₀ hsv).mpr
      calc
        _ ≤ (m:ℝ)*(B+1) := fittedBlock_size_le r m c eta K h B
        _ = (m:ℝ)*(Real.sqrt (B+1))^2 := by rw [Real.sq_sqrt hn.le]
        _ = (((m:ℝ)/Real.sqrt σ)*Real.sqrt (B+1)) *
            (Real.sqrt σ * Real.sqrt (B+1)) := by
          field_simp <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hsv,
      abs_mul, abs_of_pos hsn, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)/Real.sqrt σ)]
    calc
      _ = ((retainedSize (r B):ℝ) / Real.sqrt (rowTotalVariance (r B))) * |X B w| := by ring
      _ ≤ (((m:ℝ)/Real.sqrt σ) * Real.sqrt (B+1)) * |X B w| :=
        mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ = _ := by ring

lemma fittedBlock_cdf_sandwich {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (Z Y : Ω → ℝ) (z h : ℝ) :
    designProbability d (fun w => Z w ≤ z-h) -
        designProbability d (fun w => h < |Y w-Z w|) ≤
      designProbability d (fun w => Y w ≤ z) ∧
    designProbability d (fun w => Y w ≤ z) ≤
      designProbability d (fun w => Z w ≤ z+h) +
        designProbability d (fun w => h < |Y w-Z w|) := by
  constructor
  · have hh : designProbability d (fun w => Z w ≤ z-h) ≤
        designProbability d (fun w => Y w ≤ z) +
        designProbability d (fun w => h < |Y w-Z w|) := by
      refine (WitnessCompletion.probability_mono _ _ _ ?_).trans
        (fittedBlock_probability_union _ _ _)
      intro w hw
      by_cases he : h < |Y w-Z w|
      · exact Or.inr he
      · left
        have hb := (abs_le.mp (le_of_not_gt he)).2
        linarith
    linarith
  · refine (WitnessCompletion.probability_mono _ _ _ ?_).trans
      (fittedBlock_probability_union _ _ _)
    intro w hw
    by_cases he : h < |Y w-Z w|
    · exact Or.inr he
    · left
      have hb := (abs_le.mp (le_of_not_gt he)).1
      linarith

/-- Slutsky's CDF sandwich, expressed entirely using finite row probabilities. -/
lemma fittedBlock_cdf_transfer {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (d : ∀ n, FiniteDesign (Ω n)) (Z Y : ∀ n, Ω n → ℝ) (F : ℝ → ℝ)
    (hZ : ∀ z, Tendsto (fun n => designProbability (d n) (fun w => Z n w ≤ z))
      atTop (𝓝 (F z)))
    (hD : fittedBlock_small d (fun n w => Y n w-Z n w))
    (hF : ∀ z, ContinuousAt F z) (z : ℝ) :
    Tendsto (fun n => designProbability (d n) (fun w => Y n w ≤ z)) atTop (𝓝 (F z)) := by
  have hplus : Tendsto (fun k : ℕ => F (z+1/((k:ℝ)+1))) atTop (𝓝 (F z)) := by
    apply (hF z).tendsto.comp
    simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hminus : Tendsto (fun k : ℕ => F (z-1/((k:ℝ)+1))) atTop (𝓝 (F z)) := by
    apply (hF z).tendsto.comp
    simpa using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := (hminus.eventually (eventually_gt_nhds ha)).exists
    let h : ℝ := 1/((k:ℝ)+1)
    have hp : 0 < h := by dsimp [h]; positivity
    have hl : Tendsto (fun n => designProbability (d n) (fun w => Z n w ≤ z-h) -
        designProbability (d n) (fun w => h < |Y n w-Z n w|)) atTop (𝓝 (F (z-h))) := by
      simpa using (hZ (z-h)).sub (hD h hp)
    filter_upwards [hl.eventually (eventually_gt_nhds hk)] with n hn
    exact hn.trans_le (fittedBlock_cdf_sandwich (d n) (Z n) (Y n) z h).1
  · intro b hb
    obtain ⟨k, hk⟩ := (hplus.eventually (eventually_lt_nhds hb)).exists
    let h : ℝ := 1/((k:ℝ)+1)
    have hp : 0 < h := by dsimp [h]; positivity
    have hu : Tendsto (fun n => designProbability (d n) (fun w => Z n w ≤ z+h) +
        designProbability (d n) (fun w => h < |Y n w-Z n w|)) atTop (𝓝 (F (z+h))) := by
      simpa using (hZ (z+h)).add (hD h hp)
    filter_upwards [hu.eventually (eventually_lt_nhds hk)] with n hn
    exact lt_of_le_of_lt (fittedBlock_cdf_sandwich (d n) (Z n) (Y n) z h).2 hn

local instance fittedBlock_normalNullSingleton :
    MeasureTheory.NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1:NNReal) ≠ 0)

lemma fittedBlock_normal_cdf_continuous (z : ℝ) :
    ContinuousAt (fun t => (ProbabilityTheory.gaussianReal 0 1 (Set.Iic t)).toReal) z := by
  have hh := AronowAudit.P053.NormalCompletion.cdf_continuousAt
    (ProbabilityTheory.gaussianReal 0 1) z
  convert hh using 1
  funext t
  rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.measureReal_def]

theorem fitted_block_estimator_limit_proof {q : ℕ} (r : ∀ B, RetainedBlockRow (B+1))
    (x : ∀ B, RowCovariates (r B) q)
    (pHat : ∀ B, BlockSample (r B) → (b : Fin (B+1)) → Fin ((r B).students b) → ℝ)
    (m : ℕ) (c eta K L : ℝ) (Q : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ)
    (hbounds : UniformBlockBounds r m c eta K)
    (hx : ∀ B b i k, |x B b i k| ≤ L)
    (hQ : ∀ k l, Filter.Tendsto (fun B => populationRowGram (r B) (x B) k l)
      Filter.atTop (nhds (Q k l)))
    (hv : ∀ k, Filter.Tendsto (fun B => populationRowRhs (r B) (x B) k)
      Filter.atTop (nhds (v k)))
    (hposQ : ∀ a : Fin q → ℝ, a ≠ 0 → 0 < ∑ k, a k*(Q.mulVec a) k)
    (hp : ∀ B w b i, 0 < pHat B w b i)
    (hSim : ∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ b i, eps < Real.sqrt (B+1)*|pHat B w b i-(r B).pi b i|))
      Filter.atTop (nhds 0))
    (hg : ∀ B b i, (r B).g b i = ∑ k, x B b i k*(Q⁻¹.mulVec v) k) :
    let betaStar := Q⁻¹.mulVec v
    let betaHat := fun B w => fittedRowCoefficient (r B) (x B) (pHat B w) w
    let muHat := fun B w => fittedRowMean (r B) (x B) (betaHat B w) (pHat B w) w
    (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => blockRowProbability (r B)
      (fun w => ∃ k, eps < |betaHat B w k-betaStar k|)) Filter.atTop (nhds 0)) ∧
    (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => blockRowProbability (r B)
      (fun w => eps < Real.sqrt (B+1)*|muHat B w-oracleRowMean (r B) w|))
      Filter.atTop (nhds 0)) ∧
    (∀ eps : ℝ, 0 < eps → Filter.Tendsto (fun B => blockRowProbability (r B)
      (fun w => eps < |muHat B w-retainedPotentialMean (r B)|)) Filter.atTop (nhds 0)) ∧
    (∀ sigmaSquared : ℝ, 0 < sigmaSquared →
      (∀ B, sigmaSquared*(B+1) ≤ rowTotalVariance (r B)) →
      ∀ z : ℝ, Filter.Tendsto (fun B => blockRowProbability (r B) (fun w =>
        (retainedSize (r B):ℝ)*(muHat B w-retainedPotentialMean (r B)) /
          Real.sqrt (rowTotalVariance (r B)) ≤ z)) Filter.atTop
        (nhds ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic z)).toReal))) := by
  dsimp only
  let β := fun B w => fittedRowCoefficient (r B) (x B) (pHat B w) w
  let μ := fun B w => fittedRowMean (r B) (x B) (β B w) (pHat B w) w
  have hβ := fittedBlock_coefficient_limit r x pHat m c eta K L Q v hbounds hx hQ hv hposQ hp hSim
  have hμ := fittedBlock_remainder_small r x pHat β (Q⁻¹.mulVec v) m c eta K L
    hbounds hx hp hSim hβ hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro eps heps
    have hh := fittedBlock_exists_small _ _ hβ eps heps
    simpa only [blockRowProbability, designProbability, designMean, productDesign] using hh
  · intro eps heps
    simpa only [blockRowProbability, designProbability, designMean, productDesign,
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using hμ eps heps
  · intro eps heps
    have hh := fittedBlock_consistency_transfer r μ m c eta K hbounds hμ
    simpa only [blockRowProbability, designProbability, designMean, productDesign] using hh eps heps
  · intro σ hσ hvσ z
    let Z := fun B w => (retainedSize (r B):ℝ)*
      (oracleRowMean (r B) w-retainedPotentialMean (r B)) / Real.sqrt (rowTotalVariance (r B))
    let Y := fun B w => (retainedSize (r B):ℝ)*
      (μ B w-retainedPotentialMean (r B)) / Real.sqrt (rowTotalVariance (r B))
    have hs := fittedBlock_standardized_small r (fun B w => μ B w-oracleRowMean (r B) w)
      m c eta K σ hbounds hσ hvσ hμ
    have hD : fittedBlock_small (fun B => productDesign (r B).law)
        (fun B w => Y B w-Z B w) := by
      apply fittedBlock_small_mono _ _ _ hs
      intro B w
      apply le_of_eq
      congr 1
      dsimp [Y, Z]
      ring
    have hZ : ∀ z, Tendsto (fun B => designProbability (productDesign (r B).law)
        (fun w => Z B w ≤ z)) atTop
        (𝓝 ((ProbabilityTheory.gaussianReal 0 1 (Set.Iic z)).toReal)) := by
      simpa only [blockRowProbability, designProbability, designMean, productDesign] using
        (independent_blocks_oracle_normal r m c eta K σ hbounds hσ hvσ).2
    have hh := fittedBlock_cdf_transfer (fun B => productDesign (r B).law) Z Y
      (fun z => (ProbabilityTheory.gaussianReal 0 1 (Set.Iic z)).toReal)
      hZ hD fittedBlock_normal_cdf_continuous z
    simpa only [blockRowProbability, designProbability, designMean, productDesign] using hh

end
end AronowAudit.P037.Wave1
