import SAP.P019b.WH.W1.Leaves
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P019b.WH.W1.P.T12_L2
open MeasureTheory ProbabilityTheory Bridge
open scoped BigOperators
noncomputable section
open Classical
variable {Ω : Type} [MeasurableSpace Ω]
private theorem finite_prob_nonneg {m : ℕ} (F : Study (Fin m)) (D : Fin m → Prop) [DecidablePred D] : 0 ≤ F.law.prob D := by
  unfold FiniteLaw.prob FiniteLaw.mean
  apply Finset.sum_nonneg
  intro i hi
  by_cases h : D i <;> simp [h, F.law.nonneg i]
private theorem code_atom {m : ℕ} (F : Study (Fin m)) (i : Fin m) : AronowAudit.P019.Wave1.t19_measure (Bridge.toLaw F.law) {i} = ENNReal.ofReal (F.law.mass i) := by
  rw [AronowAudit.P019.Wave1.t19_measure_apply]
  simp [Bridge.toLaw, AronowAudit.P019.FiniteLaw.prob,
    AronowAudit.P019.FiniteLaw.mean, Set.mem_singleton_iff]
private theorem code_map (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) : S.law.map e = AronowAudit.P019.Wave1.t19_measure (Bridge.toLaw F.law) := by
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply he.1 (measurableSet_singleton i)]
  rw [code_atom]
  exact he.2.1 i
private theorem code_prob (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) (D : Fin m → Prop) [DecidablePred D] : S.prob (fun ω => D (e ω)) = F.law.prob D := by
  unfold WholeStudy.prob
  change (S.law (e ⁻¹' {i : Fin m | D i})).toReal = F.law.prob D
  rw [← Measure.map_apply he.1 (Set.toFinite _).measurableSet,
    code_map S F e he, AronowAudit.P019.Wave1.t19_measure_apply]
  let Dset : Fin m → Prop := fun i => i ∈ {j | D j}
  letI : DecidablePred Dset := fun i => Classical.propDecidable (Dset i)
  have hbridge : (Bridge.toLaw F.law).prob Dset = F.law.prob D := by
    calc
      _ = F.law.prob Dset := Bridge.prob_eq F.law Dset
      _ = F.law.prob D := by
        unfold FiniteLaw.prob FiniteLaw.mean
        simp [Dset, Set.mem_setOf_eq]
  have hn : 0 ≤ (Bridge.toLaw F.law).prob Dset := by
    rw [hbridge]
    exact finite_prob_nonneg F D
  change (ENNReal.ofReal ((Bridge.toLaw F.law).prob Dset)).toReal = F.law.prob D
  rw [ENNReal.toReal_ofReal hn]
  exact hbridge
private theorem code_mean (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) (f : Fin m → ℝ) : S.mean (fun ω => f (e ω)) = F.law.mean f := by
  unfold WholeStudy.mean
  calc
    (∫ ω, f (e ω) ∂S.law) = ∫ i, f i ∂S.law.map e := by
      symm
      exact integral_map he.1.aemeasurable (measurable_of_finite f).aestronglyMeasurable
    _ = ∫ i, f i ∂AronowAudit.P019.Wave1.t19_measure (Bridge.toLaw F.law) := by
      rw [code_map S F e he]
    _ = F.law.mean f := AronowAudit.P019.Wave1.t19_integral (Bridge.toLaw F.law) f
private theorem ae_code_iff (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) (q : Fin m → Prop) : (∀ᵐ ω ∂S.law, q (e ω)) ↔ ∀ i, 0 < F.law.mass i → q i := by
  rw [← ae_map_iff he.1.aemeasurable (Set.toFinite _).measurableSet, code_map S F e he,
    ae_iff_of_countable]
  constructor
  · intro h i hi
    apply h i
    rw [code_atom]
    exact (ENNReal.ofReal_pos.mpr hi).ne'
  · intro h i hi
    rw [code_atom] at hi
    have hne : F.law.mass i ≠ 0 := by
      intro hz
      apply hi
      rw [hz, ENNReal.ofReal_zero]
    exact h i (lt_of_le_of_ne (F.law.nonneg i) (Ne.symm hne))
private theorem mean_transport (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) (f : Ω → ℝ) (g : Fin m → ℝ) (hfg : ∀ᵐ ω ∂S.law, f ω = g (e ω)) : S.mean f = F.law.mean g := by
  unfold WholeStudy.mean
  calc
    (∫ ω, f ω ∂S.law) = ∫ ω, g (e ω) ∂S.law := integral_congr_ae hfg
    _ = F.law.mean g := code_mean S F e he g
private theorem prob_transport (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) (D : Ω → Prop) (E : Fin m → Prop) [DecidablePred D] [DecidablePred E] (hDE : ∀ᵐ ω ∂S.law, D ω ↔ E (e ω)) : S.prob D = F.law.prob E := by
  have hsets : {ω | D ω} =ᵐ[S.law] {ω | E (e ω)} := by
    filter_upwards [hDE] with ω hω
    exact propext hω
  calc
    S.prob D = S.prob (fun ω => E (e ω)) := by
      unfold WholeStudy.prob
      rw [measure_congr hsets]
    _ = F.law.prob E := code_prob S F e he E
private theorem ce_transport (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) (f : Ω → ℝ) (g : Fin m → ℝ) (D : Ω → Prop) (E : Fin m → Prop) [DecidablePred E] (hfg : ∀ᵐ ω ∂S.law, f ω = g (e ω)) (hDE : ∀ᵐ ω ∂S.law, D ω ↔ E (e ω)) : S.ce f D = F.law.ce g E := by
  letI : DecidablePred D := fun ω => Classical.propDecidable (D ω)
  have hnum : ∀ᵐ ω ∂S.law, (if D ω then f ω else 0) =
      (if E (e ω) then g (e ω) else 0) := by
    filter_upwards [hfg, hDE] with ω hf hD
    simp [hf, hD]
  calc
    S.ce f D = S.mean (fun ω => if D ω then f ω else 0) / S.prob D := by
      unfold WholeStudy.ce
      rfl
    _ = F.law.mean (fun i => if E i then g i else 0) / F.law.prob E := by
      rw [mean_transport S F e he _ (fun i => if E i then g i else 0) hnum,
        prob_transport S F e he D E hDE]
    _ = F.law.ce g E := by
      unfold FiniteLaw.ce
      rfl
private theorem ae_recovery_iff (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (p : Ω → Prop) (q : Fin m → Prop) (hpq : ∀ᵐ ω ∂S.law, p ω ↔ q (e ω)) : (∀ᵐ ω ∂S.law, p ω) ↔ ∀ᵐ ω ∂S.law, q (e ω) := by
  constructor <;> intro h
  · filter_upwards [h, hpq] with ω hp hq
    exact hq.mp hp
  · filter_upwards [h, hpq] with ω hq hp
    exact hp.mpr hq
private theorem recovered (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (he : WholeEncoding S F e) : (∀ᵐ ω ∂S.law, F.W (e ω) = S.W ω) ∧ (∀ᵐ ω ∂S.law, F.X (e ω) = S.X ω) ∧ (∀ᵐ ω ∂S.law, F.Y (e ω) = S.Y ω) ∧ (∀ᵐ ω ∂S.law, F.Z (e ω) = S.Z ω) ∧ (∀ᵐ ω ∂S.law, F.V (e ω) = S.V ω) := by
  rcases he.2.2 with h
  exact ⟨h.mono (fun ω h => h.1), h.mono (fun ω h => h.2.1),
    h.mono (fun ω h => h.2.2.1), h.mono (fun ω h => h.2.2.2.1),
    h.mono (fun ω h => h.2.2.2.2)⟩
theorem transport : SAP.P019b.WH.W1.T12_L2 := by
  intro Ω _ S m F e he
  let hr := recovered S F e he
  rcases hr with ⟨hW, hX, hY, hZ, hV⟩
  have hcell : ∀ z y, ∀ᵐ ω ∂S.law,
      S.cell z y ω ↔ F.cell z y (e ω) := by
    intro z y
    filter_upwards [hZ, hY] with ω hz hy
    simp [WholeStudy.cell, Study.cell, hz, hy]
  have hmonoRec : ∀ᵐ ω ∂S.law,
      (S.Y ω = true → S.X ω = true) ↔
        (F.Y (e ω) = true → F.X (e ω) = true) := by
    filter_upwards [hX, hY] with ω hx hy
    simp [hx, hy]
  have hdesignRec : ∀ᵐ ω ∂S.law,
      ((S.V ω : ℝ) = (S.W ω : ℝ) + bitVal (S.X ω) * bitVal (S.Z ω)) ↔
        ((F.V (e ω) : ℝ) = (F.W (e ω) : ℝ) +
          bitVal (F.X (e ω)) * bitVal (F.Z (e ω))) := by
    filter_upwards [hW, hX, hZ, hV] with ω hw hx hz hv
    simp [hw, hx, hz, hv]
  have hmono : S.monotone ↔ F.monotone := by
    unfold WholeStudy.monotone Study.monotone
    rw [ae_recovery_iff S F e (fun ω => S.Y ω = true → S.X ω = true)
      (fun i => F.Y i = true → F.X i = true) hmonoRec,
      ae_code_iff S F e he (fun i => F.Y i = true → F.X i = true)]
  have hdesign : S.noLiarsDesign ↔ F.noLiarsDesign := by
    unfold WholeStudy.noLiarsDesign Study.noLiarsDesign
    rw [ae_recovery_iff S F e
      (fun ω => (S.V ω : ℝ) = (S.W ω : ℝ) + bitVal (S.X ω) * bitVal (S.Z ω))
      (fun i => (F.V i : ℝ) = (F.W i : ℝ) + bitVal (F.X i) * bitVal (F.Z i)) hdesignRec,
      ae_code_iff S F e he
        (fun i => (F.V i : ℝ) = (F.W i : ℝ) + bitVal (F.X i) * bitVal (F.Z i))]
  have hcellProb : ∀ z y, S.prob (S.cell z y) = F.law.prob (F.cell z y) := by
    intro z y
    exact prob_transport S F e he (S.cell z y) (F.cell z y) (hcell z y)
  have hmu : S.mu = F.mu := by
    unfold WholeStudy.mu Study.mu
    exact prob_transport S F e he (fun ω => S.X ω = true) (fun i => F.X i = true) (by
      filter_upwards [hX] with ω hx
      simp [hx])
  have hmeanY : S.mean (fun ω => bitVal (S.Y ω)) =
      F.law.mean (fun i => bitVal (F.Y i)) := by
    apply mean_transport S F e he
    filter_upwards [hY] with ω hy
    simp [hy]
  have hmeanNotY : S.mean (fun ω => 1 - bitVal (S.Y ω)) =
      F.law.mean (fun i => 1 - bitVal (F.Y i)) := by
    apply mean_transport S F e he
    filter_upwards [hY] with ω hy
    simp [hy]
  have hlist : ∀ z y, S.listMean z y = F.listMean z y := by
    intro z y
    unfold WholeStudy.listMean Study.listMean
    apply ce_transport S F e he
    · filter_upwards [hV] with ω hv
      simp [hv]
    · exact hcell z y
  have hcombined : S.combined = F.combined := by
    unfold WholeStudy.combined Study.combined
    rw [hmeanY, hmeanNotY, hlist true false, hlist false false]
  have hbeta : S.beta = F.beta := by
    unfold WholeStudy.beta Study.beta
    rw [hlist true true, hlist false true]
  have hfalseMass : S.falseMass = F.law.prob (fun i => F.X i = false ∧ F.Y i = true) := by
    unfold WholeStudy.falseMass
    exact prob_transport S F e he
      (fun ω => S.X ω = false ∧ S.Y ω = true)
      (fun i => F.X i = false ∧ F.Y i = true) (by
        filter_upwards [hX, hY] with ω hx hy
        simp [hx, hy])
  have hconfProb : S.prob (fun ω => S.Y ω = true) =
      F.law.prob (fun i => F.Y i = true) := by
    exact prob_transport S F e he (fun ω => S.Y ω = true) (fun i => F.Y i = true) (by
      filter_upwards [hY] with ω hy
      simp [hy])
  have hconfX : S.confessorX = F.law.ce (fun i => bitVal (F.X i))
      (fun i => F.Y i = true) := by
    unfold WholeStudy.confessorX
    apply ce_transport S F e he
    · filter_upwards [hX] with ω hx
      simp [hx]
    · filter_upwards [hY] with ω hy
      simp [hy]
  have hcontrol : ∀ t, S.controlAtom t =
      F.law.ce (fun i => if (F.V i : ℝ) = t then 1 else 0) (F.cell false true) := by
    intro t
    unfold WholeStudy.controlAtom
    apply ce_transport S F e he
    · filter_upwards [hV] with ω hv
      simp [hv]
    · exact hcell false true
  have htreated : ∀ t, S.treatedAtom t =
      F.law.ce (fun i => if (F.V i : ℝ) = t + 1 then 1 else 0) (F.cell true true) := by
    intro t
    unfold WholeStudy.treatedAtom
    apply ce_transport S F e he
    · filter_upwards [hV] with ω hv
      simp [hv]
    · exact hcell true true
  have hcv : ∀ z y, S.cv (fun ω => (S.V ω : ℝ)) (S.cell z y) =
      F.law.cv (fun i => (F.V i : ℝ)) (F.cell z y) := by
    intro z y
    unfold WholeStudy.cv FiniteLaw.cv
    have hsq : S.ce (fun ω => (S.V ω : ℝ) ^ 2) (S.cell z y) =
        F.law.ce (fun i => (F.V i : ℝ) ^ 2) (F.cell z y) := ce_transport S F e he
      (fun ω => (S.V ω : ℝ) ^ 2) (fun i => (F.V i : ℝ) ^ 2)
      (S.cell z y) (F.cell z y) (by
        filter_upwards [hV] with ω hv
        simp [hv]) (hcell z y)
    have hav : S.ce (fun ω => (S.V ω : ℝ)) (S.cell z y) =
        F.law.ce (fun i => (F.V i : ℝ)) (F.cell z y) := ce_transport S F e he
      (fun ω => (S.V ω : ℝ)) (fun i => (F.V i : ℝ))
      (S.cell z y) (F.cell z y) (by
        filter_upwards [hV] with ω hv
        simp [hv]) (hcell z y)
    rw [hsq, hav]
  have hvarZ : S.variance (fun ω => bitVal (S.Z ω)) =
      F.law.variance (fun i => bitVal (F.Z i)) := by
    unfold WholeStudy.variance FiniteLaw.variance
    have hsq : S.mean (fun ω => bitVal (S.Z ω) ^ 2) =
        F.law.mean (fun i => bitVal (F.Z i) ^ 2) := mean_transport S F e he _ _ (by
      filter_upwards [hZ] with ω hz
      simp [hz])
    have hav : S.mean (fun ω => bitVal (S.Z ω)) =
        F.law.mean (fun i => bitVal (F.Z i)) := mean_transport S F e he _ _ (by
      filter_upwards [hZ] with ω hz
      simp [hz])
    rw [hsq, hav]
  have hvarY : S.variance (fun ω => bitVal (S.Y ω)) =
      F.law.variance (fun i => bitVal (F.Y i)) := by
    unfold WholeStudy.variance FiniteLaw.variance
    have hsq : S.mean (fun ω => bitVal (S.Y ω) ^ 2) =
        F.law.mean (fun i => bitVal (F.Y i) ^ 2) := mean_transport S F e he _ _ (by
      filter_upwards [hY] with ω hy
      simp [hy])
    have hav : S.mean (fun ω => bitVal (S.Y ω)) =
        F.law.mean (fun i => bitVal (F.Y i)) := mean_transport S F e he _ _ (by
      filter_upwards [hY] with ω hy
      simp [hy])
    rw [hsq, hav]
  have hnondeg : S.nondegenerate ↔ F.nondegenerate := by
    unfold WholeStudy.nondegenerate Study.nondegenerate
    constructor <;> intro h
    · rcases h with ⟨hc, hz, hy⟩
      refine ⟨?_, ?_, ?_⟩
      · intro z y
        have hh := hc z y
        exact ⟨by rw [← hcellProb z y]; exact hh.1,
          by rw [← hcv z y]; exact hh.2⟩
      · rw [← hvarZ]
        exact hz
      · rw [← hvarY]
        exact hy
    · rcases h with ⟨hc, hz, hy⟩
      refine ⟨?_, ?_, ?_⟩
      · intro z y
        have hh := hc z y
        rw [← hcellProb z y, ← hcv z y] at hh
        exact hh
      · rw [hvarZ]
        exact hz
      · rw [hvarY]
        exact hy
  exact ⟨hmono, hdesign, hnondeg, hcellProb, hmu, hcombined, hbeta,
    hfalseMass, hconfProb, hconfX, hcontrol, htreated⟩
end
end SAP.P019b.WH.W1.P.T12_L2
theorem SAP.P019b.WH.W1.T12_L2_proof : SAP.P019b.WH.W1.T12_L2 := by
  exact SAP.P019b.WH.W1.P.T12_L2.transport
