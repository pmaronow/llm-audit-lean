import SAP.P015b.WH.W2.Leaves
import AronowAudit.P015.P015_Regression
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P015b.WH.W2.P.T22_L2
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal
open SAP.P015b AronowAudit.P015
theorem lift_ae {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {T : Ω → E} (hT : AEMeasurable T P) {p : E → Prop}
    (hp : MeasurableSet {z | p z}) (h : ∀ᵐ z ∂(P.map T), p z) :
    ∀ᵐ s ∂P, p (T s) := (MeasureTheory.ae_map_iff hT hp).1 h
theorem lift_eq {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {T : Ω → E} (hT : AEMeasurable T P) {f g : E → ℝ}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[P.map T] g) : (fun s => f (T s)) =ᵐ[P] fun s => g (T s) := by
  apply lift_ae hT (measurableSet_eq_fun hf hg)
  exact h
end SAP.P015b.WH.W2.P.T22_L2
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal
open SAP.P015b AronowAudit.P015 SAP.P015b.WH.W2.P.T22_L2
theorem SAP.P015b.WH.W2.T22_L2_proof : SAP.P015b.WH.W2.T22_L2 := by
  intro hCE
  classical
  intro Ω hΩ P hP K D Y₀ τ X hX hD hY hτ hunconf ω hlinear hiD hiY hiτ hiDY himY hirτ hirmτ
  let J := ℝ × ℝ × ℝ × (Fin K → ℝ)
  let T : Ω → J := fun s => (D s, Y₀ s, τ s, X s)
  let d : J → ℝ := fun z => z.1
  let y : J → ℝ := fun z => z.2.1
  let t : J → ℝ := fun z => z.2.2.1
  let x : J → Fin K → ℝ := fun z => z.2.2.2
  let Q : Measure J := P.map T
  let m : J → ℝ := fun z => dotProduct (controlVector (x z)) ω
  let r : J → ℝ := fun z => d z - m z
  let m₀ : Ω → ℝ := fun s => dotProduct (controlVector (X s)) ω
  let r₀ : Ω → ℝ := fun s => D s - m₀ s
  have hT : Measurable T := by
    change Measurable (fun s => (D s, Y₀ s, τ s, X s))
    exact hD.prodMk (hY.prodMk (hτ.prodMk hX))
  have hd : Measurable d := measurable_fst
  have hy : Measurable y := measurable_snd.fst
  have ht : Measurable t := measurable_snd.snd.fst
  have hx : Measurable x := measurable_snd.snd.snd
  have hQ : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  letI : IsProbabilityMeasure Q := hQ
  have hStd : StandardBorelSpace J := inferInstance
  letI : StandardBorelSpace J := hStd
  have hdim : ∀ s, m (T s) = m₀ s := by intro s; rfl
  have hcv : Measurable (fun z : J => controlVector (x z)) := by
    refine measurable_pi_iff.mpr ?_
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [controlVector, Fin.cases_zero]
      exact measurable_const
    · simpa [controlVector, Function.comp_def] using (measurable_pi_apply k).comp hx
  have hm : Measurable m := by
    dsimp [m, dotProduct]
    exact Finset.measurable_sum Finset.univ (fun i hi =>
      ((measurable_pi_apply i).comp hcv).mul_const (ω i))
  have hm0 : Measurable m₀ := by
    dsimp [m₀, dotProduct]
    have hcv₀ : Measurable (fun s => controlVector (X s)) := by
      refine measurable_pi_iff.mpr ?_
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [controlVector, Fin.cases_zero]
        exact measurable_const
      · simpa [controlVector, Function.comp_def] using (measurable_pi_apply k).comp hX
    exact Finset.measurable_sum Finset.univ (fun i hi =>
      ((measurable_pi_apply i).comp hcv₀).mul_const (ω i))
  have hiQd : Integrable d Q := by
    apply (integrable_map_measure hd.aestronglyMeasurable hT.aemeasurable).2
    change Integrable (fun s => d (T s)) P
    simpa [d, T] using hiD
  have hiQy : Integrable y Q := by
    apply (integrable_map_measure hy.aestronglyMeasurable hT.aemeasurable).2
    change Integrable (fun s => y (T s)) P
    simpa [y, T] using hiY
  have hiQt : Integrable t Q := by
    apply (integrable_map_measure ht.aestronglyMeasurable hT.aemeasurable).2
    change Integrable (fun s => t (T s)) P
    simpa [t, T] using hiτ
  have hmy : Measurable (fun z : J => m z * y z) := hm.mul hy
  have hiQdy : Integrable (fun z : J => d z * y z) Q := by
    apply (integrable_map_measure (hd.mul hy).aestronglyMeasurable hT.aemeasurable).2
    change Integrable (fun s => d (T s) * y (T s)) P
    simpa [d, y, T] using hiDY
  have hiQmy : Integrable (fun z : J => m z * y z) Q := by
    apply (integrable_map_measure hmy.aestronglyMeasurable hT.aemeasurable).2
    change Integrable (fun s => m (T s) * y (T s)) P
    simpa [m, m₀, y, x, T] using himY
  have hirτQ : Integrable (fun z : J => r z * t z) Q := by
    apply (integrable_map_measure ((hd.sub hm).mul ht).aestronglyMeasurable hT.aemeasurable).2
    change Integrable (fun s => r (T s) * t (T s)) P
    simpa [r, d, m, t, x, T, m₀, controlVector] using hirτ
  have hirmτQ : Integrable (fun z : J => r z * m z * t z) Q := by
    apply (integrable_map_measure ((hd.sub hm).mul hm |>.mul ht).aestronglyMeasurable hT.aemeasurable).2
    change Integrable (fun s => r (T s) * m (T s) * t (T s)) P
    simpa [r, d, m, t, x, T, m₀, controlVector] using hirmτ
  have hciQ : WholeConditionalIndependent Q x (fun z => (y z, t z)) d := by
    intro A B hA hB
    let p : J → Prop := fun z => (y z, t z) ∈ A ∧ d z ∈ B
    let f : J → ℝ := ((fun z => (y z, t z)) ⁻¹' A ∩ d ⁻¹' B).indicator (fun _ => (1 : ℝ))
    let fA : J → ℝ := ((fun z => (y z, t z)) ⁻¹' A).indicator (fun _ => (1 : ℝ))
    let fB : J → ℝ := (d ⁻¹' B).indicator (fun _ => (1 : ℝ))
    have hpair : Measurable (fun z : J => (y z, t z)) := hy.prodMk ht
    have hfs : MeasurableSet ((fun z : J => (y z, t z)) ⁻¹' A ∩ d ⁻¹' B) :=
      (hpair hA).inter (hd hB)
    have hfAs : MeasurableSet ((fun z : J => (y z, t z)) ⁻¹' A) := hpair hA
    have hfBs : MeasurableSet (d ⁻¹' B) := hd hB
    have hf : Measurable f := by dsimp [f]; exact measurable_const.indicator hfs
    have hfA : Measurable fA := by dsimp [fA]; exact measurable_const.indicator hfAs
    have hfB : Measurable fB := by dsimp [fB]; exact measurable_const.indicator hfBs
    have hif : Integrable f Q := by
      dsimp [f]
      exact (integrable_const (1 : ℝ)).indicator hfs
    have hifA : Integrable fA Q := by
      dsimp [fA]
      exact (integrable_const (1 : ℝ)).indicator hfAs
    have hifB : Integrable fB Q := by
      dsimp [fB]
      exact (integrable_const (1 : ℝ)).indicator hfBs
    have hpull := hCE P T hT x hx f hf hif
    have hpullA := hCE P T hT x hx fA hfA hifA
    have hpullB := hCE P T hT x hx fB hfB hifB
    have hsrc := hunconf A B hA hB
    let f₀ : Ω → ℝ := ((fun s => (Y₀ s, τ s)) ⁻¹' A ∩ D ⁻¹' B).indicator (fun _ => (1 : ℝ))
    let fA₀ : Ω → ℝ := ((fun s => (Y₀ s, τ s)) ⁻¹' A).indicator (fun _ => (1 : ℝ))
    let fB₀ : Ω → ℝ := (D ⁻¹' B).indicator (fun _ => (1 : ℝ))
    have hcompf : (fun s => f (T s)) = f₀ := by
      funext s
      change (((fun z => (y z, t z)) ⁻¹' A ∩ d ⁻¹' B).indicator
        (fun _ => (1 : ℝ))) (T s) =
        (((fun u => (Y₀ u, τ u)) ⁻¹' A ∩ D ⁻¹' B).indicator
          (fun _ => (1 : ℝ))) s
      rw [Set.indicator_apply, Set.indicator_apply]
      simp [T, d, y, t, Set.mem_preimage, Set.mem_inter_iff]
    have hcompA : (fun s => fA (T s)) = fA₀ := by
      funext s
      change (((fun z => (y z, t z)) ⁻¹' A).indicator
        (fun _ => (1 : ℝ))) (T s) =
        (((fun u => (Y₀ u, τ u)) ⁻¹' A).indicator
          (fun _ => (1 : ℝ))) s
      rw [Set.indicator_apply, Set.indicator_apply]
      simp [T, y, t, Set.mem_preimage]
    have hcompB : (fun s => fB (T s)) = fB₀ := by
      funext s
      change ((d ⁻¹' B).indicator (fun _ => (1 : ℝ))) (T s) =
        ((D ⁻¹' B).indicator (fun _ => (1 : ℝ))) s
      rw [Set.indicator_apply, Set.indicator_apply]
      simp [T, d, Set.mem_preimage]
    have hleft : P[f₀ | MeasurableSpace.comap X inferInstance] =ᵐ[P]
        fun s => Q[f | MeasurableSpace.comap x inferInstance] (T s) := by
      simpa [Q, x, T, f₀, f, d, y, t, hcompf] using hpull
    have hleftA : P[fA₀ | MeasurableSpace.comap X inferInstance] =ᵐ[P]
        fun s => Q[fA | MeasurableSpace.comap x inferInstance] (T s) := by
      simpa [Q, x, T, fA₀, fA, y, t, hcompA] using hpullA
    have hleftB : P[fB₀ | MeasurableSpace.comap X inferInstance] =ᵐ[P]
        fun s => Q[fB | MeasurableSpace.comap x inferInstance] (T s) := by
      simpa [Q, x, T, fB₀, fB, d, hcompB] using hpullB
    have hcomp : (fun z => Q[f | MeasurableSpace.comap x inferInstance] z) =ᵐ[Q]
        fun z => Q[fA | MeasurableSpace.comap x inferInstance] z *
          Q[fB | MeasurableSpace.comap x inferInstance] z := by
      have hqf : Measurable (Q[f | MeasurableSpace.comap x inferInstance]) := by
        exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
      have hqfA : Measurable (Q[fA | MeasurableSpace.comap x inferInstance]) := by
        exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
      have hqfB : Measurable (Q[fB | MeasurableSpace.comap x inferInstance]) := by
        exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
      apply (MeasureTheory.ae_map_iff hT.aemeasurable (measurableSet_eq_fun hqf
        (hqfA.mul hqfB))).2
      filter_upwards [hleft, hsrc, hleftA, hleftB] with s hl hs hla hlb
      calc
        Q[f | MeasurableSpace.comap x inferInstance] (T s) = P[f₀ | MeasurableSpace.comap X inferInstance] s := hl.symm
        _ = P[fA₀ | MeasurableSpace.comap X inferInstance] s * P[fB₀ | MeasurableSpace.comap X inferInstance] s := hs
        _ = Q[fA | MeasurableSpace.comap x inferInstance] (T s) * Q[fB | MeasurableSpace.comap x inferInstance] (T s) := by rw [hla, hlb]
    simpa [f, fA, fB, WholeConditionalIndependent] using hcomp
  have hpairMeas : Measurable (fun z : J => (y z, t z)) := hy.prodMk ht
  have hciFun : CondIndepFun (MeasurableSpace.comap x inferInstance)
      (Measurable.comap_le hx) (fun z => (y z, t z)) d Q :=
    (condIndepFun_iff_condExp_inter_preimage_eq_mul hpairMeas hd).2 hciQ
  have hqDmeas : Measurable (Q[d | MeasurableSpace.comap x inferInstance]) := by
    exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
  have hqYmeas : Measurable (Q[y | MeasurableSpace.comap x inferInstance]) := by
    exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
  have hqDYmeas : Measurable (Q[(fun z => d z * y z) | MeasurableSpace.comap x inferInstance]) := by
    exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
  have hqRmeas : Measurable (Q[(fun z => r z * t z) | MeasurableSpace.comap x inferInstance]) := by
    exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
  have hqτmeas : Measurable (Q[t | MeasurableSpace.comap x inferInstance]) := by
    exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
  have hqMmeas : Measurable (Q[m | MeasurableSpace.comap x inferInstance]) := by
    exact stronglyMeasurable_condExp.measurable.mono (Measurable.comap_le hx) le_rfl
  have hpullD := hCE P T hT x hx d hd hiQd
  have hDpull : P[D | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => Q[d | MeasurableSpace.comap x inferInstance] (T s) := by
    simpa [Q, x, T, d] using hpullD
  have hlinQ : Q[d | MeasurableSpace.comap x inferInstance] =ᵐ[Q] m := by
    apply (MeasureTheory.ae_map_iff hT.aemeasurable
      (measurableSet_eq_fun hqDmeas hm)).2
    filter_upwards [hDpull, hlinear] with s hp hl
    calc
      Q[d | MeasurableSpace.comap x inferInstance] (T s) =
          P[D | MeasurableSpace.comap X inferInstance] s := hp.symm
      _ = m₀ s := hl
      _ = m (T s) := (hdim s).symm
  have hdonor := AronowAudit.P015.unconfounded_zero_terms
    (P := Q) K d y t x hx hd hy ht hciFun ω hlinQ hiQd hiQy hiQt hiQdy hiQmy hirτQ hirmτQ
  rcases hdonor with ⟨hDYQ, hRzeroQ, hbaseQ, hmixQ⟩
  have hqDY : Measurable (Q[(fun z => d z * y z) | MeasurableSpace.comap x inferInstance]) := hqDYmeas
  have hqR : Measurable (Q[(fun z => r z * t z) | MeasurableSpace.comap x inferInstance]) := hqRmeas
  have hDYlift := lift_eq hT.aemeasurable hqDYmeas
    (hqDmeas.mul hqYmeas) hDYQ
  have hRlift := lift_eq hT.aemeasurable hqRmeas
    (measurable_const : Measurable (fun _ : J => (0 : ℝ))) hRzeroQ
  have hpullDY := hCE P T hT x hx (fun z : J => d z * y z) (hd.mul hy) hiQdy
  have hDYpull : P[(fun s => D s * Y₀ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => Q[(fun z => d z * y z) | MeasurableSpace.comap x inferInstance] (T s) := by
    simpa [Q, x, T, d, y] using hpullDY
  have hpullY := hCE P T hT x hx y hy hiQy
  have hYpull : P[Y₀ | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => Q[y | MeasurableSpace.comap x inferInstance] (T s) := by
    simpa [Q, x, T, y] using hpullY
  have hDYsource : P[(fun s => D s * Y₀ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => P[D | MeasurableSpace.comap X inferInstance] s *
        P[Y₀ | MeasurableSpace.comap X inferInstance] s := by
    filter_upwards [hDYpull, hDpull, hYpull, hDYlift] with s hdy hd' hy' hq
    calc
      P[(fun u => D u * Y₀ u) | MeasurableSpace.comap X inferInstance] s =
          Q[(fun z => d z * y z) | MeasurableSpace.comap x inferInstance] (T s) := hdy
      _ = Q[d | MeasurableSpace.comap x inferInstance] (T s) *
          Q[y | MeasurableSpace.comap x inferInstance] (T s) := hq
      _ = P[D | MeasurableSpace.comap X inferInstance] s *
          P[Y₀ | MeasurableSpace.comap X inferInstance] s := by rw [← hd', ← hy']
  have hpullR := hCE P T hT x hx (fun z : J => r z * t z)
    ((hd.sub hm).mul ht) hirτQ
  have hRpull : P[(fun s => r₀ s * τ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => Q[(fun z => r z * t z) | MeasurableSpace.comap x inferInstance] (T s) := by
    simpa [Q, x, T, r, d, m, t, m₀, controlVector] using hpullR
  have hRsource : P[(fun s => r₀ s * τ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun _ => 0 := by
    filter_upwards [hRpull, hRlift] with s hs hr
    rw [hs, hr]
  have hXM : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hvC (j : Fin (K + 1)) :
      Measurable[MeasurableSpace.comap X inferInstance]
        (fun s => controlVector (X s) j) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [controlVector]
    · simpa [controlVector, Function.comp_def] using (measurable_pi_apply k).comp hXM
  have hmC : Measurable[MeasurableSpace.comap X inferInstance] m₀ := by
    dsimp [m₀, dotProduct]
    exact Finset.measurable_sum Finset.univ (fun j hj => (hvC j).mul_const (ω j))
  have hiM : Integrable m₀ P := by
    exact (integrable_condExp (m := MeasurableSpace.comap X inferInstance) (f := D)).congr
      hlinear
  have hsub := condExp_sub hiD hiM (MeasurableSpace.comap X inferInstance)
  have hcondM := condExp_of_stronglyMeasurable
    (Measurable.comap_le hX) hmC.stronglyMeasurable hiM
  have hResidualMean : P[r₀ | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun _ => 0 := by
    filter_upwards [hsub, hlinear] with s hs hl
    change P[D - m₀ | MeasurableSpace.comap X inferInstance] s = 0
    calc
      P[D - m₀ | MeasurableSpace.comap X inferInstance] s =
          (P[D | MeasurableSpace.comap X inferInstance] -
            P[m₀ | MeasurableSpace.comap X inferInstance]) s := hs
      _ = P[D | MeasurableSpace.comap X inferInstance] s -
          P[m₀ | MeasurableSpace.comap X inferInstance] s := rfl
      _ = m₀ s - m₀ s := by rw [hl, hcondM]
      _ = 0 := sub_self _
  have hRfactor : P[(fun s => r₀ s * τ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => P[r₀ | MeasurableSpace.comap X inferInstance] s *
        P[τ | MeasurableSpace.comap X inferInstance] s := by
    filter_upwards [hRsource, hResidualMean] with s hz hr
    rw [hz, hr]
    simp
  have hMapDY : (∫ z, d z * y z ∂Q) = ∫ s, D s * Y₀ s ∂P := by
    rw [integral_map hT.aemeasurable hiQdy.aestronglyMeasurable]
  have hMapMY : (∫ z, m z * y z ∂Q) = ∫ s, m₀ s * Y₀ s ∂P := by
    rw [integral_map hT.aemeasurable hiQmy.aestronglyMeasurable]
  have hMapMix : (∫ z, r z * m z * t z ∂Q) = ∫ s, r₀ s * m₀ s * τ s ∂P := by
    rw [integral_map hT.aemeasurable hirmτQ.aestronglyMeasurable]
  have hbase : (∫ s, D s * Y₀ s ∂P) - (∫ s, m₀ s * Y₀ s ∂P) = 0 := by
    rw [← hMapDY, ← hMapMY]
    exact hbaseQ
  have hmix : (∫ s, r₀ s * m₀ s * τ s ∂P) = 0 := by
    rw [← hMapMix]
    exact hmixQ
  change (P[(fun s => D s * Y₀ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => P[D | MeasurableSpace.comap X inferInstance] s *
        P[Y₀ | MeasurableSpace.comap X inferInstance] s) ∧
    (P[r₀ | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun _ => 0) ∧
    (P[(fun s => r₀ s * τ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => P[r₀ | MeasurableSpace.comap X inferInstance] s *
        P[τ | MeasurableSpace.comap X inferInstance] s) ∧
    (P[(fun s => r₀ s * τ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun _ => 0) ∧
    ((∫ s, D s * Y₀ s ∂P) - (∫ s, m₀ s * Y₀ s ∂P) = 0) ∧
    (∫ s, r₀ s * m₀ s * τ s ∂P) = 0
  exact ⟨hDYsource, hResidualMean, hRfactor, hRsource, hbase, hmix⟩
