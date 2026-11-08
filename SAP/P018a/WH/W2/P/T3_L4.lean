import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.Wave1.Gap.GLP0181B5

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W2.P.T3_L4

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
open SAP.P018a

def indicator {N : ℕ} (s : Finset (Fin N)) (i : Fin N) : ℝ :=
  if i ∈ s then 1 else 0

def loading {N : ℕ} (d : Dyad N) (i : Fin N) : ℝ :=
  indicator (members d) i - 2 / (N : ℝ)

def toAuditDyad {N : ℕ} (d : Dyad N) : AronowAudit.P018.Dyad N :=
  ⟨d.val, by
    rw [← SAP.P018a.Bridge.dyads_agree]
    exact d.property⟩

@[simp] lemma audit_members {N : ℕ} (d : Dyad N) :
    AronowAudit.P018.members (toAuditDyad d) = members d := rfl

lemma indicator_mul {N : ℕ} (s t : Finset (Fin N)) (i : Fin N) :
    indicator s i * indicator t i = indicator (s ∩ t) i := by
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [indicator, hs, ht]

lemma sum_indicator {N : ℕ} (s : Finset (Fin N)) :
    (∑ i, indicator s i) = (s.card : ℝ) := by
  change (∑ i, if i ∈ s then (1 : ℝ) else 0) = _
  rw [AronowAudit.P018.Wave1.appendixB_indicator_sum]
  simp

lemma sum_indicator2 {N : ℕ} (s t : Finset (Fin N)) :
    (∑ i, indicator s i * indicator t i) = ((s ∩ t).card : ℝ) := by
  calc
    _ = ∑ i, indicator (s ∩ t) i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [indicator_mul]
    _ = _ := sum_indicator _

lemma sum_indicator3 {N : ℕ} (s t u : Finset (Fin N)) :
    (∑ i, indicator s i * indicator t i * indicator u i) = ((s ∩ t ∩ u).card : ℝ) := by
  calc
    _ = ∑ i, indicator (s ∩ t) i * indicator u i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [indicator_mul]
    _ = _ := by rw [sum_indicator2]

lemma sum_indicator4 {N : ℕ} (s t u v : Finset (Fin N)) :
    (∑ i, indicator s i * indicator t i * indicator u i * indicator v i) =
      ((s ∩ t ∩ u ∩ v).card : ℝ) := by
  calc
    _ = ∑ i, indicator (s ∩ t ∩ u) i * indicator v i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [indicator_mul, indicator_mul]
    _ = _ := by rw [sum_indicator2]

lemma sum_indicator_pair {N : ℕ} (i j : Fin N) (hij : i ≠ j) (u : Fin N → ℝ) :
    (∑ l, (if l ∈ ({i,j} : Finset (Fin N)) then 1 else 0) * u l) = u i + u j := by
  have hp : ∀ l, (if l ∈ ({i,j} : Finset (Fin N)) then (1 : ℝ) else 0) * u l =
      if l ∈ ({i,j} : Finset (Fin N)) then u l else 0 := by
    intro l
    by_cases hl : l ∈ ({i,j} : Finset (Fin N)) <;> simp [hl]
  simp_rw [hp, AronowAudit.P018.Wave1.appendixB_indicator_sum]
  rw [Finset.sum_pair (by exact hij)]

lemma wholeSignLinear_pair {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ω : Fin N → Bool) :
    wholeSignLinear (fun l => indicator ({i,j} : Finset (Fin N)) l) ω =
      signValue (ω i) + signValue (ω j) := by
  unfold wholeSignLinear
  change (∑ l, (if l ∈ ({i,j} : Finset (Fin N)) then 1 else 0) *
      signValue (ω l)) = _
  exact sum_indicator_pair i j hij (fun l => signValue (ω l))

lemma sap_audit_residual {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) :
    SAP.P018a.fittedResidual (SAP.P018a.design SAP.P018a.signKernel ω)
      (SAP.P018a.response SAP.P018a.signKernel ω) d =
    AronowAudit.P018.fittedResidual (AronowAudit.P018.design AronowAudit.P018.signKernel ω)
      (AronowAudit.P018.response AronowAudit.P018.signKernel ω) (toAuditDyad d) := by
  rfl

lemma sap_audit_unitLaw (N : ℕ) :
    SAP.P018a.unitSampleLaw SAP.P018a.signKernel N =
      AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N := rfl

lemma sap_audit_signValue (b : Bool) :
    SAP.P018a.signValue b = AronowAudit.P018.signValue b := rfl

lemma sap_populationBeta_zero : SAP.P018a.populationBeta SAP.P018a.signKernel = 0 := by
  change AronowAudit.P018.populationBeta AronowAudit.P018.signKernel = 0
  exact AronowAudit.P018.Wave1.appendixB_populationBeta

lemma sap_residual_linear {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) (d : Dyad N) :
    fittedResidual (design signKernel ω) (response signKernel ω) d =
      wholeSignLinear (loading d) ω := by
  rw [sap_audit_residual]
  rw [AronowAudit.P018.Wave1.appendixB_residual_linear hN ω (toAuditDyad d)]
  simp [wholeSignLinear, loading, indicator, audit_members, ← sap_audit_signValue]
  rfl

lemma loading_dot {N : ℕ} (hN : 2 ≤ N) (d f : Dyad N) :
    dot (loading d) (loading f) = ((members d ∩ members f).card : ℝ) - 4/(N : ℝ) := by
  calc
    _ = ∫ ω, (∑ i, loading d i * AronowAudit.P018.signValue (ω i)) *
          (∑ i, loading f i * AronowAudit.P018.signValue (ω i))
          ∂ unitSampleLaw signKernel N :=
      (AronowAudit.P018.Wave1.appendixB_linear_product (loading d) (loading f)).symm
    _ = ∫ ω, AronowAudit.P018.fittedResidual
          (AronowAudit.P018.design AronowAudit.P018.signKernel ω)
          (AronowAudit.P018.response AronowAudit.P018.signKernel ω) (toAuditDyad d) *
          AronowAudit.P018.fittedResidual
          (AronowAudit.P018.design AronowAudit.P018.signKernel ω)
          (AronowAudit.P018.response AronowAudit.P018.signKernel ω) (toAuditDyad f)
          ∂ unitSampleLaw signKernel N := by
      simp_rw [AronowAudit.P018.Wave1.appendixB_residual_linear hN]
      simp [loading, indicator, audit_members]
      rfl
    _ = _ := by
      rw [sap_audit_unitLaw]
      exact AronowAudit.P018.Wave1.appendixB_residual_product hN
        (toAuditDyad d) (toAuditDyad f)

lemma residual_linear_pair {N : ℕ} (hN : 2 ≤ N) (i j : Fin N) (hij : i ≠ j)
    (ω : Fin N → Bool) :
    fittedResidual (design signKernel ω) (response signKernel ω) (wholeDyad i j hij) =
      signValue (ω i) + signValue (ω j) - (2/(N : ℝ))*wholeSignSum ω := by
  rw [sap_audit_residual]
  rw [AronowAudit.P018.Wave1.appendixB_residual_linear hN ω
    (toAuditDyad (wholeDyad i j hij))]
  have hm : AronowAudit.P018.members (toAuditDyad (wholeDyad i j hij)) = {i,j} := rfl
  rw [hm]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp_rw [← sap_audit_signValue]
  rw [sum_indicator_pair i j hij (fun l => signValue (ω l))]
  simp [wholeSignSum]

lemma sum_loading_product {N : ℕ} (A B C D : Finset (Fin N))
    (hA : A.card = 2) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 2)
    (hAB : (A ∩ B).card = 1) (hCD : (C ∩ D).card = 1)
    (hAC : (A ∩ C).card = 0) (hAD : (A ∩ D).card = 0)
    (hBC : (B ∩ C).card = 0) (hBD : (B ∩ D).card = 0)
    (hABC : (A ∩ B ∩ C).card = 0) (hABD : (A ∩ B ∩ D).card = 0)
    (hACD : (A ∩ C ∩ D).card = 0) (hBCD : (B ∩ C ∩ D).card = 0)
    (hABCD : (A ∩ B ∩ C ∩ D).card = 0) :
    (∑ i, (indicator A i - 2/(N : ℝ)) * (indicator B i - 2/(N : ℝ)) *
      (indicator C i - 2/(N : ℝ)) * (indicator D i - 2/(N : ℝ))) =
        2*(2/(N : ℝ))^2 - 8*(2/(N : ℝ))^3 + (N : ℝ)*(2/(N : ℝ))^4 := by
  let t : ℝ := 2/(N : ℝ)
  have hexp : (∑ i, (indicator A i - t) * (indicator B i - t) *
      (indicator C i - t) * (indicator D i - t)) =
      ((∑ i, indicator A i * indicator B i * indicator C i * indicator D i) -
        t * ((∑ i, indicator A i * indicator B i * indicator C i) +
          (∑ i, indicator A i * indicator B i * indicator D i) +
          (∑ i, indicator A i * indicator C i * indicator D i) +
          (∑ i, indicator B i * indicator C i * indicator D i)) +
        t^2 * ((∑ i, indicator A i * indicator B i) +
          (∑ i, indicator A i * indicator C i) +
          (∑ i, indicator A i * indicator D i) +
          (∑ i, indicator B i * indicator C i) +
          (∑ i, indicator B i * indicator D i) +
          (∑ i, indicator C i * indicator D i)) -
        t^3 * ((∑ i, indicator A i) + (∑ i, indicator B i) +
          (∑ i, indicator C i) + (∑ i, indicator D i)) +
        (N : ℝ)*t^4) := by
    calc
      _ = ∑ i, (indicator A i * indicator B i * indicator C i * indicator D i -
          t * (indicator A i * indicator B i * indicator C i +
            indicator A i * indicator B i * indicator D i +
            indicator A i * indicator C i * indicator D i +
            indicator B i * indicator C i * indicator D i) +
          t^2 * (indicator A i * indicator B i + indicator A i * indicator C i +
            indicator A i * indicator D i + indicator B i * indicator C i +
            indicator B i * indicator D i + indicator C i * indicator D i) -
          t^3 * (indicator A i + indicator B i + indicator C i + indicator D i) + t^4) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (∑ i, (indicator A i - 2/(N : ℝ)) * (indicator B i - 2/(N : ℝ)) *
      (indicator C i - 2/(N : ℝ)) * (indicator D i - 2/(N : ℝ))) =
      (∑ i, (indicator A i - t) * (indicator B i - t) *
        (indicator C i - t) * (indicator D i - t)) by rfl, hexp]
  rw [sum_indicator4, sum_indicator3, sum_indicator3, sum_indicator3, sum_indicator3,
    sum_indicator2, sum_indicator2, sum_indicator2, sum_indicator2, sum_indicator2,
    sum_indicator2, sum_indicator, sum_indicator, sum_indicator, sum_indicator]
  have hABC' : (A ∩ (B ∩ C)).card = 0 := by simpa [Finset.inter_assoc] using hABC
  have hABD' : (A ∩ (B ∩ D)).card = 0 := by simpa [Finset.inter_assoc] using hABD
  have hACD' : (A ∩ (C ∩ D)).card = 0 := by simpa [Finset.inter_assoc] using hACD
  have hBCD' : (B ∩ (C ∩ D)).card = 0 := by simpa [Finset.inter_assoc] using hBCD
  have hABCD' : (A ∩ (B ∩ (C ∩ D))).card = 0 := by simpa [Finset.inter_assoc] using hABCD
  simp [t, hAB, hCD, hAC, hAD, hBC, hBD, hABC', hABD', hACD', hBCD', hABCD',
    hA, hB, hC, hD]
  <;> ring

lemma signValue_cons {N : ℕ} (b : Bool) (ω : Fin N → Bool) :
    (fun i : Fin (N+1) => SAP.P018a.signValue
      (Fin.cons (α := fun _ : Fin (N+1) => Bool) b ω i)) =
      Matrix.vecCons (SAP.P018a.signValue b) (fun i => SAP.P018a.signValue (ω i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [SAP.P018a.signValue]
  · intro j
    simp [SAP.P018a.signValue]

lemma fairAverage_sum (N : ℕ) (f : (Fin N → ℝ) → ℝ) :
    SAP.P018a.fairAverage N f =
      (∑ ω : Fin N → Bool, f (fun i => SAP.P018a.signValue (ω i))) / (2 : ℝ)^N := by
  induction N with
  | zero =>
      simp only [SAP.P018a.fairAverage, pow_zero, div_one]
      rw [Fintype.sum_unique]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ N ih =>
      let e : (Bool × (Fin N → Bool)) ≃ (Fin (N+1) → Bool) :=
        (Fin.consEquiv (fun _ : Fin (N+1) => Bool))
      let p : (Fin N → Bool) → ℝ := fun x => f (Matrix.vecCons 1
        (fun i => SAP.P018a.signValue (x i)))
      let m : (Fin N → Bool) → ℝ := fun x => f (Matrix.vecCons (-1)
        (fun i => SAP.P018a.signValue (x i)))
      have hs : (∑ ω : Fin (N+1) → Bool,
          f (fun i => SAP.P018a.signValue (ω i))) =
          (∑ x : Fin N → Bool, p x) + ∑ x : Fin N → Bool, m x := by
        rw [← e.sum_comp (fun ω : Fin (N+1) → Bool =>
          f (fun i => SAP.P018a.signValue (ω i))), Fintype.sum_prod_type,
          Fintype.sum_bool]
        simp only [e, Fin.consEquiv_apply]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro x hx
          dsimp [p]
          congr 1
          funext i
          refine Fin.cases ?_ ?_ i
          · simp [Fin.cons, SAP.P018a.signValue, Matrix.vecCons] <;> rfl
          · intro j
            simp [Fin.cons, SAP.P018a.signValue, Matrix.vecCons] <;> rfl
        · apply Finset.sum_congr rfl
          intro x hx
          dsimp [m]
          congr 1
          funext i
          refine Fin.cases ?_ ?_ i
          · simp [Fin.cons, SAP.P018a.signValue, Matrix.vecCons] <;> rfl
          · intro j
            simp [Fin.cons, SAP.P018a.signValue, Matrix.vecCons] <;> rfl
      calc
        SAP.P018a.fairAverage (N+1) f =
            (SAP.P018a.fairAverage N (fun u => f (Matrix.vecCons 1 u)) +
              SAP.P018a.fairAverage N (fun u => f (Matrix.vecCons (-1) u))) / 2 := rfl
        _ = ((∑ x : Fin N → Bool, p x) / (2 : ℝ)^N +
              (∑ x : Fin N → Bool, m x) / (2 : ℝ)^N) / 2 := by
          rw [ih, ih]
        _ = ((∑ x : Fin N → Bool, p x) + ∑ x : Fin N → Bool, m x) /
              (2 : ℝ)^(N+1) := by rw [pow_succ]; ring
        _ = (∑ ω : Fin (N+1) → Bool,
              f (fun i => SAP.P018a.signValue (ω i))) / (2 : ℝ)^(N+1) := by rw [hs]

lemma fairIntegral_average (f : (Fin 8 → ℝ) → ℝ) :
    (∫ ω, f (fun i => SAP.P018a.signValue (ω i)) ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8) =
      SAP.P018a.fairAverage 8 f := by
  letI : IsProbabilityMeasure SAP.P018a.fairLaw := by
    unfold SAP.P018a.fairLaw
    infer_instance
  letI : IsProbabilityMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => SAP.P018a.fairLaw))
    infer_instance
  rw [integral_fintype (AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
  have hm (ω : Fin 8 → Bool) :
      (SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8).real {ω} = (1/2 : ℝ)^8 := by
    simp [SAP.P018a.unitSampleLaw, Measure.pi_singleton, SAP.P018a.signKernel,
    SAP.P018a.fairLaw, Measure.real, PMF.toMeasure_uniformOfFintype_apply,
    Fintype.card_bool, Fintype.card_fin]
  simp_rw [hm, smul_eq_mul]
  rw [← Finset.mul_sum, fairAverage_sum]
  norm_num <;> ring

end SAP.P018a.WH.W2.P.T3_L4

open SAP.P018a.WH.W2.P.T3_L4
open MeasureTheory ProbabilityTheory

theorem SAP.P018a.WH.W2.T3_L4_proof : SAP.P018a.WH.W2.T3_L4 := by
  intro hlin
  change SAP.P018a.T3FittedCovariances
  unfold SAP.P018a.T3FittedCovariances
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    let e : Fin 6 → Fin N := fun r => ⟨r.val, by have := r.isLt; omega⟩
    have einj : Function.Injective e := by
      intro a b h
      have hv : a.val = b.val := by simpa [e] using congrArg Fin.val h
      exact Fin.ext hv
    have hne (a b : Fin 6) (hab : a ≠ b) : e a ≠ e b := by
      intro h
      exact hab (einj h)
    let i0 := e 0
    let i1 := e 1
    let i2 := e 2
    let i3 := e 3
    let i4 := e 4
    let i5 := e 5
    have h01 : i0 ≠ i1 := hne 0 1 (by decide)
    have h02 : i0 ≠ i2 := hne 0 2 (by decide)
    have h03 : i0 ≠ i3 := hne 0 3 (by decide)
    have h04 : i0 ≠ i4 := hne 0 4 (by decide)
    have h05 : i0 ≠ i5 := hne 0 5 (by decide)
    have h12 : i1 ≠ i2 := hne 1 2 (by decide)
    have h13 : i1 ≠ i3 := hne 1 3 (by decide)
    have h14 : i1 ≠ i4 := hne 1 4 (by decide)
    have h15 : i1 ≠ i5 := hne 1 5 (by decide)
    have h23 : i2 ≠ i3 := hne 2 3 (by decide)
    have h24 : i2 ≠ i4 := hne 2 4 (by decide)
    have h25 : i2 ≠ i5 := hne 2 5 (by decide)
    have h34 : i3 ≠ i4 := hne 3 4 (by decide)
    have h35 : i3 ≠ i5 := hne 3 5 (by decide)
    have h45 : i4 ≠ i5 := hne 4 5 (by decide)
    let d12 : Dyad N := wholeDyad i0 i1 h01
    let d13 : Dyad N := wholeDyad i0 i2 h02
    let d45 : Dyad N := wholeDyad i3 i4 h34
    let d46 : Dyad N := wholeDyad i3 i5 h35
    dsimp only
    change (ProbabilityTheory.covariance
        (fun ω => fittedResidual (design signKernel ω) (response signKernel ω) d12 *
          fittedResidual (design signKernel ω) (response signKernel ω) d13)
        (fun ω => fittedResidual (design signKernel ω) (response signKernel ω) d45 *
          fittedResidual (design signKernel ω) (response signKernel ω) d46)
        (unitSampleLaw signKernel N) = 16*((N : ℝ)+6)/(N : ℝ)^3 ∧
      0 < 16*((N : ℝ)+6)/(N : ℝ)^3 ∧
      ProbabilityTheory.covariance
        (fun ω => epsilon signKernel ω d12 * epsilon signKernel ω d13)
        (fun ω => epsilon signKernel ω d45 * epsilon signKernel ω d46)
        (unitSampleLaw signKernel N) = 0 ∧
      overlap d12 d13 ∧ overlap d45 d46 ∧
      ({d12,d13,d45,d46} : Finset (Dyad N)).card = 4 ∧
      Disjoint (members d12 ∪ members d13) (members d45 ∪ members d46))
    have hN2 : 2 ≤ N := by omega
    let sA : Finset (Fin N) := {i0,i1}
    let sB : Finset (Fin N) := {i0,i2}
    let sC : Finset (Fin N) := {i3,i4}
    let sD : Finset (Fin N) := {i3,i5}
    have hm12 : members d12 = sA := rfl
    have hm13 : members d13 = sB := rfl
    have hm45 : members d45 = sC := rfl
    have hm46 : members d46 = sD := rfl
    have hA : sA.card = 2 := by simp [sA, h01]
    have hB : sB.card = 2 := by simp [sB, h02]
    have hC : sC.card = 2 := by simp [sC, h34]
    have hD : sD.card = 2 := by simp [sD, h35]
    have hAB : (sA ∩ sB).card = 1 := by simp [sA, sB, h01, h02, h12]
    have hCD : (sC ∩ sD).card = 1 := by simp [sC, sD, h34, h35, h45]
    have hAC : (sA ∩ sC).card = 0 := by simp [sA, sC, h03, h04, h13, h14]
    have hAD : (sA ∩ sD).card = 0 := by simp [sA, sD, h03, h05, h13, h15]
    have hBC : (sB ∩ sC).card = 0 := by simp [sB, sC, h03, h04, h23, h24]
    have hBD : (sB ∩ sD).card = 0 := by simp [sB, sD, h03, h05, h23, h25]
    have hABC : (sA ∩ sB ∩ sC).card = 0 := by
      simp [sA, sB, sC, h01, h02, h03, h04, h12, h13, h14, h23, h24]
    have hABD : (sA ∩ sB ∩ sD).card = 0 := by
      simp [sA, sB, sD, h01, h02, h03, h05, h12, h13, h15, h23, h25]
    have hACD : (sA ∩ sC ∩ sD).card = 0 := by
      simp [sA, sC, sD, h03, h04, h05, h13, h14, h15, h34, h35, h45]
    have hBCD : (sB ∩ sC ∩ sD).card = 0 := by
      simp [sB, sC, sD, h03, h04, h05, h23, h24, h25, h34, h35, h45]
    have hABCD : (sA ∩ sB ∩ sC ∩ sD).card = 0 := by
      simp [sA, sB, sC, sD, h01, h02, h03, h04, h05, h12, h13, h14, h15,
        h23, h24, h25, h34, h35, h45]
    have hABset : sA ≠ sB := by
      intro he
      have hi : i1 ∈ sB := by rw [← he]; simp [sA]
      simp [sB] at hi
      rcases hi with hi | hi
      · exact h01 hi.symm
      · exact h12 hi
    have hACset : sA ≠ sC := by
      intro he
      have hi : i0 ∈ sC := by rw [← he]; simp [sA]
      simp [sC] at hi
      rcases hi with hi | hi
      · exact h03 hi
      · exact h04 hi
    have hADset : sA ≠ sD := by
      intro he
      have hi : i0 ∈ sD := by rw [← he]; simp [sA]
      simp [sD] at hi
      rcases hi with hi | hi
      · exact h03 hi
      · exact h05 hi
    have hBCset : sB ≠ sC := by
      intro he
      have hi : i0 ∈ sC := by rw [← he]; simp [sB]
      simp [sC] at hi
      rcases hi with hi | hi
      · exact h03 hi
      · exact h04 hi
    have hBDset : sB ≠ sD := by
      intro he
      have hi : i0 ∈ sD := by rw [← he]; simp [sB]
      simp [sD] at hi
      rcases hi with hi | hi
      · exact h03 hi
      · exact h05 hi
    have hCDset : sC ≠ sD := by
      intro he
      have hi : i4 ∈ sD := by rw [← he]; simp [sC]
      simp [sD] at hi
      rcases hi with hi | hi
      · exact h34 hi.symm
      · exact h45 hi
    have hdne (x y : Dyad N) (hs : members x ≠ members y) : x ≠ y := by
      intro he
      apply hs
      exact congrArg members he
    have h12ne13 : d12 ≠ d13 := hdne d12 d13 (by simpa [hm12, hm13] using hABset)
    have h12ne45 : d12 ≠ d45 := hdne d12 d45 (by simpa [hm12, hm45] using hACset)
    have h12ne46 : d12 ≠ d46 := hdne d12 d46 (by simpa [hm12, hm46] using hADset)
    have h13ne45 : d13 ≠ d45 := hdne d13 d45 (by simpa [hm13, hm45] using hBCset)
    have h13ne46 : d13 ≠ d46 := hdne d13 d46 (by simpa [hm13, hm46] using hBDset)
    have h45ne46 : d45 ≠ d46 := hdne d45 d46 (by simpa [hm45, hm46] using hCDset)
    have h01lt : i0 < i1 := by apply Fin.mk_lt_mk.mpr; norm_num [i0, i1, e]
    have h02lt : i0 < i2 := by apply Fin.mk_lt_mk.mpr; norm_num [i0, i2, e]
    have h34lt : i3 < i4 := by apply Fin.mk_lt_mk.mpr; norm_num [i3, i4, e]
    have h35lt : i3 < i5 := by apply Fin.mk_lt_mk.mpr; norm_num [i3, i5, e]
    have hends12 : firstUnit d12 = i0 ∧ secondUnit d12 = i1 := by
      have he : toAuditDyad d12 = AronowAudit.P018.Wave1.printed_mkDyad i0 i1 h01 := by
        apply Subtype.ext
        rfl
      have hp := AronowAudit.P018.Wave1.printed_mkDyad_endpoints i0 i1 h01lt
      constructor
      · calc
          firstUnit d12 = AronowAudit.P018.firstUnit (toAuditDyad d12) := rfl
          _ = _ := by rw [he]; exact hp.1
      · calc
          secondUnit d12 = AronowAudit.P018.secondUnit (toAuditDyad d12) := rfl
          _ = _ := by rw [he]; exact hp.2
    have hends13 : firstUnit d13 = i0 ∧ secondUnit d13 = i2 := by
      have he : toAuditDyad d13 = AronowAudit.P018.Wave1.printed_mkDyad i0 i2 h02 := by
        apply Subtype.ext
        rfl
      have hp := AronowAudit.P018.Wave1.printed_mkDyad_endpoints i0 i2 h02lt
      constructor
      · calc
          firstUnit d13 = AronowAudit.P018.firstUnit (toAuditDyad d13) := rfl
          _ = _ := by rw [he]; exact hp.1
      · calc
          secondUnit d13 = AronowAudit.P018.secondUnit (toAuditDyad d13) := rfl
          _ = _ := by rw [he]; exact hp.2
    have hends45 : firstUnit d45 = i3 ∧ secondUnit d45 = i4 := by
      have he : toAuditDyad d45 = AronowAudit.P018.Wave1.printed_mkDyad i3 i4 h34 := by
        apply Subtype.ext
        rfl
      have hp := AronowAudit.P018.Wave1.printed_mkDyad_endpoints i3 i4 h34lt
      constructor
      · calc
          firstUnit d45 = AronowAudit.P018.firstUnit (toAuditDyad d45) := rfl
          _ = _ := by rw [he]; exact hp.1
      · calc
          secondUnit d45 = AronowAudit.P018.secondUnit (toAuditDyad d45) := rfl
          _ = _ := by rw [he]; exact hp.2
    have hends46 : firstUnit d46 = i3 ∧ secondUnit d46 = i5 := by
      have he : toAuditDyad d46 = AronowAudit.P018.Wave1.printed_mkDyad i3 i5 h35 := by
        apply Subtype.ext
        rfl
      have hp := AronowAudit.P018.Wave1.printed_mkDyad_endpoints i3 i5 h35lt
      constructor
      · calc
          firstUnit d46 = AronowAudit.P018.firstUnit (toAuditDyad d46) := rfl
          _ = _ := by rw [he]; exact hp.1
      · calc
          secondUnit d46 = AronowAudit.P018.secondUnit (toAuditDyad d46) := rfl
          _ = _ := by rw [he]; exact hp.2
    have hCov : ProbabilityTheory.covariance
        (fun ω => fittedResidual (design signKernel ω) (response signKernel ω) d12 *
          fittedResidual (design signKernel ω) (response signKernel ω) d13)
        (fun ω => fittedResidual (design signKernel ω) (response signKernel ω) d45 *
          fittedResidual (design signKernel ω) (response signKernel ω) d46)
        (unitSampleLaw signKernel N) = 16*((N : ℝ)+6)/(N : ℝ)^3 := by
      have hresA : (fun ω => fittedResidual (design signKernel ω) (response signKernel ω) d12 *
          fittedResidual (design signKernel ω) (response signKernel ω) d13) =
        (fun ω => wholeSignLinear (loading d12) ω * wholeSignLinear (loading d13) ω) := by
        funext ω
        rw [sap_residual_linear hN2, sap_residual_linear hN2]
      have hresB : (fun ω => fittedResidual (design signKernel ω) (response signKernel ω) d45 *
          fittedResidual (design signKernel ω) (response signKernel ω) d46) =
        (fun ω => wholeSignLinear (loading d45) ω * wholeSignLinear (loading d46) ω) := by
        funext ω
        rw [sap_residual_linear hN2, sap_residual_linear hN2]
      have hlin' := hlin N (loading d12) (loading d13) (loading d45) (loading d46)
      rw [hresA, hresB]
      have hdotAC : dot (loading d12) (loading d45) = -4/(N : ℝ) := by
        rw [loading_dot hN2, hm12, hm45, hAC]
        norm_num <;> ring
      have hdotBD : dot (loading d13) (loading d46) = -4/(N : ℝ) := by
        rw [loading_dot hN2, hm13, hm46, hBD]
        norm_num <;> ring
      have hdotAD : dot (loading d12) (loading d46) = -4/(N : ℝ) := by
        rw [loading_dot hN2, hm12, hm46, hAD]
        norm_num <;> ring
      have hdotBC : dot (loading d13) (loading d45) = -4/(N : ℝ) := by
        rw [loading_dot hN2, hm13, hm45, hBC]
        norm_num <;> ring
      have hdiag : (∑ i, loading d12 i * loading d13 i * loading d45 i * loading d46 i) =
          2*(2/(N : ℝ))^2 - 8*(2/(N : ℝ))^3 + (N : ℝ)*(2/(N : ℝ))^4 := by
        simpa [loading, hm12, hm13, hm45, hm46, sA, sB, sC, sD] using
          sum_loading_product sA sB sC sD hA hB hC hD hAB hCD hAC hAD hBC hBD
            hABC hABD hACD hBCD hABCD
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hcalc :
          dot (loading d12) (loading d45) * dot (loading d13) (loading d46) +
            dot (loading d12) (loading d46) * dot (loading d13) (loading d45) -
              2 * ∑ i, loading d12 i * loading d13 i * loading d45 i * loading d46 i =
            16*((N : ℝ)+6)/(N : ℝ)^3 := by
        rw [hdotAC, hdotBD, hdotAD, hdotBC, hdiag]
        field_simp [hn]
        <;> ring
      exact hlin'.trans hcalc
    have hPop : ProbabilityTheory.covariance
        (fun ω => epsilon signKernel ω d12 * epsilon signKernel ω d13)
        (fun ω => epsilon signKernel ω d45 * epsilon signKernel ω d46)
        (unitSampleLaw signKernel N) = 0 := by
      have hpopA : (fun ω => epsilon signKernel ω d12 * epsilon signKernel ω d13) =
          (fun ω => wholeSignLinear (fun i => indicator sA i) ω *
            wholeSignLinear (fun i => indicator sB i) ω) := by
        funext ω
        simp only [sA, sB]
        rw [wholeSignLinear_pair i0 i1 h01 ω, wholeSignLinear_pair i0 i2 h02 ω]
        simp only [epsilon, populationResidual]
        rw [sap_populationBeta_zero]
        simp [signKernel, dot, hends12.1, hends12.2, hends13.1, hends13.2]
      have hpopB : (fun ω => epsilon signKernel ω d45 * epsilon signKernel ω d46) =
          (fun ω => wholeSignLinear (fun i => indicator sC i) ω *
            wholeSignLinear (fun i => indicator sD i) ω) := by
        funext ω
        simp only [sC, sD]
        rw [wholeSignLinear_pair i3 i4 h34 ω, wholeSignLinear_pair i3 i5 h35 ω]
        simp only [epsilon, populationResidual]
        rw [sap_populationBeta_zero]
        simp [signKernel, dot, hends45.1, hends45.2, hends46.1, hends46.2]
      rw [hpopA, hpopB]
      have hlin' := hlin N (fun i => indicator sA i) (fun i => indicator sB i)
        (fun i => indicator sC i) (fun i => indicator sD i)
      rw [hlin']
      simp only [dot, sum_indicator2, sum_indicator4, hAC, hAD, hBC, hBD, hABCD]
      norm_num
    have hOverlapAB : overlap d12 d13 := ⟨i0, by simp [hm12, hm13, sA, sB]⟩
    have hOverlapCD : overlap d45 d46 := ⟨i3, by simp [hm45, hm46, sC, sD]⟩
    have hCard : ({d12,d13,d45,d46} : Finset (Dyad N)).card = 4 :=
      by simp [h12ne13, h12ne45, h12ne46, h13ne45, h13ne46, h45ne46]
    have hDisjoint : Disjoint (members d12 ∪ members d13) (members d45 ∪ members d46) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp [hm12, hm13, hm45, hm46, sA, sB, sC, sD,
        h03, h04, h05, h13, h14, h15, h23, h24, h25]
    exact ⟨hCov, by positivity, hPop, hOverlapAB, hOverlapCD, hCard, hDisjoint⟩
  · intro i j hij ω
    rw [residual_linear_pair (by norm_num : 2 ≤ 8) i j hij ω]
    simp [signResidual8, wholeSignSum]
    norm_num <;> ring
  · letI : IsProbabilityMeasure SAP.P018a.fairLaw := by
      unfold SAP.P018a.fairLaw
      infer_instance
    letI : IsProbabilityMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8) := by
      change IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => SAP.P018a.fairLaw))
      infer_instance
    intro f g
    have hf : MemLp (fun ω : Fin 8 → Bool => f (fun i => SAP.P018a.signValue (ω i))) 2
        (SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8) :=
      AronowAudit.P018.Wave1.printed_finite_L2 _ _
    have hg : MemLp (fun ω : Fin 8 → Bool => g (fun i => SAP.P018a.signValue (ω i))) 2
        (SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8) :=
      AronowAudit.P018.Wave1.printed_finite_L2 _ _
    rw [ProbabilityTheory.covariance_eq_sub hf hg]
    rw [SAP.P018a.fairCov8]
    change (SAP.P018a.fairAverage 8 (fun u => f u * g u) -
        SAP.P018a.fairAverage 8 f * SAP.P018a.fairAverage 8 g) =
      (∫ ω, f (fun i => SAP.P018a.signValue (ω i)) *
        g (fun i => SAP.P018a.signValue (ω i))
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8) -
      (∫ ω, f (fun i => SAP.P018a.signValue (ω i))
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8) *
      (∫ ω, g (fun i => SAP.P018a.signValue (ω i))
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel 8)
    rw [fairIntegral_average (fun u => f u * g u), fairIntegral_average f,
      fairIntegral_average g]
