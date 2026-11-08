import SAP.P043.Defs.WholeW1
import SAP.P043.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043.WH.W1

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

/-! Both targets need only existing donor results, finite-sum glue, and the
integral of an almost-everywhere constant. There are no unproved leaves. -/

private theorem fairAssignment {Ω : Type*} [Fintype Ω] (P : Population Ω) :
    FairAssignmentClaims P := by
  obtain ⟨hn, ht⟩ := AronowAudit.P043.randomization_probability
    (Bridge.toAuditPopulation P) (1/2) (by norm_num)
  refine ⟨?_, hn, ht, ?_, ?_⟩
  · intro z
    cases z <;> norm_num [armProb]
  · intro z
    change (∑ i, armProb (1/2) z * P.mass i) = 1/2
    rw [← mul_sum, P.total, mul_one]
    cases z <;> norm_num [armProb]
  · intro A z
    exact AronowAudit.P043.assignment_independent (Bridge.toAuditPopulation P) (1/2) z A

private theorem ivConsistency {Ω : Type*} (m : IVModel Ω) : IVConsistencyClaims m :=
  ⟨fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem perUnit_eq_effect {Ω : Type*} [Fintype Ω]
    (P : Population Ω) (m : IVModel Ω)
    (hu : ∀ i, increaser m i → m.knowledge false i = 8 ∧ m.knowledge true i = 9) :
    increaserPerUnitEffect P m = increaserEffect P m := by
  unfold increaserPerUnitEffect increaserEffect eventMean
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases hi : increaser m i
  · obtain ⟨h0, h1⟩ := hu i hi
    norm_num [hi, h0, h1, indicator]
  · simp [indicator, hi]

/-- The complete mediation witnesses. All omitted clauses are supplied by
existing pointwise/range donors and elementary algebra; no new leaf is needed. -/
theorem T1_assembly : T1WholeStatement := by
  have hl : LinearNumericClaims := AronowAudit.P043.linear_numbers
  obtain ⟨_, hmL, hdL, htL, _⟩ := hl
  have hi : IntegerNumericClaims := AronowAudit.P043.integer_numbers
  obtain ⟨_, _, _, _, _, _, hmI, hdI, htI⟩ := hi
  refine ⟨Bridge.mediationWitnesses, fairAssignment _, fairAssignment _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i
    exact AronowAudit.P043.linear_observed_support t i
  · unfold linearWitness linearModel
    congr 1
    funext t k i
    ring
  · intro i
    have h0 : integerWitness.knowledge false i = 8 :=
      (AronowAudit.P043.integer_ranges false i).1
    have h1 : integerWitness.knowledge true i = (if i.1.val = 4 then 10 else 9) :=
      (AronowAudit.P043.integer_ranges false i).2.1
    refine ⟨h0, h1, ?_, ?_⟩
    · intro hw
      have hnot : i.1.val ≠ 4 := by omega
      simpa [hnot] using h1
    · intro hw
      have heq : i.1.val = 4 := by omega
      simpa [heq] using h1
  · intro t i
    obtain ⟨_, _, _, hk0, hk15, _, hs0, hs3, _, hg0, hg5⟩ :=
      AronowAudit.P043.integer_ranges t i
    exact ⟨hk0, hk15, hs0, hs3, hg0, hg5⟩
  · intro t
    have ha : armMean integerPopulation (1/2) t (observedSupport integerWitness) =
        mean integerPopulation (observedSupport integerWitness t) :=
      AronowAudit.P043.fair_armMean AronowAudit.P043.integerPopulation t
        (AronowAudit.P043.observedSupport AronowAudit.P043.integerWitness)
    have hm : mean integerPopulation (observedSupport integerWitness t) =
        2 + (36 + 6 * assignment t - 6 * assignment t) / 100 :=
      AronowAudit.P043.integer_nested_support_mean t t
    rw [ha, hm]
    ring
  · rw [hdL, hdI]
    norm_num
  · rw [htL, hmL]
    norm_num
  · rw [htI, hmI]
    norm_num
  · intro h
    have hbad := h htL
    rw [hmL] at hbad
    norm_num at hbad
  · intro h
    have hbad := h htI
    rw [hmI] at hbad
    norm_num at hbad

/-- The complete IV witnesses. All crossed increments are one, so arbitrary
probability averages are integrable and equal one by a constant-integral proof.
The exact conditioning masses are projected from the five-type numerical donor. -/
theorem T4_assembly : T4WholeStatement := by
  have hbase : T4Statement := Bridge.ivWitnesses
  obtain ⟨_, _, _, _, _, _, _, hratio, _, _, _, _, heup, _⟩ := hbase.1
  obtain ⟨_, _, hpA, hpB, heA, heB⟩ := AronowAudit.P043.models_numbers
  have hcross (x : Bool × ℕ) (hx : UpDownCrossedMargin x) :
      x.2 = 9 ∧ doseIncrement upDownWitness x.2 x.1 = 1 := by
    obtain ⟨hi, h0, h1⟩ := hx
    obtain ⟨hk0, hk1, hd⟩ := (hbase.2.1 x.1).2.1 hi
    have hj : x.2 = 9 := by omega
    exact ⟨hj, by simpa only [doseIncrement, hj, Nat.reduceSub] using hd⟩
  refine ⟨hbase, fairAssignment _, fairAssignment _,
    ivConsistency _, ivConsistency _, ivConsistency _, ?_, hpA, hpB, ?_, ?_, ?_⟩
  · refine ⟨hcross, ?_, ?_⟩
    · intro n x w _hw hx hs
      have he (a : Fin n) : doseIncrement upDownWitness (x a).2 (x a).1 = 1 :=
        (hcross (x a) (hx a)).2
      have hav : (∑ a, w a * doseIncrement upDownWitness (x a).2 (x a).1) = 1 := by
        simpa only [he, mul_one] using hs
      exact ⟨hav, by rw [hav, hratio]; norm_num⟩
    · intro ν _ hν
      have hae : (fun x => doseIncrement upDownWitness x.2 x.1) =ᵐ[ν]
          (fun _ => (1 : ℝ)) := hν.mono (fun x hx => (hcross x hx).2)
      have hint : Integrable (fun x => doseIncrement upDownWitness x.2 x.1) ν :=
        (integrable_const (1 : ℝ)).congr hae.symm
      have hav : (∫ x, doseIncrement upDownWitness x.2 x.1 ∂ν) = 1 := by
        rw [integral_congr_ae hae]
        simp
      exact ⟨hint, hav, by rw [hav, hratio]; norm_num⟩
  · calc
      _ = increaserEffect upDownPopulation upDownWitness :=
        perUnit_eq_effect _ _ (by
          intro i hi
          have h := (hbase.2.1 i).2.1 hi
          exact ⟨h.1, h.2.1⟩)
      _ = 1 := heup
  · calc
      _ = increaserEffect (uniformPopulation (Fin 5)) modelA :=
        perUnit_eq_effect _ _ (by
          intro i hi
          have hu : FiveTypeUnitClaims modelA i := AronowAudit.P043.models_unit_properties
            AronowAudit.P043.modelA (Or.inl rfl) i
          exact hu.2.2.2 hi)
      _ = 1 := heA
  · calc
      _ = increaserEffect (uniformPopulation (Fin 5)) modelB :=
        perUnit_eq_effect _ _ (by
          intro i hi
          have hu : FiveTypeUnitClaims modelB i := AronowAudit.P043.models_unit_properties
            AronowAudit.P043.modelB (Or.inr rfl) i
          exact hu.2.2.2 hi)
      _ = 4/3 := heB

end
end SAP.P043.WH.W1
