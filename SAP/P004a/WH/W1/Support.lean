import SAP.P004a.Defs.WholeW1
import SAP.P004a.Bridge
import AronowAudit.P004.Wave1.Gap.DecideP004T1
import AronowAudit.P004.Wave1.Gap.GLP0042B3
import AronowAudit.P004.Wave1.Gap.GP0041B1
import AronowAudit.P004.Wave1.Gap.FidP004
import AronowAudit.P004.Wave1.AreaSum
import AronowAudit.P004.P004_SpatialAlgebraCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
universe u v
set_option maxHeartbeats 1000000

/-- Finite forced-coordinate expectation commutes with the spatial integral. -/
theorem forced_band {N : ℕ} {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (p : Fin N → ℝ) (d : ℝ) (hWD : WellDefined P d) :
    (∀ i, IntegrableOn (w1ForcedPointEffect P p i) (region P i d) P.zeta) ∧
    (∀ i, w1ForcedEffect p (circleAverage P d) i =
      (∫ x in region P i d, w1ForcedPointEffect P p i x ∂P.zeta) /
        (P.zeta (region P i d)).toReal) := by
  have hi (i : Fin N) (a : Bool) : IntegrableOn
      (fun x => w1ForcedMarginal p (fun _ z => P.outcome x z) i a) (region P i d) P.zeta := by
    exact integrable_finsetSum _ (fun z _ => ((hWD i).2.2.2 (Function.update z i a)).const_mul _)
  have he (i : Fin N) (a : Bool) : w1ForcedMarginal p (circleAverage P d) i a =
      (∫ x in region P i d, w1ForcedMarginal p (fun _ z => P.outcome x z) i a ∂P.zeta) /
        (P.zeta (region P i d)).toReal := by
    unfold w1ForcedMarginal circleAverage
    change AronowAudit.P004.expect p (fun z =>
      (∫ x in region P i d, P.outcome x (Function.update z i a) ∂P.zeta) / _) = _
    rw [AronowAudit.P004.expect_div,
      AronowAudit.P004.AlgebraCompletion.expect_integral _ p
        (fun x z => P.outcome x (Function.update z i a))
        (fun z => (hWD i).2.2.2 (Function.update z i a))]
    rfl
  refine ⟨fun i => (hi i true).sub (hi i false), fun i => ?_⟩
  unfold w1ForcedEffect
  rw [he i true, he i false, ← sub_div, ← integral_sub (hi i true) (hi i false)]
  rfl

/-- On the interior of the Bernoulli parameter cube, the forced and conditional forms agree. -/
theorem forced_agrees {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) :
    (∀ i, w1ForcedEffect p R i = nodeEffect p R i) ∧ w1ForcedAME p R = ame p R := by
  have he (i : Fin N) (a : Bool) : w1ForcedMarginal p R i a = marginal p R i a :=
    (AronowAudit.P004.marginal_is_marginalization p R i a hp).symm
  have hf (i : Fin N) : w1ForcedEffect p R i = nodeEffect p R i := by
    simp only [w1ForcedEffect, nodeEffect, he]
  exact ⟨hf, by simp only [w1ForcedAME, ame, hf]⟩

/-- The finite partition donor already gives the unconditional double sum. Zero common
weights can be removed, leaving only shell means whose denominators are positive. -/
theorem finite_shells : T15FiniteStatement.{v} := by
  intro A _ m N a shell δ hN ha hpos
  have h := AronowAudit.P004.Wave1.supported_shell_identity a shell δ ha hpos
  refine ⟨h.1, congrArg (fun f : Fin N → ℝ => (∑ i, f i)/(N : ℝ)) (funext h.1), ?_⟩
  intro w hw
  have hn (i : Fin N) (k : Fin m) : 0 ≤ supportedShellMass (a i) shell i k := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> first | exact ha i x | exact le_rfl
  have hw0 (k : Fin m) : 0 ≤ w k := by
    rw [← hw ⟨0,hN⟩ k]
    exact div_nonneg (hn _ k) (hpos _).le
  refine ⟨fun k hk i => ?_, (h.2 w hw).trans ?_⟩
  · have := hw i k
    have hp : 0 < supportedShellMass (a i) shell i k / (∑ x, a i x) := by rwa [this]
    rcases div_pos_iff.mp hp with hp | hp
    · exact hp.1
    · linarith [hp.2, hpos i]
  · symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    have hz : w k = 0 := le_antisymm (not_lt.mp (by simpa using hk)) (hw0 k)
    simp [hz]

/-- The zero field preserves all mass and integrability guards. -/
theorem zero_shell_wellDefined (D : Set ℝ) (h : WellDefined (shellSpatialPopulation D) 0) :
    WellDefined (w1ZeroShell D) 0 := by
  intro i
  exact ⟨(h i).1, (h i).2.1, (h i).2.2.1, fun _ => integrable_zero _ _ _⟩

theorem zero_shell_ame (D : Set ℝ) : ame (fun _ => 1/2) (circleAverage (w1ZeroShell D) 0) = 0 := by
  simp [ame, nodeEffect, marginal, expect, circleAverage, w1ZeroShell]

/-- Pair the existing spatial witness with the zero field on exactly the same geometry. -/
theorem nonidentification : T15NonidentificationStatement := by
  have h : T14Statement := AronowAudit.P004.spatial_shell_counterexample
  have hcopy := h
  obtain ⟨h4,h5,h45,h05,hbd,e4,e5,e45,e05,hw⟩ := hcopy
  have hzero : ∀ D ∈ ({({4} : Set ℝ), {5}, Set.Icc 4 5, Set.Icc 0 5} : Finset (Set ℝ)),
      WellDefined (w1ZeroShell D) 0 ∧ ame (fun _ => 1/2) (circleAverage (w1ZeroShell D) 0) = 0 := by
    intro D hD
    refine ⟨zero_shell_wellDefined D ?_, zero_shell_ame D⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl <;> assumption
  have hsupport (i : Fin 2) (r : ℝ) :
      0 < (shellSpatialPopulation {r}).zeta (region (shellSpatialPopulation {r}) i 0) ↔ r = 4 ∨ r = 5 := by
    have hm : (shellSpatialPopulation {r}).zeta (region (shellSpatialPopulation {r}) i 0) =
        ∑ x : Fin 3, if AronowAudit.P004.shellWitnessDistance i x ∈ ({r} : Set ℝ) then (1 : ENNReal) else 0 :=
      AronowAudit.P004.shell_spatial_mass {r} i
    rw [hm, Fin.sum_univ_three]
    fin_cases i <;> by_cases h4 : r = 4 <;> by_cases h5 : r = 5 <;>
      simp [AronowAudit.P004.shellWitnessDistance, h4, h5, eq_comm]
  refine ⟨h, hsupport, hzero, ?_⟩
  rintro ⟨F,hF,hG⟩
  have he : (fun j : Fin 2 => ame (fun _ => 1/2)
      (circleAverage (shellSpatialPopulation (if j = 0 then {4} else {5})) 0)) = fun _ => 0 := by
    funext j
    split_ifs <;> assumption
  simp only [he, e45, zero_shell_ame] at hF hG
  linarith

/-- Existing exact algebra suffices for all population constants in the three-type witness. -/
theorem three_population : T1PopulationStatement := by
  intro K hK
  dsimp only
  have hc : circleAverage (threeTypePopulation (3*K)) 0 = threeTypeTable (3*K) :=
    AronowAudit.P004.Wave1.LinePopulation.n3_proof _
  rw [hc]
  have hi : information (w1ThreeP (3*K)) (threeTypeONat (3*K)) = !![25/108,0;0,4/27] :=
    AronowAudit.P004.Wave1.DecideP004T1_information K hK
  have hb (a : Bool) : beta (w1ThreeP (3*K)) (threeTypeTable (3*K)) (threeTypeONat (3*K)) a = ![509/500,0] :=
    AronowAudit.P004.Wave1.DecideP004T1_beta K hK a
  have hm (i : Fin (3*K)) (a : Bool) :
      marginal (w1ThreeP (3*K)) (threeTypeTable (3*K)) i a =
        AronowAudit.P004.Wave1.DecideP004T1_q (i.val%3) :=
    AronowAudit.P004.Wave1.DecideP004T1_marginal _ i a
  have he (i : Fin (3*K)) : nodeEffect (w1ThreeP (3*K)) (threeTypeTable (3*K)) i = 0 := by
    simp only [nodeEffect, hm, sub_self]
  refine ⟨?_,hi,hb,?_,AronowAudit.P004.Wave1.DecideP004T1_gamma K hK,he,?_,?_,?_⟩
  · intro a b
    change (∑ i : Fin (3*K), AronowAudit.P004.Wave1.DecideP004T1_o (i.val%3) a *
      AronowAudit.P004.Wave1.DecideP004T1_o (i.val%3) b)/(3*K : ℕ) = _
    rw [AronowAudit.P004.Wave1.DecideP004T1_cycle_average K hK
      (fun t => AronowAudit.P004.Wave1.DecideP004T1_o t a * AronowAudit.P004.Wave1.DecideP004T1_o t b)]
    fin_cases a <;> fin_cases b <;> norm_num [AronowAudit.P004.Wave1.DecideP004T1_o]
  · funext j
    simp only [hm]
    rw [show w1ThreeP (3*K) = fun i => AronowAudit.P004.Wave1.DecideP004T1_p (i.val%3) from
      AronowAudit.P004.Wave1.DecideP004T1_propensities _]
    change (∑ i : Fin (3*K),
      ((1-AronowAudit.P004.Wave1.DecideP004T1_p (i.val%3))*AronowAudit.P004.Wave1.DecideP004T1_q (i.val%3)+
      AronowAudit.P004.Wave1.DecideP004T1_p (i.val%3)*AronowAudit.P004.Wave1.DecideP004T1_q (i.val%3))*
        AronowAudit.P004.Wave1.DecideP004T1_o (i.val%3) j)/(3*K : ℕ) = _
    rw [AronowAudit.P004.Wave1.DecideP004T1_cycle_average K hK
      (fun t => ((1-AronowAudit.P004.Wave1.DecideP004T1_p t)*AronowAudit.P004.Wave1.DecideP004T1_q t+
      AronowAudit.P004.Wave1.DecideP004T1_p t*AronowAudit.P004.Wave1.DecideP004T1_q t)*
        AronowAudit.P004.Wave1.DecideP004T1_o t j)]
    fin_cases j <;> norm_num [AronowAudit.P004.Wave1.DecideP004T1_p,
      AronowAudit.P004.Wave1.DecideP004T1_q,AronowAudit.P004.Wave1.DecideP004T1_o]
  · simp only [ame, he, Finset.sum_const_zero, zero_div]
  · simp only [homophilyQ, residualEffect, printedFits, hb, he, sub_self,
      mul_zero, Finset.sum_const_zero, zero_div]
  · simp [hb, he, dot]

/-- The two purely finite parts of T4 are exactly the already certified general results. -/
theorem raw_sah_general : T4Statement :=
  ⟨@AronowAudit.P004.sah_weighting_identity, @AronowAudit.P004.raw_sah_bound⟩

/-- A table depending only on its own treatment has the stated common node effect and
realized contrast, so no assignment enumeration is needed for the area examples. -/
theorem two_node_effect (q : Bool → ℝ) :
    hajek (fun (i : Fin 2) (z : Assignment 2) => q (z i)) areaWitnessAssignment = q true-q false ∧
    ame (fun _ => 1/2) (fun (i : Fin 2) (z : Assignment 2) => q (z i)) = q true-q false := by
  constructor
  · norm_num [hajek, armMean, armCount, areaWitnessAssignment, Fin.sum_univ_two]
  · have he (i : Fin 2) (a : Bool) : marginal (fun _ => (1/2 : ℝ))
        (fun (i : Fin 2) (z : Assignment 2) => q (z i)) i a = q a := by
      change AronowAudit.P004.marginal (fun _ : Fin 2 => (1/2 : ℝ))
        (fun (i : Fin 2) (z : Assignment 2) => q (z i)) i a = q a
      rw [AronowAudit.P004.marginal_is_marginalization
        (fun _ : Fin 2 => (1/2 : ℝ))
        (fun (i : Fin 2) (z : Assignment 2) => q (z i)) i a (fun _ => by norm_num)]
      simp only [Function.update_self]
      exact AronowAudit.P004.expect_const _ _
    norm_num [ame, nodeEffect, he, Fin.sum_univ_two]
    ring

end
end SAP.P004a.WH.W1
