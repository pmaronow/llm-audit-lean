import SAP.P018a.WH.W1.Leaves
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000

noncomputable section
namespace SAP.P018a.WH.W1.P.T11_L6

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

local instance t11_fair_probability : IsProbabilityMeasure SAP.P018a.fairLaw :=
  AronowAudit.P018.Wave1.printed_fair_probability

local instance t11_uniform_probability : IsProbabilityMeasure SAP.P018a.uniformUnitLaw := by
  change IsProbabilityMeasure AronowAudit.P018.uniformUnitLaw
  infer_instance

private abbrev K := SAP.P018a.W1MixedKernel

local instance t11_mixed_probability : IsProbabilityMeasure K.μ := by
  simp only [K, SAP.P018a.W1MixedKernel]
  infer_instance

local instance t11_sample_probability (N : ℕ) :
    IsProbabilityMeasure (SAP.P018a.unitSampleLaw K N) := by
  unfold SAP.P018a.unitSampleLaw
  infer_instance

private def coordArray {N : ℕ} (ω : Fin N → ℝ × Bool) : Fin N → ℝ :=
  fun i => (ω i).1

private def signArray {N : ℕ} (ω : Fin N → ℝ × Bool) : Fin N → Bool :=
  fun i => (ω i).2

private lemma mixed_design_measurable {N : ℕ} (hK : SAP.P018a.Standing K) :
    Measurable (SAP.P018a.design K : (Fin N → ℝ × Bool) → SAP.P018a.Dyad N → SAP.P018a.Vec 2) := by
  apply measurable_pi_iff.mpr
  intro d
  have hp : Measurable (fun ω : Fin N → ℝ × Bool =>
      (ω (SAP.P018a.firstUnit d), ω (SAP.P018a.secondUnit d))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  simpa only [Function.comp_def, SAP.P018a.design] using hK.2.1.comp hp

private def coordsLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => SAP.P018a.uniformUnitLaw)

private def signsLaw (N : ℕ) : Measure (Fin N → Bool) :=
  Measure.pi (fun _ => SAP.P018a.fairLaw)

private lemma mixed_sign_coord_measurable {N : ℕ} (i : Fin N) :
    Measurable (fun ω : Fin N → ℝ × Bool => SAP.P018a.signValue ((ω i).2)) := by
  exact (measurable_of_countable SAP.P018a.signValue).comp
    (measurable_snd.comp (measurable_pi_apply i))

private lemma mixed_array_map (N : ℕ) :
    MeasurePreserving (fun ω : Fin N → ℝ × Bool => (coordArray ω, signArray ω))
      (SAP.P018a.unitSampleLaw K N) (Measure.prod (coordsLaw N) (signsLaw N)) := by
  change MeasurePreserving
    (fun ω : Fin N → ℝ × Bool => (fun i => (ω i).1, fun i => (ω i).2))
    (Measure.pi (fun _ : Fin N => SAP.P018a.uniformUnitLaw.prod SAP.P018a.fairLaw))
    ((Measure.pi (fun _ : Fin N => SAP.P018a.uniformUnitLaw)).prod
      (Measure.pi (fun _ : Fin N => SAP.P018a.fairLaw)))
  convert (MeasureTheory.measurePreserving_arrowProdEquivProdArrow ℝ Bool (Fin N)
      (fun _ => SAP.P018a.uniformUnitLaw) (fun _ => SAP.P018a.fairLaw)) using 1
  funext ω
  ext i <;> rfl

private lemma mixed_arrays_independent (N : ℕ) :
    coordArray ⟂ᵢ[SAP.P018a.unitSampleLaw K N] signArray := by
  let P := SAP.P018a.unitSampleLaw K N
  let X := coordArray (N := N)
  let Y := signArray (N := N)
  have hmap := mixed_array_map N
  have hXm : Measurable X := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_snd.comp (measurable_pi_apply i)
  have hx : P.map X = coordsLaw N := by
    calc
      P.map X = (P.map (fun ω => (X ω, Y ω))).fst := by
        symm
        exact Measure.fst_map_prodMk hXm hYm
      _ = ((coordsLaw N).prod (signsLaw N)).fst := congrArg Measure.fst hmap.map_eq
      _ = coordsLaw N := by simp [coordsLaw, signsLaw]
  have hy : P.map Y = signsLaw N := by
    calc
      P.map Y = (P.map (fun ω => (X ω, Y ω))).snd := by
        symm
        exact Measure.snd_map_prodMk hXm hYm
      _ = ((coordsLaw N).prod (signsLaw N)).snd := congrArg Measure.snd hmap.map_eq
      _ = signsLaw N := by simp [coordsLaw, signsLaw]
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable]
  simpa [P, X, Y, hx, hy] using hmap.map_eq

private lemma mixed_sign_mean {N : ℕ} (i : Fin N) :
    (∫ ω, SAP.P018a.signValue ((ω i).2)
      ∂SAP.P018a.unitSampleLaw K N) = 0 := by
  change (∫ ω : Fin N → ℝ × Bool,
    SAP.P018a.signValue ((ω i).2) ∂Measure.pi (fun _ => K.μ)) = 0
  rw [MeasureTheory.integral_comp_eval (μ := fun _ : Fin N => K.μ) (i := i)
    (f := fun uv : ℝ × Bool => SAP.P018a.signValue uv.2)
    ((measurable_of_countable SAP.P018a.signValue).comp measurable_snd).aestronglyMeasurable]
  change (∫ uv : ℝ × Bool, SAP.P018a.signValue uv.2
    ∂SAP.P018a.uniformUnitLaw.prod SAP.P018a.fairLaw) = 0
  rw [MeasureTheory.integral_fun_snd, probReal_univ, one_smul]
  simpa [SAP.P018a.signValue, SAP.P018a.fairLaw,
    AronowAudit.P018.signValue, AronowAudit.P018.fairLaw] using
      AronowAudit.P018.Wave1.printed_fair_integral

private lemma mixed_sign_product {N : ℕ} (i j : Fin N) :
    (∫ ω, SAP.P018a.signValue ((ω i).2) * SAP.P018a.signValue ((ω j).2)
      ∂SAP.P018a.unitSampleLaw K N) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hs (b : Bool) : SAP.P018a.signValue b * SAP.P018a.signValue b = 1 := by
      cases b <;> norm_num [SAP.P018a.signValue]
    simp_rw [hs]
    simp
  · have hi : iIndepFun (fun i (ω : Fin N → ℝ × Bool) =>
        SAP.P018a.signValue ((ω i).2)) (SAP.P018a.unitSampleLaw K N) := by
      change iIndepFun (fun i (ω : Fin N → ℝ × Bool) =>
        SAP.P018a.signValue ((ω i).2)) (Measure.pi (fun _ : Fin N => K.μ))
      exact iIndepFun_pi (μ := fun _ : Fin N => K.μ)
        (X := fun _ u => SAP.P018a.signValue u.2)
        (fun _ => ((measurable_of_countable SAP.P018a.signValue).comp measurable_snd).aemeasurable)
    rw [(hi.indepFun hij).integral_fun_mul_eq_mul_integral
      (mixed_sign_coord_measurable i).aestronglyMeasurable
      (mixed_sign_coord_measurable j).aestronglyMeasurable]
    simp [mixed_sign_mean, hij]

private lemma mixed_epsilon_formula {N : ℕ} (hβ : SAP.P018a.populationBeta K = 0)
    (ω : Fin N → ℝ × Bool) (d : SAP.P018a.Dyad N) :
    SAP.P018a.epsilon K ω d =
      SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2) +
      SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2) := by
  rw [SAP.P018a.epsilon, SAP.P018a.populationResidual, hβ]
  simp [K, SAP.P018a.W1MixedKernel, SAP.P018a.dot, Fin.sum_univ_succ]

private lemma mixed_members_endpoints {N : ℕ} (d : SAP.P018a.Dyad N) :
    SAP.P018a.members d = {SAP.P018a.firstUnit d, SAP.P018a.secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · subst i
      exact Finset.min'_mem _ _
    · subst i
      exact Finset.max'_mem _ _
  · rw [SAP.P018a.members_card]
    exact le_of_eq (Finset.card_pair_eq_two_iff.mpr
      (ne_of_lt (AronowAudit.P018.Wave1.printed_endpoints_lt d))).symm

private def mixed_other {N : ℕ} (i : Fin N) (d : SAP.P018a.Dyad N) : Fin N :=
  if SAP.P018a.firstUnit d = i then SAP.P018a.secondUnit d else SAP.P018a.firstUnit d

private lemma mixed_members_other {N : ℕ} (i : Fin N) (d : SAP.P018a.Dyad N)
    (hi : i ∈ SAP.P018a.members d) :
    SAP.P018a.members d = {i, mixed_other i d} := by
  rw [mixed_members_endpoints] at hi ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  dsimp [mixed_other]
  rcases hi with hi | hi
  · simp [hi.symm]
  · by_cases h : SAP.P018a.firstUnit d = i
    · simp [h, hi.symm]
    · simp [h, hi.symm, Finset.pair_comm]

private lemma mixed_other_ne {N : ℕ} (i : Fin N) (d : SAP.P018a.Dyad N)
    (hi : i ∈ SAP.P018a.members d) : i ≠ mixed_other i d := by
  apply Finset.card_pair_eq_two_iff.mp
  rw [← mixed_members_other i d hi, SAP.P018a.members_card]

private lemma mixed_epsilon_mean {N : ℕ} (hβ : SAP.P018a.populationBeta K = 0)
    (d : SAP.P018a.Dyad N) :
    (∫ ω, SAP.P018a.epsilon K ω d ∂SAP.P018a.unitSampleLaw K N) = 0 := by
  have hi := mixed_sign_mean (N := N) (SAP.P018a.firstUnit d)
  have hj := mixed_sign_mean (N := N) (SAP.P018a.secondUnit d)
  have hfi : Integrable (fun ω : Fin N → ℝ × Bool =>
      SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2))
      (SAP.P018a.unitSampleLaw K N) := by
    have hb : ∀ᵐ ω ∂SAP.P018a.unitSampleLaw K N,
        |SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2)| ≤ (1 : ℝ) := by
      filter_upwards with ω
      cases h : (ω (SAP.P018a.firstUnit d)).2 <;> simp [SAP.P018a.signValue]
    exact (MemLp.of_bound (mixed_sign_coord_measurable (SAP.P018a.firstUnit d)).aestronglyMeasurable 1 hb :
      MemLp (fun ω : Fin N → ℝ × Bool =>
        SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2)) ∞
        (SAP.P018a.unitSampleLaw K N)).integrable (by simp)
  have hfj : Integrable (fun ω : Fin N → ℝ × Bool =>
      SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2))
      (SAP.P018a.unitSampleLaw K N) := by
    have hb : ∀ᵐ ω ∂SAP.P018a.unitSampleLaw K N,
        |SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2)| ≤ (1 : ℝ) := by
      filter_upwards with ω
      cases h : (ω (SAP.P018a.secondUnit d)).2 <;> simp [SAP.P018a.signValue]
    exact (MemLp.of_bound (mixed_sign_coord_measurable (SAP.P018a.secondUnit d)).aestronglyMeasurable 1 hb :
      MemLp (fun ω : Fin N → ℝ × Bool =>
        SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2)) ∞
        (SAP.P018a.unitSampleLaw K N)).integrable (by simp)
  calc
    _ = (∫ ω, SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2)
          ∂SAP.P018a.unitSampleLaw K N) +
        ∫ ω, SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2)
          ∂SAP.P018a.unitSampleLaw K N := by
      rw [show (fun ω => SAP.P018a.epsilon K ω d) = _ from by
        funext ω; exact mixed_epsilon_formula hβ ω d]
      exact integral_add hfi hfj
    _ = 0 := by rw [hi, hj]; ring

private lemma mixed_epsilon_product {N : ℕ} (hβ : SAP.P018a.populationBeta K = 0)
    (d f : SAP.P018a.Dyad N) :
    (∫ ω, SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f
      ∂SAP.P018a.unitSampleLaw K N) =
      ((SAP.P018a.members d ∩ SAP.P018a.members f).card : ℝ) := by
  classical
  let i := SAP.P018a.firstUnit d
  let j := SAP.P018a.secondUnit d
  let k := SAP.P018a.firstUnit f
  let l := SAP.P018a.secondUnit f
  have hdi : i ≠ j := ne_of_lt (Finset.min'_lt_max'_of_card
    (SAP.P018a.members d) (by rw [SAP.P018a.members_card]; norm_num))
  have hfk : k ≠ l := ne_of_lt (Finset.min'_lt_max'_of_card
    (SAP.P018a.members f) (by rw [SAP.P018a.members_card]; norm_num))
  have hsumd : SAP.P018a.members d = {i,j} := mixed_members_endpoints d
  have hsumf : SAP.P018a.members f = {k,l} := mixed_members_endpoints f
  have hprod (a b : Fin N) : Integrable
      (fun ω : Fin N → ℝ × Bool =>
        SAP.P018a.signValue ((ω a).2) * SAP.P018a.signValue ((ω b).2))
      (SAP.P018a.unitSampleLaw K N) := by
    have hb : ∀ᵐ ω ∂SAP.P018a.unitSampleLaw K N,
        |SAP.P018a.signValue ((ω a).2) * SAP.P018a.signValue ((ω b).2)| ≤ (1 : ℝ) := by
      filter_upwards with ω
      cases ha : (ω a).2 <;> cases hb : (ω b).2 <;>
        norm_num [SAP.P018a.signValue]
    exact (MemLp.of_bound
      ((mixed_sign_coord_measurable a).mul (mixed_sign_coord_measurable b)).aestronglyMeasurable 1 hb :
      MemLp (fun ω : Fin N → ℝ × Bool =>
        SAP.P018a.signValue ((ω a).2) * SAP.P018a.signValue ((ω b).2)) ∞
        (SAP.P018a.unitSampleLaw K N)).integrable (by simp)
  have hformula : ∀ ω, SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f =
      (SAP.P018a.signValue ((ω i).2) + SAP.P018a.signValue ((ω j).2)) *
        (SAP.P018a.signValue ((ω k).2) + SAP.P018a.signValue ((ω l).2)) := by
    intro ω
    rw [mixed_epsilon_formula hβ, mixed_epsilon_formula hβ]
  have hcountN :
      (({i,j} : Finset (Fin N)) ∩ ({k,l} : Finset (Fin N))).card =
        (if i ∈ ({k,l} : Finset (Fin N)) then 1 else 0) +
          (if j ∈ ({k,l} : Finset (Fin N)) then 1 else 0) := by
    have hi_not : i ∉ ({j} : Finset (Fin N)) := by simp [hdi]
    rw [show (({i,j} : Finset (Fin N)) ∩ ({k,l} : Finset (Fin N))) =
      ({i,j} : Finset (Fin N)).filter
      (fun x => x ∈ ({k,l} : Finset (Fin N))) from by
        ext x
        simp [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]]
    rw [Finset.card_filter, Finset.sum_insert hi_not, Finset.sum_singleton]
  have hmem (x : Fin N) :
      (if x ∈ ({k,l} : Finset (Fin N)) then (1 : ℝ) else 0) =
        (if x = k then 1 else 0) + (if x = l then 1 else 0) := by
    by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      simp_all [Finset.mem_insert, Finset.mem_singleton, hfk]
  have hcard :
      (if i = k then (1 : ℝ) else 0) + (if i = l then 1 else 0) +
        (if j = k then 1 else 0) + (if j = l then 1 else 0) =
      ((SAP.P018a.members d ∩ SAP.P018a.members f).card : ℝ) := by
    rw [hsumd, hsumf]
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hcountN
    norm_num at hc
    have hiEq : (if i = k then (1 : ℝ) else 0) + (if i = l then 1 else 0) =
        (if i = k ∨ i = l then 1 else 0) := by
      by_cases hik : i = k
      · by_cases hil : i = l
        · exact False.elim (hfk (hik.symm.trans hil))
        · simp [hik, hil, hfk, Ne.symm hfk]
      · by_cases hil : i = l <;> simp [hik, hil, hfk, Ne.symm hfk]
    have hjEq : (if j = k then (1 : ℝ) else 0) + (if j = l then 1 else 0) =
        (if j = k ∨ j = l then 1 else 0) := by
      by_cases hjk : j = k
      · by_cases hjl : j = l
        · exact False.elim (hfk (hjk.symm.trans hjl))
        · simp [hjk, hjl, hfk, Ne.symm hfk]
      · by_cases hjl : j = l <;> simp [hjk, hjl, hfk, Ne.symm hfk]
    calc
      _ = ((if i = k then (1 : ℝ) else 0) + (if i = l then 1 else 0)) +
          ((if j = k then 1 else 0) + (if j = l then 1 else 0)) := by ring
      _ = (if i = k ∨ i = l then 1 else 0) +
          (if j = k ∨ j = l then 1 else 0) := by rw [hiEq, hjEq]
      _ = _ := hc.symm
  calc
    _ = ∫ ω, (SAP.P018a.signValue ((ω i).2) + SAP.P018a.signValue ((ω j).2)) *
        (SAP.P018a.signValue ((ω k).2) + SAP.P018a.signValue ((ω l).2))
        ∂SAP.P018a.unitSampleLaw K N := by
          apply integral_congr_ae
          filter_upwards with ω
          exact hformula ω
    _ = (∫ ω, SAP.P018a.signValue ((ω i).2) * SAP.P018a.signValue ((ω k).2)
          ∂SAP.P018a.unitSampleLaw K N) +
        (∫ ω, SAP.P018a.signValue ((ω i).2) * SAP.P018a.signValue ((ω l).2)
          ∂SAP.P018a.unitSampleLaw K N) +
        (∫ ω, SAP.P018a.signValue ((ω j).2) * SAP.P018a.signValue ((ω k).2)
          ∂SAP.P018a.unitSampleLaw K N) +
        (∫ ω, SAP.P018a.signValue ((ω j).2) * SAP.P018a.signValue ((ω l).2)
          ∂SAP.P018a.unitSampleLaw K N) := by
          have hleft : Integrable (fun ω : Fin N → ℝ × Bool =>
              SAP.P018a.signValue ((ω i).2) * SAP.P018a.signValue ((ω k).2) +
                SAP.P018a.signValue ((ω i).2) * SAP.P018a.signValue ((ω l).2))
              (SAP.P018a.unitSampleLaw K N) := (hprod i k).add (hprod i l)
          have hright : Integrable (fun ω : Fin N → ℝ × Bool =>
              SAP.P018a.signValue ((ω j).2) * SAP.P018a.signValue ((ω k).2) +
                SAP.P018a.signValue ((ω j).2) * SAP.P018a.signValue ((ω l).2))
              (SAP.P018a.unitSampleLaw K N) := (hprod j k).add (hprod j l)
          calc
            _ = ∫ ω, (SAP.P018a.signValue ((ω i).2) * SAP.P018a.signValue ((ω k).2) +
                SAP.P018a.signValue ((ω i).2) * SAP.P018a.signValue ((ω l).2)) +
                (SAP.P018a.signValue ((ω j).2) * SAP.P018a.signValue ((ω k).2) +
                SAP.P018a.signValue ((ω j).2) * SAP.P018a.signValue ((ω l).2))
                ∂SAP.P018a.unitSampleLaw K N := by
              apply integral_congr_ae
              filter_upwards with ω
              ring
            _ = _ := by
              rw [integral_add hleft hright,
                integral_add (hprod i k) (hprod i l),
                integral_add (hprod j k) (hprod j l)]
              ring
    _ = _ := by rw [mixed_sign_product, mixed_sign_product, mixed_sign_product,
      mixed_sign_product, hcard]

private lemma mixed_bridge_standing (hK : SAP.P018a.Standing K) :
    AronowAudit.P018.Standing (SAP.P018a.Bridge.toKernel K) :=
  (SAP.P018a.Bridge.kernel_assumptions_agree K).mp hK

private lemma mixed_bridge_law (N : ℕ) :
    SAP.P018a.unitSampleLaw K N =
      AronowAudit.P018.unitSampleLaw (SAP.P018a.Bridge.toKernel K) N :=
  (SAP.P018a.Bridge.kernel_sample_agrees K (fun _ : Fin N => (0, false))).1

private lemma mixed_bridge_design (N : ℕ) :
    (SAP.P018a.design K : (Fin N → ℝ × Bool) → SAP.P018a.Dyad N → SAP.P018a.Vec 2) =
      (AronowAudit.P018.design (SAP.P018a.Bridge.toKernel K) :
        (Fin N → ℝ × Bool) → SAP.P018a.Dyad N → SAP.P018a.Vec 2) := by
  funext ω
  exact (SAP.P018a.Bridge.kernel_sample_agrees K ω).2.1

private lemma mixed_bridge_epsilon (N : ℕ) :
    (SAP.P018a.epsilon K : (Fin N → ℝ × Bool) → SAP.P018a.Dyad N → ℝ) =
      (AronowAudit.P018.epsilon (SAP.P018a.Bridge.toKernel K) :
        (Fin N → ℝ × Bool) → SAP.P018a.Dyad N → ℝ) := by
  funext ω d
  exact congrFun (SAP.P018a.Bridge.kernel_sample_agrees K ω).2.2.2 d

private lemma mixed_bridge_scoreH :
    SAP.P018a.scoreH K =
      AronowAudit.P018.scoreH (SAP.P018a.Bridge.toKernel K) := by
  rfl

private lemma mixed_bridge_projectionGamma :
    SAP.P018a.projectionGamma K =
      AronowAudit.P018.projectionGamma (SAP.P018a.Bridge.toKernel K) := by
  rfl

private lemma mixed_eps_indep_design {N : ℕ} (hK : SAP.P018a.Standing K)
    (hβ : SAP.P018a.populationBeta K = 0) (d f : SAP.P018a.Dyad N) :
    (fun ω : Fin N → ℝ × Bool => SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f)
      ⟂ᵢ[SAP.P018a.unitSampleLaw K N] SAP.P018a.design K := by
  let P := SAP.P018a.unitSampleLaw K N
  let E : (Fin N → ℝ × Bool) → ℝ := fun ω => SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f
  have hsign := (mixed_arrays_independent N).symm
  have hmE : Measurable (fun s : Fin N → Bool =>
      (SAP.P018a.signValue (s (SAP.P018a.firstUnit d)) +
        SAP.P018a.signValue (s (SAP.P018a.secondUnit d))) *
      (SAP.P018a.signValue (s (SAP.P018a.firstUnit f)) +
        SAP.P018a.signValue (s (SAP.P018a.secondUnit f)))) := by fun_prop
  have hmD : Measurable (fun z : Fin N → ℝ =>
      fun q : SAP.P018a.Dyad N => ![1,z (SAP.P018a.firstUnit q)+z (SAP.P018a.secondUnit q)]) := by
    apply measurable_pi_lambda
    intro q
    fun_prop
  have hcomp := hsign.comp hmE hmD
  have he : E = fun ω =>
      (SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2) +
        SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2)) *
      (SAP.P018a.signValue ((ω (SAP.P018a.firstUnit f)).2) +
        SAP.P018a.signValue ((ω (SAP.P018a.secondUnit f)).2)) := by
    funext ω
    change SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f = _
    rw [mixed_epsilon_formula hβ, mixed_epsilon_formula hβ]
  have hEmeas : Measurable E := by rw [he]; fun_prop
  have hd : SAP.P018a.design K = fun ω =>
      fun q : SAP.P018a.Dyad N => ![1,(coordArray ω) (SAP.P018a.firstUnit q)+
        (coordArray ω) (SAP.P018a.secondUnit q)] := by
    funext ω q
    simp [SAP.P018a.design, SAP.P018a.W1MixedKernel, coordArray]
  simpa [E, P, he, hd, signArray, coordArray, SAP.P018a.Vec, Function.comp_def] using hcomp

private lemma mixed_condmean_zero {N : ℕ} (hK : SAP.P018a.Standing K)
    (hβ : SAP.P018a.populationBeta K = 0) (d : SAP.P018a.Dyad N) :
    SAP.P018a.conditionalResidualMean K d =ᵐ[SAP.P018a.unitSampleLaw K N] 0 := by
  let P := SAP.P018a.unitSampleLaw K N
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  let E : (Fin N → ℝ × Bool) → ℝ := fun ω => SAP.P018a.epsilon K ω d
  have hsign := (mixed_arrays_independent N).symm
  have hmE : Measurable (fun s : Fin N → Bool =>
      SAP.P018a.signValue (s (SAP.P018a.firstUnit d)) +
        SAP.P018a.signValue (s (SAP.P018a.secondUnit d))) := by fun_prop
  have hmD : Measurable (fun z : Fin N → ℝ =>
      fun q : SAP.P018a.Dyad N => ![1,z (SAP.P018a.firstUnit q)+z (SAP.P018a.secondUnit q)]) := by
    apply measurable_pi_lambda
    intro q
    fun_prop
  have hcomp := hsign.comp hmE hmD
  have he : E = fun ω =>
      SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2) +
        SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2) := by
    funext ω
    exact mixed_epsilon_formula hβ ω d
  have hEmeas : Measurable E := by rw [he]; fun_prop
  have hd : SAP.P018a.design K = fun ω =>
      fun q : SAP.P018a.Dyad N => ![1,(coordArray ω) (SAP.P018a.firstUnit q)+
        (coordArray ω) (SAP.P018a.secondUnit q)] := by
    funext ω q
    simp [SAP.P018a.design, SAP.P018a.W1MixedKernel, coordArray]
  have hInd : E ⟂ᵢ[P] SAP.P018a.design K := by
    simpa [E, hd, he, signArray, coordArray, SAP.P018a.Vec, Function.comp_def] using hcomp
  have hce := MeasureTheory.condExp_indep_eq hEmeas.comap_le
    (mixed_design_measurable hK).comap_le
    (comap_measurable E).stronglyMeasurable
    ((ProbabilityTheory.IndepFun_iff_Indep E (SAP.P018a.design K) P).mp hInd)
  have hmean : (∫ ω, E ω ∂P) = 0 := by
    simpa [P, E] using mixed_epsilon_mean hβ d
  filter_upwards [hce] with ω hω
  simpa [SAP.P018a.conditionalResidualMean, SAP.P018a.designSigma,
    E, P, hmean] using hω

private lemma mixed_condcov_card {N : ℕ} (hK : SAP.P018a.Standing K)
    (hβ : SAP.P018a.populationBeta K = 0) (d f : SAP.P018a.Dyad N) :
    SAP.P018a.conditionalResidualCov K d f =ᵐ[SAP.P018a.unitSampleLaw K N]
      fun _ => ((SAP.P018a.members d ∩ SAP.P018a.members f).card : ℝ) := by
  let P := SAP.P018a.unitSampleLaw K N
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hm1 := mixed_condmean_zero hK hβ d
  have hm2 := mixed_condmean_zero hK hβ f
  have hcenter : (fun ω =>
      (SAP.P018a.epsilon K ω d-SAP.P018a.conditionalResidualMean K d ω) *
      (SAP.P018a.epsilon K ω f-SAP.P018a.conditionalResidualMean K f ω)) =ᵐ[P]
        fun ω => SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f := by
    filter_upwards [hm1, hm2] with ω h1 h2
    simp [h1, h2]
  have hInd := mixed_eps_indep_design hK hβ d f
  let E : (Fin N → ℝ × Bool) → ℝ := fun ω => SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f
  have hEmeas : Measurable E := by
    have he : E = fun ω =>
        (SAP.P018a.signValue ((ω (SAP.P018a.firstUnit d)).2) +
          SAP.P018a.signValue ((ω (SAP.P018a.secondUnit d)).2)) *
        (SAP.P018a.signValue ((ω (SAP.P018a.firstUnit f)).2) +
          SAP.P018a.signValue ((ω (SAP.P018a.secondUnit f)).2)) := by
      funext ω
      change SAP.P018a.epsilon K ω d * SAP.P018a.epsilon K ω f = _
      rw [mixed_epsilon_formula hβ, mixed_epsilon_formula hβ]
    rw [he]
    fun_prop
  have hce := MeasureTheory.condExp_indep_eq hEmeas.comap_le
    (mixed_design_measurable hK).comap_le
    (comap_measurable E).stronglyMeasurable
    ((ProbabilityTheory.IndepFun_iff_Indep E (SAP.P018a.design K) P).mp hInd)
  have hprod : (∫ ω, E ω ∂P) =
      ((SAP.P018a.members d ∩ SAP.P018a.members f).card : ℝ) := by
    simpa [E] using mixed_epsilon_product hβ d f
  unfold SAP.P018a.conditionalResidualCov
  exact (MeasureTheory.condExp_congr_ae hcenter).trans (by
    filter_upwards [hce] with ω hω
    simpa [SAP.P018a.designSigma, E, P, hprod] using hω)

private lemma mixed_conditionalTerm_formula {N : ℕ} (hK : SAP.P018a.Standing K)
    (hβ : SAP.P018a.populationBeta K = 0) (d f : SAP.P018a.Dyad N) :
    SAP.P018a.conditionalTerm K d f =
      ((SAP.P018a.members d ∩ SAP.P018a.members f).card : ℝ) •
        meanMat (SAP.P018a.unitSampleLaw K N)
          (fun ω => SAP.P018a.outer (SAP.P018a.design K ω d) (SAP.P018a.design K ω f)) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  unfold SAP.P018a.conditionalTerm
  ext a b
  change (∫ ω, SAP.P018a.conditionalResidualCov K d f ω *
      (SAP.P018a.design K ω d a * SAP.P018a.design K ω f b)
      ∂SAP.P018a.unitSampleLaw K N) = _
  have he : (fun ω => SAP.P018a.conditionalResidualCov K d f ω *
      (SAP.P018a.design K ω d a * SAP.P018a.design K ω f b)) =ᵐ[
        SAP.P018a.unitSampleLaw K N] (fun ω =>
          ((SAP.P018a.members d ∩ SAP.P018a.members f).card : ℝ) *
            (SAP.P018a.design K ω d a * SAP.P018a.design K ω f b)) := by
    filter_upwards [mixed_condcov_card hK hβ d f] with ω hω
    rw [hω]
  rw [integral_congr_ae he]
  simp [meanMat, outer, integral_const_mul, mul_assoc]

private lemma mixed_same_design_moment {N : ℕ} (hK : SAP.P018a.Standing K)
    (d : SAP.P018a.Dyad N) :
    meanMat (SAP.P018a.unitSampleLaw K N)
      (fun ω => SAP.P018a.outer (SAP.P018a.design K ω d) (SAP.P018a.design K ω d)) =
      SAP.P018a.populationGram K := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hm := AronowAudit.P018.Wave1.vc3_pair_preserving K.μ
    (SAP.P018a.firstUnit d) (SAP.P018a.secondUnit d)
    (ne_of_lt (Finset.min'_lt_max'_of_card (SAP.P018a.members d)
      (by rw [SAP.P018a.members_card]; norm_num)))
  ext a b
  change (∫ ω, SAP.P018a.design K ω d a * SAP.P018a.design K ω d b
      ∂SAP.P018a.unitSampleLaw K N) =
    ∫ uv, K.X uv.1 uv.2 a * K.X uv.1 uv.2 b ∂K.μ.prod K.μ
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable
    (((measurable_pi_apply a).comp hK.2.1).mul
      ((measurable_pi_apply b).comp hK.2.1)).aestronglyMeasurable).symm

private lemma mixed_design_at_members {N : ℕ} (hK : SAP.P018a.Standing K)
    (d : SAP.P018a.Dyad N) (i j : Fin N) (hij : i ≠ j)
    (hd : SAP.P018a.members d = {i,j}) (ω : Fin N → ℝ × Bool) :
    SAP.P018a.design K ω d = K.X (ω i) (ω j) := by
  have he : ({SAP.P018a.firstUnit d, SAP.P018a.secondUnit d} : Set (Fin N)) = {i,j} := by
    have hh := (mixed_members_endpoints d).symm.trans hd
    have hh' := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) hh
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hh'
  rcases Set.pair_eq_pair_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · change K.X (ω (SAP.P018a.firstUnit d)) (ω (SAP.P018a.secondUnit d)) = _
    rw [h1,h2]
  · change K.X (ω (SAP.P018a.firstUnit d)) (ω (SAP.P018a.secondUnit d)) = _
    rw [h1,h2]
    exact (hK.2.2.2.1 (ω j) (ω i)).1

private lemma mixed_shared_design_moment {N : ℕ} (hK : SAP.P018a.Standing K)
    (d f : SAP.P018a.Dyad N) (hne : d ≠ f) (hov : SAP.P018a.overlap d f) :
    meanMat (SAP.P018a.unitSampleLaw K N)
      (fun ω => SAP.P018a.outer (SAP.P018a.design K ω d) (SAP.P018a.design K ω f)) =
      SAP.P018a.W1CrossGram K := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨i, hi⟩ := hov
  obtain ⟨hid,hif⟩ := Finset.mem_inter.mp hi
  let j := mixed_other i d
  let l := mixed_other i f
  have hij : i ≠ j := mixed_other_ne i d hid
  have hil : i ≠ l := mixed_other_ne i f hif
  have hd : SAP.P018a.members d = {i,j} := mixed_members_other i d hid
  have hf : SAP.P018a.members f = {i,l} := mixed_members_other i f hif
  have hjl : j ≠ l := by
    intro h
    apply hne
    apply Subtype.ext
    change SAP.P018a.members d = SAP.P018a.members f
    rw [hd, hf, h]
  have hm := AronowAudit.P018.Wave1.vc3_triple_preserving K.μ i j l hij hil hjl
  ext a b
  change (∫ ω, SAP.P018a.design K ω d a * SAP.P018a.design K ω f b
      ∂SAP.P018a.unitSampleLaw K N) =
    ∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
      K.X z.1.1 z.1.2 a * K.X z.1.1 z.2 b ∂(K.μ.prod K.μ).prod K.μ
  calc
    _ = ∫ ω, K.X (ω i) (ω j) a * K.X (ω i) (ω l) b
        ∂SAP.P018a.unitSampleLaw K N := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [mixed_design_at_members hK d i j hij hd ω,
        mixed_design_at_members hK f i l hil hf ω]
    _ = ∫ z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool),
        K.X z.1.1 z.1.2 a * K.X z.1.1 z.2 b ∂(K.μ.prod K.μ).prod K.μ := by
      rw [← hm.map_eq]
      have hA : Measurable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
          K.X z.1.1 z.1.2 a) :=
        ((measurable_pi_apply a).comp hK.2.1).comp measurable_fst
      have hB : Measurable (fun z : ((ℝ × Bool) × (ℝ × Bool)) × (ℝ × Bool) =>
          K.X z.1.1 z.2 b) :=
        ((measurable_pi_apply b).comp hK.2.1).comp
          (measurable_fst.fst.prodMk measurable_snd)
      exact (integral_map hm.aemeasurable (hA.mul hB).aestronglyMeasurable).symm
    _ = SAP.P018a.W1CrossGram K a b := rfl

private lemma mixed_intersection_card_one {N : ℕ} (d f : SAP.P018a.Dyad N)
    (hf : f ∈ SAP.P018a.neighbors d) :
    (SAP.P018a.members d ∩ SAP.P018a.members f).card = 1 := by
  have hne : d ≠ f := (Finset.mem_filter.mp hf).2.1.symm
  have hov : (SAP.P018a.members d ∩ SAP.P018a.members f).Nonempty :=
    (Finset.mem_filter.mp hf).2.2
  have hpos : 0 < (SAP.P018a.members d ∩ SAP.P018a.members f).card := Finset.card_pos.mpr hov
  have hle : (SAP.P018a.members d ∩ SAP.P018a.members f).card ≤ 1 := by
    by_contra hn
    have hcard : (SAP.P018a.members d ∩ SAP.P018a.members f).card = 2 := by
      have hle2 : (SAP.P018a.members d ∩ SAP.P018a.members f).card ≤ 2 := by
        calc
          _ ≤ (SAP.P018a.members d).card := Finset.card_mono Finset.inter_subset_left
          _ = 2 := SAP.P018a.members_card d
      omega
    have heq : SAP.P018a.members d ∩ SAP.P018a.members f = SAP.P018a.members d :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hcard, SAP.P018a.members_card])
    have hsub : SAP.P018a.members d ⊆ SAP.P018a.members f := by
      intro i hi
      have hi' : i ∈ SAP.P018a.members d ∩ SAP.P018a.members f := by rw [heq]; exact hi
      exact (Finset.mem_inter.mp hi').2
    have hdf : d = f := by
      apply Subtype.ext
      change SAP.P018a.members d = SAP.P018a.members f
      exact Finset.eq_of_subset_of_card_le hsub (by rw [SAP.P018a.members_card, SAP.P018a.members_card])
    exact hne hdf
  omega

private lemma mixed_scoreCov_moment {N : ℕ} (hK : SAP.P018a.Standing K)
    (d f : SAP.P018a.Dyad N) :
    SAP.P018a.covMat (SAP.P018a.unitSampleLaw K N)
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d))
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω f) (SAP.P018a.epsilon K ω f)) =
    meanMat (SAP.P018a.unitSampleLaw K N) (fun ω =>
      SAP.P018a.outer (SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d))
        (SAP.P018a.score (SAP.P018a.design K ω f) (SAP.P018a.epsilon K ω f))) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hK' := mixed_bridge_standing hK
  letI : IsProbabilityMeasure (SAP.P018a.Bridge.toKernel K).μ := hK'.1
  ext a b
  have hLpDsrc := AronowAudit.P018.Wave1.vc3_score_lp
    (SAP.P018a.Bridge.toKernel K) hK' d a 2
  have hLpFsrc := AronowAudit.P018.Wave1.vc3_score_lp
    (SAP.P018a.Bridge.toKernel K) hK' f b 2
  have hLpD : MemLp (fun ω => SAP.P018a.score
      (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d) a) 2
      (SAP.P018a.unitSampleLaw K N) := by
    simpa only [← mixed_bridge_design (N := N), ← mixed_bridge_epsilon (N := N),
      ← mixed_bridge_law (N := N), SAP.P018a.score, AronowAudit.P018.score] using hLpDsrc
  have hLpF : MemLp (fun ω => SAP.P018a.score
      (SAP.P018a.design K ω f) (SAP.P018a.epsilon K ω f) b) 2
      (SAP.P018a.unitSampleLaw K N) := by
    simpa only [← mixed_bridge_design (N := N), ← mixed_bridge_epsilon (N := N),
      ← mixed_bridge_law (N := N), SAP.P018a.score, AronowAudit.P018.score] using hLpFsrc
  change ProbabilityTheory.covariance
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d) a)
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω f) (SAP.P018a.epsilon K ω f) b)
      (SAP.P018a.unitSampleLaw K N) = _
  rw [ProbabilityTheory.covariance_eq_sub hLpD hLpF]
  simp only [SAP.P018a.meanMat, SAP.P018a.outer]
  have hd := congrFun (AronowAudit.P018.Wave1.vc3_dyad_mean
    (SAP.P018a.Bridge.toKernel K) hK' d) a
  have hf := congrFun (AronowAudit.P018.Wave1.vc3_dyad_mean
    (SAP.P018a.Bridge.toKernel K) hK' f) b
  have hd' : (∫ ω, SAP.P018a.score (SAP.P018a.design K ω d)
      (SAP.P018a.epsilon K ω d) a ∂SAP.P018a.unitSampleLaw K N) = 0 := by
    simpa only [SAP.P018a.meanVec, AronowAudit.P018.meanVec,
      ← mixed_bridge_law (N := N),
      ← mixed_bridge_design (N := N), ← mixed_bridge_epsilon (N := N),
      SAP.P018a.score, AronowAudit.P018.score, Pi.zero_apply] using hd
  have hf' : (∫ ω, SAP.P018a.score (SAP.P018a.design K ω f)
      (SAP.P018a.epsilon K ω f) b ∂SAP.P018a.unitSampleLaw K N) = 0 := by
    simpa only [SAP.P018a.meanVec, AronowAudit.P018.meanVec,
      ← mixed_bridge_law (N := N),
      ← mixed_bridge_design (N := N), ← mixed_bridge_epsilon (N := N),
      SAP.P018a.score, AronowAudit.P018.score, Pi.zero_apply] using hf
  rw [hd', hf']
  simp

private lemma mixed_scoreCov_same {N : ℕ} (hK : SAP.P018a.Standing K)
    (d : SAP.P018a.Dyad N) :
    SAP.P018a.covMat (SAP.P018a.unitSampleLaw K N)
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d))
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d)) =
      SAP.P018a.scoreH K := by
  rw [mixed_scoreCov_moment hK]
  rw [mixed_bridge_scoreH]
  ext a b
  have hs := AronowAudit.P018.Wave1.vc3_same_moment
    (SAP.P018a.Bridge.toKernel K) (mixed_bridge_standing hK) d
  have hsab := congrFun (congrFun hs a) b
  simpa only [SAP.P018a.meanMat, AronowAudit.P018.meanMat,
    SAP.P018a.outer, AronowAudit.P018.outer,
    SAP.P018a.score, AronowAudit.P018.score,
    ← mixed_bridge_design (N := N), ← mixed_bridge_epsilon (N := N),
    ← mixed_bridge_law (N := N)] using hsab

private lemma mixed_scoreCov_overlap {N : ℕ} (hK : SAP.P018a.Standing K)
    (d f : SAP.P018a.Dyad N) (hne : d ≠ f) (hov : SAP.P018a.overlap d f) :
    SAP.P018a.covMat (SAP.P018a.unitSampleLaw K N)
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d))
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω f) (SAP.P018a.epsilon K ω f)) =
      SAP.P018a.projectionGamma K := by
  rw [mixed_scoreCov_moment hK]
  rw [mixed_bridge_projectionGamma]
  ext a b
  have hs := AronowAudit.P018.Wave1.vc3_overlap_moment
    (SAP.P018a.Bridge.toKernel K) (mixed_bridge_standing hK) d f hne hov
  have hsab := congrFun (congrFun hs a) b
  simpa only [SAP.P018a.meanMat, AronowAudit.P018.meanMat,
    SAP.P018a.outer, AronowAudit.P018.outer,
    SAP.P018a.score, AronowAudit.P018.score,
    ← mixed_bridge_design (N := N), ← mixed_bridge_epsilon (N := N),
    ← mixed_bridge_law (N := N)] using hsab

private lemma mixed_conditional_row {N : ℕ} (hK : SAP.P018a.Standing K)
    (hβ : SAP.P018a.populationBeta K = 0)
    (hQ : SAP.P018a.populationGram K = !![1,0;0,2/3])
    (hC : SAP.P018a.W1CrossGram K = !![1,0;0,1/3])
    (hN : 3 ≤ N) (d : SAP.P018a.Dyad N) :
    SAP.P018a.W1ConditionalRow K d = !![2*(N : ℝ)-2,0;0,2*(N : ℝ)/3] := by
  have hself : SAP.P018a.conditionalTerm K d d = 2 • SAP.P018a.populationGram K := by
    rw [mixed_conditionalTerm_formula hK hβ, Finset.inter_self,
      SAP.P018a.members_card, mixed_same_design_moment hK d]
    ext a b
    simp [meanMat, outer, integral_const_mul, smul_eq_mul]
  have hneighbor (f : SAP.P018a.Dyad N) (hf : f ∈ SAP.P018a.neighbors d) :
      SAP.P018a.conditionalTerm K d f = SAP.P018a.W1CrossGram K := by
    have hne : d ≠ f := (Finset.mem_filter.mp hf).2.1.symm
    have hov : SAP.P018a.overlap d f := (Finset.mem_filter.mp hf).2.2
    rw [mixed_conditionalTerm_formula hK hβ,
      mixed_intersection_card_one d f hf]
    simp [mixed_shared_design_moment hK d f hne hov]
  have hsum : (∑ f ∈ SAP.P018a.neighbors d, SAP.P018a.conditionalTerm K d f) =
      ((SAP.P018a.neighbors d).card : ℝ) • SAP.P018a.W1CrossGram K := by
    calc
      _ = ∑ f ∈ SAP.P018a.neighbors d, SAP.P018a.W1CrossGram K := by
        rw [Finset.sum_congr rfl hneighbor]
      _ = (SAP.P018a.neighbors d).card • SAP.P018a.W1CrossGram K := by simp
      _ = ((SAP.P018a.neighbors d).card : ℝ) • SAP.P018a.W1CrossGram K := by
        rw [← Nat.cast_smul_eq_nsmul ℝ]
  have hcount := (AronowAudit.P018.Wave1.dyad_counts_proof N (by omega)).2.1 d
  have hneighbors : SAP.P018a.neighbors d = AronowAudit.P018.neighbors d := rfl
  have hcount' : (SAP.P018a.neighbors d).card = 2*(N-2) := by
    rw [hneighbors]
    exact hcount
  have hcast : ((SAP.P018a.neighbors d).card : ℝ) = 2*((N : ℝ)-2) := by
    rw [hcount']
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 2 ≤ N)]
    norm_num
  rw [SAP.P018a.W1ConditionalRow, hself, hsum, hQ, hC]
  rw [hcast]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

private lemma mixed_score_row {N : ℕ} (hK : SAP.P018a.Standing K)
    (hH : SAP.P018a.scoreH K = !![2,0;0,4/3])
    (hΓ : SAP.P018a.projectionGamma K = !![1,0;0,1/3])
    (hN : 3 ≤ N) (d : SAP.P018a.Dyad N) :
    SAP.P018a.W1ScoreCovRow K d = !![2*(N : ℝ)-2,0;0,2*(N : ℝ)/3] := by
  have hself : SAP.P018a.covMat (SAP.P018a.unitSampleLaw K N)
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d))
      (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d)) =
      SAP.P018a.scoreH K := mixed_scoreCov_same hK d
  have hneighbor (f : SAP.P018a.Dyad N) (hf : f ∈ SAP.P018a.neighbors d) :
      SAP.P018a.covMat (SAP.P018a.unitSampleLaw K N)
        (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d))
        (fun ω => SAP.P018a.score (SAP.P018a.design K ω f) (SAP.P018a.epsilon K ω f)) =
      SAP.P018a.projectionGamma K := by
    exact mixed_scoreCov_overlap hK d f
      ((Finset.mem_filter.mp hf).2.1.symm) ((Finset.mem_filter.mp hf).2.2)
  have hsum : (∑ f ∈ SAP.P018a.neighbors d,
      SAP.P018a.covMat (SAP.P018a.unitSampleLaw K N)
        (fun ω => SAP.P018a.score (SAP.P018a.design K ω d) (SAP.P018a.epsilon K ω d))
        (fun ω => SAP.P018a.score (SAP.P018a.design K ω f) (SAP.P018a.epsilon K ω f)) ) =
      ((SAP.P018a.neighbors d).card : ℝ) • SAP.P018a.projectionGamma K := by
    calc
      _ = ∑ f ∈ SAP.P018a.neighbors d, SAP.P018a.projectionGamma K := by
        rw [Finset.sum_congr rfl hneighbor]
      _ = (SAP.P018a.neighbors d).card • SAP.P018a.projectionGamma K := by simp
      _ = ((SAP.P018a.neighbors d).card : ℝ) • SAP.P018a.projectionGamma K := by
        rw [← Nat.cast_smul_eq_nsmul ℝ]
  have hcount := (AronowAudit.P018.Wave1.dyad_counts_proof N (by omega)).2.1 d
  have hneighbors : SAP.P018a.neighbors d = AronowAudit.P018.neighbors d := rfl
  have hcount' : (SAP.P018a.neighbors d).card = 2*(N-2) := by
    rw [hneighbors]
    exact hcount
  have hcast : ((SAP.P018a.neighbors d).card : ℝ) = 2*((N : ℝ)-2) := by
    rw [hcount']
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 2 ≤ N)]
    norm_num
  rw [SAP.P018a.W1ScoreCovRow, hself, hsum, hH, hΓ]
  rw [hcast]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

end SAP.P018a.WH.W1.P.T11_L6

theorem SAP.P018a.WH.W1.T11_L6_proof : SAP.P018a.WH.W1.T11_L6 := by
  intro hMom
  rcases hMom with ⟨hK,hβ,hQ,hC,_,hH,hΓ⟩
  intro N hN d
  exact ⟨SAP.P018a.WH.W1.P.T11_L6.mixed_conditional_row hK hβ hQ hC hN d,
    SAP.P018a.WH.W1.P.T11_L6.mixed_score_row hK hH hΓ hN d⟩
