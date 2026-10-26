import AronowAudit.P001.Wave1.Lib.TailA.MatchingEndpointIntegrals

/-! Exact finite-sample identities and transport to arbitrary iid streams. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA

universe u
local instance instDecidableMatchingFiniteEndpoints (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem matching_endpoint_twodraw (n : ℕ) (f : (Fin n → Fin n) → ℝ) :
    mean (UniformResampling n) (fun a => mean (UniformResampling n)
      (fun b => (f a-f b)^2)) =
        2*(mean (UniformResampling n) (fun a => (f a)^2) -
          mean (UniformResampling n) (fun a => mean (UniformResampling n)
            (fun b => f a*f b))) := by
  have he (a : Fin n → Fin n) :
      mean (UniformResampling n) (fun b => (f a-f b)^2) =
        (f a)^2+mean (UniformResampling n) (fun b => (f b)^2) -
          2*mean (UniformResampling n) (fun b => f a*f b) := by
    have hpoly : (fun b => (f a-f b)^2) =
        fun b => ((f a)^2+(f b)^2)-2*(f a*f b) := by funext b; ring
    rw [hpoly]
    unfold mean
    rw [integral_sub (Integrable.of_finite.add Integrable.of_finite) Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,integral_const,
      probReal_univ,smul_eq_mul,one_mul]
    congr 1
    rw [← integral_const_mul]
  simp_rw [he]
  unfold mean
  rw [integral_sub (Integrable.of_finite.add Integrable.of_finite) Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite,integral_const,
    probReal_univ,smul_eq_mul,one_mul,integral_const_mul]
  ring

theorem matching_endpoint_twodraw_population (n : ℕ) (j : Fin n) :
    (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n,
      mean (MatchProduct n) (fun z => (U z a j-U z b j)^2)) / ((n : ℝ)^n)^2 =
        2*(mean (MatchProduct n) (fun z => matchingEndpointMoment 1 z j) -
          mean (MatchProduct n) (fun z => matchingEndpointMoment 2 z j)) := by
  have hterm (a b : Fin n → Fin n) :
      Integrable (fun z => (U z a j-U z b j)^2) (MatchProduct n) :=
    ((matching_U_memLp (MatchProduct n) a j 2).sub
      (matching_U_memLp (MatchProduct n) b j 2)).integrable_sq
  have hh : mean (MatchProduct n) (fun z => mean (UniformResampling n)
      (fun a => mean (UniformResampling n) (fun b => (U z a j-U z b j)^2))) =
        (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n,
          mean (MatchProduct n) (fun z => (U z a j-U z b j)^2)) / ((n : ℝ)^n)^2 := by
    simp_rw [uniform_resampling_mean]
    unfold mean
    rw [integral_div,integral_finsetSum _ (fun a _ =>
      (integrable_finsetSum _ (fun b _ => hterm a b)).div_const _)]
    simp_rw [integral_div,integral_finsetSum _ (fun b _ => hterm _ b)]
    rw [← Finset.sum_div]
    ring
  rw [← hh]
  simp_rw [matching_endpoint_twodraw]
  change (∫ z, 2*(matchingEndpointMoment 1 z j-matchingEndpointMoment 2 z j)
    ∂MatchProduct n) = _
  rw [integral_const_mul,integral_sub
    (matching_endpoint_moment_integrable 1 _ j) (matching_endpoint_moment_integrable 2 _ j)]
  rfl

theorem matching_endpoint_scaled_original_product (n : ℕ) :
    (n+1 : ℕ)*var (MatchProduct (n+1)) hotDeck =
      mean (MatchProduct (n+1)) (fun z => matchingEndpointMoment 0 z 0) := by
  rw [matching_original_variance (n+1) (by omega)]
  have hs : (∑ j : Fin (n+1), mean (MatchProduct (n+1)) (fun z => (W z j)^2)) =
      (n+1 : ℕ)*mean (MatchProduct (n+1)) (fun z => matchingEndpointMoment 0 z 0) := by
    change (∑ j, mean (MatchProduct (n+1)) (fun z => matchingEndpointMoment 0 z j)) = _
    simp only [matching_endpoint_moment_exchangeable 0 _ (0 : Fin (n+1)),Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hs]
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem matching_endpoint_scaled_bootstrap_product (n : ℕ) :
    mean (MatchProduct (n+1)) (fun z => (n+1 : ℕ)*bootVar hotDeck z) =
      mean (MatchProduct (n+1)) (fun z => matchingEndpointMoment 1 z 0) -
        mean (MatchProduct (n+1)) (fun z => matchingEndpointMoment 2 z 0) := by
  let N := n+1
  let D : ℝ := (N : ℝ)^N
  have hN : (N : ℝ) ≠ 0 := by dsimp [N]; positivity
  have hD : D ≠ 0 := pow_ne_zero _ hN
  have hj (j : Fin N) := (div_eq_iff (pow_ne_zero 2 hD)).mp
    (matching_endpoint_twodraw_population N j)
  have hsum : (∑ a : Fin N → Fin N, ∑ b : Fin N → Fin N, ∑ j : Fin N,
      mean (MatchProduct N) (fun z => (U z a j-U z b j)^2)) =
        (N : ℝ)*(2*(mean (MatchProduct N) (fun z => matchingEndpointMoment 1 z 0) -
          mean (MatchProduct N) (fun z => matchingEndpointMoment 2 z 0))*D^2) := by
    have hswap : (∑ a : Fin N → Fin N, ∑ b : Fin N → Fin N, ∑ j : Fin N,
        mean (MatchProduct N) (fun z => (U z a j-U z b j)^2)) =
          ∑ j : Fin N, ∑ a : Fin N → Fin N, ∑ b : Fin N → Fin N,
            mean (MatchProduct N) (fun z => (U z a j-U z b j)^2) := by
      calc
        _ = ∑ a : Fin N → Fin N, ∑ j : Fin N, ∑ b : Fin N → Fin N,
            mean (MatchProduct N) (fun z => (U z a j-U z b j)^2) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    rw [hswap]
    simp_rw [hj,matching_endpoint_moment_exchangeable 1 _ (0 : Fin N),
      matching_endpoint_moment_exchangeable 2 _ (0 : Fin N)]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (∫ z, (N : ℝ)*bootVar hotDeck z ∂MatchProduct N) = _
  rw [integral_const_mul]
  change (N : ℝ)*mean (MatchProduct N) (bootVar hotDeck) = _
  rw [matching_bootstrap_expectation N (by dsimp [N]; omega),hsum]
  change (N : ℝ)*((N : ℝ)*(2*((mean (MatchProduct N) (fun z => matchingEndpointMoment 1 z 0))-
    mean (MatchProduct N) (fun z => matchingEndpointMoment 2 z 0))*D^2)/(2*(N : ℝ)^2*D^2)) = _
  field_simp
  <;> ring

theorem matching_endpoint_first_measurable {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : ℕ → Ω → MatchUnit} (hiid : IID μ Z) (n : ℕ) :
    Measurable (firstSample Z n) :=
  Measurable.of_eval (fun i : Fin n => hiid.1 i)

theorem matching_endpoint_variance_transport {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → MatchUnit)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = matchingUnitLaw) (n : ℕ)
    {T : (Fin n → MatchUnit) → ℝ} (hT : Measurable T) :
    var μ (fun ω => T (firstSample Z n ω)) = var (MatchProduct n) T := by
  exact (show MeasurePreserving (firstSample Z n) μ (MatchProduct n) from
    ⟨matching_endpoint_first_measurable hiid n,matching_finite_law μ Z hiid hlaw n⟩).variance_fun_comp
      hT.aemeasurable

theorem matching_endpoint_reflection_variance (n : ℕ) :
    var (MatchProduct n) causalMatch = var (MatchProduct n) hotDeck := by
  unfold var
  have hp := matching_product_reflection n
  rw [show (@causalMatch n) = fun z => -(hotDeck (matchingReflectSample z)-50) from
    funext matching_reflection_statistic,variance_fun_neg]
  rw [hp.variance_fun_comp (f := fun z => hotDeck z-50)
    ((matching_hotDeck_measurable n).sub_const 50).aemeasurable,
    variance_sub_const (matching_hotDeck_measurable n).aestronglyMeasurable]

theorem matching_endpoint_reflection_bootstrap (n : ℕ) :
    mean (MatchProduct n) (fun z => (n : ℝ)*bootVar causalMatch z) =
      mean (MatchProduct n) (fun z => (n : ℝ)*bootVar hotDeck z) := by
  simp_rw [matching_bootVar_reflection]
  have hh := integral_map (μ := MatchProduct n) (matching_product_reflection n).measurable.aemeasurable
    (show Measurable (fun z : Fin n → MatchUnit => (n : ℝ)*bootVar hotDeck z) from
      measurable_const.mul (matching_bootVar_measurable (matching_hotDeck_measurable n))).aestronglyMeasurable
  rw [(matching_product_reflection n).map_eq] at hh
  exact hh.symm

end AronowAudit.P001.TailA
