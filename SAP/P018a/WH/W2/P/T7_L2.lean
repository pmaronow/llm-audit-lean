import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section

namespace SAP.P018a.WH.W2.P.T7_L2

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise ENNReal

abbrev K : AronowAudit.P018.Kernel (Bool × Bool) 2 :=
  AronowAudit.P018.signPairKernel

lemma hK : AronowAudit.P018.Standing K :=
  AronowAudit.P018.Wave1.TailBSign.tb05_standing

lemma residual_eq (u v : Bool × Bool) :
    AronowAudit.P018.populationResidual K u v = K.Y u v := by
  exact AronowAudit.P018.Wave1.TailBSign.tb05_population_residual u v

lemma signPair_scoreH_donor :
    AronowAudit.P018.scoreH K =
      (2 : ℝ) • (!![1,1;1,2] : AronowAudit.P018.Mat 2) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  ext a b
  fin_cases a <;> fin_cases b
  all_goals
    simp only [AronowAudit.P018.scoreH, AronowAudit.P018.meanMat,
      AronowAudit.P018.outer, AronowAudit.P018.populationScore,
      AronowAudit.P018.score, Pi.smul_apply, smul_eq_mul]
    change (∫ uv, (AronowAudit.P018.populationResidual K uv.1 uv.2 * K.X uv.1 uv.2 _)
        * (AronowAudit.P018.populationResidual K uv.1 uv.2 * K.X uv.1 uv.2 _)
        ∂ K.μ.prod K.μ) = _
    rw [AronowAudit.P018.Wave1.TailBSign.tb05_units_integral]
    simp_rw [AronowAudit.P018.Wave1.TailBSign.tb05_population_residual]
    norm_num [AronowAudit.P018.Wave1.TailBSign.tb05_average,
      AronowAudit.P018.signPairKernel, AronowAudit.P018.signValue]

lemma signPair_scoreH :
    SAP.P018a.scoreH SAP.P018a.signPairKernel =
      (2 : ℝ) • (!![1,1;1,2] : SAP.P018a.Mat 2) := by
  change AronowAudit.P018.scoreH K = _
  exact signPair_scoreH_donor

lemma signPair_gamma :
    SAP.P018a.projectionGamma SAP.P018a.signPairKernel = !![1,1;1,1] :=
  AronowAudit.P018.Wave1.TailBSign.tb05_projection_gamma

lemma three_unit_integral
    (f : ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool) → ℝ) :
    (∫ z, f z ∂(K.μ.prod K.μ).prod K.μ) =
      AronowAudit.P018.Wave1.TailBSign.tb05_average (fun u =>
        AronowAudit.P018.Wave1.TailBSign.tb05_average (fun v =>
          AronowAudit.P018.Wave1.TailBSign.tb05_average (fun w => f ((u,v),w)))) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  rw [integral_prod (μ := K.μ.prod K.μ) (ν := K.μ) f
    (AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
  rw [AronowAudit.P018.Wave1.TailBSign.tb05_units_integral]
  simp_rw [AronowAudit.P018.Wave1.TailBSign.tb05_unit_integral]

lemma design_at_members {N : ℕ} (d : AronowAudit.P018.Dyad N)
    (i j : Fin N) (_hij : i ≠ j) (hd : AronowAudit.P018.members d = {i,j})
    (ω : Fin N → Bool × Bool) :
    AronowAudit.P018.design K ω d = K.X (ω i) (ω j) := by
  have he : ({AronowAudit.P018.firstUnit d, AronowAudit.P018.secondUnit d} : Set (Fin N)) = {i,j} := by
    have hh := (AronowAudit.P018.Wave1.WeightedConsistency.members_eq_endpoints d).symm.trans hd
    have hh' := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) hh
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hh'
  rcases Set.pair_eq_pair_iff.mp he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · change K.X (ω (AronowAudit.P018.firstUnit d)) (ω (AronowAudit.P018.secondUnit d)) = _
    rw [h₁,h₂]
  · change K.X (ω (AronowAudit.P018.firstUnit d)) (ω (AronowAudit.P018.secondUnit d)) = _
    rw [h₁,h₂]
    exact (hK.2.2.2.1 (ω j) (ω i)).1

lemma design_overlap_moment {N : ℕ} (d f : AronowAudit.P018.Dyad N)
    (hne : d ≠ f) (hov : AronowAudit.P018.overlap d f) :
    AronowAudit.P018.meanMat (AronowAudit.P018.unitSampleLaw K N)
      (fun ω => AronowAudit.P018.outer (AronowAudit.P018.design K ω d)
        (AronowAudit.P018.design K ω f)) = !![1,1;1,1] := by
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨i, hi⟩ := hov
  have hid : i ∈ AronowAudit.P018.members d := Finset.mem_inter.mp hi |>.1
  have hif : i ∈ AronowAudit.P018.members f := Finset.mem_inter.mp hi |>.2
  let j := AronowAudit.P018.Wave1.vc3_other i d
  let l := AronowAudit.P018.Wave1.vc3_other i f
  have hij : i ≠ j := AronowAudit.P018.Wave1.vc3_other_ne i d hid
  have hil : i ≠ l := AronowAudit.P018.Wave1.vc3_other_ne i f hif
  have hjl : j ≠ l := by
    intro h
    apply hne
    apply Subtype.ext
    change AronowAudit.P018.members d = AronowAudit.P018.members f
    rw [AronowAudit.P018.Wave1.vc3_members_other i d hid,
      AronowAudit.P018.Wave1.vc3_members_other i f hif]
    exact congrArg (fun x : Fin N => ({i,x} : Finset (Fin N))) h
  have hd := AronowAudit.P018.Wave1.vc3_members_other i d hid
  have hf := AronowAudit.P018.Wave1.vc3_members_other i f hif
  have hm := AronowAudit.P018.Wave1.vc3_triple_preserving K.μ i j l hij hil hjl
  have hDesign (a b : Fin 2) (ω : Fin N → Bool × Bool) :
      AronowAudit.P018.outer (AronowAudit.P018.design K ω d)
          (AronowAudit.P018.design K ω f) a b =
        K.X (ω i) (ω j) a * K.X (ω i) (ω l) b := by
    rw [design_at_members d i j hij hd ω, design_at_members f i l hil hf ω]
    rfl
  have hInt (a b : Fin 2) :
      (∫ ω, K.X (ω i) (ω j) a * K.X (ω i) (ω l) b
        ∂ AronowAudit.P018.unitSampleLaw K N) =
        ∫ z : ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool),
          K.X z.1.1 z.1.2 a * K.X z.1.1 z.2 b ∂ (K.μ.prod K.μ).prod K.μ := by
    calc
      _ = ∫ ω, (fun z : ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool) =>
          K.X z.1.1 z.1.2 a * K.X z.1.1 z.2 b) ((ω i, ω j), ω l)
          ∂ AronowAudit.P018.unitSampleLaw K N := by rfl
      _ = ∫ z : ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool),
          K.X z.1.1 z.1.2 a * K.X z.1.1 z.2 b ∂ (K.μ.prod K.μ).prod K.μ := by
        rw [← hm.map_eq]
        exact (integral_map hm.aemeasurable
          (measurable_of_countable (fun z : ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool) =>
            K.X z.1.1 z.1.2 a * K.X z.1.1 z.2 b)).aestronglyMeasurable).symm
  have hEval (a b : Fin 2) :
      (∫ z : ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool),
        K.X z.1.1 z.1.2 a * K.X z.1.1 z.2 b ∂ (K.μ.prod K.μ).prod K.μ) = 1 := by
    fin_cases a <;> fin_cases b
    all_goals rw [three_unit_integral]
    all_goals norm_num [AronowAudit.P018.Wave1.TailBSign.tb05_average,
      AronowAudit.P018.signPairKernel, AronowAudit.P018.signValue]
  have hEntry (a b : Fin 2) :
      AronowAudit.P018.meanMat (AronowAudit.P018.unitSampleLaw K N)
        (fun ω => AronowAudit.P018.outer (AronowAudit.P018.design K ω d)
          (AronowAudit.P018.design K ω f)) a b = 1 := by
    change (∫ ω, AronowAudit.P018.outer (AronowAudit.P018.design K ω d)
      (AronowAudit.P018.design K ω f) a b ∂ AronowAudit.P018.unitSampleLaw K N) = 1
    calc
      _ = ∫ ω, K.X (ω i) (ω j) a * K.X (ω i) (ω l) b
          ∂ AronowAudit.P018.unitSampleLaw K N := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (hDesign a b)
      _ = _ := hInt a b
      _ = 1 := hEval a b
  ext a b
  rw [hEntry a b]
  fin_cases a <;> fin_cases b <;> norm_num [AronowAudit.P018.signPairKernel]

end SAP.P018a.WH.W2.P.T7_L2

theorem SAP.P018a.WH.W2.T7_L2_proof : SAP.P018a.WH.W2.T7_L2 := by
  change SAP.P018a.T7Moments
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hm := AronowAudit.P018.Wave1.vc3_population_mean
      SAP.P018a.WH.W2.P.T7_L2.K SAP.P018a.WH.W2.P.T7_L2.hK
    change AronowAudit.P018.meanVec
      (SAP.P018a.WH.W2.P.T7_L2.K.μ.prod SAP.P018a.WH.W2.P.T7_L2.K.μ)
      (fun uv => AronowAudit.P018.score
        (SAP.P018a.WH.W2.P.T7_L2.K.X uv.1 uv.2)
        (SAP.P018a.WH.W2.P.T7_L2.K.Y uv.1 uv.2)) = 0
    simpa [AronowAudit.P018.populationScore,
      SAP.P018a.WH.W2.P.T7_L2.residual_eq] using hm
  · exact AronowAudit.P018.Wave1.TailBSign.tb05_population_residual
  · intro N hN d f hne hov
    refine ⟨?_, ?_, ?_⟩
    · have hsame := AronowAudit.P018.Wave1.vc3_same_moment
        SAP.P018a.WH.W2.P.T7_L2.K SAP.P018a.WH.W2.P.T7_L2.hK d
      change SAP.P018a.meanMat (SAP.P018a.unitSampleLaw SAP.P018a.signPairKernel N)
        (fun ω => SAP.P018a.outer
          (SAP.P018a.score (SAP.P018a.design SAP.P018a.signPairKernel ω d)
            (SAP.P018a.epsilon SAP.P018a.signPairKernel ω d))
          (SAP.P018a.score (SAP.P018a.design SAP.P018a.signPairKernel ω d)
            (SAP.P018a.epsilon SAP.P018a.signPairKernel ω d))) =
          SAP.P018a.scoreH SAP.P018a.signPairKernel at hsame
      have h00 := congrFun (congrFun hsame 0) 0
      rw [SAP.P018a.WH.W2.P.T7_L2.signPair_scoreH] at h00
      simpa [SAP.P018a.meanMat, SAP.P018a.outer, SAP.P018a.score,
        SAP.P018a.design, SAP.P018a.signPairKernel, pow_two] using h00
    · have hovmom := AronowAudit.P018.Wave1.vc3_overlap_moment
        SAP.P018a.WH.W2.P.T7_L2.K SAP.P018a.WH.W2.P.T7_L2.hK d f hne hov
      change SAP.P018a.meanMat (SAP.P018a.unitSampleLaw SAP.P018a.signPairKernel N)
        (fun ω => SAP.P018a.outer
          (SAP.P018a.score (SAP.P018a.design SAP.P018a.signPairKernel ω d)
            (SAP.P018a.epsilon SAP.P018a.signPairKernel ω d))
          (SAP.P018a.score (SAP.P018a.design SAP.P018a.signPairKernel ω f)
            (SAP.P018a.epsilon SAP.P018a.signPairKernel ω f))) =
          SAP.P018a.projectionGamma SAP.P018a.signPairKernel at hovmom
      have h00 := congrFun (congrFun hovmom 0) 0
      rw [SAP.P018a.WH.W2.P.T7_L2.signPair_gamma] at h00
      simpa [SAP.P018a.meanMat, SAP.P018a.outer, SAP.P018a.score,
        SAP.P018a.design, SAP.P018a.signPairKernel] using h00
    · exact SAP.P018a.WH.W2.P.T7_L2.design_overlap_moment d f hne hov
  · exact SAP.P018a.WH.W2.P.T7_L2.signPair_scoreH
  · intro N hN
    have hs := AronowAudit.P018.Wave1.vc3_sparse_variance
      (N := N) SAP.P018a.WH.W2.P.T7_L2.K SAP.P018a.WH.W2.P.T7_L2.hK
    have hc := AronowAudit.P018.Wave1.vc3_closed_covariance
      (N := N) SAP.P018a.WH.W2.P.T7_L2.K SAP.P018a.WH.W2.P.T7_L2.hK
    calc
      _ = (SAP.P018a.Dreal N) • SAP.P018a.scoreH SAP.P018a.signPairKernel +
          ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) •
            SAP.P018a.projectionGamma SAP.P018a.signPairKernel := by
        change AronowAudit.P018.varMat (AronowAudit.P018.unitSampleLaw
          SAP.P018a.WH.W2.P.T7_L2.K N) (AronowAudit.P018.scoreSum
          SAP.P018a.WH.W2.P.T7_L2.K) =
          (AronowAudit.P018.Dreal N) • AronowAudit.P018.scoreH
            SAP.P018a.WH.W2.P.T7_L2.K +
          ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) •
            AronowAudit.P018.projectionGamma SAP.P018a.WH.W2.P.T7_L2.K
        rw [hs, hc]
      _ = (2 * SAP.P018a.Dreal N) • (!![1,1;1,2] : SAP.P018a.Mat 2) +
          ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) •
            (!![1,1;1,1] : SAP.P018a.Mat 2) := by
        rw [SAP.P018a.WH.W2.P.T7_L2.signPair_scoreH,
          SAP.P018a.WH.W2.P.T7_L2.signPair_gamma]
        rw [smul_smul]
        congr 1
        ring_nf
  · intro N hN d f hne hov
    have hovmom := AronowAudit.P018.Wave1.vc3_overlap_moment
      SAP.P018a.WH.W2.P.T7_L2.K SAP.P018a.WH.W2.P.T7_L2.hK d f hne hov
    change SAP.P018a.meanMat (SAP.P018a.unitSampleLaw SAP.P018a.signPairKernel N)
      (fun ω => SAP.P018a.outer
        (SAP.P018a.score (SAP.P018a.design SAP.P018a.signPairKernel ω d)
          (SAP.P018a.epsilon SAP.P018a.signPairKernel ω d))
        (SAP.P018a.score (SAP.P018a.design SAP.P018a.signPairKernel ω f)
          (SAP.P018a.epsilon SAP.P018a.signPairKernel ω f))) =
        SAP.P018a.projectionGamma SAP.P018a.signPairKernel at hovmom
    rw [SAP.P018a.WH.W2.P.T7_L2.signPair_gamma] at hovmom
    exact hovmom
