import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.DesignLimits.DL4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T1_L4

open MeasureTheory ProbabilityTheory Filter Set
open AronowAudit.P004
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000

theorem three_sqrt_tendsto_atTop :
    Tendsto (fun K : ℕ => Real.sqrt ((3*K : ℕ) : ℝ)) atTop atTop := by
  have hN : Tendsto (fun K : ℕ => ((3*K : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hK : ∀ᶠ K : ℕ in atTop, b/3 < (K : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_gt_atTop (b/3)
    filter_upwards [hK] with K hK
    have hcast : ((3*K : ℕ) : ℝ) = 3*(K : ℝ) := by norm_num
    rw [hcast]
    nlinarith
  exact Real.tendsto_sqrt_atTop.comp hN

theorem three_prob_pos (K : ℕ) (i : Fin (3*K)) :
    0 < w1ThreeP (3*K) i ∧ w1ThreeP (3*K) i < 1 := by
  have h := three_spatial.2.2.2.2.2.2.1 (3*K) i
  constructor <;> linarith [h.1, h.2]

theorem three_prob_pos_all (K : ℕ) :
    ∀ i : Fin (3*K), 0 < w1ThreeP (3*K) i ∧ w1ThreeP (3*K) i < 1 :=
  fun i => three_prob_pos K i

theorem prob_mono_events {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop)
    (hAB : ∀ z, A z → B z) : prob p A ≤ prob p B := by
  unfold prob
  apply AronowAudit.P004.expect_mono p hp
  intro z
  by_cases hz : A z
  · simp [hz, hAB z hz]
  · simp [hz]
    split_ifs <;> norm_num

/-- The root-scaled expansion error is negligible, since `sqrt(N)/N` tends to zero. -/
theorem scaled_expansion_small
    (θhat : ∀ N, Assignment N → Fin 2 → ℝ)
    (hExp : T1ExpansionStatement θhat) :
    W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => Real.sqrt (3*K : ℕ) *
        (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z)) := by
  intro ε hε
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [] with K
    exact lt_of_lt_of_le ha
      (AronowAudit.P004.Wave1.DesignLimits.prob_nonneg_finite _ (three_prob_pos_all K) _)
  · intro b hb
    obtain ⟨C,hC,hbound⟩ := hExp b hb
    have hlarge := three_sqrt_tendsto_atTop.eventually_gt_atTop (C/ε)
    filter_upwards [hbound,hlarge,eventually_gt_atTop (0 : ℕ)] with K hboundK hlargeK hK
    let N : ℝ := ((3*K : ℕ) : ℝ)
    let s : ℝ := Real.sqrt (3*K : ℕ)
    have hNpos : 0 < N := by dsimp [N]; positivity
    have hspos : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 (by positivity)
    have hsquare : s^2 = N := by
      dsimp [s,N]
      exact Real.sq_sqrt (by positivity)
    have hCb : C < ε*s := by
      have hlargeS : C/ε < s := by change C/ε < s at hlargeK; exact hlargeK
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hlargeS
    have hscale : C * |N⁻¹| * s ≤ ε := by
      have heq : C * |N⁻¹| * s = C/s := by
        rw [abs_of_pos (inv_pos.mpr hNpos)]
        rw [← hsquare]
        field_simp
      rw [heq]
      apply (div_le_iff₀ hspos).2
      nlinarith [hCb]
    have himp : ∀ z : Assignment (3*K),
        ε < |s * (w1ThreeIPW θhat (3*K) z -
          w1ThreeLinear w1ThreeA (3*K) z)| →
        C * |N⁻¹| < |w1ThreeIPW θhat (3*K) z -
          w1ThreeLinear w1ThreeA (3*K) z| := by
      intro z hz
      have hz' : ε < s * |w1ThreeIPW θhat (3*K) z -
          w1ThreeLinear w1ThreeA (3*K) z| := by
        simpa only [abs_mul, abs_of_pos hspos] using hz
      have hmul : C * |N⁻¹| * s < s *
          |w1ThreeIPW θhat (3*K) z -
            w1ThreeLinear w1ThreeA (3*K) z| := lt_of_le_of_lt hscale hz'
      exact lt_of_mul_lt_mul_left (by simpa only [mul_comm] using hmul) hspos.le
    have hprob := prob_mono_events (w1ThreeP (3*K)) (three_prob_pos_all K)
      (fun z => ε < |Real.sqrt (3*K : ℕ) *
        (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z)|)
      (fun z => C * |(((3*K : ℕ) : ℝ)⁻¹)| <
        |w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z|)
      (by
        intro z hz
        have hz' := himp z hz
        simpa [N] using hz')
    exact lt_of_le_of_lt hprob hboundK

theorem remainder_small
    (hMom : T1MomentStatement)
    (θhat : ∀ N, Assignment N → Fin 2 → ℝ)
    (hExp : T1ExpansionStatement θhat) :
    W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => Real.sqrt (3*K : ℕ) *
        (w1ThreeIPW θhat (3*K) z - w1ThreePrinted (3*K) z) -
          w1ThreeU K z) := by
  have hsmall := scaled_expansion_small θhat hExp
  intro ε hε
  have heq : (fun K => prob (w1ThreeP (3*K)) (fun z => ε <
      |Real.sqrt (3*K : ℕ) *
        (w1ThreeIPW θhat (3*K) z - w1ThreePrinted (3*K) z) -
          w1ThreeU K z|)) =ᶠ[atTop]
      (fun K => prob (w1ThreeP (3*K)) (fun z => ε <
        |Real.sqrt (3*K : ℕ) * (w1ThreeIPW θhat (3*K) z -
          w1ThreeLinear w1ThreeA (3*K) z)|)) := by
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hident := (hMom K hK).1
    have hprinted := (three_linear K hK).1
    have hevents : (fun z : Assignment (3*K) => ε <
        |Real.sqrt (3*K : ℕ) *
          (w1ThreeIPW θhat (3*K) z - w1ThreePrinted (3*K) z) -
            w1ThreeU K z|) =
        (fun z => ε < |Real.sqrt (3*K : ℕ) *
          (w1ThreeIPW θhat (3*K) z -
            w1ThreeLinear w1ThreeA (3*K) z)|) := by
      funext z
      apply propext
      have hval : Real.sqrt (3*K : ℕ) *
          (w1ThreeIPW θhat (3*K) z - w1ThreePrinted (3*K) z) - w1ThreeU K z =
          Real.sqrt (3*K : ℕ) *
            (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z) := by
        rw [hprinted z, ← hident z]
        ring
      rw [hval]
    rw [hevents]
  exact (tendsto_congr' heq).2 (hsmall ε hε)

theorem tail_excludes_zero_limit
    (hMom : T1MomentStatement) :
    ¬ W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => w1ThreeU K z) := by
  intro hU
  let δ : ℝ := Real.sqrt ((10369/750000 : ℝ)/2)
  let c : ℝ := 107516161/2205448981
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact Real.sqrt_pos.2 (by norm_num)
  have hδsq : δ^2 = (10369/750000 : ℝ)/2 := by
    dsimp [δ]
    rw [Real.sq_sqrt (by norm_num)]
  have hcpos : 0 < c := by norm_num [c]
  have hlim := hU δ hδpos
  have hsmall : ∀ᶠ K : ℕ in atTop,
      prob (w1ThreeP (3*K)) (fun z => δ < |w1ThreeU K z|) < c :=
    hlim.eventually (eventually_lt_nhds hcpos)
  have hfalse : ∀ᶠ K : ℕ in atTop, False := by
    filter_upwards [hsmall, eventually_gt_atTop 0] with K hsmallK hK
    have hm := hMom K hK
    have htail := hm.2.2.2.2
    have hcomp : prob (w1ThreeP (3*K))
        (fun z => (10369/750000 : ℝ)/2 < (w1ThreeU K z)^2) ≤
        prob (w1ThreeP (3*K)) (fun z => δ < |w1ThreeU K z|) := by
      apply prob_mono_events (w1ThreeP (3*K)) (three_prob_pos_all K)
      intro z hz
      have hsq : δ^2 < |w1ThreeU K z|^2 := by
        rw [hδsq]
        simpa only [sq_abs] using hz
      by_contra hnot
      have hle : |w1ThreeU K z| ≤ δ := le_of_not_gt hnot
      have hprod : 0 ≤ (δ-|w1ThreeU K z|)*(δ+|w1ThreeU K z|) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith [hprod, hsq]
    have hlower : c ≤ prob (w1ThreeP (3*K))
        (fun z => δ < |w1ThreeU K z|) := le_trans htail hcomp
    linarith
  rcases hfalse.exists with ⟨K,hK⟩
  exact hK

end
end SAP.P004a.WH.W1.P.T1_L4

open SAP.P004a.WH.W1 AronowAudit.P004 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal

/-- The order-`N⁻¹` fitted remainder is negligible at root-`N` scale, while the exact
coefficient difference retains a uniformly positive tail and therefore cannot tend to zero. -/
theorem SAP.P004a.WH.W1.T1_L4_proof : SAP.P004a.WH.W1.T1_L4 := by
  intro hMom θhat hExp
  have hsmall := SAP.P004a.WH.W1.P.T1_L4.remainder_small hMom θhat hExp
  have hUconv : ¬ W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => w1ThreeU K z) :=
    SAP.P004a.WH.W1.P.T1_L4.tail_excludes_zero_limit hMom
  refine ⟨hsmall, ?_⟩
  intro hprinted
  let R : ∀ K, Assignment (3*K) → ℝ := fun K z =>
    Real.sqrt (3*K : ℕ) * (w1ThreeIPW θhat (3*K) z - w1ThreePrinted (3*K) z) -
      w1ThreeU K z
  let T : ∀ K, Assignment (3*K) → ℝ := fun K z =>
    Real.sqrt (3*K : ℕ) * (w1ThreeIPW θhat (3*K) z - w1ThreePrinted (3*K) z)
  have hR : W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K)) R := by
    simpa only [R] using hsmall
  have hT : W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K)) T := by
    simpa only [T] using hprinted
  have hneg : W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => -R K z) := by
    intro ε hε
    have heq : (fun K => prob (w1ThreeP (3*K))
        (fun z => ε < |-R K z|)) =
        (fun K => prob (w1ThreeP (3*K)) (fun z => ε < |R K z|)) := by
      funext K
      congr 1
      funext z
      simp
    simpa only [heq] using hR ε hε
  have hadd : W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => T K z + -R K z) := by
    intro ε hε
    have hhalf : 0 < ε/2 := by positivity
    have hupper : Tendsto (fun K => prob (w1ThreeP (3*K))
        (fun z => ε/2 < |T K z|) + prob (w1ThreeP (3*K))
        (fun z => ε/2 < |-R K z|)) atTop (nhds 0) := by
      simpa only [zero_add] using (hT (ε/2) hhalf).add (hneg (ε/2) hhalf)
    have hbound : ∀ K, prob (w1ThreeP (3*K))
        (fun z => ε < |T K z + -R K z|) ≤
        prob (w1ThreeP (3*K)) (fun z => ε/2 < |T K z|) +
          prob (w1ThreeP (3*K)) (fun z => ε/2 < |-R K z|) := by
      intro K
      apply AronowAudit.P004.Wave1.DesignLimits.prob_le_add_of_imp_finite
        (w1ThreeP (3*K)) (SAP.P004a.WH.W1.P.T1_L4.three_prob_pos_all K)
      intro z hz
      by_cases ht : ε/2 < |T K z|
      · exact Or.inl ht
      · right
        by_contra hr
        have ht' : |T K z| ≤ ε/2 := le_of_not_gt ht
        have hr' : |-R K z| ≤ ε/2 := le_of_not_gt hr
        have habs : |T K z + -R K z| ≤ |T K z| + |-R K z| := abs_add_le _ _
        linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Filter.Eventually.of_forall (fun K =>
        AronowAudit.P004.Wave1.DesignLimits.prob_nonneg_finite _
          (SAP.P004a.WH.W1.P.T1_L4.three_prob_pos_all K) _))
      (Filter.Eventually.of_forall hbound)
  have heq : (fun K z => T K z + -R K z) =
      (fun K z => w1ThreeU K z) := by
    funext K z
    dsimp [T,R]
    ring
  have hU : W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => w1ThreeU K z) := heq ▸ hadd
  exact hUconv hU

