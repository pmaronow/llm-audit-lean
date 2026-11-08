import SAP.P004b.Defs.WholeW3
import SAP.P004b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

/-- Count the atoms in every disk, including its center. Restrict the finite
Dirac sum and integrate the one nonzero atom. Generalize T27_atom_region,
T27_mass, T27_restrict and T27_circle; the number of atoms is positive. -/
def T27_L1 : Prop := WholeSparseDisks

/-- All-distance NED from the disk formula. When s>d, the only relevant coin
lies in the conditioning ball. For s≤d use conditional variance ≤1. Take
g=1 and psi(s)=1{s≤d}; it has compact support and any polynomial decay.
Use FiniteConditioning.conditionOn_of_depends and conditionOn's contraction.
The explicit L2 bound records the proposed coefficient, not just its existence. -/
def T27_L2 : Prop := WholeSparseDisks → WholeSparseNED

/-- Exact linearized variance. T27_linear_identity expresses it in the first
coin and the treatment count. Expand finite covariances, use T27_count_moments
and T27_selected_update to obtain Cov(Z1,N1)=1/4, and simplify. -/
def T27_L3 : Prop := ∀ N : ℕ, 3 ≤ N →
  variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (wholeSparseR N)) =
    25*((N : ℝ)-1)/(16*(N : ℝ)^3)

/-- Conditional count law and exact moments. Split off the first coordinate
with splitAssignment and join_design_weight. Subsets of k matching remaining
coins are counted by Finset.card_powersetCard. The endpoint events q=1,N
give 4/2^N; sum independent fair indicators for the two conditional moments. -/
def T27_L4 : Prop := WholeSparseCountLaw

/-- Conditional law of large numbers for q/N. Apply the finite-design
Chebyshev inequality to the moments in T27_L4; the mean differs from 1/2
by 1/(2N). Work eventually at N≥3; the extension at N=0 is irrelevant. -/
def T27_L5 : Prop := WholeSparseCountLaw → WholeSparseCountLimit

/-- Exact valid-interval formulas on 2≤q≤N-1. Substitute T27_armMean,
T27_spike_variance and T27_ame. Both arms are positive; q-1>0 makes the
variance positive. Real.sqrt_div, Real.sqrt_mul and field algebra give T.
This is a finite calculation, without a limiting probability argument. -/
def T27_L6 : Prop := WholeSparseFinite

/-- Conditional continuous mapping for the statistic. Use q/N→1/2,
1/N→0 and the formulas in T27_L6. Exclude q=1,N using the endpoint
probability in T27_L4, whose conditional probability is at most twice its
unconditional probability. The limits are 5/8 and -5/2. -/
def T27_L7 : Prop := WholeSparseCountLaw → WholeSparseCountLimit →
  WholeSparseFinite → WholeSparseStatisticLimit

/-- The actual 97.5-percent Gaussian quantile lies strictly between 5/8
and 5/2. Bound Phi(5/8) using the maximum Gaussian density. For 5/2 use
the Mills bound exp(-x^2/2)/(x sqrt(2 pi)), with exp(25/8)>8 and sqrt(2 pi)>2.
Invert the strict CDF inequalities using DesignLimits.nf_proof. -/
def T27_L8 : Prop := (5/8 : ℝ) < normalQuantile (39/40) ∧ normalQuantile (39/40) < 5/2

/-- Conditional convergence transfers to unconditional coverage for any
fixed symmetric critical value strictly between the two limiting magnitudes.
Use the first-coin mass 1/2 and the vanishing exceptional probability; retain
validity as a conjunction. Each branch stays away from the interval boundary. -/
def T27_L9 : Prop := WholeSparseCountLaw → WholeSparseFinite →
  WholeSparseStatisticLimit → ∀ a : ℝ, 5/8 < a → a < 5/2 →
  Tendsto (fun N => prob (fun _ => 1/2)
    (wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N) (-a) a)) atTop (nhds (1/2))

/-- Finite V1 and V2 bounds and E[V2]. The kernel is diagonal. For V1
the residual sum is y^2(1-1/q), so V1≤4/N² even on empty-arm extensions.
For V2 substitute population centers 1/N and 1/(4N), expand the square,
and use first and second Bernoulli moments; its mean is 17(N-1)/(8N³).
The independent V1 identity can be proved by the route of T28_L1. -/
def T27_L10 : Prop := WholeSparseVarianceBounds

/-- Rates from the finite bounds. On SparseGood, q is between 2N/5 and
3N/5, so T27_spike_variance bounds HAC by a constant times N^-2.
T27_bad_limit removes its complement. The deterministic V1/V2 bounds
and that probability bound imply all three scaled errors vanish.
For the deterministic supremum use the nonempty finite assignment cube. -/
def T27_L11 : Prop := WholeSparseVarianceBounds → WholeSparseFinite → WholeSparseRates

/-- The independent V1 expansion equals the random row sum, including finite
empty-arm extensions. Expand the two inverse-propensity factors, restrict
using TailB_Ned_kernel_support, split diagonal/off-diagonal terms with
HACCompletion.split_diagonal, and combine cross terms by symmetry.
This is the missing identity, not the definitional second conjunct of hac_expansion. -/
def T28_L1 : Prop := ∀ {N : ℕ} (p : ℝ) (R : CircleTable N)
  (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b : ℝ),
  (0 < p ∧ p < 1) → 0 < b → KernelConditions K →
  (∀ i j, D i j = D j i) → (∀ i, D i i = 0) →
  wholeV1Five p R D K b = nedV1 p R D K b

/-- Valid Wald coverage from a CLT, a bias liminf and a raw o_p error.
Copy the shortfall argument in TailB_Ned_liminf_wald, retaining positivity
from GP0042B2b_capped_pd_one_sided_wald. Intersect with nonempty arms
using GP0042B2b_capped_pd_prob_difference. Quantile symmetry converts
the absolute-value event into the two-sided event. No independence is needed. -/
def T28_L2 : Prop := ∀ (p : ℝ) (R : ∀ N, CircleTable N)
  (Q : ∀ N, Matrix (Fin N) (Fin N) ℝ) (V E : ℕ → ℝ),
  (0 < p ∧ p < 1) → Nondegenerate V →
  NormalLimit (fun _ _ => p) (fun N z =>
    (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt (V N)) →
  LiminfAtLeast (fun N => (N : ℝ)*(E N-V N)) 0 →
  InProb (fun _ _ => p) (fun N z => (N : ℝ)*
    (kernelVariance z (residual (R N) z) (Q N)-E N)) →
  Tendsto (fun N => prob (fun _ => p) (fun z : Assignment N => ¬ ValidArms z)) atTop (nhds 0) →
  ∀ α : ℝ, 0 < α → α < 1 →
  Conservative (fun N => prob (fun _ => p)
    (wholeCovered p (R N) (Q N) (normalQuantile (α/2)) (normalQuantile (1-α/2)))) α

/-- Empty-arm law for positive sizes, and its vanishing probability. The
two events are the all-treated and all-control assignments, disjoint for N>0.
Their product weights are p^N and (1-p)^N. Apply geometric convergence.
The exact identity is deliberately restricted to N>0, since at N=0 they coincide. -/
def T28_L3 : Prop := ∀ p : ℝ, (0 < p ∧ p < 1) →
  (∀ N : ℕ, 0 < N → prob (fun _ => p) (fun z : Assignment N => ¬ ValidArms z) =
    p^N+(1-p)^N) ∧
  Tendsto (fun N => prob (fun _ => p) (fun z : Assignment N => ¬ ValidArms z)) atTop (nhds 0)

/-- Nonempty complete-randomization supports. Choose a subset of the N-1
remaining indices of size n1-a, using Finset.exists_subset_card_eq and
Fintype.card_subtype_compl. Its Bool indicator belongs to remainderSupport;
join_treated_count puts its extension in the conditioning event. -/
def T30_L1 : Prop := ∀ N n1 : ℕ, 1 ≤ n1 → n1 ≤ N-1 → ∀ i : Fin N, ∀ a : Bool,
  0 < ((completeSupport N n1).filter (fun z => z i = a)).card ∧
  0 < (remainderSupport n1 i a).card

/-- Exact count/HT covariance. Expand HT and the centered treated fraction.
The diagonal terms are (1-p)mu_i1+p mu_i0. For i≠j the term is
p(E[R_i|Zi=1,Zj=1]-E[R_i|Zi=0,Zj=1]-tau_i). Sum and divide by N².
Use expect_sum, selected_update, pair_marginal_forced and independent
Bernoulli count moments (T34_count_moments works at general p). -/
def T30_L2 : Prop := WholeCountCovariance

/-- Complete the variance square from the finite moments. First show
A(c1,c0)=HT-(c1/p+c0/(1-p))*(N1/N-p). Expand its variance, substitute
T30_L2, and complete the square. Nonnegativity of C follows by choosing
c1=p*tStar,c0=0. Substitute population centers to obtain the exact
Delta² remainder, its epsilon bound, and equality at Delta=0. -/
def T30_L3 : Prop := WholeCountCovariance → WholeVarianceSquare

theorem T27_assembly (h1 : T27_L1) (h2 : T27_L2)
    (h3 : T27_L3) (h4 : T27_L4) (h5 : T27_L5) (h6 : T27_L6)
    (h7 : T27_L7) (h8 : T27_L8) (h9 : T27_L9) (h10 : T27_L10)
    (h11 : T27_L11) : T27WholeStatement := by
  have hHom (N : ℕ) (hN : 3 ≤ N) :
      kernelHomophily sparsePopulation (1/2) 1 uniformKernel sparseBandwidth N =
        9*((N : ℝ)-1)/(16*(N : ℝ)^2) := by

    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hcircle : circleAverage (sparsePopulation N) 1 = sparseTable N :=
      AronowAudit.P004.Wave1.T27_circle N
    have heffect (i : Fin N) : nodeEffect (fun _ => 1/2) (sparseTable N) i =
        if i.val = 0 then 3/4 else 0 := AronowAudit.P004.Wave1.T27_effect i
    have hame : ame (fun _ => 1/2) (sparseTable N) = (3/4 : ℝ)/N :=
      AronowAudit.P004.Wave1.T27_ame (by omega)
    have hkernel (i j : Fin N) :
        uniformKernel (nodeSeparation (sparsePopulation N) i j/sparseBandwidth N) =
          if i=j then 1 else 0 := AronowAudit.P004.Wave1.T27_kernel_eq (by omega) i j
    unfold kernelHomophily
    simp only [hcircle,heffect,hame,hkernel]
    have hpoint (i : Fin N) : (∑ j : Fin N, (if i=j then (1 : ℝ) else 0)*
        ((if i.val=0 then 3/4 else 0)-(3/4 : ℝ)/N)*
        ((if j.val=0 then 3/4 else 0)-(3/4 : ℝ)/N)) =
          ((if i.val=0 then 3/4 else 0)-(3/4 : ℝ)/N)^2 := by
      simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,pow_two]
    simp_rw [hpoint]
    have hsquare (i : Fin N) : ((if i.val=0 then (3/4 : ℝ) else 0)-(3/4 : ℝ)/N)^2 =
        (if i.val=0 then (3/4 : ℝ)^2-2*(3/4 : ℝ)*((3/4 : ℝ)/N) else 0)+((3/4 : ℝ)/N)^2 := by
      split_ifs <;> ring
    simp_rw [hsquare]
    have hspike (c : ℝ) : (∑ i : Fin N, if i.val=0 then c else 0) = c :=
      AronowAudit.P004.Wave1.T27_sum_zero (by omega) c
    rw [Finset.sum_add_distrib,hspike]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    ring
  have hstat := h7 h4 (h5 h4) h6
  have hcov := h9 h4 h6 hstat
  have hold : T27Statement := by
    obtain ⟨a,b,c,d,e,f,g,h,i,_,j,k,l⟩ :=
      AronowAudit.P004.Wave1.ned_coverage_counterexample_proof
    refine ⟨a,b,c,d,e,f,g,h,i,AronowAudit.P004.Wave1.T27_bad_limit,?_,
      (fun N hN => AronowAudit.P004.Wave1.T27_first_probability hN),j,k,l⟩
    intro N hN z hg
    dsimp only
    have hv := Bridge.sparse_validInterval hN z hg
    refine ⟨hv, ?_⟩
    have he := AronowAudit.P004.Wave1.T27_good_coverage hN z hg
    change (ValidInterval _ _ z → _) ↔ _
    rw [show (ValidInterval _ _ z → _) ↔ _ from imp_iff_right hv]
    rw [show circleAverage (sparsePopulation N) 1 = sparseTable N from
      AronowAudit.P004.Wave1.T27_circle N]
    exact he
  have hmetric : MetricNodeDistances sparsePopulation := by
    intro N
    have he (i j : Fin N) : nodeSeparation (sparsePopulation N) i j =
        dist (planePoint (((i : ℝ)+1)*N^2) 0) (planePoint (((j : ℝ)+1)*N^2) 0) := by
      simp [nodeSeparation, sparsePopulation]
    refine ⟨fun i j => by rw [he]; exact dist_nonneg, ?_,
      fun i j => by rw [he, he]; exact dist_comm _ _,
      fun i j k => by rw [he, he, he]; exact dist_triangle _ _ _⟩
    intro i j
    rw [he, dist_eq_zero]
    refine ⟨?_, ?_⟩
    · intro hij
      exact AronowAudit.P004.Wave1.T27_point_injective
        (lt_of_le_of_lt (Nat.zero_le _) i.isLt) hij
    · rintro rfl
      rfl
  have hconstants : ∀ N : ℕ, 3 ≤ N →
      (∀ x z, |(sparsePopulation N).outcome x z| < 2) ∧
      (∀ i s, 0 ≤ s → ((ball (nodeSeparation (sparsePopulation N)) i s).card : ℝ) ≤ 3*(1+s^2)) ∧
      (∀ i, nodeEffect (fun _ => 1/2) (wholeSparseR N) i = if i.val = 0 then 3/4 else 0) ∧
      ame (fun _ => 1/2) (wholeSparseR N) = 3/(4*(N : ℝ)) ∧
      (∀ i j, wholeSparseQmat N i j = if i = j then 1 else 0) ∧
      sparseBandwidth N / (N : ℝ)^(1/6 : ℝ) ≤ (N : ℝ)^(-1/12 : ℝ) := by
    intro N hN
    refine ⟨AronowAudit.P004.Wave1.T27_outcome_bound (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro i s hs
      by_cases hsmall : s < (N : ℝ)^2
      · rw [show ball (nodeSeparation (sparsePopulation N)) i s = {i} from
          AronowAudit.P004.Wave1.T27_ball_small i s hs hsmall]
        simp only [Finset.card_singleton, Nat.cast_one]
        nlinarith [sq_nonneg s]
      · have hc : ((ball (nodeSeparation (sparsePopulation N)) i s).card : ℝ) ≤ N := by
          have hc := Finset.card_le_card (Finset.subset_univ
            (ball (nodeSeparation (sparsePopulation N)) i s))
          simpa using (Nat.cast_le (α := ℝ)).mpr hc
        have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
        have hlarge : (N : ℝ)^2 ≤ s := le_of_not_gt hsmall
        nlinarith [sq_nonneg (s-1)]
    · intro i
      change nodeEffect (fun _ => 1/2) (circleAverage (sparsePopulation N) 1) i = _
      rw [show circleAverage (sparsePopulation N) 1 = sparseTable N from AronowAudit.P004.Wave1.T27_circle N]
      exact AronowAudit.P004.Wave1.T27_effect i
    · rw [wholeSparseR, show circleAverage (sparsePopulation N) 1 = sparseTable N from
        AronowAudit.P004.Wave1.T27_circle N]
      have ha : ame (fun _ => 1/2) (sparseTable N) = (3/4 : ℝ)/N :=
        AronowAudit.P004.Wave1.T27_ame (show 0 < N by omega)
      rw [ha]
      ring
    · exact AronowAudit.P004.Wave1.T27_kernel_eq (by omega)
    · have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      calc
        sparseBandwidth N / (N : ℝ)^(1/6 : ℝ) ≤
            (N : ℝ)^(1/12 : ℝ) / (N : ℝ)^(1/6 : ℝ) :=
          div_le_div_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg hn.le _))
            (Real.rpow_nonneg hn.le _)
        _ = (N : ℝ)^(-1/12 : ℝ) := by
          rw [← Real.rpow_sub hn]
          norm_num
  have hsym : normalQuantile (1/40) = -normalQuantile (39/40) := by
    obtain ⟨_, hstrict, _, hneg, hquant, _, _⟩ := AronowAudit.P004.Wave1.DesignLimits.nf_proof
    have hm : StrictMono normalCDF := hstrict
    have hn : ∀ x : ℝ, normalCDF (-x) = 1-normalCDF x := hneg
    have hq : ∀ a : ℝ, 0 < a → a < 1 → normalCDF (normalQuantile a) = a := hquant
    apply hm.injective
    rw [hq _ (by norm_num) (by norm_num), hn,
      hq _ (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hold,h1,h2 h1,hmetric,hconstants,
    (fun N hN => ⟨hHom N hN,h3 N hN⟩),h4,h5 h4,h6,hstat,h8.1,h8.2,
    hcov 2 (by norm_num) (by norm_num),?_,by norm_num,h10,h11 h10 h6,?_⟩
  · rw [hsym]
    exact hcov _ h8.1 h8.2
  · intro N hN
    rw [(h10 N hN).2.2, h3 N hN]
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have he : (N : ℝ)*(17*((N : ℝ)-1)/(8*(N : ℝ)^3)-
        25*((N : ℝ)-1)/(16*(N : ℝ)^3)) = 9*((N : ℝ)-1)/(16*(N : ℝ)^2) := by
      field_simp
      ring
    rw [he]
    have hn1 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    exact ⟨rfl, div_nonneg (by nlinarith) (by positivity)⟩

theorem T28_assembly (h1 : T28_L1) (h2 : T28_L2) (h3 : T28_L3) : T28WholeStatement := by
  intro Space _ _ P p d K bw hp hd hb hWD hNED hmetric hspacing hK hbpos hbdiv hbrate hhom
  let R := circleSequence P d
  let D := fun N => nodeSeparation (P N)
  let W := fun N z => kernelVariance z (residual (R N) z) (distanceKernel (D N) K (bw N))
  let V1 := fun N => nedV1 p (R N) (D N) K (bw N)
  let V2 := fun N => nedV2 p (R N) (D N) K (bw N)
  let E := fun N => expect (fun _ => p) (V2 N)
  obtain ⟨a,b,c,e,_⟩ := AronowAudit.P004.Wave1.TailB_ned_hac_correction
    (Bridge.sequence P) p d K bw hp hd hb hWD hNED hmetric hspacing hK hbpos hbdiv hbrate hhom
  have aS : InProb (fun _ _ => p) (fun N z => N*(W N z-V1 N z)) := a
  have bS : InProb (fun _ _ => p) (fun N z => N*(V1 N z-V2 N z)) := b
  have cS : InProb (fun _ _ => p) (fun N z => N*(V2 N z-E N)) := c
  have eS : LiminfAtLeast (fun N => (N : ℝ)*(E N-
      variance (fun _ => p) (linearHajek (fun _ => p) (R N)))) 0 := e
  have heq (N : ℕ) : wholeV1Five p (R N) (D N) K (bw N) = V1 N :=
    h1 p _ _ K _ hp (hbpos N) hK (hmetric N).2.2.1
      (fun i => ((hmetric N).2.1 i i).mpr rfl)
  change (∀ N z, ValidArms z → wholeV1Five p (R N) (D N) K (bw N) z = V1 N z) ∧ _
  refine ⟨(fun N z _ => congrFun (heq N) z),(fun _ _ => rfl),?_,?_,cS,eS,?_⟩
  · change InProb (fun _ _ => p) (fun N z => N*(W N z-wholeV1Five p (R N) (D N) K (bw N) z))
    simpa only [heq] using aS
  · change InProb (fun _ _ => p) (fun N z => N*(wholeV1Five p (R N) (D N) K (bw N) z-V2 N z))
    simpa only [heq] using bS
  · intro hv α hα0 hα1
    have hclt : NormalLimit (fun _ _ => p) (fun N z =>
        (hajek (R N) z-ame (fun _ => p) (R N))/
          Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (R N)))) :=
      (AronowAudit.P004.Wave1.ned_headline_under_uniform_spacing
        (Bridge.sequence P) p d hp hd hb (Eventually.of_forall hWD) hNED hmetric hspacing).2.2.2 hv
    have hab : InProb (fun _ _ => p) (fun N z => N*(W N z-V1 N z)+N*(V1 N z-V2 N z)) :=
      (AronowAudit.P004.Wave1.DesignLimits.dl4_proof _ (fun _ _ => hp)).1 _ _ aS bS
    have habc : InProb (fun _ _ => p) (fun N z =>
        (N*(W N z-V1 N z)+N*(V1 N z-V2 N z))+N*(V2 N z-E N)) :=
      (AronowAudit.P004.Wave1.DesignLimits.dl4_proof _ (fun _ _ => hp)).1 _ _ hab cS
    have herr : InProb (fun _ _ => p) (fun N z => (N : ℝ)*(W N z-E N)) := by
      have he : (fun (N : ℕ) z => (N : ℝ)*(W N z-E N)) =
          (fun N z => (N*(W N z-V1 N z)+N*(V1 N z-V2 N z))+N*(V2 N z-E N)) := by
        funext N z
        ring
      rw [he]
      exact habc
    have hfinite : ∀ x : ℝ, 0 < x → x < 1 → FiniteQuantile x := by
      intro x hx0 hx1
      obtain ⟨_, hstrict, _, _, hquant, _, _⟩ := AronowAudit.P004.Wave1.DesignLimits.nf_proof
      have hq : normalCDF (normalQuantile x) = x := hquant x hx0 hx1
      have hm : StrictMono normalCDF := hstrict
      refine ⟨⟨normalQuantile x, hq.ge⟩, ⟨normalQuantile x, ?_⟩⟩
      intro y hy
      exact hm.le_iff_le.mp (hq.le.trans hy)
    exact ⟨hfinite _ (by linarith) (by linarith),hfinite _ (by linarith) (by linarith),
      h2 p R _ _ E hp hv hclt eS herr (h3 p hp).2 α hα0 hα1⟩

theorem T30_assembly (h1 : T30_L1) (h2 : T30_L2) (h3 : T30_L3) : T30WholeStatement := by
  refine ⟨?_,?_,?_,h3 h2⟩
  · intro N n1 hlo hhi i
    have hs : 0 < (completeSupport N n1).card :=
      lt_of_lt_of_le (h1 N n1 hlo hhi i false).1 (Finset.card_le_card (Finset.filter_subset _ _))
    refine ⟨hs,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro u hu hv
      simp only [remainderSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.false_eq_true, ite_false, ite_true, Nat.sub_zero] at hu hv
      omega
    · intro a
      have ha := h1 N n1 hlo hhi i a
      refine ⟨ha.1,ha.2,div_pos (by exact_mod_cast ha.1) (by exact_mod_cast hs),?_⟩
      exact AronowAudit.P004.complete_randomization_conditioning n1 hlo hhi i a
  · intro N p hp i
    have hcoin (a : Bool) : 0 < coin (p i) a := by cases a <;> simp [coin] <;> linarith [(hp i).1,(hp i).2]
    have hmass (a : Bool) : prob p (fun z => z i = a) = coin (p i) a := by
      have hm := AronowAudit.P004.ComponentCompletion.selected_update p hp (fun _ => (1 : ℝ)) i a
      simp only [prob]
      have hmS : expect p (fun z => if z i = a then 1 else 0) =
          coin (p i) a * expect p (fun _ : Assignment N => (1 : ℝ)) := hm
      have hc : expect p (fun _ : Assignment N => (1 : ℝ)) = 1 := AronowAudit.P004.expect_const p 1
      rw [hc,mul_one] at hmS
      convert hmS using 1
      congr 1
      funext z
      by_cases hz : z i = a <;> simp [hz]
    have hpoint (a : Bool) (u : {j : Fin N // j ≠ i} → Bool) :
        prob p (fun z => z i = a ∧ ∀ j : {j : Fin N // j ≠ i}, z j = u j) =
          coin (p i) a * ∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j) := by
      have he : (fun z : Assignment N => z i = a ∧ ∀ j : {j : Fin N // j ≠ i}, z j = u j) =
          fun z => z = AronowAudit.P004.joinAssignment i a u := by
        funext z
        apply propext
        constructor
        · rintro ⟨ha,hu⟩
          funext j
          by_cases hj : j = i
          · subst j; simpa [AronowAudit.P004.joinAssignment] using ha
          · simpa [AronowAudit.P004.joinAssignment,hj] using hu ⟨j,hj⟩
        · rintro rfl
          refine ⟨by simp [AronowAudit.P004.joinAssignment], ?_⟩
          intro j
          simp only [AronowAudit.P004.joinAssignment, dite_eq_right j.property]
      rw [he]
      simp only [prob,expect,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      exact AronowAudit.P004.join_design_weight p i a u
    have hlaw (a : Bool) (u : {j : Fin N // j ≠ i} → Bool) :
        prob p (fun z => z i = a ∧ ∀ j : {j : Fin N // j ≠ i}, z j = u j) /
          prob p (fun z => z i = a) = ∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j) := by
      rw [hpoint,hmass]
      exact mul_div_cancel_left₀ _ (hcoin a).ne'
    exact ⟨fun a => ⟨by rw [hmass]; exact hcoin a,hlaw a⟩,
      (fun u => (hlaw false u).trans (hlaw true u).symm),
      fun R a => AronowAudit.P004.marginal_is_marginalization p R i a hp⟩
  · intro N hN p hp R
    have hform : linearHajek (fun _ => p) R = linearFormula (fun _ => p) R :=
      funext (Bridge.linearFormula_eq _ _ hN)
    have hdiff : ∀ z, augmented (fun _ => p) R (fun _ _ => barMu (fun _ => p) R true) z -
        linearHajek (fun _ => p) R z =
        (barMu (fun _ => p) R true-barMu (fun _ => p) R false)*
          (armCount z false/(N*(1-p))-1) :=
      fun z => AronowAudit.P004.wrong_hajek_class_difference p R z hN hp
    refine ⟨hform,rfl,?_,hdiff,?_⟩
    · rw [← hform]; rfl
    · constructor
      · intro heq
        have hd := hdiff (fun _ => true)
        have he := congrFun heq (fun _ => true)
        rw [he,sub_self] at hd
        simp only [armCount,Bool.true_eq_false,ite_false,Finset.sum_const_zero,zero_div,zero_sub,mul_neg_one] at hd
        linarith
      · intro heq
        funext z
        have hd := hdiff z
        rw [heq,sub_self,zero_mul] at hd
        rw [heq]
        exact sub_eq_zero.mp hd

end
end SAP.P004b.WH.W3
