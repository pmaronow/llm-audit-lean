import SAP.P004b.Defs.WholeW2
import SAP.P004b.WH.W2.Models
import SAP.P004b.Bridge
import AronowAudit.P004.Wave1.Gap.GP0041B1
import AronowAudit.P004.Wave1.Gap.GLP0041B2
import AronowAudit.P004.Wave1.Gap.GP0041B2
import AronowAudit.P004.Wave1.Gap.GP0041B3
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.Wave1.Gap.TailBIpwThreeType
import AronowAudit.P004.Wave1.Gap.GLP0042B6
import AronowAudit.P004.P004_DependencyCompletion
import AronowAudit.P004.P004_SpatialCLTCompletion
import AronowAudit.P004.P004_VarianceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2

universe u
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- Exact vertical projection onto the source rectangle, uniformly in L.
Prove the lower bound from the second coordinate of every source point; the point
(x_1,2) is in the rectangle and attains it. Apply the infDist inequalities.
The remaining interval bounds follow from 0<=x_2<=1. About 80 lines. -/
def T16_L1 : Prop :=
  ∀ L : ℝ, 2 ≤ L → ∀ x ∈ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1,
    Metric.infDist x (rectangle 0 (L+1) 2 3) = 2-x 1 ∧
    1 ≤ Metric.infDist x (rectangle 0 (L+1) 2 3) ∧
    Metric.infDist x (rectangle 0 (L+1) 2 3) ≤ 2

/-- Exact horizontal rectangle separation. All cross distances are at least L-1 by
the first coordinate, and (1,0),(L,0) attain it. Use csInf_le/le_csInf on the
nonempty set of nonnegative distances. About 60 lines. -/
def T16_L2 : Prop :=
  ∀ L : ℝ, 2 ≤ L → planeSeparation (rectangle 0 1 0 1) (rectangle L (L+1) 0 1) = L-1

/-- Zero-radius integrals for every prescribed L (not the donor's selected L).
Closedness identifies each zero-distance region with its rectangle. Their masses
are 1,1,L+1; on the rectangles the outcomes are respectively z_C,z_C,0.
Use spacing_rectangle_volume and setIntegral_const/congr_fun. About 150 lines. -/
def T16_L3 : Prop :=
  ∀ L : ℝ, ∀ hL : 2 ≤ L,
    WellDefined (polygonRangeFamily L hL) 0 ∧
    ∀ z, circleAverage (polygonRangeFamily L hL) 0 0 z = bit (z 2) ∧
      circleAverage (polygonRangeFamily L hL) 0 1 z = bit (z 2) ∧
      circleAverage (polygonRangeFamily L hL) 0 2 z = 0

/-- The six atom-to-rectangle distances for the positive-radius example.
Use coordinate-wise closest points and Euclidean norm squared: the vertical gaps
are 1 and each cross gap has squared norm (19/2)^2+1=365/4.
All rectangles are nonempty and closed. About 180 lines. -/
def T16_L4 : Prop :=
  nodeDistance positiveRectangleWitness 0 (positiveAtom false) = 1 ∧
  nodeDistance positiveRectangleWitness 1 (positiveAtom true) = 1 ∧
  (∀ a, nodeDistance positiveRectangleWitness 2 (positiveAtom a) = 1) ∧
  (nodeDistance positiveRectangleWitness 0 (positiveAtom true))^2 = 365/4 ∧
  (nodeDistance positiveRectangleWitness 1 (positiveAtom false))^2 = 365/4

/-- Atomic averaging certificate. The radius-one regions are measurable (infDist
is continuous); evaluate the two Dirac masses and their set integrals, obtaining
masses 1,1,2 and the common average z_C. The outcome is measurable and bounded on
a finite measure, so prove integrability explicitly. Recompute the six elementary
distances as needed, or establish them as local helpers. About 180 lines. -/
def T16_L5 : Prop :=
  WellDefined positiveRectangleWitness 1 ∧
  (∀ i, positiveRectangleWitness.zeta (region positiveRectangleWitness i 1) =
    if i = 2 then 2 else 1) ∧
  ∀ i z, circleAverage positiveRectangleWitness 1 i z = bit (z 2)

/-- Exact attained distance of the two radius-one contours. Compact rectangles
attain each point's distance. A point on the first contour has x-coordinate <=2,
and one on the second has x-coordinate >=9. Thus every cross distance is >=7;
(2,1/2),(9,1/2) attain 7. Prove both memberships and nonemptiness before using
sInf. No triangle inequality for polygon-to-polygon separation is used.
About 180 lines. -/
def T16_L6 : Prop :=
  planeSeparation (region positiveRectangleWitness 0 1)
    (region positiveRectangleWitness 1 1) = 7 ∧
  ∃ x ∈ region positiveRectangleWitness 0 1,
    ∃ y ∈ region positiveRectangleWitness 1 1, dist x y = 7

/-- Exact thin-rectangle squared separation. The horizontal gap is 1; the vertical
gap is max(0,2k/n-1). Exhibit closest points with vertically clamped coordinates,
and match the squared-distance lower bound for every pair of points. Then use
0<=k<n and n>0 to prove the strict bound <2. About 180 lines. -/
def T16_L7 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ k : Fin n,
    let δ := planeSeparation (thinPolygon n 0) (thinPolygon n ⟨k.val+1, by omega⟩)
    0 ≤ δ ∧ δ^2 = 1+(max 0 (2*(k : ℝ)/n-1))^2 ∧ δ^2 < 2

/-- Balanced finite-array calculation. Split the sum into two blocks of m terms;
each marginal of a fixed outcome is that outcome. Subtract the displayed formulas.
Independence makes the variance of sum (1-Z_i)a_i equal N*p*(1-p); substitute p=1/4.
Use expect_split/bernoulli moments and variance_sum. About 200 lines. -/
def T18_L1 : Prop := BalancedLinearFacts

/-- A uniform positive tail for the printed-minus-corrected error on even rows.
For X=sqrt(N)*(printed-corrected), pair coordinates into independent symmetric
blocks Z_k-Z_(m+k). Their second and fourth moments are 3/8 and their odd moments
vanish. Induction over blocks gives E[X^2]=4/3 and E[X^4]<=16/3.
Use the pointwise polynomial inequality 8X^2<=2+X^4+14*1{|X|>1/2}; expectation
gives a tail at least 5/21, hence at least 1/8. The recurrence follows the proof
of TailBIpw_centered_moments, and the tail step follows t9b6_two_sided_tail.
This avoids inferring nonconvergence from variance alone. About 300 lines. -/
def T18_L2 : Prop :=
  ∀ m : ℕ, 0 < m → (1/8 : ℝ) ≤ prob (fun _ : Fin (2*m) => 1/4) (fun z =>
    (1/2 : ℝ) < |Real.sqrt (2*m : ℕ) *
      (printedLinear (1/4) (balancedTable (2*m)) z -
        linearHajek (fun _ => 1/4) (balancedTable (2*m)) z)|)

/-- Cancellation of the explicit odd array. Split off index zero and group
indices 2k+1,2k+2; they have the same source k+1 and opposite signs.
A sum over Fin(2m) can be reindexed by Fin m x Fin 2. About 80 lines. -/
def T19_L1 : Prop :=
  ∀ m : ℕ, ∀ z, (∑ i, cancellingArray m i z) = 2*bit (z 0)-1

/-- Genuine tuple independence and the degree bound for cancelling pairs.
For separated vertex sets their cancellingSource images are disjoint. Apply
GraphCompletion.expect_mul_of_disjoint_depends to the two tuple-event indicators.
A source fiber is {0}, or {2k-1,2k}; count these fibers to obtain degree <=2.
This is full family independence, not merely zero covariances. About 200 lines. -/
def T19_L2 : Prop :=
  ∀ m : ℕ, FiniteDependencyGraph (fun _ => 1/2) (cancellingArray m)
    (cancellingNeighborhood m) ∧ ∀ i, (cancellingNeighborhood m i).card ≤ 2

/-- Rescale U by sqrt(N) and apply corrected_dependency_clt. The new bound is K,
the squared-sum integral is N, and measurable deterministic scaling preserves
independence of full tuples. Discard N=0 when simplifying the normalization;
no variance-one premise is imposed on the empty row. About 180 lines. -/
def T20_L1 : Prop := NormalizedDependencyCLT.{u}

/-- Sharp contrast constants. Let q=min(p,1-p)>0. A Boolean case split gives
|A_i|<=b/q and |W_i|<=2b/q, since |barMu_a|<=b. Expectation preserves each bound;
subtracting the mean doubles it. Use T42_barMu_bound and t18_expect_abs_le.
About 100 lines. -/
def T20_L2 : Prop := CLTSharpBounds

private theorem range_indicators (R : CircleTable 3)
    (hR : ∀ i z, R i z = if i = 2 then 0 else bit (z 2)) : RangeIndicatorTable R := by
  intro i j
  constructor
  · rintro (hij | ⟨z,z',he,hn⟩)
    · exact Or.inl hij
    · right
      have hi : i ≠ 2 := by
        intro hi
        simp [hR, hi] at hn
      refine ⟨hi, ?_⟩
      by_contra hj
      have hz := he 2 (Ne.symm hj)
      exact hn (by simp [hR, hi, hz])
  · rintro (hij | ⟨hi, rfl⟩)
    · exact Or.inl hij
    · right
      refine ⟨fun _ => false, Function.update (fun _ => false) 2 true, ?_, ?_⟩
      · intro k hk
        simp [hk]
      · simp [hR, hi, bit]

private theorem shares_coordinate {N : ℕ} (R : CircleTable N) (i j k : Fin N)
    (hi : ∀ z, R i z = bit (z k)) (hj : ∀ z, R j z = bit (z k)) : sharesSource R i j := by
  have hh (l : Fin N) (hl : ∀ z, R l z = bit (z k)) : interferes R l k := by
    right
    refine ⟨fun _ => false, Function.update (fun _ => false) k true, ?_, ?_⟩
    · intro s hs
      simp [hs]
    · simp [hl, bit]
  exact ⟨k,hh i hi,hh j hj⟩

private theorem coordinate_covariance (R : CircleTable 3)
    (h0 : ∀ z, R 0 z = bit (z 2)) (h1 : ∀ z, R 1 z = bit (z 2)) :
    cov (fun _ => 1/2) (R 0) (R 1) = 1/4 := by
  rw [show R 0 = fun z => bit (z 2) from funext h0,
    show R 1 = fun z => bit (z 2) from funext h1]
  change AronowAudit.P004.cov (fun _ => 1/2)
    (fun z => AronowAudit.P004.bit (z 2)) (fun z => AronowAudit.P004.bit (z 2)) = 1/4
  unfold AronowAudit.P004.cov
  rw [AronowAudit.P004.Wave1.t18_expect_coordinate _ 2 (fun a => AronowAudit.P004.bit a*AronowAudit.P004.bit a),
    AronowAudit.P004.Wave1.t18_expect_coordinate _ 2 AronowAudit.P004.bit]
  norm_num [bit, AronowAudit.P004.bit]

theorem T16_assembly (h1 : T16_L1) (h2 : T16_L2) (h3 : T16_L3)
    (h4 : T16_L4) (h5 : T16_L5) (h6 : T16_L6) (h7 : T16_L7) : T16WholeStatement := by
  have fixed : RangeFailure := AronowAudit.P004.Wave1.polygon_range_counterexample_proof
  have avg := fixed.2.2.2.1
  refine ⟨fixed, AronowAudit.P004.Wave1.no_polygon_cutoff_from_range_alone_proof,
    ?_, ?_, ?_, ?_, ?_, AronowAudit.P004.Wave1.polygon_spacing_counterexample_proof,
    Bridge.thin_count, h7, ?_⟩
  · intro x z z' hz
    simp [rectangleWitness,hz]
  · intro x hx
    change x ∈ rectangle 0 1 0 1 ∪ rectangle 10 11 0 1 at hx
    have hg := h1 10 (by norm_num) x (by norm_num at hx ⊢; exact hx)
    norm_num at hg
    simpa [nodeDistance,rectangleWitness] using hg
  · apply range_indicators
    intro i z
    fin_cases i
    · simpa using (avg z).1
    · simpa using (avg z).2.1
    · simpa using (avg z).2.2
  · intro L hL _
    let P := polygonRangeFamily L hL
    have havg := (h3 L hL).2
    have geom : ∀ x ∈ P.node 0 ∪ P.node 1,
        nodeDistance P 2 x = 2-x 1 ∧ 1 ≤ nodeDistance P 2 x ∧ nodeDistance P 2 x ≤ 2 := by
      simpa [P, polygonRangeFamily, nodeDistance] using h1 L hL
    refine ⟨(h3 L hL).1, ?_, ?_, ?_, geom, havg, ?_,
      shares_coordinate _ 0 1 2 (fun z => (havg z).1) (fun z => (havg z).2.1),
      ?_, coordinate_covariance _ (fun z => (havg z).1) (fun z => (havg z).2.1)⟩
    · intro l x z z' he hd
      by_cases hl : l = 2
      · subst l
        by_cases hx : x ∈ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1
        · have hg := (h1 L hL x hx).2.2
          exact False.elim ((not_lt_of_ge hg) hd)
        · simpa only [P, polygonRangeFamily, if_neg hx]
      · have hz := he 2 (Ne.symm hl)
        simp [P, polygonRangeFamily, hz]
    · intro x z
      dsimp [P, polygonRangeFamily]
      split_ifs <;> cases hz : z 2 <;> norm_num [bit, hz]
    · intro x z z' hz
      simp [P,polygonRangeFamily,hz]
    · apply range_indicators
      intro i z
      fin_cases i
      · simpa using (havg z).1
      · simpa using (havg z).2.1
      · simpa using (havg z).2.2
    · simpa [P, nodeSeparation, polygonRangeFamily, planeSeparation] using h2 L hL
  · obtain ⟨ha,hb,hc,hab,hba⟩ := h4
    obtain ⟨hwd,hm,havg⟩ := h5
    refine ⟨hwd, ?_, ?_, ?_, ha,hb,hc,hab,hba,by norm_num,hm,havg,
      shares_coordinate _ 0 1 2 (havg 0) (havg 1), ?_, by norm_num,
      h6.1, by norm_num, h6.2⟩
    · intro l x z z' he hd
      by_cases hl : l = 2
      · subst l
        by_cases hx : x = positiveAtom false ∨ x = positiveAtom true
        · rcases hx with rfl | rfl
          · exact False.elim ((not_lt_of_ge (hc false).le) hd)
          · exact False.elim ((not_lt_of_ge (hc true).le) hd)
        · simp [positiveRectangleWitness,hx]
      · have hz := he 2 (Ne.symm hl)
        simp [positiveRectangleWitness,hz]
    · intro x z
      dsimp [positiveRectangleWitness]
      split_ifs <;> cases hz : z 2 <;> norm_num [bit,hz]
    · intro x z z' hz
      simp [positiveRectangleWitness,hz]
    · convert h2 10 (by norm_num) using 1 <;>
        norm_num [nodeSeparation, positiveRectangleWitness, planeSeparation]
  · rintro ⟨C,hC⟩
    obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hC
    obtain ⟨n,hnpos,hnC⟩ := (AronowAudit.P004.Wave1.polygon_spacing_counterexample_proof).2 (max C K)
    have hKn : K ≤ n := by
      have hk : (K : ℝ) < (n : ℝ)+1 := (le_max_right C (K : ℝ)).trans_lt hnC
      have hk' : K < n+1 := by exact_mod_cast hk
      omega
    have hh := hK n hKn
    rw [show (Finset.univ.filter (fun i : Fin (n+1) =>
      planeSeparation (thinPolygon n 0) (thinPolygon n i) ≤ 2)).card = n+1 from
        Bridge.thin_count n hnpos] at hh
    have hc : C < (n+1 : ℝ) := (le_max_left C (K : ℝ)).trans_lt hnC
    exact (not_lt_of_ge hh) (by exact_mod_cast hc)

private theorem evenInProb_sub (U V : ∀ m : ℕ, Assignment (2*m) → ℝ)
    (hU : EvenInProb U) (hV : EvenInProb V) : EvenInProb (fun m z => U m z-V m z) := by
  intro ε hε
  have hh : 0 < ε/2 := by linarith
  have hsum : Tendsto (fun m =>
      prob (fun _ : Fin (2*m) => (1/4 : ℝ)) (fun z => ε/2 < |U m z|) +
      prob (fun _ : Fin (2*m) => (1/4 : ℝ)) (fun z => ε/2 < |V m z|)) atTop (nhds 0) := by
    convert (hU (ε/2) hh).add (hV (ε/2) hh) using 1 <;> simp
  apply squeeze_zero
    (fun m => AronowAudit.P004.Wave1.t18_prob_nonneg _ (fun _ => by norm_num) _)
    (fun m => ?_) hsum
  unfold prob
  calc
    _ ≤ expect (fun _ => 1/4) (fun z =>
        (if ε/2 < |U m z| then 1 else 0) + (if ε/2 < |V m z| then 1 else 0)) := by
      apply AronowAudit.P004.expect_mono _ (fun _ => by norm_num)
      intro z
      have ht := abs_sub (U m z) (V m z)
      split_ifs <;> (try norm_num) <;> (exfalso; linarith)
    _ = _ := AronowAudit.P004.expect_add _ _ _

private theorem balanced_even_remainder :
    EvenInProb (fun m z => Real.sqrt (2*m : ℕ) *
      (linearHajek (fun _ => 1/4) (balancedTable (2*m)) z-hajek (balancedTable (2*m)) z)) := by
  have hh : InProb (fun _ _ => 1/4) (fun N z => Real.sqrt N *
      (linearHajek (fun _ => 1/4) (circleAverage (balancedLine N) 0) z-
        hajek (circleAverage (balancedLine N) 0) z)) :=
    (AronowAudit.P004.Wave1.hajek_linearization_proof (Bridge.sequence balancedLine)
      (1/4) 0 (by norm_num) (by norm_num) balancedLine_local
      (Eventually.of_forall balancedLine_defined)).1
  simp_rw [balancedLine_circle] at hh
  intro ε hε
  exact (hh ε hε).comp (tendsto_atTop_mono (fun m => show m ≤ 2*m by omega) tendsto_id)

theorem T18_assembly (h1 : T18_L1) (h2 : T18_L2) : T18WholeStatement := by
  have h3 := balanced_even_remainder
  refine ⟨?_, ?_, h1, ?_, ?_, ?_, ?_⟩
  · intro Space _ _ P p d hp hd hP hWD
    exact AronowAudit.P004.Wave1.hajek_linearization_proof (Bridge.sequence P) p d hp hd hP hWD
  · exact fun p R hN z => Bridge.linearFormula_eq p R hN z
  · intro N i z
    simp only [balancedTable, balancedSign]
    split_ifs <;> norm_num
  · intro N i z z'
    rfl
  · intro hbad
    have hdiff := evenInProb_sub _ _ hbad h3
    have heq : (fun m z => Real.sqrt (2*m : ℕ)*
        (printedLinear (1/4) (balancedTable (2*m)) z-hajek (balancedTable (2*m)) z) -
        Real.sqrt (2*m : ℕ)*(linearHajek (fun _ => 1/4) (balancedTable (2*m)) z-
          hajek (balancedTable (2*m)) z)) =
        (fun m z => Real.sqrt (2*m : ℕ)*(printedLinear (1/4) (balancedTable (2*m)) z-
          linearHajek (fun _ => 1/4) (balancedTable (2*m)) z)) := by
      funext m z
      ring
    rw [heq] at hdiff
    have ht := (tendsto_order.mp (hdiff (1/2) (by norm_num))).2 (1/8) (by norm_num)
    obtain ⟨m,hm,hmpos⟩ := (ht.and (eventually_gt_atTop 0)).exists
    exact (not_lt_of_ge (h2 m hmpos)) hm
  · intro N R z
    by_cases hN : N = 0
    · subst N
      simp [printedLinear, linearHajek, augmented, ame]
    · rw [Bridge.linearFormula_eq _ _ (Nat.pos_of_ne_zero hN) z]
      unfold printedLinear linearFormula
      norm_num

theorem T19_assembly (h1 : T19_L1) (h2 : T19_L2) : T19WholeStatement := by
  have old : T19Statement := AronowAudit.P004.Wave1.dependency_clt_counterexample_proof
  have facts : CancellingFacts := by
    intro m
    dsimp only
    have habs : ∀ i z, |cancellingArray m i z| = 1 := by
      intro i z
      unfold cancellingArray
      split_ifs <;> cases hz : z (cancellingSource m i) <;> norm_num [bit,hz]
    have hmean : ∀ i, expect (fun _ => 1/2) (cancellingArray m i) = 0 := by
      intro i
      have ec (f : Bool → ℝ) : expect (fun _ : Fin (2*m+1) => 1/2)
          (fun z => f (z (cancellingSource m i))) = (1/2)*f true+(1-1/2)*f false :=
        AronowAudit.P004.Wave1.t18_expect_coordinate _ _ f
      let f : Bool → ℝ := fun a => if i.val = 0 ∨ i.val % 2 = 1 then 2*bit a-1 else -(2*bit a-1)
      change expect _ (fun z => f (z (cancellingSource m i))) = 0
      calc
        _ = (1/2)*f true+(1-1/2)*f false := ec f
        _ = 0 := by dsimp [f]; split_ifs <;> norm_num [bit]
    have hfour : ∀ i, expect (fun _ => 1/2) (fun z => (cancellingArray m i z)^4) = 1 := by
      intro i
      have he : (fun z => (cancellingArray m i z)^4) = fun _ => (1 : ℝ) := by
        funext z
        have hs : (cancellingArray m i z)^2 = 1 := by
          nlinarith [sq_abs (cancellingArray m i z), habs i z]
        calc
          _ = ((cancellingArray m i z)^2)^2 := by ring
          _ = 1 := by rw [hs]; norm_num
      rw [he]
      exact AronowAudit.P004.expect_const _ _
    have hvar : ∀ i, variance (fun _ => 1/2) (cancellingArray m i) = 1 := by
      intro i
      have he : (fun z => cancellingArray m i z*cancellingArray m i z) = fun _ => (1 : ℝ) := by
        funext z
        nlinarith [sq_abs (cancellingArray m i z), habs i z]
      unfold variance cov
      rw [he,hmean]
      simp only [zero_mul,sub_zero]
      exact AronowAudit.P004.expect_const _ _
    have hsame : (fun z => ∑ i, cancellingArray m i z) =
        fun z => ∑ i, loneRademacher (2*m+1) i z := by
      funext z
      rw [h1 m z]
      exact (AronowAudit.P004.Wave1.t19_sum (by omega) z).symm
    have hv : variance (fun _ => 1/2) (fun z => ∑ i, cancellingArray m i z) = 1 := by
      rw [hsame]
      exact AronowAudit.P004.Wave1.t19_variance (by omega)
    refine ⟨habs,hmean,hfour,hvar,(h2 m).1,(h2 m).2,h1 m,hv,?_,?_⟩
    · intro z
      rw [hv,Real.sqrt_one,div_one,h1]
    · rw [hv,Real.sqrt_one]
      simp only [div_one]
      simp_rw [show ∀ z, (∑ i, cancellingArray m i z) = ∑ i, loneRademacher (2*m+1) i z from
        fun z => congrFun hsame z]
      exact AronowAudit.P004.Wave1.t19_cdf (by omega)
  refine ⟨old, ?_, facts, ?_, ?_⟩
  · intro N hN z
    have hv : variance (fun _ => 1/2) (fun z => ∑ i, loneRademacher N i z) = 1 :=
      AronowAudit.P004.Wave1.t19_variance hN
    refine ⟨AronowAudit.P004.Wave1.t19_sum hN z, ?_⟩
    rw [hv,Real.sqrt_one,div_one]
    exact AronowAudit.P004.Wave1.t19_sum hN z
  · have hd : Tendsto (fun m : ℕ => 2*m+1) atTop atTop :=
      tendsto_atTop_mono (fun m => show m ≤ 2*m+1 by omega) tendsto_id
    have hr := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hd
    convert ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4)).mul
      (tendsto_inv_atTop_zero.comp hr)) using 1 <;> norm_num [div_eq_mul_inv]
  · intro hh
    have he : (fun m => prob (fun _ => 1/2) (fun z =>
        (∑ i, cancellingArray m i z)/Real.sqrt
          (variance (fun _ => 1/2) (fun z' => ∑ i, cancellingArray m i z')) ≤ -(1/2 : ℝ))) =
        fun _ => (1/2 : ℝ) := by
      funext m
      exact (facts m).2.2.2.2.2.2.2.2.2
    have hlim := hh (-(1/2 : ℝ))
    rw [he] at hlim
    have hx := tendsto_nhds_unique hlim tendsto_const_nhds
    exact (ne_of_lt old.2.2.1) hx

private theorem residualFirst_eq {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (i : Fin N) (a : Bool) :
    residualFirst p R i a = marginal (fun _ => p) R i a-barMu (fun _ => p) R a := by
  change AronowAudit.P004.marginal (fun _ => p)
    (fun j z => R j z-AronowAudit.P004.barMu (fun _ => p) R a) i a =
    AronowAudit.P004.marginal (fun _ => p) R i a-AronowAudit.P004.barMu (fun _ => p) R a
  rw [AronowAudit.P004.marginal_is_marginalization _ _ _ _ (fun _ => hp),
    AronowAudit.P004.marginal_is_marginalization _ R _ _ (fun _ => hp),
    AronowAudit.P004.expect_sub, AronowAudit.P004.expect_const]

private theorem own_interferes {N : ℕ} (R : CircleTable N)
    (hR : ∀ i z z', z i = z' i → R i z = R i z') :
    ∀ i j, interferes R i j ↔ i = j := by
  intro i j
  constructor
  · rintro (h | ⟨z,z',he,hn⟩)
    · exact h
    · by_contra hij
      exact hn (hR i z z' (he i hij))
  · exact Or.inl

private theorem bound_witness_values :
    barMu (fun _ => 1/4) sahBoundWitness true = 0 ∧
    barMu (fun _ => 1/4) sahBoundWitness false = 0 ∧
    variance (fun _ => 1/4) (linearHajek (fun _ => 1/4) sahBoundWitness) = 1/6 ∧
    printedSAH (1/4) sahBoundWitness (fun i => {i}) = 0 ∧
    sahLimit (fun _ => 1/4) sahBoundWitness (fun i => {i})
      (fun _ a => barMu (fun _ => 1/4) sahBoundWitness a) = 2/3 := by
  norm_num [barMu, marginal, expect, AronowAudit.P004.assignment_two_univ,
    designWeight, coin, bit, sahBoundWitness, variance, cov, linearHajek, augmented,
    printedSAH, residualSecond, sahLimit, Fin.sum_univ_two]

private theorem node_witness_values :
    barMu (fun _ => 1/4) sahNodeWitness true = 0 ∧
    barMu (fun _ => 1/4) sahNodeWitness false = 0 ∧
    variance (fun _ => 1/4) (cltRaw (1/4) sahNodeWitness true 0) = 3/4 ∧
    printedNodeVariance (1/4) sahNodeWitness 0 = 15/16 := by
  norm_num [barMu, marginal, expect, AronowAudit.P004.assignment_two_univ,
    designWeight, coin, bit, sahNodeWitness, variance, cov, cltRaw, residualContrast,
    printedNodeVariance, residualSecond, residualFirst, Fin.sum_univ_two]

theorem T21_assembly : T21WholeStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N p R B hN hp hself hsym hout
    exact ⟨fun i => AronowAudit.P004.node_variance_identity (fun _ => p) R
      (fun _ a => barMu (fun _ => p) R a) i (fun _ => hp),
      AronowAudit.P004.hajek_sah_bound p R B hN hp hself hsym hout⟩
  · intro N p R _ hp i
    have hm : residualEffect (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) i =
        residualFirst p R i true-residualFirst p R i false := by
      rw [residualFirst_eq p R hp i true,residualFirst_eq p R hp i false]
      unfold residualEffect nodeEffect
      ring
    have hc := AronowAudit.P004.node_variance_identity (fun _ => p) R
      (fun _ a => barMu (fun _ => p) R a) i (fun _ => hp)
    change variance (fun _ => p) (cltRaw p R true i) =
      residualSecond p R i true/p+residualSecond p R i false/(1-p)-
        (residualEffect (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) i)^2 at hc
    rw [hm] at hc
    exact ⟨by rw [hc]; ring, hc⟩
  · intro N X _ _ P p d h hN hp _ hh _ hloc
    apply AronowAudit.P004.hajek_sah_bound p (circleAverage P d) _ hN hp
    · intro i
      simp only [ball,Finset.mem_filter,Finset.mem_univ,true_and]
      have hz : nodeSeparation P i i = 0 :=
        AronowAudit.P004.CLTCompletion.nodeSeparation_self (Bridge.population P) i
      rwa [hz]
    · intro i j
      simp only [ball,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [show nodeSeparation P i j = nodeSeparation P j i from
        AronowAudit.P004.CLTCompletion.nodeSeparation_symm (Bridge.population P) i j]
    · intro i j hj
      apply hloc i j
      exact lt_of_not_ge (by simpa [ball] using hj)
  · obtain ⟨ha,hb,hv,hp,hc⟩ := bound_witness_values
    refine ⟨ha,hb,?_,hv,hp,hc⟩
    apply own_interferes
    intro i z z' he
    simp [sahBoundWitness,he]
  · obtain ⟨ha,hb,hv,hp⟩ := node_witness_values
    refine ⟨ha,hb,?_,hv,hp⟩
    intro z
    norm_num [sahNodeWitness,bit]

private theorem variance_scale {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (c : ℝ) :
    variance p (fun z => c*X z) = c^2*variance p X := by
  change AronowAudit.P004.variance p (fun z => c*X z) = c^2*AronowAudit.P004.variance p X
  unfold AronowAudit.P004.variance AronowAudit.P004.cov
  have he : (fun z => (c*X z)*(c*X z)) = fun z => (c*c)*(X z*X z) := by
    funext z
    ring
  rw [he,AronowAudit.P004.expect_mul,AronowAudit.P004.expect_mul]
  ring

private theorem contrast_identities : CLTContrastIdentities := by
  intro N p R hN hp
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let π := fun _ : Fin N => p
  have hb : barMu π R true-barMu π R false = ame π R :=
    AronowAudit.P004.barMu_difference π R
  have hm : ∀ a i, expect π (cltRaw p R a i) = nodeEffect π R i-if a then ame π R else 0 := by
    intro a i
    cases a
    · have hh := AronowAudit.P004.residualContrast_mean π R (fun _ _ => 0) i (fun _ => hp)
      change expect π (cltRaw p R false i) = nodeEffect π R i-0
      simp only [cltRaw,Bool.false_eq_true,ite_false]
      calc
        _ = residualEffect π R (fun _ _ => 0) i := hh
        _ = nodeEffect π R i-0 := by simp [residualEffect]
    · have hh : expect π (cltRaw p R true i) = nodeEffect π R i-(barMu π R true-barMu π R false) :=
        AronowAudit.P004.residualContrast_mean π R (fun _ a => barMu π R a) i (fun _ => hp)
      change expect π (cltRaw p R true i) = nodeEffect π R i-ame π R
      simpa only [hb] using hh
  have hs : (∑ i, expect π (cltRaw p R true i)) = 0 := by
    simp_rw [hm]
    simp only [if_true,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    unfold ame
    field_simp
    <;> ring
  have hcmean : ∀ a i, expect π (cltCentered p R a i) = 0 := by
    intro a i
    change AronowAudit.P004.expect π
      (fun z => cltRaw p R a i z-AronowAudit.P004.expect π (cltRaw p R a i)) = 0
    rw [AronowAudit.P004.expect_sub,AronowAudit.P004.expect_const,sub_self]
  have hsum : ∀ a z, (∑ i, cltCentered p R a i z) = N*(cltEstimator p R a z-ame π R) := by
    intro a z
    change (∑ i, (cltRaw p R a i z-expect π (cltRaw p R a i))) = _
    rw [Finset.sum_sub_distrib]
    cases a
    · simp_rw [hm]
      simp only [cltRaw,cltEstimator,Bool.false_eq_true,ite_false,residualContrast,sub_zero]
      change (∑ i, (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p))) -
        (∑ i, nodeEffect π R i) =
        N*((∑ i, (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p)))/N-ame π R)
      unfold ame
      field_simp
    · rw [hs]
      simp only [sub_zero]
      change (∑ i, cltRaw p R true i z) = N*(linearHajek π R z-ame π R)
      rw [Bridge.linearFormula_eq π R hN z]
      change (∑ i, (bit (z i)*(R i z-barMu π R true)/p-
        (1-bit (z i))*(R i z-barMu π R false)/(1-p))) =
        N*(ame π R+(∑ i, (bit (z i)*(R i z-barMu π R true)/p-
        (1-bit (z i))*(R i z-barMu π R false)/(1-p)))/N-ame π R)
      field_simp
      <;> ring
  refine ⟨hm,hs,hcmean,hsum,?_⟩
  intro a
  rw [show (fun z => ∑ i, cltCentered p R a i z) =
    fun z => (N : ℝ)*(cltEstimator p R a z-ame π R) from funext (hsum a)]
  rw [variance_scale]
  congr 1
  exact AronowAudit.P004.GraphCompletion.variance_add_const π (cltEstimator p R a) (-ame π R)

private theorem centered_shared_graph {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (a : Bool) :
    FiniteDependencyGraph (fun _ => p) (cltCentered p R a) (sharedNeighborhood R) := by
  have hG : FiniteDependencyGraph (fun _ => p) (cltRaw p R a) (sharedNeighborhood R) := by
    change AronowAudit.P004.FiniteDependencyGraph (fun _ => p)
      (fun i z => AronowAudit.P004.residualContrast (fun _ => p) R
        (fun _ b => if a then barMu (fun _ => p) R b else 0) i z) (sharedNeighborhood R)
    apply AronowAudit.P004.design_dependency_graph _ R _ _ (fun _ => hp)
    · intro i
      simp only [sharedNeighborhood,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨i,Or.inl rfl,Or.inl rfl⟩
    · intro i j
      simp only [sharedNeighborhood,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor <;> rintro ⟨k,hik,hjk⟩ <;> exact ⟨k,hjk,hik⟩
    · intro i j hj
      have hj' : ¬ sharesSource R i j := by
        simpa only [sharedNeighborhood,Finset.mem_filter,Finset.mem_univ,true_and] using hj
      exact hj'
  refine ⟨hG.1,hG.2.1,?_⟩
  intro I J hsep A C
  exact hG.2.2 I J hsep
    (fun v => A (fun i => v i-expect (fun _ => p) (cltRaw p R a i)))
    (fun v => C (fun i => v i-expect (fun _ => p) (cltRaw p R a i)))

private theorem spatial_applications (hsharp : CLTSharpBounds) : SpatialCLTApplications.{u} := by
  intro Space _ _ P p d hp hd hP hWD
  dsimp only
  let R := circleSequence P d
  refine ⟨fun N a => centered_shared_graph p (R N) hp a, ?_, ?_⟩
  · obtain ⟨b,hb,hbout⟩ := hP.1
    obtain ⟨h,hh,hloc⟩ := hP.2.1
    obtain ⟨c,hcount⟩ := hP.2.2
    refine ⟨b,hb,Nat.ceil (c (h d)),?_⟩
    filter_upwards [eventually_gt_atTop 0,hbout,hWD,hloc d hd,hcount (h d) (hh d hd)]
      with N hN hbN hwdN hlocN hcN
    have hR : ∀ i z, |R N i z| ≤ b :=
      AronowAudit.P004.CLTCompletion.circleAverage_abs_le (Bridge.population (P N)) d b hwdN
        (fun x z => (hbN x z).le)
    refine ⟨hsharp p b (R N) hN hp hb.le hR false,
      hsharp p b (R N) hN hp hb.le hR true,?_⟩
    intro i
    have hsub : sharedNeighborhood (R N) i ⊆ ball (nodeSeparation (P N)) i (h d) := by
      intro j hj
      simp only [sharedNeighborhood,Finset.mem_filter,Finset.mem_univ,true_and] at hj
      simp only [ball,Finset.mem_filter,Finset.mem_univ,true_and]
      by_contra hn
      exact hlocN i j (lt_of_not_ge hn) hj
    have hcard : ((sharedNeighborhood (R N) i).card : ℝ) ≤ Nat.ceil (c (h d)) := by
      calc
        _ ≤ ((ball (nodeSeparation (P N)) i (h d)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ ≤ c (h d) := hcN i
        _ ≤ Nat.ceil (c (h d)) := Nat.le_ceil _
    exact_mod_cast hcard
  · intro a hv
    have hvkeep := hv
    obtain ⟨v,hv,hvN⟩ := hv
    refine ⟨⟨v,hv,?_⟩,?_⟩
    · filter_upwards [eventually_gt_atTop 0,hvN] with N hN hvN
      rw [(contrast_identities p (R N) hN hp).2.2.2.2 a]
      have hx := mul_le_mul_of_nonneg_left hvN (Nat.cast_nonneg (α := ℝ) N)
      nlinarith
    · cases a
      · exact AronowAudit.P004.ht_central_limit (Bridge.sequence P) p d hp hd hP hWD hvkeep
      · exact AronowAudit.P004.Wave1.T42_linear_clt (Bridge.sequence P) p d hp hd hP hWD hvkeep

theorem T20_assembly (h1 : T20_L1.{u}) (h2 : T20_L2) : T20WholeStatement.{u} := by
  exact ⟨@AronowAudit.P004.corrected_dependency_clt, h1, contrast_identities, h2,
    spatial_applications h2⟩

end
end SAP.P004b.WH.W2
