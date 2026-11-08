import SAP.P003a.WH.W2.Helpers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2

open scoped BigOperators
open SAP.P003a.Bridge
attribute [local instance 0] Classical.propDecidable

/-- The chronological sentinel run reaches an adjacent final bracket without exhausting its d+1 fuel. Every recorded bracket stays inside the initial one, every evaluated midpoint is strictly interior, and the query list is valid and distinct. Prove by induction on fuel with the invariant 0<b-a≤fuel; interior midpoint arithmetic is omega, and strict nesting excludes repeats. About 150–250 lines. No assumption on replies, including their time dependence. -/
def T5_L1 : Prop :=
  ∀ (k₁ k₂ : ℤ), k₁ ≤ k₂ → ∀ reply : ℕ → ℤ → Bool,
    W2SearchGeometry k₁ k₂ reply

/-- Chronological replies obey the same sharp query bound. First prove the power-width bound: b-a≤2^q implies at most q queries for every fuel, time and reply sequence. Induct on q, halving the width; then use Nat.lt_pow_succ_log_self with d>0. Adapt sentinel_queries_le_pow by retaining the time argument through recursive calls. About 60–100 lines. -/
def T5_L2 : Prop :=
  ∀ (k₁ k₂ : ℤ), k₁ ≤ k₂ → ∀ reply : ℕ → ℤ → Bool,
    (w2Queries k₁ k₂ reply).length ≤ Nat.log 2 (k₂-k₁+1).toNat+1

/-- Identify the balanced search domains, including the estimator numerator, the entire candidate lattice, both domain cardinalities and their n+1 bounds. Use the two arm-sum equalities, cast to integers before subtraction, and unfold candidateNumerators. Membership in its range image is an integer interval; Int.card_Icc and omega finish. Clear the positive real denominator m to obtain n*T=2*Delta. About 100–180 lines. -/
def T5_L3 : Prop :=
  ∀ (o : Counts) (m : ℕ), 0 < m → o.a+o.b = m → o.c+o.d = m →
    W2BalancedDomains o m

/-- A positive finite law has a largest attained nonrejecting tail threshold; all real rejecting thresholds are strictly above it. Prove tail antitonicity, use the minimum attained value to show the nonrejecting support is nonempty, and choose its maximum with Finset.exists_max_image. For a threshold between atoms, compare with the next attained value, or partition the finite sum. About 100–180 lines. Positivity makes every represented value actual support. -/
def T11_L1 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (w D : Ω → ℝ),
    (∀ i, 0 < w i) → (∑ i, w i) = 1 →
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ i : Ω, α ≤ finiteTail w D (D i) ∧
      (∀ j, α ≤ finiteTail w D (D j) → D j ≤ D i) ∧
      (∀ x : ℝ, finiteTail w D x < α ↔ D i < x)

/-- Transfer the finite-tail rejection bound to an arbitrary real probability measure concentrated on a finite set. Discard zero-mass atoms, give each remaining point weight (mu {x}).toReal, prove their weights sum to one and the tail/event sums equal the corresponding measure.toReal values. Apply finite_tail_support_repair (or finite_tail_repair with zero weights). Finite unions of measurable singletons suffice; probability implies all measures are finite. About 150–250 lines; no integrability premise is needed. -/
def T12_L1 : Prop :=
  ∀ (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (s : Finset ℝ), μ (s : Set ℝ) = 1 → ∀ α : ℝ, 0 < α → α < 1 →
    (μ {d | (μ (Set.Ici d)).toReal < α}).toReal < α

/-- The count p-value equals the actual absolute-deviation tail of an arbitrary labeled table at its observation. Use couplingB2_observed for the observed count identity, neyman_estimator_eq and table_effect for the statistic, then neyman_tail_iff and neyman_event_pushforward. Avoid dependent casts by proving the tail comparison for arbitrary n first. Expand pValue/tailCount only at the last finite-sum step. About 120–220 lines, with no balance assumption. Possibility and effect agreement are already proved in Helpers. -/
def T12_L2 : Prop :=
  ∀ (n m : ℕ) (y : PotentialTable n), 0 < m → m < n →
    ∀ z : Assignment n m,
      let o := unitObserved (unitOutcomes y z.val) z.val
      (pValue (tableCounts y) o : ℝ) = w2Tail m y (w2Deviation y z)

/-- Transport a source lattice pmf under the coordinate bijection j↦j/k. Construct Equiv.ofBijective using point_bijective, use Equiv.summable_iff and Equiv.tsum_eq for normalization, and point_coordinate to reduce the pushforward atom sum to tsum_ite_eq. Normalization assumes only a pmf, including laws without a first moment. About 60–120 lines. -/
def T14_L1 : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ f : W2Lattice k → ℝ, W2LatticePMF f →
    IsPMF (w2Rescale f) ∧ ∀ j, w2ImageMass f j = w2Rescale f j

/-- Reindex the first moment through the same bijection and divide by k. Summable real series are absolutely summable; use summable_div_const_iff with k≠0 in both directions, then Equiv.tsum_eq and tsum_div_const. Cancel k for the half-integer center equivalence. About 70–130 lines. -/
def T14_L2 : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ f : W2Lattice k → ℝ,
    (W2LatticeMoment f ↔ Summable (fun j : ℤ => (j : ℝ)*w2Rescale f j)) ∧
    (W2LatticeMoment f →
      w2SourceMean f = (∑' j : ℤ, (j : ℝ)*w2Rescale f j)/(k : ℝ) ∧
      ∀ c₂ : ℤ, w2SourceMean f = (c₂ : ℝ)/(2*k) ↔
        (∑' j : ℤ, (j : ℝ)*w2Rescale f j) = (c₂ : ℝ)/2)

/-- The uniform law on {-1,0,1} is SD with mean zero. Add three hasSum_ite_eq identities for normalization and the first moment. For SDShape at twice-center zero, split the finitely many nonzero cells and use omega. Alternatively use discordant_estimator_sd_finite_mass and mean_of_symmetry. About 60–100 lines. -/
def T9_L1 : Prop :=
  IsSD w2ThreeMass ∧ (∑' j : ℤ, (j : ℝ)*w2ThreeMass j) = 0

/-- The sum law is a finite-first-moment pmf, has mean one half, and is symmetric about one half. Add its four delta masses and first moments; reflection j↦1-j permutes equal-weight pairs. About 60–100 lines. The assembly proves failure of SD directly from the unequal masses at 1,2. -/
def T9_L2 : Prop :=
  IsMass w2BSumMass ∧ (∑' j : ℤ, (j : ℝ)*w2BSumMass j) = 1/2 ∧
    ∀ j, w2BSumMass (1-j) = w2BSumMass j

theorem T11_assembly (h1 : T11_L1) : T11WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m y α hm hmn hα hα1
    let : Nonempty (Assignment n m) := assignment_nonempty n m hmn.le
    let D : Assignment n m → ℝ := w2Deviation y
    let w : Assignment n m → ℝ := fun _ => 1/Fintype.card (Assignment n m)
    have ht (x : ℝ) : finiteTail w D x = w2Tail m y x := (uniform_tail D x).symm
    obtain ⟨i, hi, hmax, hreal⟩ := h1 w D uniform_weights_pos uniform_weights_total α hα hα1
    have hmem (z : Assignment n m) : D z ∈ w2Support m y :=
      Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
    have hr (x : ℝ) : w2Tail m y x < α ↔ D i < x := by simpa only [ht] using hreal x
    refine ⟨⟨D i, hmem i⟩, D i, hmem i, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [ht] using hi
    · intro e he hae
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp he
      exact hmax z (by simpa only [ht] using hae)
    · ext x; exact hr x
    · exact ⟨D i+1, (hr _).mpr (by linarith)⟩
    · rintro ⟨x,hx,hleast⟩
      have hix := (hr x).mp hx
      have hu := (hr ((D i+x)/2)).mpr (by linarith)
      have := hleast _ hu
      linarith
  · let y : PotentialTable 2 := fun _ => (false,false)
    let : Nonempty (Assignment 2 1) := assignment_nonempty 2 1 (by omega)
    have hτ : tableTau y = 0 := by simp [tableTau, y, bit]
    have hT (z : Assignment 2 1) : tableEstimator y z.val = 0 := by
      simp [tableEstimator, y, bit]
    have hq (x : ℝ) : w2Tail 1 y x = if x ≤ 0 then 1 else 0 := by
      unfold w2Tail
      simp only [w2Deviation, hT, hτ, sub_self, abs_zero]
      exact uniform_const _
    refine ⟨hτ,hT,hq,?_⟩
    ext x
    rw [Set.mem_ofPred_eq, hq, Set.mem_Ioi]
    by_cases hx : x ≤ 0
    · norm_num [hx, not_lt_of_ge hx]
    · norm_num [hx, lt_of_not_ge hx]
  · exact ⟨AronowAudit.P003.real_threshold_counterexample, AronowAudit.P003.zero_population_tail⟩

theorem T14_assembly (h1 : T14_L1) (h2 : T14_L2) : T14WholeStatement := by
  refine ⟨AronowAudit.P003.corrected_sd_definition, AronowAudit.P003.fair_mass_sd.2, ?_, ?_⟩
  · intro k hk f hf
    exact ⟨(h1 k hk f hf).1, (h1 k hk f hf).2, point_coordinate k hk,
      (fun _ => Iff.rfl), Iff.rfl, (h2 k hk f).1, (h2 k hk f).2⟩
  · refine ⟨half_point_pmf, half_point_correct, ?_, half_point_wrong, ?_⟩
    · intro j
      dsimp [w2Point]
      push_cast
      ring
    · intro hp
      have he : w2PrintedRescale = fun _ => (0 : ℝ) := funext half_point_wrong
      have hs := hp.2.2
      rw [he, tsum_zero] at hs
      norm_num at hs

theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) : T9WholeStatement := by
  refine ⟨⟨AronowAudit.P003.dependent_convolution_counterexample,
    AronowAudit.P003.dependent_joint_law⟩, ?_, ?_, b_joint, h1.1, h1.2,
    h2.1, h2.2.1, h2.2.2, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [w2BW]
  · norm_num [w2BW, Fin.sum_univ_succ]
  · norm_num [w2BSumMass]
  · rintro ⟨_, c, hmean, hshape⟩
    have hcR : (c : ℝ) = 1 := by rw [h2.2.1] at hmean; linarith
    have hc : c = 1 := by exact_mod_cast hcR
    subst c
    have h := hshape.2 1 2 (by norm_num) (by norm_num)
    norm_num [w2BSumMass] at h

theorem T12_assembly (h1 : T12_L1) (h2 : T12_L2) : T12WholeStatement := by
  refine ⟨@AronowAudit.P003.finite_tail_support_repair, h1, ?_⟩
  intro n m y α hm hmn hα hα1
  let : Nonempty (Assignment n m) := assignment_nonempty n m hmn.le
  let D : Assignment n m → ℝ := w2Deviation y
  let w : Assignment n m → ℝ := fun _ => 1/Fintype.card (Assignment n m)
  have ht (x : ℝ) : finiteTail w D x = w2Tail m y x := (uniform_tail D x).symm
  have h := AronowAudit.P003.finite_tail_support_repair w D
    uniform_weights_pos uniform_weights_total α ⟨hα,hα1⟩
  change ((∀ i, α ≤ finiteTail w D (D i)) ∨
    ∃ i, 0 < w i ∧ finiteTail w D (D i) < α ∧
      (∀ j, finiteTail w D (D j) < α ↔ D i ≤ D j) ∧
      (∑ j, if finiteTail w D (D j) < α then w j else 0) = finiteTail w D (D i)) ∧
    (∑ j, if finiteTail w D (D j) < α then w j else 0) < α at h
  have hevent : (∑ j, if finiteTail w D (D j) < α then w j else 0) =
      uniformProb (fun j => w2Tail m y (D j) < α) := by
    simp only [ht, uniform_event_sum, w]
  have hrej : uniformProb (fun z : Assignment n m => w2Tail m y (D z) < α) < α := by
    rw [← hevent]; exact h.2
  have hs : W2SupportRepair m y α := by
    refine ⟨?_, hrej⟩
    rcases h.1 with hnone | ⟨i, _, hi, heq, hsum⟩
    · left
      refine ⟨?_, ?_⟩
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hx,hr⟩ := Finset.mem_filter.mp hx
        obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hx
        exact (not_lt_of_ge (by simpa only [ht] using hnone z)) hr
      · intro z
        exact not_lt_of_ge (by simpa only [ht] using hnone z)
    · right
      refine ⟨D i, ?_, ?_, ?_, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, by simpa only [ht] using hi⟩
      · intro d hd
        obtain ⟨hd,hr⟩ := Finset.mem_filter.mp hd
        obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hd
        exact (heq z).mp (by simpa only [ht] using hr)
      · intro z; simpa only [ht] using heq z
      · rw [← hevent]; simpa only [ht] using hsum
      · simpa only [ht] using hi
  have hτ := table_effect n y (by omega)
  have hb := h2 n m y hm hmn
  have hpoint (z : Assignment n m) (hz : α ≤ w2Tail m y (D z)) :
      α ≤ (pValue (tableCounts y) (unitObserved (unitOutcomes y z.val) z.val) : ℝ) ∧
      tableTau y ∈ accepted α (unitObserved (unitOutcomes y z.val) z.val) ∧
      tableTau y ∈ exactInterval α (unitObserved (unitOutcomes y z.val) z.val) := by
    let o := unitObserved (unitOutcomes y z.val) z.val
    have hp : α ≤ (pValue (tableCounts y) o : ℝ) := by rw [hb z]; exact hz
    have hk : tau (tableCounts y) ∈ accepted α o := by
      have hp' : α ≤ (AronowAudit.P003.pValue (toAudit (tableCounts y)) (toAudit o) : ℝ) := by
        simpa only [to_pValue] using hp
      have hv' := (to_possible o (tableCounts y)).mpr (true_counts_possible n m y z)
      simpa only [to_tau, to_accepted] using
        AronowAudit.P003.accepted_of_possible α (toAudit o) (toAudit (tableCounts y)) hv' hp'
    rw [← hτ] at hk
    exact ⟨hp, hk, ⟨tableTau y, hk, tableTau y, hk, le_rfl, le_rfl⟩⟩
  refine ⟨hs, ?_, ?_⟩
  · intro z
    exact ⟨rfl, true_counts_possible n m y z, hpoint z⟩
  · exact uniform_cover (fun z => w2Tail m y (D z)) _ α
      (fun z hz => (hpoint z hz).2.2) hrej

theorem endpoint_cost_bound (h1 : T5_L1) (h2 : T5_L2)
    (k₁ k₂ : ℤ) (hk : k₁ ≤ k₂) (n : ℕ) (hd : (k₂-k₁+1).toNat ≤ n+1)
    (reply : ℕ → ℤ → Bool) (cost : ℤ → ℕ)
    (hc : ∀ x ∈ w2Queries k₁ k₂ reply, cost x ≤ if x = 0 then 2*(n+1) else n+1) :
    w2Cost cost (w2Queries k₁ k₂ reply) ≤ (n+1)*(Nat.log 2 (n+1)+2) := by
  have hg := h1 k₁ k₂ hk reply
  have hnd := hg.2.2.2.2.2.1
  have hb := cost_with_zero (n+1) cost _ hc hnd
  have hl := (h2 k₁ k₂ hk reply).trans (Nat.add_le_add_right (Nat.log_mono_right hd) 1)
  exact hb.trans (Nat.mul_le_mul_left _ (by omega))

theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) : T5WholeStatement := by
  refine ⟨?_, ?_, ?_, two_budget⟩
  · intro k₁ k₂ hk reply
    refine ⟨h1 k₁ k₂ hk reply, ?_⟩
    have hd : 0 < (k₂-k₁+1).toNat := by omega
    have hl := h2 k₁ k₂ hk reply
    refine ⟨hl, ?_, ?_⟩
    · rw [log_floor _ hd]; exact_mod_cast hl
    · rw [log_floor _ hd, show ⌊logTwo ((k₂-k₁+1).toNat : ℝ)+2⌋ =
          (Nat.log 2 (k₂-k₁+1).toNat : ℤ)+2 from log_floor_add _ hd 2]
      push_cast
      linarith
  · intro k₁ k₂ r f hk hr₁ hr₂ hf
    let reply : ℕ → ℤ → Bool := fun _ c => f c
    let s := w2Run k₁ k₂ reply
    have hg := h1 k₁ k₂ hk reply
    have he : sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1) =
        (s.1.1, w2Queries k₁ k₂ reply) := static_search _ f 0 _ _
    have hret := AronowAudit.P003.corrected_search k₁ k₂ r f hk ⟨hr₁,hr₂⟩ hf
    dsimp only at hret
    rw [sentinelSearch_eq, he] at hret
    have hsr : s.1.1 = r := hret.1
    have hfinal : r < s.1.2 := by have ha := hg.1; change s.1.2 = s.1.1+1 at ha; omega
    refine ⟨hsr, hg.2.2.1, hsr.le, hfinal, hg.2.2.2.1, ?_, he⟩
    intro p hp
    have hframe := hg.2.2.2.2.1 p hp
    have hthreshold := threshold_frames ((k₂-k₁+1).toNat+1) f 0 (k₁-1) (k₂+1) r
      ⟨hr₁,by omega⟩ (fun x hx hy => hf x (by omega) (by omega)) p hp
    exact ⟨hframe.1, hthreshold.1, hthreshold.2, hframe.2.1⟩
  · intro o m hm ho₁ ho₂
    have hd := h3 o m hm ho₁ ho₂
    refine ⟨hd, ?_⟩
    let n := 2*m
    let Δ : ℤ := (o.a : ℤ)-o.c
    have hlo : -(m : ℤ) ≤ Δ := hd.2.1
    have hhi : Δ ≤ m := hd.2.2.1
    have hUdom : 2*Δ ≤ Δ+m := by omega
    have hLdom : Δ-m ≤ 2*Δ := by omega
    have hUd : (Δ+m-2*Δ+1).toNat ≤ n+1 := by dsimp [n]; omega
    have hLd : (2*Δ-(Δ-m)+1).toNat ≤ n+1 := by dsimp [n]; omega
    intro ru rl cu cl hcu hcl
    have hU := endpoint_cost_bound h1 h2 (2*Δ) (Δ+m) hUdom n hUd ru cu hcu
    have hL := endpoint_cost_bound h1 h2 (Δ-m) (2*Δ) hLdom n hLd rl cl hcl
    have hB : (((n+1)*(Nat.log 2 (n+1)+2) : ℕ) : ℝ) ≤
        ((n+1 : ℕ) : ℝ)*((⌊logTwo (n+1 : ℕ)+3⌋ : ℤ) : ℝ) := by
      rw [show ⌊logTwo (n+1 : ℕ)+3⌋ = (Nat.log 2 (n+1) : ℤ)+3 from
        log_floor_add _ (by omega) 3]
      push_cast
      nlinarith
    refine ⟨hU, hL, hB, ?_⟩
    intro hn
    have hboth : ((w2Cost cu (w2Queries (2*Δ) (Δ+m) ru)+
        w2Cost cl (w2Queries (Δ-m) (2*Δ) rl) : ℕ) : ℝ) ≤
        2*((n+1 : ℕ) : ℝ)*((⌊logTwo (n+1 : ℕ)+3⌋ : ℤ) : ℝ) := by
      have huR := (Nat.cast_le (α := ℝ)).mpr hU
      have hlR := (Nat.cast_le (α := ℝ)).mpr hL
      push_cast at *
      linarith
    exact hboth.trans (two_budget n hn)

end SAP.P003a.WH.W2
