import SAP.P045a.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W1
noncomputable section

theorem sap_expect_sub {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X Y : Ω → ℝ) :
    expect p (fun w => X w-Y w) = expect p X-expect p Y :=
  AronowAudit.P045.expect_sub p X Y

/-- The coupled experiment is a genuine probability law whenever its first stage exists. -/
theorem joint_mass_probability {G C : ℕ} {n : Fin G → ℕ} (hCG : C ≤ G)
    (Q : Finset (Fin G) → Design (GroupAssignments n)) :
    (∀ w, 0 ≤ w1JointMass C Q w) ∧ (∑ w, w1JointMass C Q w) = 1 := by
  have hc : 0 < (firstStageSets G C).card := by
    apply Finset.card_pos.mpr
    exact Finset.powersetCard_nonempty.mpr (by simpa using hCG)
  constructor
  · intro w
    unfold w1JointMass
    split_ifs
    · exact div_nonneg ((Q w.1).nonneg w.2) (Nat.cast_nonneg _)
    · exact le_rfl
  · calc
      (∑ w, w1JointMass C Q w) =
          (∑ H ∈ firstStageSets G C, ∑ u, (Q H).mass u) / (firstStageSets G C).card := by
        unfold w1JointMass
        rw [Fintype.sum_prod_type]
        simp [Finset.sum_div]
      _ = 1 := by simp [Design.total, ne_of_gt (Nat.cast_pos.mpr hc)]

/-- First-moment linearity supplies all four contrasts without independence. -/
theorem contrasts_of_means {Ω : Type*} [Fintype Ω] (law : Ω → ℝ)
    (X : Bool → Bool → Ω → ℝ) (μ : Bool → Bool → ℝ)
    (h : ∀ high b, expect law (X high b) = μ high b) : w1UnbiasedContrasts law X μ := by
  refine ⟨h, ?_, ?_, ?_⟩
  · intro high
    change AronowAudit.P045.expect law (fun w => X high true w-X high false w) = _
    rw [AronowAudit.P045.expect_sub]
    exact congrArg₂ (fun x y : ℝ => x-y) (h high true) (h high false)
  · change AronowAudit.P045.expect law (fun w => X true false w-X false false w) = _
    rw [AronowAudit.P045.expect_sub]
    exact congrArg₂ (fun x y : ℝ => x-y) (h true false) (h false false)
  · change AronowAudit.P045.expect law (fun w => X true true w-X false false w) = _
    rw [AronowAudit.P045.expect_sub]
    exact congrArg₂ (fun x y : ℝ => x-y) (h true true) (h false false)

/-- A fixed-count arm has exactly its prescribed positive number of observations. -/
theorem cr_arm_denominator {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (z : Assignment n) (hz : z ∈ fixedAssignments n k) (b : Bool) :
    (∑ i, if z i=b then (1 : ℝ) else 0) = (if b then k else n-k : ℕ) ∧
    0 < (∑ i, if z i=b then (1 : ℝ) else 0) := by
  have hc : (univ.filter (fun i => z i=true)).card=k := (Finset.mem_filter.mp hz).2
  have hden : (∑ i, if z i=b then (1 : ℝ) else 0) = (if b then k else n-k : ℕ) := by
    cases b
    · have hn := Finset.card_filter_add_card_filter_not (s := univ) (fun i : Fin n => z i=true)
      have hf : (univ.filter (fun i : Fin n => ¬z i=true)) = univ.filter (fun i => z i=false) := by
        ext i; cases z i <;> simp
      rw [hf, hc] at hn
      have hc0 : (univ.filter (fun i => z i=false)).card=n-k := by
        simp only [Finset.card_univ, Fintype.card_fin] at hn
        omega
      simp [hc0]
    · simp [hc]
  refine ⟨hden, ?_⟩
  rw [hden]
  exact_mod_cast (show 0 < (if b then k else n-k : ℕ) by cases b <;> simp <;> omega)

/-- Positive joint mass forces membership in every prescribed fixed-count local support. -/
theorem coupled_cr_support {G C : ℕ} {n : Fin G → ℕ}
    (Q : Finset (Fin G) → Design (GroupAssignments n))
    (k : Bool → Fin G → ℕ)
    (hc : ∀ high, w1CoordinateLaw C high Q (fun g => crMass (n g) (k high g)))
    (w : Finset (Fin G) × GroupAssignments n) (hw : 0 < w1JointMass C Q w)
    (high : Bool) (g : Fin G) (hg : g ∈ w1RegimeSet high w.1) :
    w.2 g ∈ fixedAssignments (n g) (k high g) := by
  have hH : w.1 ∈ firstStageSets G C := by
    by_contra hn
    simp [w1JointMass, hn] at hw
  have hmass : 0 < (Q w.1).mass w.2 := by
    have h := hw
    simp only [w1JointMass, hH, ite_true] at h
    exact (div_pos_iff.mp h).elim (fun h => h.1)
      (fun h => False.elim (not_lt_of_ge ((Q w.1).nonneg w.2) h.1))
  have hle : (Q w.1).mass w.2 ≤ prob (Q w.1).mass (fun u => u g=w.2 g) := by
    unfold prob expect
    dsimp only
    simp only [mul_ite, mul_one, mul_zero]
    simpa using (Finset.single_le_sum
      (f := fun u : GroupAssignments n => if u g=w.2 g then (Q w.1).mass u else 0)
      (fun u _ => by split_ifs <;> first | exact (Q w.1).nonneg u | exact le_rfl)
      (Finset.mem_univ w.2))
  have hp : 0 < crMass (n g) (k high g) (w.2 g) := by
    have he : prob (Q w.1).mass (fun u => u g=w.2 g) = crMass (n g) (k high g) (w.2 g) :=
      hc high w.1 hH g hg (w.2 g)
    rw [← he]
    exact lt_of_lt_of_le hmass hle
  by_contra hn
  simp [crMass, hn] at hp

/-- Selected fixed-count groups have both arms on the support of the actual joint law. -/
theorem coupled_cr_domains {G C : ℕ} {n : Fin G → ℕ}
    (Q : Finset (Fin G) → Design (GroupAssignments n))
    (k : Bool → Fin G → ℕ) (hk : ∀ high g, 0 < k high g ∧ k high g < n g)
    (hc : ∀ high, w1CoordinateLaw C high Q (fun g => crMass (n g) (k high g))) :
    ∀ w, 0 < w1JointMass C Q w → ∀ high g, g ∈ w1RegimeSet high w.1 → ∀ b,
      armExists b (w.2 g) := by
  intro w hw high g hg b
  have hden := (cr_arm_denominator (hk high g).1 (hk high g).2 (w.2 g)
    (coupled_cr_support Q k hc w hw high g hg) b).2
  by_contra h
  have hall : ∀ i, w.2 g i ≠ b := by simpa [armExists] using h
  simp [hall] at hden

/-- Finite probability at the original biased ratio's own-arm domain. -/
theorem ratio_failure : w1RatioFailure := by
  rcases retained_T1 with ⟨h, ha, hd, _, _⟩
  have htarget : mean (fun i : Fin 4 => marginal (bernoulli (1/2)) coMembers i true) = 3/2 := by
    have hi (i : Fin 4) : marginal (bernoulli (1/2)) coMembers i true = 3/2 := by
      have he := AronowAudit.P045.co_members_marginal_four (1/2) (by norm_num) (by norm_num) i true
      change marginal (bernoulli (1/2)) coMembers i true = 3*(1/2) at he
      norm_num at he ⊢
      exact he
    simp_rw [hi]
    norm_num [mean]
  refine ⟨?_, ha.1, htarget, by norm_num, fun high => (hd high).2,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩
  have hd : (fun z : Assignment 4 => armExists true z) =
      (fun z => 0 < (AronowAudit.P045.countIndex4 z).val) := by
    funext z
    exact propext (AronowAudit.P045.four_arm_domains z).1
  rw [hd]
  change AronowAudit.P045.prob (AronowAudit.P045.bernoulli (1/2))
    (fun z => 0 < (AronowAudit.P045.countIndex4 z).val) = _
  refine (AronowAudit.P045.bernoulli_count_event_probability (1/2) (fun k => 0 < k.val)).trans ?_
  norm_num [AronowAudit.P045.prob, AronowAudit.P045.expect,
    AronowAudit.P045.binomial4, Fin.sum_univ_succ, Nat.choose]

/-- Marginal law computation for the three possible singleton labels. -/
theorem toy_local (high : Bool) :
    let m := if high then 2 else 1
    let x := w1ToyBaseline
    (∀ z ∈ fixedAssignments 3 m,
      directGroup (fun i => x i+1) x z =
        if high then 4-(3/2)*w1SingletonBaseline high z else (3/2)*w1SingletonBaseline high z-2) ∧
    (∀ t ∈ ({1,2,3} : Finset ℝ), prob (crMass 3 m) (fun z => w1SingletonBaseline high z=t) = 1/3) ∧
    (∀ t ∈ ({-1/2,1,5/2} : Finset ℝ),
      prob (crMass 3 m) (fun z => directGroup (fun i => x i+1) x z=t) = 1/3) ∧
    expect (crMass 3 m) (w1TwoArmVariance high) = 1 := by
  have h1 : fixedAssignments 3 1 = {![true,false,false],![false,true,false],![false,false,true]} :=
    AronowAudit.P045.fixed_three_supports.1
  have h2 : fixedAssignments 3 2 = {![false,true,true],![true,false,true],![true,true,false]} :=
    AronowAudit.P045.fixed_three_supports.2
  have he (m : ℕ) (F : Assignment 3 → ℝ) :
      expect (crMass 3 m) F = average (fixedAssignments 3 m) F :=
    AronowAudit.P045.cr_expect_average 3 m F
  cases high <;>
    norm_num [prob, he, h1, h2, average, directGroup, treatedSet,
      w1ToyBaseline, w1SingletonBaseline, w1TwoArmVariance, rawSampleVar,
      Fin.univ_succ, Fin.sum_univ_succ, Finset.filter_insert, Finset.filter_singleton,
      Finset.sdiff_singleton_eq_erase, Finset.sdiff_insert, Finset.erase_insert,
      Finset.erase_insert_of_ne]

/-- The expected between-group sample variance under the existing same-regime extension. -/
theorem toy_sample_variance (m : ℕ) (hm : m ∈ ({1,2} : Finset ℕ)) :
    expect (selectedLaw (fun _ : Fin 6 => 3) 3 (fun _ => crMass 3 m))
      (fun w => rawSampleVar w.1 (fun g => directGroup (fun i => w1ToyBaseline i+1) w1ToyBaseline (w.2 g))) = 3/2 := by
  have hm3 : m ≤ 3 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  have hloc := AronowAudit.P045.singleton_group_finite_moments m hm
  have h := AronowAudit.P045.Wave1.dvc_selected_sample_variance (G := 6) (C := 3)
    (by norm_num) (by norm_num) (fun _ => 3) (fun _ => AronowAudit.P045.crMass 3 m)
    (fun _ => AronowAudit.P045.directGroup (fun i => (i.val : ℝ)+1+1) (fun i => (i.val : ℝ)+1))
    (fun _ => (AronowAudit.P045.cr_mass_probability (n := 3) (k := m) hm3).2)
  simp_rw [hloc.1, hloc.2.1] at h
  have h' : expect (selectedLaw (fun _ : Fin 6 => 3) 3 (fun _ => crMass 3 m))
      (fun w => rawSampleVar w.1 (fun g => directGroup (fun i => w1ToyBaseline i+1) w1ToyBaseline (w.2 g))) =
      AronowAudit.P045.popVar (fun _ : Fin 6 => (1 : ℝ)) + (∑ _g : Fin 6, (3/2 : ℝ))/6 := h
  rw [h']
  norm_num [AronowAudit.P045.popVar, AronowAudit.P045.rawSampleVar, AronowAudit.P045.average]

end
end SAP.P045a.WH.W1
