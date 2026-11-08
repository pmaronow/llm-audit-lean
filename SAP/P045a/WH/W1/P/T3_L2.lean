import SAP.P045a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W1.P.T3_L2

noncomputable section

private theorem fintype_const_mul_sum {T : Type*} [Fintype T]
    (c : ℝ) (f : T → ℝ) : (∑ x, c * f x) = c * (∑ x, f x) := by
  classical
  simpa using (Finset.mul_sum (Finset.univ : Finset T) f c).symm

/-- Product expectation of a function of a coordinate subset depends only on
those coordinates' local laws. -/
theorem product_expect_projection {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (S : Set I)
    (q : ∀ i, Ω i → ℝ) (hq : ∀ i, (∑ z, q i z) = 1)
    (X : ((i : {i // i ∈ S}) → Ω i) → ℝ) :
    SAP.P045a.expect (fun w : ∀ i, Ω i => ∏ i, q i (w i))
      (fun w => X (fun i : {i // i ∈ S} => w i.1)) =
    SAP.P045a.expect (fun w : ∀ i : {i // i ∈ S}, Ω i => ∏ i, q i.1 (w i)) X := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) Ω
  have hfactor (w : ∀ i, Ω i) :
      (∏ i, q i (w i)) =
        (∏ i : {i // i ∈ S}, q i.1 (w i.1)) *
          (∏ i : {i // i ∉ S}, q i.1 (w i.1)) := by
    exact (Fintype.prod_subtype_mul_prod_subtype (fun i : I => i ∈ S)
      (fun i => q i (w i))).symm
  have hout :
      (∑ v : (i : {i // i ∉ S}) → Ω i, ∏ i, q i.1 (v i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hq]
  unfold SAP.P045a.expect
  calc
    (∑ w : (i : I) → Ω i,
        (∏ i, q i (w i)) * X (fun i : {i // i ∈ S} => w i.1)) =
      ∑ v : ((i : {i // i ∈ S}) → Ω i) × ((i : {i // i ∉ S}) → Ω i),
        ((∏ i, q i.1 (v.1 i)) * (∏ i, q i.1 (v.2 i))) * X v.1 := by
          apply Fintype.sum_equiv e
          intro w
          dsimp [e, Equiv.piEquivPiSubtypeProd]
          rw [hfactor]
    _ = ∑ x : (i : {i // i ∈ S}) → Ω i,
          (∏ i, q i.1 (x i)) * X x := by
          simp only [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x hx
          calc
            (∑ y : (i : {i // i ∉ S}) → Ω i,
                ((∏ i, q i.1 (x i)) * (∏ i, q i.1 (y i))) * X x) =
              ((∏ i, q i.1 (x i)) * X x) *
                (∑ y : (i : {i // i ∉ S}) → Ω i, ∏ i, q i.1 (y i)) := by
                  calc
                    _ = ∑ y : (i : {i // i ∉ S}) → Ω i,
                        ((∏ i, q i.1 (x i)) * X x) * (∏ i, q i.1 (y i)) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      ring
                    _ = ((∏ i, q i.1 (x i)) * X x) *
                        (∑ y : (i : {i // i ∉ S}) → Ω i,
                          ∏ i, q i.1 (y i)) := by
                          calc
                            _ = ∑ y : (i : {i // i ∉ S}) → Ω i,
                                ((∏ i, q i.1 (x i)) * X x) * (∏ i, q i.1 (y i)) := by
                                  apply Finset.sum_congr rfl
                                  intro y hy
                                  ring
                            _ = _ := fintype_const_mul_sum _ _
            _ = (∏ i, q i.1 (x i)) * X x := by rw [hout]; ring

/-- A two-stage product experiment is the uniform average of its conditional
product laws. -/
theorem toy_expect_average (F : SAP.P045a.W1ToyOutcome → ℝ) :
    expect SAP.P045a.w1ToyMass F =
      average (firstStageSets 6 3) (fun H =>
        expect (fun u : GroupAssignments (fun _ : Fin 6 => 3) =>
          ∏ g, crMass 3 (if g ∈ H then 2 else 1) (u g))
          (fun u => F (H,u))) := by
  classical
  unfold SAP.P045a.expect SAP.P045a.w1ToyMass SAP.P045a.average
  simp only [Fintype.sum_prod_type]
  simp [Finset.sum_ite, Finset.mul_sum, Finset.sum_div, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]

/-- The selected-law version of the two-stage expectation expansion. -/
theorem selected_expect_average_sap {G : ℕ} (n : Fin G → ℕ) (C : ℕ)
    (q : (g : Fin G) → Assignment (n g) → ℝ)
    (F : Finset (Fin G) × GroupAssignments n → ℝ) :
    SAP.P045a.expect (SAP.P045a.selectedLaw n C q) F =
      SAP.P045a.average (SAP.P045a.firstStageSets G C)
        (fun H => SAP.P045a.expect (fun u => ∏ g, q g (u g)) (fun u => F (H,u))) := by
  classical
  unfold SAP.P045a.expect SAP.P045a.selectedLaw SAP.P045a.average
  simp only [Fintype.sum_prod_type]
  simp [Finset.sum_ite, Finset.mul_sum, Finset.sum_div, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]

/-- Complementing a uniform subset of groups reindexes its finite average. -/
theorem complement_average_sap {N s : ℕ} (hs : s ≤ N)
    (f : Finset (Fin N) → ℝ) :
    SAP.P045a.average (SAP.P045a.firstStageSets N s)
      (fun S => f (univ \ S)) =
    SAP.P045a.average (SAP.P045a.firstStageSets N (N-s)) f := by
  classical
  have hmem {S : Finset (Fin N)} {k : ℕ} :
      S ∈ SAP.P045a.firstStageSets N k ↔ S.card = k := by
    simp [SAP.P045a.firstStageSets, Finset.mem_powersetCard]
  have hc (S : Finset (Fin N)) : (univ \ S).card = N - S.card := by
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hinv (S : Finset (Fin N)) : univ \ (univ \ S) = S := by
    ext i
    simp
  have hsum (f : Finset (Fin N) → ℝ) :
      (∑ S ∈ SAP.P045a.firstStageSets N s, f (univ \ S)) =
        ∑ S ∈ SAP.P045a.firstStageSets N (N-s), f S := by
    apply Finset.sum_bij (fun S _ => univ \ S)
    · intro S hS
      rw [hmem, hc, hmem.mp hS]
    · intro S hS T hT he
      simpa only [hinv] using congrArg (fun U => univ \ U) he
    · intro T hT
      refine ⟨univ \ T, ?_, hinv T⟩
      rw [hmem, hc, hmem.mp hT, Nat.sub_sub_self hs]
    · intro S hS
      rfl
  have hcard : ((SAP.P045a.firstStageSets N s).card : ℝ) =
      (SAP.P045a.firstStageSets N (N-s)).card := by
    have h := hsum (fun _ => (1 : ℝ))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h
  unfold SAP.P045a.average
  rw [hsum, hcard]

/-- Complete randomization on a feasible fixed-count support is normalized. -/
theorem cr_mass_total_sap {n k : ℕ} (hkn : k ≤ n) :
    (∑ z : SAP.P045a.Assignment n, SAP.P045a.crMass n k z) = 1 := by
  classical
  have h := (AronowAudit.P045.cr_mass_probability (n := n) (k := k) hkn).2
  simpa [SAP.P045a.crMass, AronowAudit.P045.crMass,
    SAP.P045a.fixedAssignments, AronowAudit.P045.fixedAssignments] using h

/-- The selected-coordinate law agrees for arbitrary functions of the selected
assignments, after integrating all other groups. -/
theorem toy_selected_transfer (high : Bool)
    (F : Finset (Fin 6) × GroupAssignments (fun _ : Fin 6 => 3) → ℝ)
    (hF : ∀ H u v, (∀ g ∈ w1RegimeSet high H, u g = v g) → F (w1RegimeSet high H,u) = F (w1RegimeSet high H,v)) :
    expect SAP.P045a.w1ToyMass (fun w => F (w1RegimeSet high w.1,w.2)) =
      expect (selectedLaw (fun _ : Fin 6 => 3) 3 (fun _ => crMass 3 (if high then 2 else 1))) F := by
  classical
  let m : ℕ := if high then 2 else 1
  let n : Fin 6 → ℕ := fun _ => 3
  let q : (g : Fin 6) → Assignment (n g) → ℝ := fun _ => crMass 3 m
  have hq (g : Fin 6) : (∑ z, q g z) = 1 := by
    exact cr_mass_total_sap (by dsimp [m]; cases high <;> norm_num)
  have havg := toy_expect_average (fun w => F (w1RegimeSet high w.1,w.2))
  rw [havg]
  have hterm (H : Finset (Fin 6)) (hH : H ∈ firstStageSets 6 3) :
      expect (fun u : GroupAssignments n =>
        ∏ g, crMass 3 (if g ∈ H then 2 else 1) (u g))
        (fun u => F (w1RegimeSet high H,u)) =
      expect (fun u : GroupAssignments n => ∏ g, q g (u g))
        (fun u => F (w1RegimeSet high H,u)) := by
    let S : Set (Fin 6) := {g | if high then g ∈ H else g ∉ H}
    letI : DecidablePred (fun g : Fin 6 => g ∈ S) :=
      fun g => Classical.propDecidable (g ∈ S)
    let ext : ((g : {g // g ∈ S}) → Assignment 3) → GroupAssignments n :=
      fun x => (Equiv.piEquivPiSubtypeProd (fun g : Fin 6 => g ∈ S)
        (fun _ => Assignment 3)).symm (x, fun _ => fun _ => false)
    let X : ((g : {g // g ∈ S}) → Assignment 3) → ℝ :=
      fun x => F (w1RegimeSet high H, ext x)
    have hdep (u : GroupAssignments n) : F (w1RegimeSet high H,u) = X (fun g => u g) := by
      change F (w1RegimeSet high H,u) = F (w1RegimeSet high H, ext (fun g => u g))
      apply hF H u (ext (fun g => u g))
      intro g hg
      have hgs : g ∈ S := by
        cases high <;> simpa [S, w1RegimeSet] using hg
      change u g =
        (Equiv.piEquivPiSubtypeProd (fun j : Fin 6 => j ∈ S)
          (fun _ => Assignment 3)).symm
          (fun j => u j, fun _ => fun _ => false) g
      simp [Equiv.piEquivPiSubtypeProd, hgs]
    have hsame : ∀ g, g ∈ S →
        crMass 3 (if g ∈ H then 2 else 1) = q g := by
      intro g hg
      dsimp [q, m]
      by_cases hh : high
      · have : g ∈ H := by simpa [S, hh] using hg
        simp [hh, this]
      · have : g ∉ H := by simpa [S, hh] using hg
        simp [hh, this]
    rw [show (fun u : GroupAssignments n =>
        F (w1RegimeSet high H,u)) = (fun u => X (fun g => u g)) by
          funext u
          exact hdep u]
    have hlocal := product_expect_projection (S := S)
      (q := fun g => crMass 3 (if g ∈ H then 2 else 1))
      (hq := fun g => cr_mass_total_sap (by
        by_cases hh : g ∈ H <;> simp [hh]))
      X
    have hlocal' := product_expect_projection (S := S) q hq X
    have hprod :
        (fun x : (g : {g // g ∈ S}) → Assignment 3 =>
          ∏ g, crMass 3 (if g.1 ∈ H then 2 else 1) (x g)) =
        (fun x => ∏ g, q g.1 (x g)) := by
      funext x
      apply Finset.prod_congr rfl
      intro g hg
      exact congrArg (fun f : Assignment 3 → ℝ => f (x g)) (hsame g g.2)
    calc
      _ = SAP.P045a.expect (fun x : (g : {g // g ∈ S}) → Assignment 3 =>
          ∏ g, crMass 3 (if g.1 ∈ H then 2 else 1) (x g)) X := hlocal
      _ = SAP.P045a.expect (fun x : (g : {g // g ∈ S}) → Assignment 3 =>
          ∏ g, q g.1 (x g)) X := by rw [hprod]
      _ = _ := hlocal'.symm
  have hterms :
      (∑ H ∈ firstStageSets 6 3,
        expect (fun u : GroupAssignments n =>
          ∏ g, crMass 3 (if g ∈ H then 2 else 1) (u g))
          (fun u => F (w1RegimeSet high H,u))) =
      ∑ H ∈ firstStageSets 6 3,
        expect (fun u : GroupAssignments n => ∏ g, q g (u g))
          (fun u => F (w1RegimeSet high H,u)) := by
    apply Finset.sum_congr rfl
    intro H hH
    exact hterm H hH
  have htarget := selected_expect_average_sap n 3 q F
  have htermsAverage :
      SAP.P045a.average (SAP.P045a.firstStageSets 6 3)
        (fun H => expect (fun u : GroupAssignments n =>
          ∏ g, crMass 3 (if g ∈ H then 2 else 1) (u g))
          (fun u => F (w1RegimeSet high H,u))) =
      SAP.P045a.average (SAP.P045a.firstStageSets 6 3)
        (fun H => expect (fun u : GroupAssignments n => ∏ g, q g (u g))
          (fun u => F (w1RegimeSet high H,u))) := by
    unfold SAP.P045a.average
    exact congrArg (fun t : ℝ => t / (SAP.P045a.firstStageSets 6 3).card) hterms
  have hreg :
      SAP.P045a.average (SAP.P045a.firstStageSets 6 3)
        (fun H => expect (fun u : GroupAssignments n => ∏ g, q g (u g))
          (fun u => F (w1RegimeSet high H,u))) =
      SAP.P045a.average (SAP.P045a.firstStageSets 6 3)
        (fun H => expect (fun u : GroupAssignments n => ∏ g, q g (u g))
          (fun u => F (H,u))) := by
    by_cases hh : high
    · simp [w1RegimeSet, hh]
    · simpa [w1RegimeSet, hh, Nat.sub_self] using
        complement_average_sap (by norm_num : 3 ≤ 6)
          (fun H => expect (fun u : GroupAssignments n => ∏ g, q g (u g))
            (fun u => F (H,u)))
  calc
    _ = SAP.P045a.average (SAP.P045a.firstStageSets 6 3)
        (fun H => expect (fun u : GroupAssignments n => ∏ g, q g (u g))
          (fun u => F (w1RegimeSet high H,u))) := htermsAverage
    _ = SAP.P045a.expect (SAP.P045a.selectedLaw n 3 q) F := hreg.trans htarget.symm

end

end SAP.P045a.WH.W1.P.T3_L2

namespace SAP.P045a.WH.W1.P.T3_L2

open SAP.P045a

private theorem rawSampleVar_congr_on {I : Type*} (S : Finset I)
    (x y : I → ℝ) (hxy : ∀ i ∈ S, x i = y i) :
    rawSampleVar S x = rawSampleVar S y := by
  have havg : average S x = average S y := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hxy i hi]
  unfold rawSampleVar
  rw [havg]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hxy i hi]

private theorem selectedMean_dep (high : Bool) (a b : Fin 3 → ℝ)
    (H : Finset (Fin 6)) (u v : GroupAssignments (fun _ : Fin 6 => 3))
    (huv : ∀ g ∈ w1RegimeSet high H, u g = v g) :
    selectedMean 3 (fun _ => directGroup a b) (w1RegimeSet high H,u) =
      selectedMean 3 (fun _ => directGroup a b) (w1RegimeSet high H,v) := by
  unfold selectedMean
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  change directGroup a b (u g) = directGroup a b (v g)
  exact congrArg (directGroup a b) (huv g (by simpa using hg))

private theorem sampleVar_dep (high : Bool) (a b : Fin 3 → ℝ)
    (H : Finset (Fin 6)) (u v : GroupAssignments (fun _ : Fin 6 => 3))
    (huv : ∀ g ∈ w1RegimeSet high H, u g = v g) :
    rawSampleVar (w1RegimeSet high H)
      (fun g => directGroup a b (u g)) =
    rawSampleVar (w1RegimeSet high H)
      (fun g => directGroup a b (v g)) := by
  apply rawSampleVar_congr_on
  intro g hg
  change directGroup a b (u g) = directGroup a b (v g)
  exact congrArg (directGroup a b) (huv g (by simpa using hg))

private theorem vest_dep (high : Bool) (a b : Fin 3 → ℝ)
    (H : Finset (Fin 6)) (u v : GroupAssignments (fun _ : Fin 6 => 3))
    (huv : ∀ g ∈ w1RegimeSet high H, u g = v g) :
    directVarianceEstimate (n := fun _ : Fin 6 => 3) 3 (fun _ => a) (fun _ => b)
      (w1RegimeSet high H,u) =
    directVarianceEstimate (n := fun _ : Fin 6 => 3) 3 (fun _ => a) (fun _ => b)
      (w1RegimeSet high H,v) := by
  unfold directVarianceEstimate
  rw [sampleVar_dep high a b H u v huv]
  congr 1
  apply congrArg (fun z : ℝ => z / ((3 : ℝ) * 6))
  apply Finset.sum_congr rfl
  intro g hg
  change droppedWithin a b (u g) = droppedWithin a b (v g)
  exact congrArg (droppedWithin a b) (huv g (by simpa using hg))

end SAP.P045a.WH.W1.P.T3_L2

theorem SAP.P045a.WH.W1.T3_L2_proof : SAP.P045a.WH.W1.T3_L2 := by
  classical
  intro high a b
  let m : ℕ := if high then 2 else 1
  let n : Fin 6 → ℕ := fun _ => 3
  let law := SAP.P045a.selectedLaw n 3 (fun _ => SAP.P045a.crMass 3 m)
  let μ := SAP.P045a.expect law
    (SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b))
  have hpointDep (H : Finset (Fin 6)) (u v : SAP.P045a.GroupAssignments n)
      (huv : ∀ g ∈ SAP.P045a.w1RegimeSet high H, u g = v g) :
      SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b)
          (SAP.P045a.w1RegimeSet high H,u) =
        SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b)
          (SAP.P045a.w1RegimeSet high H,v) := by
    exact SAP.P045a.WH.W1.P.T3_L2.selectedMean_dep high a b H u v huv
  have hmean := SAP.P045a.WH.W1.P.T3_L2.toy_selected_transfer high
    (fun p => SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b) p)
    hpointDep
  have hpoint : SAP.P045a.expect SAP.P045a.w1ToyMass
      (SAP.P045a.w1ToyPoint high a b) = μ := by
    change SAP.P045a.expect SAP.P045a.w1ToyMass
        (fun w => SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b)
          (SAP.P045a.w1RegimeSet high w.1,w.2)) =
      SAP.P045a.expect law
        (fun p => SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b) p)
    simpa [law, n, m, μ] using hmean
  have hcenterDep (H : Finset (Fin 6)) (u v : SAP.P045a.GroupAssignments n)
      (huv : ∀ g ∈ SAP.P045a.w1RegimeSet high H, u g = v g) :
      (SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b)
          (SAP.P045a.w1RegimeSet high H,u) - μ)^2 =
        (SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b)
          (SAP.P045a.w1RegimeSet high H,v) - μ)^2 := by
    rw [hpointDep H u v huv]
  have hcenter := SAP.P045a.WH.W1.P.T3_L2.toy_selected_transfer high
    (fun p =>
      (SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b) p - μ)^2)
    hcenterDep
  have hvariance : SAP.P045a.variance SAP.P045a.w1ToyMass
      (SAP.P045a.w1ToyPoint high a b) = SAP.P045a.variance law
        (SAP.P045a.selectedMean 3 (fun _ => SAP.P045a.directGroup a b)) := by
    unfold SAP.P045a.variance
    rw [hpoint]
    exact hcenter
  have hvest := SAP.P045a.WH.W1.P.T3_L2.toy_selected_transfer high
    (fun p => SAP.P045a.directVarianceEstimate (n := n) 3 (fun _ => a) (fun _ => b) p)
    (SAP.P045a.WH.W1.P.T3_L2.vest_dep high a b)
  have hsample := SAP.P045a.WH.W1.P.T3_L2.toy_selected_transfer high
    (fun p => SAP.P045a.rawSampleVar p.1
      (fun g => SAP.P045a.directGroup a b (p.2 g)))
    (SAP.P045a.WH.W1.P.T3_L2.sampleVar_dep high a b)
  refine ⟨hpoint, hvariance, ?_, ?_⟩
  · change SAP.P045a.expect SAP.P045a.w1ToyMass
        (fun w => SAP.P045a.directVarianceEstimate (n := n) 3
          (fun _ => a) (fun _ => b) (SAP.P045a.w1RegimeSet high w.1,w.2)) =
      SAP.P045a.expect law
        (fun p => SAP.P045a.directVarianceEstimate (n := n) 3
          (fun _ => a) (fun _ => b) p)
    simpa [SAP.P045a.w1ToyVest, law, n, m] using hvest
  · change SAP.P045a.expect SAP.P045a.w1ToyMass
        (fun w => SAP.P045a.rawSampleVar (SAP.P045a.w1RegimeSet high w.1)
          (fun g => SAP.P045a.directGroup a b (w.2 g))) =
      SAP.P045a.expect law
        (fun p => SAP.P045a.rawSampleVar p.1
          (fun g => SAP.P045a.directGroup a b (p.2 g)))
    simpa [law, n, m] using hsample
