import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.Gap.GP0042B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T30_L2

open MeasureTheory
open scoped BigOperators Matrix Classical Topology
open SAP.P004b
noncomputable section

lemma ex_sub {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) : expect p (fun z => X z-Y z) = expect p X-expect p Y := by
  change AronowAudit.P004.expect p (fun z => X z-Y z) = AronowAudit.P004.expect p X-AronowAudit.P004.expect p Y; exact AronowAudit.P004.expect_sub p X Y
lemma ex_div {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (c : ℝ) : expect p (fun z => X z/c) = expect p X/c := by
  change AronowAudit.P004.expect p (fun z => X z/c) = AronowAudit.P004.expect p X/c; exact AronowAudit.P004.expect_div p X c
lemma ex_const {N : ℕ} (p : Fin N → ℝ) (c : ℝ) : expect p (fun _ => c) = c := by
  change AronowAudit.P004.expect p (fun _ => c) = c; exact AronowAudit.P004.expect_const p c
lemma ex_mul {N : ℕ} (p : Fin N → ℝ) (c : ℝ) (X : Assignment N → ℝ) : expect p (fun z => c*X z) = c*expect p X := by
  change AronowAudit.P004.expect p (fun z => c*X z) = c*AronowAudit.P004.expect p X; exact AronowAudit.P004.expect_mul p c X
lemma ex_sum {N : ℕ} {A : Type*} [Fintype A] (p : Fin N → ℝ) (X : A → Assignment N → ℝ) : expect p (fun z => ∑ a, X a z) = ∑ a, expect p (X a) := by
  change AronowAudit.P004.expect p (fun z => ∑ a, X a z) = ∑ a, AronowAudit.P004.expect p (X a); exact AronowAudit.P004.expect_sum p X

lemma cov_sum_sum {N : ℕ} {A B : Type*} [Fintype A] [Fintype B] (p : Fin N → ℝ)
    (X : A → Assignment N → ℝ) (Y : B → Assignment N → ℝ) :
    cov p (fun z => ∑ i, X i z) (fun z => ∑ j, Y j z) = ∑ i, ∑ j, cov p (X i) (Y j) := by
  have hprod : expect p (fun z => (∑ i, X i z)*(∑ j, Y j z)) = ∑ i, ∑ j, expect p (fun z => X i z*Y j z) := by
    have hfun : (fun z => (∑ i, X i z)*(∑ j, Y j z)) = (fun z => ∑ i, ∑ j, X i z*Y j z) := by
      funext z
      calc (∑ i, X i z)*(∑ j, Y j z) = ∑ i, X i z*(∑ j, Y j z) := Finset.sum_mul ..
        _ = ∑ i, ∑ j, X i z*Y j z := by simp only [Finset.mul_sum]
    calc _ = expect p (fun z => ∑ i, ∑ j, X i z*Y j z) := congrArg (expect p) hfun
      _ = ∑ i, expect p (fun z => ∑ j, X i z*Y j z) := ex_sum p _
      _ = ∑ i, ∑ j, expect p (fun z => X i z*Y j z) := by
        apply Finset.sum_congr rfl; intro i hi; exact ex_sum p _
  have hmeans : expect p (fun z => ∑ i, X i z)*expect p (fun z => ∑ j, Y j z) = ∑ i, ∑ j, expect p (X i)*expect p (Y j) := by
    rw [ex_sum p X, ex_sum p Y]
    exact Finset.sum_mul_sum Finset.univ Finset.univ (fun i => expect p (X i)) (fun j => expect p (Y j))
  unfold cov
  rw [hprod, hmeans]
  simp only [Finset.sum_sub_distrib]

lemma cov_div_sub {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) (c d : ℝ) :
    cov p (fun z => X z/c) (fun z => Y z/c-d) = cov p X Y/c^2 := by
  have hprod : expect p (fun z => X z/c*(Y z/c-d)) = expect p (fun z => X z*Y z)/c^2-d*expect p X/c := by
    have hfun : (fun z => X z/c*(Y z/c-d)) = (fun z => X z*Y z/c^2-d*X z/c) := by funext z; ring
    calc _ = expect p (fun z => X z*Y z/c^2-d*X z/c) := congrArg (expect p) hfun
      _ = expect p (fun z => X z*Y z/c^2)-expect p (fun z => d*X z/c) := ex_sub p _ _
      _ = expect p (fun z => X z*Y z)/c^2-d*expect p X/c := by
        have hxy := ex_div p (fun z => X z*Y z) (c^2)
        have hdx := ex_div p (fun z => d*X z) c
        have hmul := ex_mul p d X
        calc _ = expect p (fun z => X z*Y z)/c^2-(expect p (fun z => d*X z)/c) := congrArg₂ (·-·) hxy hdx
          _ = expect p (fun z => X z*Y z)/c^2-d*expect p X/c := by rw [hmul]
  have hx : expect p (fun z => X z/c) = expect p X/c := ex_div p X c
  have hy : expect p (fun z => Y z/c-d) = expect p Y/c-d := by
    calc _ = expect p (fun z => Y z/c)-expect p (fun _ => d) := ex_sub p _ _
      _ = expect p Y/c-d := by rw [ex_div p Y c, ex_const p d]
  unfold cov
  rw [hprod, hx, hy]
  ring

end
end SAP.P004b.WH.W3.P.T30_L2

open MeasureTheory
open scoped BigOperators Matrix Classical Topology
open SAP.P004b
open SAP.P004b.WH.W3.P.T30_L2

theorem SAP.P004b.WH.W3.T30_L2_proof : SAP.P004b.WH.W3.T30_L2 := by
  change WholeCountCovariance
  intro N hN p hp R
  let π : Fin N → ℝ := fun _ => p
  let X : Fin N → Assignment N → ℝ := fun i z =>
    bit (z i) * R i z / p - (1 - bit (z i)) * R i z / (1-p)
  let Z : Fin N → Assignment N → ℝ := fun j z => if z j = true then 1 else 0
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcnt := AronowAudit.P004.Wave1.T34_count_moments (N := N) p hp true
  have hcntmean : expect π (fun z => armCount z true) = (N : ℝ) * p := by
    change AronowAudit.P004.expect (fun _ : Fin N => p) (fun z => AronowAudit.P004.armCount z true) = (N : ℝ) * p; simpa [AronowAudit.P004.coin] using hcnt.1
  have hfluctMean :
      expect π (wholeCountFluctuation (N := N) p) = 0 := by
    change expect π (fun z => armCount z true / (N : ℝ) - p) = 0
    rw [ex_sub, ex_div, ex_const, hcntmean]
    field_simp [hn]
    ring
  have hfracvar : variance π (wholeCountFluctuation (N := N) p) = p * (1-p) / (N : ℝ) := by
    have hsecond := (AronowAudit.P004.Wave1.T34_fraction_moments p hp hN true).2
    change AronowAudit.P004.variance (fun _ : Fin N => p) (wholeCountFluctuation (N := N) p) = p * (1-p) / (N : ℝ)
    have hm : AronowAudit.P004.expect (fun _ : Fin N => p) (wholeCountFluctuation (N := N) p) = 0 := hfluctMean
    rw [AronowAudit.P004.variance, AronowAudit.P004.cov, hm]
    simp only [mul_zero, sub_zero]
    simpa [wholeCountFluctuation, AronowAudit.P004.coin, AronowAudit.P004.armCount, SAP.P004b.armCount, pow_two] using hsecond
  have hZmean (j : Fin N) : expect π (Z j) = p := by
    change AronowAudit.P004.expect π (fun z => if z j = true then 1 else 0) = p
    have hs := AronowAudit.P004.ComponentCompletion.selected_update π (fun _ => hp) (fun _ => (1 : ℝ)) j true
    calc
      _ = AronowAudit.P004.coin (π j) true * AronowAudit.P004.expect π (fun _ => (1 : ℝ)) := by simpa using hs
      _ = p := by rw [AronowAudit.P004.expect_const]; simp [π, AronowAudit.P004.coin]
  have hseltrue (i : Fin N) :
      expect π (fun z => if z i = true then R i z else 0) =
        p * marginal π R i true := by
    unfold marginal
    simp [π, coin]
    field_simp [hp.1.ne']
  have hselfalse (i : Fin N) :
      expect π (fun z => if z i = false then R i z else 0) =
        (1-p) * marginal π R i false := by
    have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
    unfold marginal
    simp [π, coin]
    field_simp [hq]
  have hXmean (i : Fin N) : expect π (X i) = nodeEffect π R i := by
    have htreated :
        expect π (fun z => bit (z i) * R i z / p) = marginal π R i true := by
      have heq : (fun z => bit (z i) * R i z / p) =
          (fun z => (if z i = true then R i z else 0) / p) := by
        funext z
        cases z i <;> simp [bit]
      calc
        _ = expect π (fun z => (if z i = true then R i z else 0) / p) :=
          congrArg (expect π) heq
        _ = expect π (fun z => if z i = true then R i z else 0) / p :=
          ex_div π _ p
        _ = marginal π R i true := by rw [hseltrue i]; field_simp [hp.1.ne']
    have hcontrol :
        expect π (fun z => (1 - bit (z i)) * R i z / (1-p)) = marginal π R i false := by
      have heq : (fun z => (1 - bit (z i)) * R i z / (1-p)) =
          (fun z => (if z i = false then R i z else 0) / (1-p)) := by
        funext z
        cases z i <;> simp [bit]
      calc
        _ = expect π (fun z => (if z i = false then R i z else 0) / (1-p)) :=
          congrArg (expect π) heq
        _ = expect π (fun z => if z i = false then R i z else 0) / (1-p) :=
          ex_div π _ (1-p)
        _ = marginal π R i false := by
          have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
          rw [hselfalse i]
          field_simp [hq]
    calc
      expect π (X i) = expect π (fun z => bit (z i) * R i z / p -
          (1 - bit (z i)) * R i z / (1-p)) := by rfl
      _ = expect π (fun z => bit (z i) * R i z / p) -
          expect π (fun z => (1 - bit (z i)) * R i z / (1-p)) :=
        ex_sub π _ _
      _ = nodeEffect π R i := by rw [htreated, hcontrol]; rfl
  have hdiagprod (i : Fin N) :
      expect π (fun z => X i z * Z i z) = marginal π R i true := by
    have heq : (fun z => X i z * Z i z) =
        (fun z => (if z i = true then R i z else 0) / p) := by
      funext z
      cases hz : z i <;> simp [X, Z, bit, hz]
    calc
      _ = expect π (fun z => (if z i = true then R i z else 0) / p) :=
        congrArg (expect π) heq
      _ = expect π (fun z => if z i = true then R i z else 0) / p :=
        ex_div π _ p
      _ = marginal π R i true := by rw [hseltrue i]; field_simp [hp.1.ne']
  have hnum (i j : Fin N) (a b : Bool) :
      expect π (fun z => if z i = a ∧ z j = b then R i z else 0) =
        coin p a * coin p b * pairMarginal π (fun z => R i z) i j a b := by
    have hca : coin p a ≠ 0 := by
      cases a <;> simp [coin] <;> linarith [hp.1, hp.2]
    have hcb : coin p b ≠ 0 := by
      cases b <;> simp [coin] <;> linarith [hp.1, hp.2]
    dsimp [pairMarginal, π]
    field_simp [hca, hcb]
  have hpairprod (i j : Fin N) (hij : i ≠ j) :
      expect π (fun z => X i z * Z j z) = p *
        (pairMarginal π (fun z => R i z) i j true true -
          pairMarginal π (fun z => R i z) i j false true) := by
    have heq : (fun z => X i z * Z j z) =
        (fun z => (if z i = true ∧ z j = true then R i z else 0) / p -
          (if z i = false ∧ z j = true then R i z else 0) / (1-p)) := by
      funext z
      cases hi : z i <;> cases hj : z j <;>
        simp [X, Z, bit, hi, hj]
    calc
      _ = expect π (fun z =>
          (if z i = true ∧ z j = true then R i z else 0) / p -
            (if z i = false ∧ z j = true then R i z else 0) / (1-p)) :=
        congrArg (expect π) heq
      _ = expect π (fun z =>
          (if z i = true ∧ z j = true then R i z else 0) / p) -
            expect π (fun z =>
              (if z i = false ∧ z j = true then R i z else 0) / (1-p)) :=
        ex_sub π _ _
      _ = expect π (fun z => if z i = true ∧ z j = true then R i z else 0) / p -
            expect π (fun z => if z i = false ∧ z j = true then R i z else 0) / (1-p) := by
        have h11 := ex_div π (fun z => if z i = true ∧ z j = true then R i z else 0) p
        have h01 := ex_div π (fun z => if z i = false ∧ z j = true then R i z else 0) (1-p)
        exact congrArg₂ (· - ·) h11 h01
      _ = p * (pairMarginal π (fun z => R i z) i j true true -
            pairMarginal π (fun z => R i z) i j false true) := by
        have h11 : expect π (fun z => if z i = true ∧ z j = true then R i z else 0) =
            p*p*pairMarginal π (fun z => R i z) i j true true := by
          simpa [coin] using hnum i j true true
        have h01 : expect π (fun z => if z i = false ∧ z j = true then R i z else 0) =
            (1-p)*p*pairMarginal π (fun z => R i z) i j false true := by
          simpa [coin] using hnum i j false true
        have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
        rw [h11, h01]
        field_simp [hp.1.ne', hq]
        <;> ring
  have hdiagcov (i : Fin N) :
      cov π (X i) (Z i) =
        (1-p) * marginal π R i true + p * marginal π R i false := by
    rw [cov, hdiagprod, hXmean, hZmean]
    simp only [nodeEffect]
    ring
  have hoffcov (i j : Fin N) (hij : i ≠ j) :
      cov π (X i) (Z j) = p *
        (pairMarginal π (fun z => R i z) i j true true -
          pairMarginal π (fun z => R i z) i j false true - nodeEffect π R i) := by
    rw [cov, hpairprod i j hij, hXmean, hZmean]
    ring
  have hsumCov :
      cov π (fun z => ∑ i, X i z) (fun z => ∑ j, Z j z) =
        ∑ i, ∑ j, cov π (X i) (Z j) := cov_sum_sum π X Z
  have hsplitCov :
      (∑ i, ∑ j, cov π (X i) (Z j)) =
        (∑ i, ((1-p) * marginal π R i true + p * marginal π R i false)) +
          p * (∑ i, ∑ j ∈ Finset.univ.erase i,
            (pairMarginal π (fun z => R i z) i j true true -
              pairMarginal π (fun z => R i z) i j false true - nodeEffect π R i)) := by
    calc
      _ = ∑ i, (cov π (X i) (Z i) + ∑ j ∈ Finset.univ.erase i, cov π (X i) (Z j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin N))
          (fun j => cov π (X i) (Z j)) (Finset.mem_univ i)]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp_rw [hdiagcov]
        · calc
            (∑ i, ∑ j ∈ Finset.univ.erase i, cov π (X i) (Z j)) =
                ∑ i, ∑ j ∈ Finset.univ.erase i,
                  p * (pairMarginal π (fun z => R i z) i j true true -
                    pairMarginal π (fun z => R i z) i j false true - nodeEffect π R i) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              exact hoffcov i j (Finset.ne_of_mem_erase hj).symm
            _ = p * (∑ i, ∑ j ∈ Finset.univ.erase i,
                  (pairMarginal π (fun z => R i z) i j true true -
                    pairMarginal π (fun z => R i z) i j false true - nodeEffect π R i)) := by
              simp_rw [Finset.mul_sum]
  have hht : ht π R = fun z => (∑ i, X i z) / (N : ℝ) := by
    funext z
    simp [ht, X, π]
  have hzsum : (fun z => ∑ j, Z j z) = fun z => armCount z true := by
    funext z
    rfl
  have hfluct : wholeCountFluctuation (N := N) p =
      fun z => (∑ j, Z j z) / (N : ℝ) - p := by
    funext z
    simp [wholeCountFluctuation, Z, armCount]
  have hscale :
      cov π (ht π R) (wholeCountFluctuation (N := N) p) =
        cov π (fun z => ∑ i, X i z) (fun z => ∑ j, Z j z) / (N : ℝ)^2 := by
    rw [hht, hfluct]
    exact cov_div_sub π (fun z => ∑ i, X i z) (fun z => ∑ j, Z j z) (N : ℝ) p
  have hS :
      (∑ i, ((1-p) * marginal π R i true + p * marginal π R i false)) =
        (N : ℝ) * ((1-p) * barMu π R true + p * barMu π R false) := by
    simp only [barMu]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    field_simp [hn]
    <;> ring
  have hT :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        (pairMarginal π (fun z => R i z) i j true true -
          pairMarginal π (fun z => R i z) i j false true - nodeEffect π R i)) =
        (N : ℝ) * wholeDelta p R := by
    change _ = (N : ℝ) *
      ((∑ i, ∑ j ∈ Finset.univ.erase i,
        (pairMarginal π (fun z => R i z) i j true true -
          pairMarginal π (fun z => R i z) i j false true - nodeEffect π R i)) / (N : ℝ))
    field_simp [hn]
    <;> ring
  refine ⟨hfluctMean, hfracvar, ?_⟩
  rw [hscale, hsumCov, hsplitCov, hS, hT]
  field_simp [hn]
  <;> ring

