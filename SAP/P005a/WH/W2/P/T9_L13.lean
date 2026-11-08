import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L13

noncomputable section
open Finset Filter SAP.P005a.Bridge
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

abbrev Wmat {n d : ℕ} (P : SAP.P005a.Population n d) :=
  AronowAudit.P005.Wave1.CondT8T9_W (toPopulation P)

def radius {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  sSup (Set.range (fun i : Fin n => ∑ j, (W i j)^2))

def rowX {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ) (R : ℝ) (i : Fin n) :
    Matrix (Fin k) (Fin k) ℝ := fun a b => R⁻¹ * (W i a * W i b)

lemma row_sq_le_radius {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin n) : (∑ j, (W i j)^2) ≤ radius W := by
  classical
  apply le_csSup
  · exact (Set.finite_range (fun i : Fin n => ∑ j, (W i j)^2)).bddAbove
  · exact ⟨i, rfl⟩

lemma radius_pos_augmented {n d : ℕ} (P : SAP.P005a.Population n d)
    (hn : 0 < n) : 0 < radius (Wmat P) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let i : Fin n := ⟨0, hn⟩
  have hcoord : Wmat P i 0 = (Real.sqrt (n : ℝ))⁻¹ := by
    simp [Wmat, AronowAudit.P005.Wave1.CondT8T9_W, i, toPopulation]
  have hcoordpos : 0 < (Wmat P i 0)^2 := by
    rw [hcoord]
    positivity
  have hterm : (Wmat P i 0)^2 ≤ ∑ j : Fin (d+1), (Wmat P i j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (Wmat P i j)) (mem_univ 0)
  exact lt_of_lt_of_le hcoordpos (hterm.trans (row_sq_le_radius (Wmat P) i))

lemma rowX_psd {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ) (R : ℝ)
    (hR : 0 < R) (i : Fin n) : (rowX W R i).PosSemidef := by
  have h := (Matrix.posSemidef_vecMulVec_self_star (W i)).smul
    (show 0 ≤ R⁻¹ by positivity)
  have heq : rowX W R i = R⁻¹ • Matrix.vecMulVec (W i) (W i) := by
    ext a b
    simp [rowX, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [heq]
  exact h

lemma rowX_quad {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ) (R : ℝ)
    (i : Fin n) (v : Fin k → ℝ) :
    quadratic (rowX W R i) v = R⁻¹ * (∑ j, W i j * v j)^2 := by
  have hmul : rowX W R i *ᵥ v =
      (R⁻¹ * (∑ j, W i j * v j)) • W i := by
    ext j
    simp only [rowX, Matrix.mulVec]
    calc
      (∑ x, R⁻¹ * (W i j * W i x) * v x) =
          R⁻¹ * W i j * (∑ x, W i x * v x) := by
        calc
          _ = ∑ x, (R⁻¹ * W i j) * (W i x * v x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = R⁻¹ * W i j * (∑ x, W i x * v x) := by rw [Finset.mul_sum]
      _ = R⁻¹ * (∑ x, W i x * v x) * W i j := by ring
  rw [quadratic, SAP.P005a.dot, hmul]
  simp only [Pi.smul_apply]
  calc
    (∑ x, v x * ((R⁻¹ * (∑ j, W i j * v j)) * W i x)) =
        ∑ x, (R⁻¹ * (∑ j, W i j * v j)) * (W i x * v x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (R⁻¹ * (∑ j, W i j * v j)) * (∑ x, W i x * v x) := by
          simpa only [mul_assoc] using
            (Finset.mul_sum Finset.univ (fun x => W i x * v x)
              (R⁻¹ * (∑ j, W i j * v j))).symm
    _ = R⁻¹ * (∑ j, W i j * v j)^2 := by ring

lemma quadratic_one {k : ℕ} (v : Fin k → ℝ) :
    quadratic (1 : Matrix (Fin k) (Fin k) ℝ) v =
      AronowAudit.Literature.coordinateNormSq k v := by
  simp [quadratic, SAP.P005a.dot, AronowAudit.Literature.coordinateNormSq,
    Matrix.one_mulVec, pow_two]

lemma rowX_le_one {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ) (R : ℝ)
    (hR : 0 < R) (i : Fin n)
    (hrow : (∑ j, (W i j)^2) ≤ R) : matrixLE (rowX W R i) 1 := by
  rw [matrixLE, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · exact (Matrix.isHermitian_one.sub (rowX_psd W R hR i).1)
  · intro v
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : Fin k => W i j)
      (fun j => v j)
    have hv : 0 ≤ AronowAudit.Literature.coordinateNormSq k v :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hprod : (∑ j, W i j * v j)^2 ≤ R *
        AronowAudit.Literature.coordinateNormSq k v := by
      exact hcs.trans (mul_le_mul_of_nonneg_right hrow hv)
    have hdiv : R⁻¹ * (∑ j, W i j * v j)^2 ≤
        AronowAudit.Literature.coordinateNormSq k v := by
      calc
        R⁻¹ * (∑ j, W i j * v j)^2 =
            (∑ j, W i j * v j)^2 / R := by rw [div_eq_mul_inv]; ring
        _ ≤ AronowAudit.Literature.coordinateNormSq k v :=
          (div_le_iff₀ hR).2 (by nlinarith [hprod])
    have hq : quadratic (1 - rowX W R i) v =
        AronowAudit.Literature.coordinateNormSq k v -
          R⁻¹ * (∑ j, W i j * v j)^2 := by
      calc
        quadratic (1 - rowX W R i) v =
            quadratic (1 : Matrix (Fin k) (Fin k) ℝ) v -
              quadratic (rowX W R i) v := by
          simp [quadratic, SAP.P005a.dot, Matrix.sub_mulVec, Matrix.one_mulVec,
            Finset.sum_sub_distrib, mul_sub]
        _ = AronowAudit.Literature.coordinateNormSq k v -
              R⁻¹ * (∑ j, W i j * v j)^2 := by rw [quadratic_one, rowX_quad]
    have hnonneg : 0 ≤ quadratic (1 - rowX W R i) v := by rw [hq]; linarith
    simpa [quadratic, SAP.P005a.dot, dotProduct, star_trivial] using hnonneg

lemma rowX_sum_mean {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ) (R μ : ℝ)
    (horth : ∀ a b : Fin k,
      (∑ i, W i a * W i b) = if a = b then 1 else 0)
    (hμ : μ = 1 / ((n : ℝ) * R)) :
    (n : ℝ)⁻¹ • (∑ i, rowX W R i) = μ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  rw [Matrix.smul_eq_diagonal_mul, Matrix.smul_eq_diagonal_mul]
  ext a b
  have hentry : (∑ i, rowX W R i) a b =
      R⁻¹ * (if a = b then 1 else 0) := by
    simp only [Matrix.sum_apply, rowX]
    rw [← Finset.mul_sum, horth a b]
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply, Matrix.one_apply,
    hentry, hμ, mul_comm]

lemma rowX_quadratic_sum {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ)
    (R : ℝ) (S : Finset (Fin n)) (v : Fin k → ℝ) :
    quadratic (subsetSum (fun i => rowX W R i) S) v =
      AronowAudit.Literature.restrictedNormSq n k W S v / R := by
  calc
    quadratic (subsetSum (fun i => rowX W R i) S) v =
        ∑ i ∈ S, quadratic (rowX W R i) v := by
      unfold quadratic subsetSum SAP.P005a.dot
      rw [Matrix.sum_mulVec]
      simp only [Finset.sum_apply]
      change (∑ j, v j * (∑ i ∈ S, (rowX W R i *ᵥ v) j)) =
        ∑ i ∈ S, ∑ j, v j * (rowX W R i *ᵥ v) j
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = AronowAudit.Literature.restrictedNormSq n k W S v / R := by
      simp_rw [rowX_quad]
      rw [show AronowAudit.Literature.restrictedNormSq n k W S v =
        ∑ i ∈ S, (∑ j, W i j * v j)^2 by rfl, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_eq_mul_inv]
      ring

lemma bad_iff_rowX {n d s : ℕ} (P : SAP.P005a.Population n d)
    (S : Finset (Fin n)) (R μ : ℝ) (hR : 0 < R)
    (hμ : μ = 1 / ((n : ℝ) * R)) :
    AronowAudit.P005.Wave1.CondT8T9_bad (toPopulation P) s S ↔
      ∃ v : Fin (d+1) → ℝ, unitVector v ∧
        (quadratic (subsetSum (fun i => rowX (Wmat P) R i) S) v <
            (s : ℝ)*μ/2 ∨
          2*(s : ℝ)*μ <
            quadratic (subsetSum (fun i => rowX (Wmat P) R i) S) v) := by
  constructor
  · intro hbad
    dsimp only [AronowAudit.P005.Wave1.CondT8T9_bad,
      AronowAudit.P005.Wave1.CondT8T9_W] at hbad
    norm_num at hbad
    rcases hbad with ⟨v, hv, hbad⟩
    have hvdot : dot v v = 1 := by
      simpa [AronowAudit.Literature.coordinateNormSq, SAP.P005a.dot, pow_two] using hv
    have hv' : unitVector v := by
      change dot v v = 1
      exact hvdot
    refine ⟨v, hv', ?_⟩
    rw [rowX_quadratic_sum]
    rcases hbad with hlow | hhigh
    · left
      have hdiv := (div_lt_div_iff_of_pos_right hR).2 hlow
      have heq : ((1/2 : ℝ)*(s : ℝ) / n) / R = (s : ℝ)*μ/2 := by
        rw [hμ]
        field_simp
      have hdiv' : (AronowAudit.Literature.restrictedNormSq n (d+1)
          (Wmat P) S v) / R < ((1/2 : ℝ)*(s : ℝ)/n) / R := by
        simpa [Wmat] using hdiv
      rw [← heq]
      exact hdiv'
    · right
      have hdiv := (div_lt_div_iff_of_pos_right hR).2 hhigh
      have heq : (2*(s : ℝ)/n) / R = 2*(s : ℝ)*μ := by
        rw [hμ]
        field_simp
      rw [← heq]
      exact hdiv
  · rintro ⟨v, hv, hbad⟩
    refine ⟨v, ?_, ?_⟩
    ·
      change dot v v = 1 at hv
      simpa [AronowAudit.Literature.coordinateNormSq, SAP.P005a.dot, pow_two] using hv
    rw [rowX_quadratic_sum] at hbad
    change AronowAudit.Literature.restrictedNormSq n (d+1) (Wmat P) S v <
          (1-(1/2 : ℝ))*(s : ℝ)/n ∨
        (1+(1 : ℝ))*(s : ℝ)/n <
          AronowAudit.Literature.restrictedNormSq n (d+1) (Wmat P) S v
    rcases hbad with hlow | hhigh
    · left
      have heq : ((1/2 : ℝ)*(s : ℝ)/n) / R = (s : ℝ)*μ/2 := by
        rw [hμ]
        field_simp
      have hdiv' := hlow
      rw [← heq] at hdiv'
      have hh := (div_lt_div_iff_of_pos_right hR).1 hdiv'
      simpa only [show (1-(1/2 : ℝ)) = 1/2 by norm_num] using hh
    · right
      have heq : (2*(s : ℝ)/n) / R = 2*(s : ℝ)*μ := by
        rw [hμ]
        field_simp
      have hdiv' : (2*(s : ℝ)/n) / R <
          (AronowAudit.Literature.restrictedNormSq n (d+1) (Wmat P) S v) / R := by
        rw [← heq] at hhigh
        exact hhigh
      have hh := (div_lt_div_iff_of_pos_right hR).1 hdiv'
      simpa only [show (1+(1 : ℝ)) = 2 by norm_num] using hh

end
end SAP.P005a.WH.W2.P.T9_L13

open SAP.P005a.WH.W2.P.T9_L13

theorem SAP.P005a.WH.W2.T9_L13_proof : SAP.P005a.WH.W2.T9_L13 := by
  intro hChernoff
  unfold SAP.P005a.WH.W2.finiteGramControl
  intro ε hε
  let b : ℝ := Real.exp (-(1/8 : ℝ))
  have hb : 0 < b := by positivity
  have hb1 : b < 1 := by
    dsimp [b]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨A, hA, huniform⟩ :=
    AronowAudit.P005.Wave1.CondT8T9_chernoff_uniform b hb hb1 (ε/2) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro n d s P hn hd hP hsn hs
  let Pold := SAP.P005a.Bridge.toPopulation P
  let W := Wmat P
  let R := radius W
  let μ : ℝ := 1 / ((n : ℝ) * R)
  have hPo : AronowAudit.P005.standardized Pold := by
    simpa [Pold, SAP.P005a.Bridge.standardized_eq] using hP
  have horth := AronowAudit.P005.Wave1.CondT8T9_augmented_orthogonal Pold hn hPo
  have horth' : ∀ a b : Fin (d+1), (∑ i, W i a * W i b) = if a = b then 1 else 0 := by
    simpa [W, Wmat, Pold, AronowAudit.P005.Wave1.CondT8T9_W] using horth
  have hRpos : 0 < R := by
    simpa [R, W] using radius_pos_augmented P hn
  have hrow0 := AronowAudit.P005.Wave1.CondT8T9_augmented_row_bound Pold hn hd hPo
  have hrow : (n : ℝ) * R ≤ 2 * (n : ℝ) * kappa P := by
    simpa [R, W, Wmat, Pold, radius, AronowAudit.P005.Wave1.CondT8T9_W,
      SAP.P005a.Bridge.kappa_eq] using hrow0
  have hnR : 0 < (n : ℝ) * R := mul_pos (by exact_mod_cast hn) hRpos
  have hRcap : R ≤ 2 * kappa P := by nlinarith
  have hμpos : 0 < μ := by simp [μ]; positivity
  have hμle : μ ≤ 1 := by
    let i : Fin n := ⟨0, hn⟩
    have hq := row_sq_le_radius W i
    have hcoord : W i 0 = (Real.sqrt (n : ℝ))⁻¹ := by
      simp [W, Wmat, AronowAudit.P005.Wave1.CondT8T9_W, i, SAP.P005a.Bridge.toPopulation]
    have hterm : (W i 0)^2 ≤ ∑ j : Fin (d+1), (W i j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (W i j)) (Finset.mem_univ 0)
    have hsqrt : (Real.sqrt (n : ℝ))^2 = n :=
      Real.sq_sqrt (le_of_lt (by exact_mod_cast hn))
    have hinv : (Real.sqrt (n : ℝ))⁻¹ ^ 2 = 1 / (n : ℝ) := by
      field_simp [hsqrt]
      exact hsqrt.symm
    rw [hcoord, hinv] at hterm
    have hqlo : 1 / (n : ℝ) ≤ R := hterm.trans hq
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_left hqlo hnreal.le
    have hinv' : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
    rw [hinv'] at hmul
    have hnle : 1 ≤ (n : ℝ) * R := by nlinarith [hmul]
    dsimp [μ]
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnle)
  have hmean : (n : ℝ)⁻¹ • (∑ i, rowX W R i) = μ • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) := by
    apply rowX_sum_mean W R μ horth'
    rfl
  have hX : ∀ i : Fin n, (rowX W R i).PosSemidef ∧ matrixLE (rowX W R i) 1 := by
    intro i
    refine ⟨rowX_psd W R hRpos i, rowX_le_one W R hRpos i ?_⟩
    exact (row_sq_le_radius W i)
  have hk : (2 : ℝ) ≤ (d+1 : ℕ) := by exact_mod_cast (show 2 ≤ d+1 by omega)
  have hlog : 0 ≤ Real.log (d+1 : ℕ) := Real.log_nonneg (by linarith)
  have hsample : A * ((n : ℝ) * R) * Real.log (d+1 : ℕ) ≤ (s : ℝ) := by
    have hcoef : (n : ℝ) * R ≤ 2 * (n : ℝ) * kappa P := hrow
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoef hA.le) hlog).trans hs
  let X : Fin n → Matrix (Fin (d+1)) (Fin (d+1)) ℝ := fun i => rowX W R i
  have hX' : ∀ i : Fin n, (X i).PosSemidef ∧ matrixLE (X i) 1 := by
    simpa [X] using hX
  have hmeanX : (n : ℝ)⁻¹ • (∑ i, X i) = μ • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) := by
    simpa [X] using hmean
  have hC := hChernoff n (d+1) s hn (by omega) hsn X hX' μ hμpos hμle hmeanX
  -- The rank-one quadratic form is the row-restricted squared norm divided by R.
  have hbad : probability s (AronowAudit.P005.Wave1.CondT8T9_bad Pold s) =
      probability s (fun S => ∃ v : Fin (d+1) → ℝ, unitVector v ∧
        (quadratic (subsetSum X S) v <
            (s : ℝ)*μ/2 ∨
          2*(s : ℝ)*μ <
            quadratic (subsetSum X S) v)) := by
    classical
    have hfilter : (Finset.filter (AronowAudit.P005.Wave1.CondT8T9_bad Pold s)
        (design n s)) = Finset.filter (fun S => ∃ v : Fin (d+1) → ℝ,
        unitVector v ∧ (quadratic (subsetSum X S) v < (s : ℝ)*μ/2 ∨
          2*(s : ℝ)*μ < quadratic (subsetSum X S) v)) (design n s) := by
      apply Finset.filter_congr
      intro S hS
      simpa [X, W, Wmat, R, μ, Pold] using bad_iff_rowX P S R μ hRpos rfl
    unfold probability
    rw [hfilter]
  have hkbound := huniform (d+1 : ℕ) hk
  have hprod : A * Real.log (d+1 : ℕ) ≤ (s : ℝ) * μ := by
    have hmul := mul_le_mul_of_nonneg_right hsample hμpos.le
    have hident : ((n : ℝ) * R) * μ = 1 := by
      dsimp [μ]
      field_simp
    calc
      A * Real.log (d+1 : ℕ) =
          (A * Real.log (d+1 : ℕ)) * (((n : ℝ) * R) * μ) := by rw [hident]; ring
      _ = A * ((n : ℝ) * R) * Real.log (d+1 : ℕ) * μ := by ring
      _ ≤ (s : ℝ) * μ := hmul
  have hexp : Real.exp (-((s : ℝ) * μ)/8) ≤ Real.rpow b (A * Real.log (d+1 : ℕ)) := by
    have hpow : Real.rpow b (A * Real.log (d+1 : ℕ)) =
        Real.exp (-(A * Real.log (d+1 : ℕ))/8) := by
      change b ^ (A * Real.log (d+1 : ℕ)) = _
      rw [Real.rpow_def_of_pos hb]
      simp [b, Real.log_exp]
      ring
    rw [hpow]
    exact Real.exp_le_exp.mpr (by nlinarith [hprod])
  -- Finish by comparing the fixed Chernoff rate to the uniform scalar bound.
  have : probability s (AronowAudit.P005.Wave1.CondT8T9_bad Pold s) < ε := by
    rw [hbad]
    have hC' : probability s (fun S => ∃ v : Fin (d+1) → ℝ, unitVector v ∧
        (quadratic (subsetSum X S) v < (s : ℝ)*μ/2 ∨
          2*(s : ℝ)*μ < quadratic (subsetSum X S) v)) ≤
        2*(d+1 : ℝ)*Real.rpow b (A*Real.log (d+1 : ℕ)) := by
      apply hC.trans
      have he := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 2*(d+1 : ℝ))
      convert he using 1
      norm_num [Nat.cast_add]
    have hU := huniform (d+1 : ℕ) hk
    have hU' : ((d : ℝ) + 1) * Real.rpow b (A*Real.log (d+1 : ℕ)) < ε/2 := by
      simpa using hU
    have hfinal : 2*((d : ℝ)+1)*Real.rpow b (A*Real.log (d+1 : ℕ)) < ε := by
      calc
        2*((d : ℝ)+1)*Real.rpow b (A*Real.log (d+1 : ℕ)) =
            2 * (((d : ℝ)+1)*Real.rpow b (A*Real.log (d+1 : ℕ))) := by ring
        _ < 2*(ε/2) := mul_lt_mul_of_pos_left hU' (by norm_num)
        _ = ε := by ring
    exact hC'.trans_lt hfinal
  simpa [Pold] using this
