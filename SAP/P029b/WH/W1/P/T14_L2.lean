import SAP.P029b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P029b.WH.W1.P.T14_L2

open Set

private theorem log_tangent_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    Real.log x - Real.log t ≤ (x - t) / t := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx ht)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ht)] at h
  have heq : x / t - 1 = (x - t) / t := by field_simp [ne_of_gt ht]
  rw [heq] at h
  exact h

private theorem log_tangent_lt {x t : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hne : x ≠ t) : Real.log x - Real.log t < (x - t) / t := by
  have hr : x / t ≠ 1 := by
    intro h
    apply hne
    exact (div_eq_one_iff_eq (ne_of_gt ht)).1 h
  have h := Real.log_lt_sub_one_of_pos (div_pos hx ht) hr
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ht)] at h
  have heq : x / t - 1 = (x - t) / t := by field_simp [ne_of_gt ht]
  rw [heq] at h
  exact h

noncomputable def armLog (n k : ℕ) (x : ℝ) : ℝ :=
  (k : ℝ) * Real.log x + ((n-k : ℕ) : ℝ) * Real.log (1-x)

private theorem armLog_tangent_le {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    {x t : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    armLog n k x ≤ armLog n k t +
      ((k : ℝ) - (n : ℝ) * t) / (t * (1-t)) * (x-t) := by
  have hx' : 0 < 1-x := sub_pos.mpr hx.2
  have ht' : 0 < 1-t := sub_pos.mpr ht.2
  have hs := log_tangent_le hx.1 ht.1
  have hf := log_tangent_le hx' ht'
  have hncast : (n : ℝ) = (k : ℝ) + ((n-k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk]
    ring
  have hlin : (k : ℝ) * ((x-t)/t) + ((n-k : ℕ) : ℝ) * ((1-x-(1-t))/(1-t)) =
      ((k : ℝ) - (n : ℝ)*t)/(t*(1-t))*(x-t) := by
    rw [hncast]
    field_simp [ne_of_gt ht.1, ne_of_gt ht']
    <;> ring
  have hs' := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k)
  have hf' := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (n-k))
  unfold armLog
  nlinarith [hlin, hs', hf']

private theorem armLog_tangent_lt {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    {x t : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hne : x ≠ t) :
    armLog n k x < armLog n k t +
      ((k : ℝ) - (n : ℝ) * t) / (t * (1-t)) * (x-t) := by
  have hx' : 0 < 1-x := sub_pos.mpr hx.2
  have ht' : 0 < 1-t := sub_pos.mpr ht.2
  have hs := log_tangent_lt hx.1 ht.1 hne
  have hf := log_tangent_lt hx' ht' (by
    intro heq
    apply hne
    linarith)
  have hncast : (n : ℝ) = (k : ℝ) + ((n-k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk]
    ring
  have hlin : (k : ℝ) * ((x-t)/t) + ((n-k : ℕ) : ℝ) * ((1-x-(1-t))/(1-t)) =
      ((k : ℝ) - (n : ℝ)*t)/(t*(1-t))*(x-t) := by
    rw [hncast]
    field_simp [ne_of_gt ht.1, ne_of_gt ht']
    <;> ring
  by_cases hk0 : k = 0
  · have hnsub : 0 < n-k := by simpa [hk0] using hn
    have hf' := mul_lt_mul_of_pos_left hf (by exact_mod_cast hnsub : (0:ℝ) < ((n-k : ℕ) : ℝ))
    have hs' := mul_le_mul_of_nonneg_left (le_of_lt hs) (Nat.cast_nonneg k)
    unfold armLog
    nlinarith [hlin, hs', hf']
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hs' := mul_lt_mul_of_pos_left hs (by exact_mod_cast hkpos : (0:ℝ) < (k : ℝ))
    have hf' := mul_le_mul_of_nonneg_left (le_of_lt hf) (Nat.cast_nonneg (n-k))
    unfold armLog
    nlinarith [hlin, hs', hf']

private theorem log_binomialKernel {n k : ℕ} (hk : k ≤ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log (BinomialKernelW1 n k x) = armLog n k x := by
  have hxp : 0 < x := hx.1
  have hfp : 0 < 1-x := sub_pos.mpr hx.2
  unfold BinomialKernelW1
  rw [Real.log_mul (pow_ne_zero _ (ne_of_gt hxp)) (pow_ne_zero _ (ne_of_gt hfp)),
    Real.log_pow, Real.log_pow]
  rfl

private theorem binomialKernel_pos {n k : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < BinomialKernelW1 n k x := by
  unfold BinomialKernelW1
  exact mul_pos (pow_pos hx.1 _) (pow_pos (sub_pos.mpr hx.2) _)

private theorem log_saturatedLikelihood {n1 n0 k1 k0 : ℕ} (hk1 : k1 ≤ n1)
    (hk0 : k0 ≤ n0) {p q : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log (SaturatedLikelihoodW1 n1 n0 k1 k0 (p,q)) =
      armLog n1 k1 p + armLog n0 k0 q := by
  change Real.log (BinomialKernelW1 n1 k1 p * BinomialKernelW1 n0 k0 q) = _
  rw [Real.log_mul (ne_of_gt (binomialKernel_pos hp))
      (ne_of_gt (binomialKernel_pos hq)),
    log_binomialKernel hk1 hp, log_binomialKernel hk0 hq]

end SAP.P029b.WH.W1.P.T14_L2

open SAP.P029b.WH.W1.P.T14_L2

 theorem SAP.P029b.WH.W1.T14_L2_proof : SAP.P029b.WH.W1.T14_L2 := by
  intro n1 n0 k1 k0 hn1 hn0 hk1 hk0 hr
  dsimp only
  let t : ℝ := ((k1 : ℝ) + k0) / (n1+n0)
  have hn1r : (0 : ℝ) < n1 := by exact_mod_cast hn1
  have hn0r : (0 : ℝ) < n0 := by exact_mod_cast hn0
  have hNnat : 0 < n1+n0 := by omega
  have hN : (0 : ℝ) < (n1 : ℝ)+n0 := by exact_mod_cast hNnat
  have hr0le : (k0 : ℝ)/n0 ≤ 1 :=
    (div_le_one hn0r).2 (by exact_mod_cast hk0)
  have hk0pos : 0 < k0 := by
    by_contra hnot
    have hz : k0 = 0 := Nat.eq_zero_of_not_pos hnot
    have hrz : (k0 : ℝ)/n0 = 0 := by simp [hz]
    rw [hrz] at hr
    have hnonneg : 0 ≤ (k1 : ℝ)/n1 := by positivity
    linarith
  have hk1lt : k1 < n1 := by
    by_contra hnot
    have heq : k1 = n1 := Nat.le_antisymm hk1 (Nat.not_lt.mp hnot)
    subst k1
    have hrone : (n1 : ℝ)/n1 = 1 := by field_simp [ne_of_gt hn1r]
    rw [hrone] at hr
    linarith
  have hnum : 0 < (k1 : ℝ) + k0 := by positivity
  have hnumlt : (k1 : ℝ) + k0 < (n1 : ℝ) + n0 := by
    have hk1r : (k1 : ℝ) < n1 := by exact_mod_cast hk1lt
    have hk0r : (k0 : ℝ) ≤ n0 := by exact_mod_cast hk0
    linarith
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos hnum hN
  have htlt : t < 1 := by
    dsimp [t]
    exact (div_lt_one hN).2 hnumlt
  have htmem : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨htpos, htlt⟩
  have hrprod : (k1 : ℝ)*n0 < (k0 : ℝ)*n1 :=
    (div_lt_div_iff₀ hn1r hn0r).mp hr
  have hrat : (k1 : ℝ)/n1 < t := by
    apply (div_lt_div_iff₀ hn1r hN).2
    push_cast
    nlinarith [hrprod]
  have hderiv : (k1 : ℝ) - n1*t < 0 := by
    have hh := mul_lt_mul_of_pos_left hrat hn1r
    have hcalc : (n1 : ℝ) * ((k1 : ℝ)/n1) = (k1 : ℝ) := by
      field_simp [ne_of_gt hn1r]
    linarith
  have hbalance : (k1 : ℝ) - n1*t = -((k0 : ℝ) - n0*t) := by
    dsimp [t]
    field_simp [ne_of_gt hN]
    ring
  have hden : 0 < t*(1-t) := mul_pos htpos (sub_pos.mpr htlt)
  have hcoef : (k1 : ℝ)-n1*t < 0 := hderiv
  have htri : (t,t) ∈ ReceiptTriangleW1 := by
    change 0 ≤ t ∧ t ≤ t ∧ t ≤ 1
    exact ⟨le_of_lt htpos, le_rfl, le_of_lt htlt⟩
  refine ⟨htri, ?_⟩
  intro v hv
  have hq0 : 0 ≤ v.2 := hv.1
  have hqp : v.2 ≤ v.1 := hv.2.1
  have hp1 : v.1 ≤ 1 := hv.2.2
  have hp0 : 0 ≤ v.1 := le_trans hq0 hqp
  have hq1 : v.2 ≤ 1 := le_trans hqp hp1
  have hLstar : 0 < SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t) := by
    unfold SaturatedLikelihoodW1
    exact mul_pos (binomialKernel_pos htmem) (binomialKernel_pos htmem)
  have hzero_left : v.1 = 0 → SaturatedLikelihoodW1 n1 n0 k1 k0 v = 0 := by
    intro hpz
    have hqz : v.2 = 0 := le_antisymm (by simpa [hpz] using hqp) hq0
    unfold SaturatedLikelihoodW1 BinomialKernelW1
    simp [hpz, hqz, Nat.ne_of_gt hk0pos]
  have hzero_top : v.1 = 1 → SaturatedLikelihoodW1 n1 n0 k1 k0 v = 0 := by
    intro hpt
    have hsub : 0 < n1-k1 := Nat.sub_pos_of_lt hk1lt
    unfold SaturatedLikelihoodW1 BinomialKernelW1
    simp [hpt, Nat.ne_of_gt hsub]
  have hzero_bottom : v.2 = 0 → SaturatedLikelihoodW1 n1 n0 k1 k0 v = 0 := by
    intro hqz
    unfold SaturatedLikelihoodW1 BinomialKernelW1
    simp [hqz, Nat.ne_of_gt hk0pos]
  have hzero_right : v.2 = 1 → SaturatedLikelihoodW1 n1 n0 k1 k0 v = 0 := by
    intro hqt
    have hpt : v.1 = 1 := le_antisymm hp1 (by simpa [hqt] using hqp)
    exact hzero_top hpt
  have boundary_cert (hz : SaturatedLikelihoodW1 n1 n0 k1 k0 v = 0)
      (hne : v ≠ (t,t)) :
      SaturatedLikelihoodW1 n1 n0 k1 k0 v ≤ SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t) ∧
      (SaturatedLikelihoodW1 n1 n0 k1 k0 v = SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t) ↔
        v = (t,t)) := by
    refine ⟨by rw [hz]; exact le_of_lt hLstar, ?_⟩
    constructor
    · intro he
      rw [hz] at he
      linarith
    · intro hvEq
      exact False.elim (hne hvEq)
  by_cases hpz : v.1 = 0
  · exact boundary_cert (hzero_left hpz) (by
      intro he
      have ht0 : t = 0 := (congrArg Prod.fst he.symm).trans hpz
      linarith)
  · by_cases hpt : v.1 = 1
    · exact boundary_cert (hzero_top hpt) (by
        intro he
        have ht1 : t = 1 := (congrArg Prod.fst he.symm).trans hpt
        linarith)
    · by_cases hqz : v.2 = 0
      · exact boundary_cert (hzero_bottom hqz) (by
          intro he
          have ht0 : t = 0 := (congrArg Prod.snd he.symm).trans hqz
          linarith)
      · by_cases hqt : v.2 = 1
        · exact boundary_cert (hzero_right hqt) (by
            intro he
            have ht1 : t = 1 := (congrArg Prod.snd he.symm).trans hqt
            linarith)
        · have hpint : v.1 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor
            · rcases eq_or_lt_of_le hp0 with h | h
              · exact False.elim (hpz h.symm)
              · exact h
            · rcases lt_or_eq_of_le hp1 with h | h
              · exact h
              · exact False.elim (hpt h)
          have hqint : v.2 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor
            · rcases eq_or_lt_of_le hq0 with h | h
              · exact False.elim (hqz h.symm)
              · exact h
            · rcases lt_or_eq_of_le hq1 with h | h
              · exact h
              · exact False.elim (hqt h)
          have hweak1 := armLog_tangent_le hn1 hk1 hpint htmem
          have hweak0 := armLog_tangent_le hn0 hk0 hqint htmem
          have hcoef0 : ((k0 : ℝ)-n0*t)/(t*(1-t)) = -(((k1 : ℝ)-n1*t)/(t*(1-t))) := by
            rw [hbalance]
            ring
          have hsum : ((k1 : ℝ)-n1*t)/(t*(1-t))*(v.1-t) +
              ((k0 : ℝ)-n0*t)/(t*(1-t))*(v.2-t) =
              ((k1 : ℝ)-n1*t)/(t*(1-t))*(v.1-v.2) := by
            rw [hcoef0]
            ring
          have hbound : ((k1 : ℝ)-n1*t)/(t*(1-t))*(v.1-v.2) ≤ 0 := by
            apply mul_nonpos_of_nonpos_of_nonneg
            · exact div_nonpos_of_nonpos_of_nonneg hcoef.le (le_of_lt hden)
            · exact sub_nonneg.mpr hqp
          have hLv : 0 < SaturatedLikelihoodW1 n1 n0 k1 k0 v := by
            unfold SaturatedLikelihoodW1
            exact mul_pos (binomialKernel_pos hpint) (binomialKernel_pos hqint)
          have hlogle : Real.log (SaturatedLikelihoodW1 n1 n0 k1 k0 v) ≤
              Real.log (SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t)) := by
            rw [log_saturatedLikelihood hk1 hk0 hpint hqint,
              log_saturatedLikelihood hk1 hk0 htmem htmem]
            unfold armLog at hweak1 hweak0 ⊢
            nlinarith [hweak1, hweak0, hsum, hbound]
          have hcompare : SaturatedLikelihoodW1 n1 n0 k1 k0 v ≤
              SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t) := by
            exact (Real.log_le_log_iff hLv hLstar).mp hlogle
          refine ⟨hcompare, ?_⟩
          constructor
          · intro heq
            by_contra hvne
            have hstrictArm : armLog n1 k1 v.1 + armLog n0 k0 v.2 <
                armLog n1 k1 t + armLog n0 k0 t := by
              have hpne : v.1 ≠ t ∨ v.2 ≠ t := by
                by_cases hpeq : v.1 = t
                · right
                  intro hqeq
                  exact hvne (Prod.ext hpeq hqeq)
                · exact Or.inl hpeq
              rcases hpne with hpne | hqne
              · have hs := armLog_tangent_lt hn1 hk1 hpint htmem hpne
                unfold armLog at hs hweak0 ⊢
                nlinarith [hs, hweak0, hsum, hbound]
              · have hs := armLog_tangent_lt hn0 hk0 hqint htmem hqne
                unfold armLog at hs hweak1 ⊢
                nlinarith [hs, hweak1, hsum, hbound]
            have hlogstrict : Real.log (SaturatedLikelihoodW1 n1 n0 k1 k0 v) <
                Real.log (SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t)) := by
              rw [log_saturatedLikelihood hk1 hk0 hpint hqint,
                log_saturatedLikelihood hk1 hk0 htmem htmem]
              exact hstrictArm
            have hlt := (Real.log_lt_log_iff hLv hLstar).mp hlogstrict
            rw [heq] at hlt
            exact (lt_irrefl _ hlt)
          · rintro rfl
            rfl
