import SAP.P029b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W1.P.T14_L1

open Set

lemma interior_log_kernel (n k : ℕ) (hk : k ≤ n) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.log (BinomialKernelW1 n k x) =
      AronowAudit.P029.cellLog (k : ℝ) (n - k : ℝ) x := by
  have hx0 : 0 < x := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  unfold BinomialKernelW1 AronowAudit.P029.cellLog
  rw [Real.log_mul (pow_ne_zero _ (ne_of_gt hx0))
      (pow_ne_zero _ (ne_of_gt hx1)), Real.log_pow, Real.log_pow]
  rw [Nat.cast_sub hk]

end SAP.P029b.WH.W1.P.T14_L1

open Set SAP.P029b.WH.W1.P.T14_L1

theorem SAP.P029b.WH.W1.T14_L1_proof : SAP.P029b.WH.W1.T14_L1 := by
  intro n k hn hk
  by_cases hk0 : k = 0
  · subst k
    have hr0 : (0 : ℝ) / (n : ℝ) = 0 := by simp
    constructor
    · simp [BinomialKernelW1, hr0]
    · intro p hp
      have hbase : 0 ≤ 1 - p := by linarith [hp.2]
      have hbase1 : 1 - p ≤ 1 := by linarith [hp.1]
      constructor
      · simpa [BinomialKernelW1, hr0] using (pow_le_one₀ hbase hbase1 : (1 - p) ^ n ≤ 1)
      · constructor
        · intro he
          have he' : (1 - p) ^ n = 1 := by
            simpa [BinomialKernelW1, hr0] using he
          have he'' : (1 - p) ^ n = (1 : ℝ) ^ n := by
            simpa only [one_pow] using he'
          have hb : 1 - p = 1 :=
            (pow_left_inj₀ hbase (by norm_num) (Nat.ne_of_gt hn)).1 he''
          linarith
        · intro he
          have hp0 : p = 0 := by simpa [hr0] using he
          subst p
          simp [BinomialKernelW1, hr0]
  · by_cases hkn : k = n
    · subst k
      have hr1 : (n : ℝ) / (n : ℝ) = 1 := div_self (ne_of_gt (Nat.cast_pos.mpr hn))
      constructor
      · simp [BinomialKernelW1, hr1]
      · intro p hp
        constructor
        · simpa [BinomialKernelW1, hr1] using
            (pow_le_one₀ hp.1 hp.2 : p ^ n ≤ 1)
        · constructor
          · intro he
            have he' : p ^ n = 1 := by
              simpa [BinomialKernelW1, hr1] using he
            have he'' : p ^ n = (1 : ℝ) ^ n := by
              simpa only [one_pow] using he'
            have hb : p = 1 :=
              (pow_left_inj₀ hp.1 (by norm_num) (Nat.ne_of_gt hn)).1 he''
            simpa [hr1] using hb
          · intro he
            have hp1 : p = 1 := by simpa [hr1] using he
            subst p
            simp [BinomialKernelW1, hr1]
    · have hkne : k ≠ n := hkn
      have hklt : k < n := lt_of_le_of_ne hk hkne
      have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
      have hfr : 0 < (n - k : ℝ) := sub_pos.mpr (by exact_mod_cast hklt)
      have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      let S : ℝ := (k : ℝ)
      let F : ℝ := (n - k : ℝ)
      have hS : 0 < S := by simpa [S] using hkr
      have hF : 0 < F := by simpa [F] using hfr
      have hsum : S + F = (n : ℝ) := by
        dsimp [S, F]
        ring
      have hrate : (k : ℝ) / (n : ℝ) = S / (S + F) := by
        rw [hsum]
      have hcert := AronowAudit.P029.weighted_cell_unique_max S F hS hF
      have hrateI : (k : ℝ) / (n : ℝ) ∈ Ioo (0 : ℝ) 1 := by
        rw [hrate]
        exact hcert.1
      have hcenter : 0 < BinomialKernelW1 n k ((k : ℝ) / (n : ℝ)) := by
        have hrpow : 0 < ((k : ℝ) / (n : ℝ)) ^ k :=
          pow_pos (div_pos hkr hnr) k
        have hfbase : 0 < 1 - (k : ℝ) / (n : ℝ) := by
          exact sub_pos.mpr hrateI.2
        have hfpow : 0 < (1 - (k : ℝ) / (n : ℝ)) ^ (n - k) := pow_pos hfbase _
        simpa [BinomialKernelW1] using mul_pos hrpow hfpow
      constructor
      · exact hcenter
      · intro p hp
        by_cases hp0 : p = 0
        · subst p
          have hzero : BinomialKernelW1 n k 0 = 0 := by
            simp [BinomialKernelW1, Nat.ne_of_gt (Nat.pos_of_ne_zero hk0)]
          refine ⟨by rw [hzero]; exact le_of_lt hcenter, ?_⟩
          constructor
          · intro he
            rw [hzero] at he
            linarith
          · intro he
            have : (0 : ℝ) = (k : ℝ) / (n : ℝ) := he
            linarith [hrateI.1]
        · by_cases hp1 : p = 1
          · subst p
            have hzero : BinomialKernelW1 n k 1 = 0 := by
              simp [BinomialKernelW1, Nat.ne_of_gt (Nat.sub_pos_of_lt hklt)]
            refine ⟨by rw [hzero]; exact le_of_lt hcenter, ?_⟩
            constructor
            · intro he
              rw [hzero] at he
              linarith
            · intro he
              have : (1 : ℝ) = (k : ℝ) / (n : ℝ) := he
              linarith [hrateI.2]
          · have hpI : p ∈ Ioo (0 : ℝ) 1 := by
              constructor
              · exact lt_of_le_of_ne hp.1 (Ne.symm hp0)
              · exact lt_of_le_of_ne hp.2 hp1
            have hplog := interior_log_kernel n k hk p hpI
            have hrlog := interior_log_kernel n k hk ((k : ℝ) / (n : ℝ)) hrateI
            have hposp : 0 < BinomialKernelW1 n k p := by
              unfold BinomialKernelW1
              exact mul_pos (pow_pos hpI.1 _) (pow_pos (sub_pos.mpr hpI.2) _)
            have hposr : 0 < BinomialKernelW1 n k ((k : ℝ) / (n : ℝ)) := hcenter
            have hcell := (hcert.2 p hpI).1
            have hkernel :
                BinomialKernelW1 n k p ≤ BinomialKernelW1 n k ((k : ℝ) / (n : ℝ)) := by
              apply (Real.log_le_log_iff hposp hposr).1
              rw [hplog, hrlog, hrate]
              exact hcell
            refine ⟨hkernel, ?_⟩
            constructor
            · intro he
              have hecell : AronowAudit.P029.cellLog S F p =
                  AronowAudit.P029.cellLog S F (S / (S + F)) := by
                calc
                  AronowAudit.P029.cellLog S F p = Real.log (BinomialKernelW1 n k p) := hplog.symm
                  _ = Real.log (BinomialKernelW1 n k ((k : ℝ) / (n : ℝ))) := congrArg Real.log he
                  _ = AronowAudit.P029.cellLog S F (S / (S + F)) := by
                    rw [hrlog, hrate]
              have hu := (hcert.2 p hpI).2.1 hecell
              rw [← hrate] at hu
              exact hu
            · intro he
              subst p
              rfl
