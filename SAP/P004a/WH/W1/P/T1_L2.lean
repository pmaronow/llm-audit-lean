import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T1_L2

open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000

private abbrev Block := Assignment 3

private def blockWeight (a : Block) : ℝ := designWeight (w1ThreeP 3) a

private def productExpect {K : ℕ} (F : (Fin K → Block) → ℝ) : ℝ :=
  ∑ b : Fin K → Block, (∏ j, blockWeight (b j)) * F b

private theorem blockWeight_sum : (∑ a : Block, blockWeight a) = 1 := by
  unfold blockWeight designWeight
  rw [← Fintype.prod_sum]
  simp [coin, Fintype.sum_bool]

private theorem productWeight_sum (K : ℕ) :
    (∑ b : Fin K → Block, ∏ j, blockWeight (b j)) = 1 := by
  rw [← Fintype.prod_sum]
  simp [blockWeight_sum]

private theorem productExpect_const {K : ℕ} (c : ℝ) :
    productExpect (K := K) (fun _ => c) = c := by
  unfold productExpect
  rw [← Finset.sum_mul, productWeight_sum, one_mul]

private theorem productExpect_add {K : ℕ} (F G : (Fin K → Block) → ℝ) :
    productExpect (fun b => F b + G b) = productExpect F + productExpect G := by
  unfold productExpect
  simp only [mul_add, Finset.sum_add_distrib]

private theorem productExpect_mul {K : ℕ} (c : ℝ) (F : (Fin K → Block) → ℝ) :
    productExpect (fun b => c * F b) = c * productExpect F := by
  unfold productExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem productExpect_congr {K : ℕ} {F G : (Fin K → Block) → ℝ}
    (h : ∀ b, F b = G b) : productExpect F = productExpect G := by
  unfold productExpect
  apply Finset.sum_congr rfl
  intro b _
  rw [h b]

private theorem productExpect_succ {K : ℕ} (F : (Fin (K+1) → Block) → ℝ) :
    productExpect (K := K+1) F =
      ∑ a : Block, blockWeight a * productExpect (K := K)
        (fun c => F (Fin.cons a c)) := by
  unfold productExpect
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (K+1) => Block))
    (fun b => (∏ j, blockWeight (b j)) * F b)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hcons : (Fin.consEquiv (fun _ : Fin (K+1) => Block)) (a,c) = Fin.cons a c := by
    funext i
    simp only [Fin.consEquiv_apply]
  rw [hcons]
  ring

private theorem productExpect_succ_factor {K : ℕ}
    (f : Block → ℝ) (G : (Fin K → Block) → ℝ) :
    productExpect (K := K+1) (fun b => f (b 0) * G (Fin.tail b)) =
      (∑ a : Block, blockWeight a * f a) * productExpect G := by
  rw [productExpect_succ]
  simp_rw [Fin.cons_zero, Fin.tail_cons]
  simp_rw [productExpect_mul]
  calc
    (∑ a : Block, blockWeight a * (f a * productExpect G)) =
        (∑ a : Block, (blockWeight a * f a) * productExpect G) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a : Block, blockWeight a * f a) * productExpect G := by
      rw [← Finset.sum_mul]

private theorem productExpect_succ_tail {K : ℕ} (G : (Fin K → Block) → ℝ) :
    productExpect (K := K+1) (fun b => G (Fin.tail b)) = productExpect G := by
  calc
    productExpect (K := K+1) (fun b => G (Fin.tail b)) =
        productExpect (fun b => (1:ℝ) * G (Fin.tail b)) := by
          apply productExpect_congr
          intro b
          ring
    _ = (∑ a : Block, blockWeight a * 1) * productExpect G :=
      productExpect_succ_factor (fun _ => 1) G
    _ = productExpect G := by
      simp only [mul_one]
      rw [blockWeight_sum]
      ring

private theorem productExpect_succ_head {K : ℕ} (f : Block → ℝ) :
    productExpect (K := K+1) (fun b => f (b 0)) =
      ∑ a : Block, blockWeight a * f a := by
  calc
    productExpect (K := K+1) (fun b => f (b 0)) =
        productExpect (fun b => f (b 0) * (1:ℝ)) := by
          apply productExpect_congr
          intro b
          ring
    _ = (∑ a : Block, blockWeight a * f a) * productExpect (fun _ => (1:ℝ)) :=
      productExpect_succ_factor f (fun _ => 1)
    _ = ∑ a : Block, blockWeight a * f a := by rw [productExpect_const]; ring

private theorem product_sum_moments (K : ℕ) (g : Block → ℝ)
    (hg0 : ∑ a : Block, blockWeight a * g a = 0)
    (hg2 : ∑ a : Block, blockWeight a * (g a)^2 = 10369/250000)
    (hg4 : ∑ a : Block, blockWeight a * (g a)^4 = 915255049/250000000000) :
    productExpect (K := K) (fun b => ∑ j, g (b j)) = 0 ∧
    productExpect (K := K) (fun b => (∑ j, g (b j))^2) = (K : ℝ)*(10369/250000) ∧
    productExpect (K := K) (fun b => (∑ j, g (b j))^4) =
      (K : ℝ)*(915255049/250000000000) +
        3*(K : ℝ)*((K : ℝ)-1)*(10369/250000)^2 := by
  induction K with
  | zero =>
      have hz : (fun b : Fin 0 → Block => ∑ j, g (b j)) = fun _ => (0:ℝ) := by
        funext b
        simp
      have hz2 : (fun b : Fin 0 → Block => (∑ j, g (b j))^2) = fun _ => (0:ℝ) := by
        funext b
        simp
      have hz4 : (fun b : Fin 0 → Block => (∑ j, g (b j))^4) = fun _ => (0:ℝ) := by
        funext b
        simp
      constructor
      · rw [hz, productExpect_const]
      constructor
      · rw [hz2, productExpect_const]
        norm_num
      · rw [hz4, productExpect_const]
        norm_num
  | succ K ih =>
      rcases ih with ⟨ih1, ih2, ih4⟩
      let S : (Fin K → Block) → ℝ := fun c => ∑ j, g (c j)
      have hsum (a : Block) (c : Fin K → Block) :
          (∑ j : Fin (K+1), g ((Fin.cons a c : Fin (K+1) → Block) j)) = g a + S c := by
        let q : Fin (K+1) → Block := Fin.cons a c
        rw [Fin.sum_univ_succ]
        simp [q, S, Fin.cons_zero, Fin.cons_succ]
      have htail1 : productExpect (K := K+1) (fun b => S (Fin.tail b)) = 0 := by
        calc
          productExpect (K := K+1) (fun b => S (Fin.tail b)) = productExpect S :=
            productExpect_succ_tail S
          _ = 0 := by simpa [S] using ih1
      have hhead1 : productExpect (K := K+1) (fun b => g (b 0)) = 0 := by
        calc
          productExpect (K := K+1) (fun b => g (b 0)) =
              ∑ a : Block, blockWeight a * g a := productExpect_succ_head g
          _ = 0 := hg0
      have hfirst :
          productExpect (K := K+1) (fun b => ∑ j, g (b j)) = 0 := by
        have heq : (fun b : Fin (K+1) → Block => ∑ j, g (b j)) =
            fun b => S (Fin.tail b) + g (b 0) := by
          funext b
          have := hsum (b 0) (Fin.tail b)
          have hb : (Fin.cons (b 0) (Fin.tail b) : Fin (K+1) → Block) = b := by
            funext j
            simp
          calc
            (∑ j, g (b j)) =
                ∑ j, g ((Fin.cons (b 0) (Fin.tail b) : Fin (K+1) → Block) j) := by
              exact congrArg (fun q : Fin (K+1) → Block => ∑ j, g (q j)) hb.symm
            _ = g (b 0) + S (Fin.tail b) := this
            _ = S (Fin.tail b) + g (b 0) := by ring
        rw [heq, productExpect_add, htail1, hhead1]
        ring
      have htail2 : productExpect (K := K+1) (fun b => (S (Fin.tail b))^2) =
          (K : ℝ)*(10369/250000) := by
        calc
          productExpect (K := K+1) (fun b => (S (Fin.tail b))^2) =
              productExpect (fun c => (S c)^2) :=
                productExpect_succ_tail (fun c => (S c)^2)
          _ = (K : ℝ)*(10369/250000) := by simpa [S] using ih2
      have hcross2 : productExpect (K := K+1)
          (fun b => 2*(g (b 0) * S (Fin.tail b))) = 0 := by
        rw [productExpect_mul]
        rw [productExpect_succ_factor g S]
        simp [hg0]
      have hhead2 : productExpect (K := K+1) (fun b => (g (b 0))^2) =
          10369/250000 := by
        calc
          productExpect (K := K+1) (fun b => (g (b 0))^2) =
              ∑ a : Block, blockWeight a * (g a)^2 :=
                productExpect_succ_head (fun a => (g a)^2)
          _ = 10369/250000 := hg2
      have hsecond : productExpect (K := K+1)
          (fun b => (∑ j, g (b j))^2) = ((K+1 : ℕ) : ℝ)*(10369/250000) := by
        have heq : (fun b : Fin (K+1) → Block => (∑ j, g (b j))^2) =
            fun b => (S (Fin.tail b))^2 + 2*(g (b 0)*S (Fin.tail b)) + (g (b 0))^2 := by
          funext b
          have hb : (Fin.cons (b 0) (Fin.tail b) : Fin (K+1) → Block) = b := by
            funext j
            simp
          have hs : (∑ j, g (b j)) = g (b 0) + S (Fin.tail b) := by
            calc
              (∑ j, g (b j)) =
                  ∑ j, g ((Fin.cons (b 0) (Fin.tail b) : Fin (K+1) → Block) j) := by
                exact congrArg (fun q : Fin (K+1) → Block => ∑ j, g (q j)) hb.symm
              _ = g (b 0) + S (Fin.tail b) := hsum (b 0) (Fin.tail b)
          rw [hs]
          ring
        rw [heq, productExpect_add, productExpect_add, htail2, hcross2, hhead2]
        push_cast
        ring
      have htail4 : productExpect (K := K+1) (fun b => (S (Fin.tail b))^4) =
          (K : ℝ)*(915255049/250000000000) +
            3*(K : ℝ)*((K : ℝ)-1)*(10369/250000)^2 := by
        calc
          productExpect (K := K+1) (fun b => (S (Fin.tail b))^4) =
              productExpect (fun c => (S c)^4) :=
                productExpect_succ_tail (fun c => (S c)^4)
          _ = (K : ℝ)*(915255049/250000000000) +
              3*(K : ℝ)*((K : ℝ)-1)*(10369/250000)^2 := by simpa [S] using ih4
      have hcross41 : productExpect (K := K+1)
          (fun b => 4*(g (b 0)*(S (Fin.tail b))^3)) = 0 := by
        rw [productExpect_mul, productExpect_succ_factor g (fun c => (S c)^3)]
        simp [hg0]
      have hcross42 : productExpect (K := K+1)
          (fun b => 6*((g (b 0))^2*(S (Fin.tail b))^2)) =
          6*(10369/250000)*((K : ℝ)*(10369/250000)) := by
        rw [productExpect_mul, productExpect_succ_factor (fun a => (g a)^2)
          (fun c => (S c)^2)]
        have hi2 : productExpect (fun c => (S c)^2) = (K : ℝ)*(10369/250000) := by
          simpa [S] using ih2
        rw [hi2, hg2]
        ring
      have hcross43 : productExpect (K := K+1)
          (fun b => 4*((g (b 0))^3*S (Fin.tail b))) = 0 := by
        rw [productExpect_mul, productExpect_succ_factor (fun a => (g a)^3) S]
        have hi1 : productExpect S = 0 := by simpa [S] using ih1
        simp [hi1]
      have hhead4 : productExpect (K := K+1) (fun b => (g (b 0))^4) =
          915255049/250000000000 := by
        calc
          productExpect (K := K+1) (fun b => (g (b 0))^4) =
              ∑ a : Block, blockWeight a * (g a)^4 :=
                productExpect_succ_head (fun a => (g a)^4)
          _ = 915255049/250000000000 := hg4
      have hfourth : productExpect (K := K+1)
          (fun b => (∑ j, g (b j))^4) =
          (((K+1 : ℕ) : ℝ)*(915255049/250000000000) +
            3*((K+1 : ℕ) : ℝ)*(((K+1 : ℕ) : ℝ)-1)*(10369/250000)^2) := by
        have heq : (fun b : Fin (K+1) → Block => (∑ j, g (b j))^4) = fun b =>
            (S (Fin.tail b))^4 + 4*(g (b 0)*(S (Fin.tail b))^3) +
            6*((g (b 0))^2*(S (Fin.tail b))^2) +
            4*((g (b 0))^3*S (Fin.tail b)) + (g (b 0))^4 := by
          funext b
          have hb : (Fin.cons (b 0) (Fin.tail b) : Fin (K+1) → Block) = b := by
            funext j
            simp
          have hs : (∑ j, g (b j)) = g (b 0) + S (Fin.tail b) := by
            calc
              (∑ j, g (b j)) =
                  ∑ j, g ((Fin.cons (b 0) (Fin.tail b) : Fin (K+1) → Block) j) := by
                exact congrArg (fun q : Fin (K+1) → Block => ∑ j, g (q j)) hb.symm
              _ = g (b 0) + S (Fin.tail b) := hsum (b 0) (Fin.tail b)
          rw [hs]
          ring
        rw [heq, productExpect_add, productExpect_add, productExpect_add,
          productExpect_add, htail4, hcross41, hcross42, hcross43, hhead4]
        push_cast
        ring
      exact ⟨hfirst, hsecond, hfourth⟩

private theorem expect_div {N : ℕ} (p : Fin N → ℝ) (F : Assignment N → ℝ)
    (c : ℝ) : expect p (fun z => F z / c) = expect p F / c := by
  unfold expect
  simp only [← mul_div_assoc, Finset.sum_div]

private def blockIndexEquiv (K : ℕ) : Fin K × Fin 3 ≃ Fin (3*K) :=
  finProdFinEquiv.trans (finCongr (by omega))

private theorem blockIndexEquiv_apply (K : ℕ) (j : Fin K) (t : Fin 3) :
    blockIndexEquiv K (j,t) = w1ThreeBlockIndex j t := by
  apply Fin.ext
  simp [blockIndexEquiv, finProdFinEquiv_apply_val, w1ThreeBlockIndex]
  <;> omega
  <;> omega

private theorem block_sum_reindex (K : ℕ) (f : Fin (3*K) → ℝ) :
    (∑ i : Fin (3*K), f i) =
      ∑ j : Fin K, ∑ t : Fin 3, f (w1ThreeBlockIndex j t) := by
  rw [← Equiv.sum_comp (blockIndexEquiv K) f]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  rw [blockIndexEquiv_apply]

private theorem propensity_block_index (K : ℕ) (j : Fin K) (t : Fin 3) :
    w1ThreeP (3*K) (w1ThreeBlockIndex j t) = w1ThreeP 3 t := by
  have hpN : w1ThreeP (3*K) = fun i =>
      AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
    AronowAudit.P004.Wave1.DecideP004T1_propensities (3*K)
  have hp3 : w1ThreeP 3 = fun i =>
      AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
    AronowAudit.P004.Wave1.DecideP004T1_propensities 3
  rw [hpN, hp3]
  simp [w1ThreeBlockIndex, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt t.isLt]

private theorem three_linear_difference (K : ℕ) (hK : 0 < K)
    (z : Assignment (3*K)) :
    Real.sqrt (3*K : ℕ) *
        (w1ThreeLinear w1ThreeA (3*K) z-w1ThreeLinear w1ThreeB (3*K) z) =
      w1ThreeU K z := by
  let N := 3*K
  let S : ℝ := ∑ i : Fin N,
    w1ThreeD (i.val % 3) * (bit (z i)-w1ThreeP N i)
  have hd : w1ThreeLinear w1ThreeA N z-w1ThreeLinear w1ThreeB N z = S/N := by
    dsimp [S]
    unfold w1ThreeLinear
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w1ThreeD]
    ring
  have hblocks : S = ∑ j : Fin K, w1ThreeBlock z j := by
    dsimp [S]
    rw [block_sum_reindex]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro t _
    have hp := propensity_block_index K j t
    have hp' : w1ThreeP N ⟨3*j.val+t.val, by omega⟩ = w1ThreeP 3 t := by
      simpa [N, w1ThreeBlockIndex] using hp
    simp only [w1ThreeBlock, w1ThreeBlockIndex]
    rw [hp']
    have hm : (3*j.val+t.val)%3 = t.val := by omega
    simp only [hm]
  have hsqrt : (Real.sqrt ((3*K : ℕ) : ℝ))^2 = ((3*K : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hden : ((3*K : ℕ) : ℝ) ≠ 0 := by positivity
  have hroot : Real.sqrt ((3*K : ℕ) : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
  rw [hd, show (3*K : ℕ)=N from rfl]
  dsimp [S] at hblocks ⊢
  rw [hblocks]
  unfold w1ThreeU
  change Real.sqrt ((3*K : ℕ) : ℝ) *
      ((∑ j : Fin K, w1ThreeBlock z j)/((3*K : ℕ) : ℝ)) =
    (∑ j : Fin K, w1ThreeBlock z j)/Real.sqrt ((3*K : ℕ) : ℝ)
  field_simp [hden, hroot]
  linear_combination (∑ j : Fin K, w1ThreeBlock z j) * hsqrt

end
end SAP.P004a.WH.W1.P.T1_L2

open SAP.P004a.WH.W1
open SAP.P004a.WH.W1.P.T1_L2
theorem SAP.P004a.WH.W1.T1_L2_proof : SAP.P004a.WH.W1.T1_L2 := by
  intro hLaw K hK
  have h0 : expect (w1ThreeP 3) w1OneBlock = 0 := hLaw.2.1
  have h2 : expect (w1ThreeP 3) (fun z => (w1OneBlock z)^2) =
      10369/250000 := by
    have hh := hLaw.2.2.1
    norm_num at hh ⊢
    exact hh
  have h4 : expect (w1ThreeP 3) (fun z => (w1OneBlock z)^4) =
      915255049/250000000000 := hLaw.2.2.2
  have hm := product_sum_moments K w1OneBlock h0 h2 h4
  refine ⟨three_linear_difference K hK, ?_, ?_⟩
  · have he := hLaw.1 K (fun x => (∑ j, x j)^2)
    have hs : expect (w1ThreeP (3*K)) (fun z => (∑ j, w1ThreeBlock z j)^2) =
        (K : ℝ)*(10369/250000) := by
      simpa [productExpect] using he.trans hm.2.1
    have hscale : ∀ z : Assignment (3*K), (w1ThreeU K z)^2 =
        (∑ j, w1ThreeBlock z j)^2/(3*K : ℝ) := by
      intro z
      unfold w1ThreeU
      change ((∑ j, w1ThreeBlock z j)/Real.sqrt ((3*K : ℕ) : ℝ))^2 = _
      rw [div_pow]
      rw [Real.sq_sqrt (show (0:ℝ) ≤ ((3*K : ℕ) : ℝ) by positivity)]
      norm_cast
    rw [show (fun z : Assignment (3*K) => (w1ThreeU K z)^2) =
        fun z => (∑ j, w1ThreeBlock z j)^2/(3*K : ℝ) from funext hscale]
    rw [expect_div, hs]
    have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
    field_simp
    <;> norm_num
  · have he := hLaw.1 K (fun x => (∑ j, x j)^4)
    have hs : expect (w1ThreeP (3*K)) (fun z => (∑ j, w1ThreeBlock z j)^4) =
        (K : ℝ)*(915255049/250000000000) +
          3*(K : ℝ)*((K : ℝ)-1)*(10369/250000)^2 := by
      simpa [productExpect] using he.trans hm.2.2
    have hscale : ∀ z : Assignment (3*K), (w1ThreeU K z)^4 =
        (∑ j, w1ThreeBlock z j)^4/(3*K : ℝ)^2 := by
      intro z
      unfold w1ThreeU
      change ((∑ j, w1ThreeBlock z j)/Real.sqrt ((3*K : ℕ) : ℝ))^4 = _
      rw [div_pow]
      have hsqrt : (Real.sqrt ((3*K : ℕ) : ℝ))^2 = ((3*K : ℕ) : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hsqrt4 : (Real.sqrt ((3*K : ℕ) : ℝ))^4 = (((3*K : ℕ) : ℝ)^2) := by
        calc
          (Real.sqrt ((3*K : ℕ) : ℝ))^4 =
              ((Real.sqrt ((3*K : ℕ) : ℝ))^2)^2 := by ring
          _ = _ := by rw [hsqrt]
      rw [hsqrt4]
      norm_cast
    rw [show (fun z : Assignment (3*K) => (w1ThreeU K z)^4) =
        fun z => (∑ j, w1ThreeBlock z j)^4/(3*K : ℝ)^2 from funext hscale]
    rw [expect_div, hs]
    have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
    field_simp
    <;> norm_num
    <;> ring

