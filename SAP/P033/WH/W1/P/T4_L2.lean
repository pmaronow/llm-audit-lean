import SAP.P033.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P033.WH.W1.P.T4_L2

open scoped BigOperators

noncomputable section

lemma fintype_mul_sum {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    a * (∑ i, f i) = ∑ i, a * f i := by
  simpa using (Finset.mul_sum Finset.univ f a)

lemma fintype_sum_mul {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ) :
    (∑ i, f i) * a = ∑ i, f i * a := by
  simpa using (Finset.sum_mul Finset.univ f a)

lemma fintype_sum_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  calc
    (∑ a, ∑ b, f a b) = ∑ ab : α × β, f ab.1 ab.2 :=
      (Fintype.sum_prod_type' (fun a b => f a b)).symm
    _ = ∑ ba : β × α, f ba.2 ba.1 :=
      Fintype.sum_equiv (Equiv.prodComm α β) _ _ (by intro ab; rfl)
    _ = ∑ b, ∑ a, f a b := Fintype.sum_prod_type' (fun b a => f a b)

lemma gridGram_posDef {ι : Type*} [Fintype ι] (x w : ι → ℝ) (p : ℕ)
    (hw₀ : ∀ i, 0 ≤ w i)
    (heval : ∀ c : Fin (p+1) → ℝ, c ≠ 0 →
      ∃ i, 0 < w i ∧ (∑ r, c r * x i ^ r.val) ≠ 0) :
    (wholeGridGram x w p).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    simp [wholeGridGram, Nat.add_comm]
  · intro c hc
    let ev : ι → ℝ := fun i => ∑ r, c r * x i ^ r.val
    have hquad : star c ⬝ᵥ (wholeGridGram x w p).mulVec c =
        ∑ i, w i * (ev i)^2 := by
      simp only [dotProduct, Matrix.mulVec, wholeGridGram]
      simp_rw [star_trivial, fintype_sum_mul, pow_add]
      simp_rw [fintype_mul_sum]
      have hswap :
          (∑ r, ∑ s, ∑ i, c r * (w i * (x i ^ r.val * x i ^ s.val) * c s)) =
          ∑ i, ∑ r, ∑ s, c r * (w i * (x i ^ r.val * x i ^ s.val) * c s) := by
        calc
          _ = ∑ r, ∑ i, ∑ s,
                c r * (w i * (x i ^ r.val * x i ^ s.val) * c s) := by
              congr 1
              funext r
              exact fintype_sum_comm _
          _ = _ := fintype_sum_comm _
      rw [hswap]
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ r, ∑ s, c r * (w i * (x i ^ r.val * x i ^ s.val) * c s)) =
            w i * (∑ r, c r * x i ^ r.val) * (∑ s, c s * x i ^ s.val) := by
          calc
            _ = ∑ r, ∑ s, w i *
                ((c r * x i ^ r.val) * (c s * x i ^ s.val)) := by
                  apply Finset.sum_congr rfl
                  intro r _
                  apply Finset.sum_congr rfl
                  intro s _
                  ring
            _ = w i * ∑ r, ∑ s,
                (c r * x i ^ r.val) * (c s * x i ^ s.val) := by
                  simp_rw [← fintype_mul_sum]
            _ = w i * ((∑ r, c r * x i ^ r.val) *
                (∑ s, c s * x i ^ s.val)) := by
                  simpa using congrArg (fun z : ℝ => w i * z)
                    ((Fintype.sum_mul_sum _ _).symm)
            _ = (w i * (∑ r, c r * x i ^ r.val)) *
                (∑ s, c s * x i ^ s.val) := by ring
        _ = w i * (ev i)^2 := by simp [ev, pow_two] <;> ring
    rw [hquad]
    obtain ⟨i, hiw, hie⟩ := heval c hc
    apply Finset.sum_pos' (fun i _ => mul_nonneg (hw₀ i) (sq_nonneg (ev i)))
    exact ⟨i, Finset.mem_univ _, mul_pos hiw (sq_pos_of_ne_zero hie)⟩

lemma no_three_roots (x : Fin 3 → ℝ) (h01 : x 0 ≠ x 1)
    (h12 : x 1 ≠ x 2) (h02 : x 0 ≠ x 2)
    (p : ℕ) (hp : p = 1 ∨ p = 2) (c : Fin (p+1) → ℝ) (hc : c ≠ 0) :
    ∃ k : Fin 3, (∑ r, c r * x k ^ r.val) ≠ 0 := by
  classical
  have hnot : ¬ ∀ k : Fin 3, (∑ r, c r * x k ^ r.val) = 0 := by
    intro hall
    rcases hp with hp | hp
    · subst p
      have h0 : c 0 + c 1 * x 0 = 0 := by simpa using hall 0
      have h1 : c 0 + c 1 * x 1 = 0 := by simpa using hall 1
      have hmul : c 1 * (x 1 - x 0) = 0 := by nlinarith
      have hb : c 1 = 0 := by
        rcases mul_eq_zero.mp hmul with h | h
        · exact h
        · exact False.elim ((sub_ne_zero.mpr (Ne.symm h01)) h)
      have ha : c 0 = 0 := by rw [hb] at h0; linarith
      apply hc
      funext r
      fin_cases r <;> simp [ha, hb]
    · subst p
      have h0 : c 0 + (c 1 * x 0 + c 2 * x 0 ^ 2) = 0 := by simpa [Fin.sum_univ_succ] using hall 0
      have h1 : c 0 + (c 1 * x 1 + c 2 * x 1 ^ 2) = 0 := by simpa [Fin.sum_univ_succ] using hall 1
      have h2 : c 0 + (c 1 * x 2 + c 2 * x 2 ^ 2) = 0 := by simpa [Fin.sum_univ_succ] using hall 2
      have hf01 : (x 1 - x 0) * (c 1 + c 2 * (x 0 + x 1)) = 0 := by
        calc
          _ = (c 0 + (c 1 * x 1 + c 2 * x 1 ^ 2)) -
              (c 0 + (c 1 * x 0 + c 2 * x 0 ^ 2)) := by ring
          _ = 0 := by rw [h1, h0]; ring
      have hb01 : c 1 + c 2 * (x 0 + x 1) = 0 := by
        rcases mul_eq_zero.mp hf01 with h | h
        · exact False.elim ((sub_ne_zero.mpr (Ne.symm h01)) h)
        · exact h
      have hf12 : (x 2 - x 1) * (c 1 + c 2 * (x 1 + x 2)) = 0 := by
        calc
          _ = (c 0 + (c 1 * x 2 + c 2 * x 2 ^ 2)) -
              (c 0 + (c 1 * x 1 + c 2 * x 1 ^ 2)) := by ring
          _ = 0 := by rw [h2, h1]; ring
      have hb12 : c 1 + c 2 * (x 1 + x 2) = 0 := by
        rcases mul_eq_zero.mp hf12 with h | h
        · exact False.elim ((sub_ne_zero.mpr (Ne.symm h12)) h)
        · exact h
      have hc2 : c 2 = 0 := by
        have hh : c 2 * (x 0 - x 2) = 0 := by nlinarith
        rcases mul_eq_zero.mp hh with h | h
        · exact h
        · exact False.elim ((sub_ne_zero.mpr h02) h)
      have hc1 : c 1 = 0 := by rw [hc2] at hb01; linarith
      have hc0 : c 0 = 0 := by rw [hc1, hc2] at h0; linarith
      apply hc
      funext r
      fin_cases r <;> simp [hc0, hc1, hc2]
  by_contra h
  apply hnot
  intro k
  by_contra hk
  exact h ⟨k, hk⟩

end
end SAP.P033.WH.W1.P.T4_L2

namespace SAP.P033.WH.W1.P.T4_L2

def firstNode (n : ℕ) (hn : 3 ≤ n) (k : Fin 3) : Fin n := ⟨k.val, by omega⟩

def physicalNode (n : ℕ) (hn : 3 ≤ n) (k : Fin 3) : Fin (n*(n+1)) × Fin 5 :=
  (wholeActiveIndex n (firstNode n hn k), 0)

end SAP.P033.WH.W1.P.T4_L2

theorem SAP.P033.WH.W1.T4_L2_proof : SAP.P033.WH.W1.T4_L2 := by
  intro n hn hgeo
  classical
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnormPos : ∀ j : Fin n, 0 < shrinkingKernel n j := by
    intro j
    rw [← hgeo.2.2.2.2.1 j]
    apply (hgeo.2.2.1 (wholeActiveIndex n j)).2
    simp [wholeActiveIndex]
  have hnormNN : ∀ j : Fin n, 0 ≤ shrinkingKernel n j :=
    fun j => (hnormPos j).le
  let hnormNodes : Fin 3 → ℝ := fun k =>
    shrinkingDistance n (SAP.P033.WH.W1.P.T4_L2.firstNode n hn k)
  have hdenNorm : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnorm0 : hnormNodes 0 = 1 / ((n : ℝ) + 1) := by
    simp [hnormNodes, SAP.P033.WH.W1.P.T4_L2.firstNode, shrinkingDistance]
  have hnorm1 : hnormNodes 1 = 2 / ((n : ℝ) + 1) := by
    simp [hnormNodes, SAP.P033.WH.W1.P.T4_L2.firstNode, shrinkingDistance]
    ring
  have hnorm2 : hnormNodes 2 = 3 / ((n : ℝ) + 1) := by
    simp [hnormNodes, SAP.P033.WH.W1.P.T4_L2.firstNode, shrinkingDistance]
    ring
  have hnorm01 : hnormNodes 0 ≠ hnormNodes 1 := by
    rw [hnorm0, hnorm1]
    intro he
    field_simp [hdenNorm] at he
    norm_num at he
  have hnorm12 : hnormNodes 1 ≠ hnormNodes 2 := by
    rw [hnorm1, hnorm2]
    intro he
    field_simp [hdenNorm] at he
    norm_num at he
  have hnorm02 : hnormNodes 0 ≠ hnormNodes 2 := by
    rw [hnorm0, hnorm2]
    intro he
    field_simp [hdenNorm] at he
    norm_num at he
  have hphysNN : ∀ ji : Fin (n*(n+1)) × Fin 5,
      0 ≤ wholePhysicalKernel n ji.1 := by
    intro ji
    exact le_max_left 0 _
  let hphysNodes : Fin 3 → ℝ := fun k =>
    wholePhysicalDistance n
      (wholeActiveIndex n (SAP.P033.WH.W1.P.T4_L2.firstNode n hn k))
  have hdenPhys : (n : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  have hphys0 : hphysNodes 0 = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    simp [hphysNodes, wholePhysicalDistance, wholeActiveIndex,
      SAP.P033.WH.W1.P.T4_L2.firstNode]
  have hphys1 : hphysNodes 1 = 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    simp [hphysNodes, wholePhysicalDistance, wholeActiveIndex,
      SAP.P033.WH.W1.P.T4_L2.firstNode]
    ring
  have hphys2 : hphysNodes 2 = 3 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    simp [hphysNodes, wholePhysicalDistance, wholeActiveIndex,
      SAP.P033.WH.W1.P.T4_L2.firstNode]
    ring
  have hphys01 : hphysNodes 0 ≠ hphysNodes 1 := by
    rw [hphys0, hphys1]
    intro he
    field_simp [hdenPhys] at he
    norm_num at he
  have hphys12 : hphysNodes 1 ≠ hphysNodes 2 := by
    rw [hphys1, hphys2]
    intro he
    field_simp [hdenPhys] at he
    norm_num at he
  have hphys02 : hphysNodes 0 ≠ hphysNodes 2 := by
    rw [hphys0, hphys2]
    intro he
    field_simp [hdenPhys] at he
    norm_num at he
  have hnormEval (p : ℕ) (hp : p = 1 ∨ p = 2) :
      ∀ c : Fin (p+1) → ℝ, c ≠ 0 →
        ∃ j : Fin n, 0 < shrinkingKernel n j ∧
          (∑ r, c r * shrinkingDistance n j ^ r.val) ≠ 0 := by
    intro c hc
    obtain ⟨k, hk⟩ :=
      SAP.P033.WH.W1.P.T4_L2.no_three_roots hnormNodes hnorm01 hnorm12
        hnorm02 p hp c hc
    exact ⟨SAP.P033.WH.W1.P.T4_L2.firstNode n hn k, hnormPos _, by simpa [hnormNodes] using hk⟩
  have hphysEval (p : ℕ) (hp : p = 1 ∨ p = 2) :
      ∀ c : Fin (p+1) → ℝ, c ≠ 0 →
        ∃ ji : Fin (n*(n+1)) × Fin 5, 0 < wholePhysicalKernel n ji.1 ∧
          (∑ r, c r * wholePhysicalDistance n ji.1 ^ r.val) ≠ 0 := by
    intro c hc
    obtain ⟨k, hk⟩ :=
      SAP.P033.WH.W1.P.T4_L2.no_three_roots hphysNodes hphys01 hphys12
        hphys02 p hp c hc
    refine ⟨SAP.P033.WH.W1.P.T4_L2.physicalNode n hn k, ?_, ?_⟩
    · apply (hgeo.2.2.1 _).2
      simp [SAP.P033.WH.W1.P.T4_L2.physicalNode,
        SAP.P033.WH.W1.P.T4_L2.firstNode, wholeActiveIndex]
      omega
    · simpa [hphysNodes, SAP.P033.WH.W1.P.T4_L2.physicalNode,
        SAP.P033.WH.W1.P.T4_L2.firstNode, wholePhysicalDistance,
        wholeActiveIndex] using hk
  intro p hp
  refine ⟨?_, ?_⟩
  · apply (SAP.P033.WH.W1.P.T4_L2.gridGram_posDef
      (shrinkingDistance n) (shrinkingKernel n) p hnormNN (hnormEval p hp)).isUnit
  · apply (SAP.P033.WH.W1.P.T4_L2.gridGram_posDef
      (fun ji : Fin (n*(n+1)) × Fin 5 => wholePhysicalDistance n ji.1)
      (fun ji => wholePhysicalKernel n ji.1) p hphysNN (hphysEval p hp)).isUnit
