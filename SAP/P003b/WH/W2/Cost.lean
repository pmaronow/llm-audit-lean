import SAP.P003b.WH.W2.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2
open scoped BigOperators
open SAP.P003b.Bridge
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxHeartbeats 1600000

theorem bases_length (full : Bool) (o : Counts) (x : ℤ) :
    (wholeCostBases full o x).length ≤ o.total+1 := by
  have h := List.length_filterMap_le (fun j =>
    (wholeFastBase o x j).map fun v => (j,v)) (List.range (o.total+1))
  simp only [List.length_range] at h
  cases full
  · exact (List.length_take_le' _ _).trans h
  · exact h

theorem base_index (full : Bool) (o : Counts) (x : ℤ) (jv : ℕ × Counts)
    (hv : jv ∈ wholeCostBases full o x) : jv.1 ≤ o.total := by
  have hv' : jv ∈ (List.range (o.total+1)).filterMap (fun j =>
      (wholeFastBase o x j).map fun v => (j,v)) := by
    cases full
    · exact List.mem_of_mem_take hv
    · exact hv
  obtain ⟨j,hj,hv⟩ := List.mem_filterMap.mp hv'
  obtain ⟨v,_,he⟩ := Option.map_eq_some_iff.mp hv
  have he' := congrArg Prod.fst he
  have hj' := List.mem_range.mp hj
  dsimp at he'
  omega

theorem cost_reuse_length (o : Counts) (x : ℤ) (j : ℕ) (v : Counts) (hj : j ≤ o.total) :
    (wholeCostReuse o x j v).length ≤ o.total := by
  have hu : wholeLineUpper o x j ≤ (j : ℤ) :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hun : (wholeLineUpper o x j).toNat ≤ j := by omega
  simp only [wholeCostReuse,List.length_map,List.length_range]
  omega

theorem cost_counts (full : Bool) (o : Counts) (K : ℕ) :
    wholeCostDraws full o K ≤ (o.total+1)^2*K ∧
    wholeCostUpdates full o K ≤ (o.total+1)^2*o.total*K := by
  constructor
  · have h := AronowAudit.P003.list_cost_bound (candidateNumerators o)
      (fun x => (wholeCostBases full o x).length*K) ((o.total+1)*K)
      (fun x _ => Nat.mul_le_mul_right K (bases_length full o x))
    simpa [wholeCostDraws,candidateNumerators,pow_two,Nat.mul_assoc] using h
  · have hinner (x : ℤ) :
        ((wholeCostBases full o x).map fun jv => K*(wholeCostReuse o x jv.1 jv.2).length).sum ≤
          (o.total+1)*(K*o.total) := by
      have h := AronowAudit.P003.list_cost_bound (wholeCostBases full o x)
        (fun jv => K*(wholeCostReuse o x jv.1 jv.2).length) (K*o.total) (by
          intro jv hjv
          exact Nat.mul_le_mul_left K (cost_reuse_length o x jv.1 jv.2 (base_index full o x jv hjv)))
      exact h.trans (Nat.mul_le_mul_right _ (bases_length full o x))
    have h := AronowAudit.P003.list_cost_bound (candidateNumerators o) _
      ((o.total+1)*(K*o.total)) (fun x _ => hinner x)
    simpa [wholeCostUpdates,candidateNumerators,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem cost_finite (full : Bool) (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ)
    (hc : 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂) :
    wholeCostDraws full o K ≤ (o.total+1)^2*K ∧
    wholeCostUpdates full o K ≤ (o.total+1)^2*o.total*K ∧
    0 ≤ wholeCostOperations full o K c₀ c₁ c₂ ∧
    wholeCostOperations full o K c₀ c₁ c₂ ≤ generalEnvelope o.total K c₀ c₁ c₂ ∧
    (1 ≤ o.total → 1 ≤ K → wholeCostOperations full o K c₀ c₁ c₂ ≤
      4*(c₀+2*(c₁+c₂))*K*(o.total : ℝ)^3) := by
  have hc₀ := hc.1
  have hc₁ := hc.2.1
  have hc₂ := hc.2.2
  have h := cost_counts full o K
  have hdR : (wholeCostDraws full o K : ℝ) ≤ ((o.total : ℝ)+1)^2*K := by exact_mod_cast h.1
  have huR : (wholeCostUpdates full o K : ℝ) ≤ ((o.total : ℝ)+1)^2*o.total*K := by exact_mod_cast h.2
  have hpos : 0 ≤ wholeCostOperations full o K c₀ c₁ c₂ := by
    unfold wholeCostOperations
    positivity
  have he : wholeCostOperations full o K c₀ c₁ c₂ ≤ generalEnvelope o.total K c₀ c₁ c₂ := by
    unfold wholeCostOperations generalEnvelope
    have h₁ := mul_le_mul_of_nonneg_left hdR (show 0 ≤ 2*c₁*o.total by positivity)
    have h₂ := mul_le_mul_of_nonneg_left huR (show 0 ≤ 2*c₂ by positivity)
    nlinarith
  refine ⟨h.1,h.2,hpos,he,?_⟩
  intro hn hK
  exact he.trans (AronowAudit.P003.general_envelope_bound o.total K hn hK c₀ c₁ c₂ hc)

theorem cost_joint (full : Bool) (c₀ c₁ c₂ : ℝ) (hc : 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂)
    (o : ℕ × ℕ → Counts) (ho : ∀ p, (o p).total = p.1) :
    (fun p : ℕ × ℕ => wholeCostOperations full (o p) p.2 c₀ c₁ c₂)
      =O[Filter.atTop] (fun p : ℕ × ℕ => (p.2 : ℝ)*(p.1 : ℝ)^3) := by
  apply Asymptotics.IsBigO.of_bound (4*(c₀+2*(c₁+c₂)))
  apply Filter.eventually_atTop.mpr
  refine ⟨(1,1),?_⟩
  intro p hp
  have h := cost_finite full (o p) p.2 c₀ c₁ c₂ hc
  rw [Real.norm_eq_abs,abs_of_nonneg h.2.2.1,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (p.2 : ℝ)*(p.1 : ℝ)^3)]
  have hb := h.2.2.2.2 (by rw [ho]; exact hp.1) hp.2
  rw [ho] at hb
  nlinarith

theorem cost_schedule (full : Bool) (c₀ c₁ c₂ : ℝ) (hc : 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂)
    (o : ℕ → Counts) (K : ℕ → ℕ) (ho : ∀ n, (o n).total = n)
    (hK : ∀ᶠ n in Filter.atTop, 1 ≤ K n) :
    (fun n => wholeCostOperations full (o n) (K n) c₀ c₁ c₂)
      =O[Filter.atTop] (fun n : ℕ => (K n : ℝ)*(n : ℝ)^3) := by
  apply Asymptotics.IsBigO.of_bound (4*(c₀+2*(c₁+c₂)))
  filter_upwards [hK,Filter.eventually_ge_atTop (1 : ℕ)] with n hkn hn
  have h := cost_finite full (o n) (K n) c₀ c₁ c₂ hc
  rw [Real.norm_eq_abs,abs_of_nonneg h.2.2.1,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (K n : ℝ)*(n : ℝ)^3)]
  have hb := h.2.2.2.2 (by rw [ho]; exact hn) hkn
  rw [ho] at hb
  nlinarith

end
end SAP.P003b.WH.W2
