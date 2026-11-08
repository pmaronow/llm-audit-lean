import SAP.P006a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P006a.WH.W1.P.T2_L2

lemma bestValue_eq_local {P : Type*} {PiSet : Set P} {f : P → ℝ} {π : P}
    (h : IsBest PiSet f π) : bestValue PiSet f = f π := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨π, h.1, rfl⟩, ?_⟩
  rintro y ⟨q, hq, rfl⟩
  exact h.2 q hq

lemma prefix_right {K : ℕ} (p : Fin K → ℝ) (j : Fin K) :
    prefixMass p j + p j = ∑ i, if i ≤ j then p i else 0 := by
  have hsingle : (∑ i : Fin K, if i = j then p j else 0) = p j := by simp
  rw [prefixMass, ← hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : i < j
  · simp [hij, hij.le, ne_of_lt hij]
  · by_cases heq : i = j
    · subst i
      simp
    · have hnle : ¬ i ≤ j := by
        intro h
        exact heq (le_antisymm h (le_of_not_gt hij))
      simp [hij, heq, hnle]

lemma prefix_cover {K : ℕ} (hK : 0 < K) (p : Fin K → ℝ)
    (hsum : ∑ i, p i = 1) (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∃ j, prefixMass p j ≤ q ∧ q ≤ prefixMass p j + p j := by
  let last : Fin K := ⟨K - 1, by omega⟩
  have hlast : prefixMass p last + p last = 1 := by
    rw [prefix_right, ← hsum]
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i ≤ last := by
      change i.val ≤ K - 1
      omega
    simp only [if_pos hil]
  let s : Finset (Fin K) := Finset.univ.filter (fun j => q ≤ prefixMass p j + p j)
  have hs : s.Nonempty := by
    refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hlast]
    exact hq.2
  let j : Fin K := s.min' hs
  have hjmem : j ∈ s := Finset.min'_mem s hs
  refine ⟨j, ?_, (Finset.mem_filter.mp hjmem).2⟩
  by_cases hj0 : j.val = 0
  · have hpref : prefixMass p j = 0 := by
      unfold prefixMass
      apply Finset.sum_eq_zero
      intro i hi
      have hnlt : ¬ i < j := by change ¬ i.val < j.val; omega
      simp only [if_neg hnlt]
    rw [hpref]
    exact hq.1
  · let k : Fin K := ⟨j.val - 1, by omega⟩
    have hkj : k < j := by change j.val - 1 < j.val; omega
    have hprev : prefixMass p k + p k = prefixMass p j := by
      rw [prefix_right]
      unfold prefixMass
      apply Finset.sum_congr rfl
      intro i hi
      have he : i ≤ k ↔ i < j := by
        change i.val ≤ j.val - 1 ↔ i.val < j.val
        omega
      simp only [he]
    have hknot : ¬ q ≤ prefixMass p k + p k := by
      intro hk
      have hkmem : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      have hjk : j ≤ k := Finset.min'_le s k hkmem
      exact (not_le_of_gt hkj) hjk
    rw [hprev] at hknot
    exact (lt_of_not_ge hknot).le

end SAP.P006a.WH.W1.P.T2_L2

open SAP.P006a.WH.W1.P.T2_L2

theorem SAP.P006a.WH.W1.T2_L2_proof : SAP.P006a.WH.W1.T2_L2 := by
  intro K hK n hn p m hp hsum hm hfront hglobal
  have hpref_nonneg (j : Fin K) : 0 ≤ prefixMass p j := by
    unfold prefixMass
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact (hp i).le
    · exact le_rfl
  have hright_le (j : Fin K) : prefixMass p j + p j ≤ 1 := by
    rw [prefix_right, ← hsum]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hij : i ≤ j
    · simp [hij]
    · simp only [if_neg hij]
      exact (hp i).le
  have fiberBest (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
      ∃ π, IsBest {π | π ∈ finitePolicies ∧ finiteMass p π = q}
        (finiteA p m) π := by
    obtain ⟨j, hlo, hhi⟩ := prefix_cover hK p hsum q ⟨hq.1, hq.2⟩
    obtain ⟨ht, hmass, hvalue, hupper⟩ := hfront j q hlo hhi
    refine ⟨thresholdRule p j q, ⟨⟨ht, hmass⟩, ?_⟩⟩
    intro π hπ
    calc
      finiteA p m π ≤ prefixA p m j + m j * (q - prefixMass p j) :=
        hupper π hπ.1 hπ.2
      _ = finiteA p m (thresholdRule p j q) := hvalue.symm
  have hfiber_affine : ∀ j q, prefixMass p j ≤ q → q ≤ prefixMass p j + p j →
      finiteFrontier p m q = prefixA p m j + m j * (q - prefixMass p j) := by
    intro j q hlo hhi
    obtain ⟨ht, hmass, hvalue, hupper⟩ := hfront j q hlo hhi
    have hbest : IsBest {π | π ∈ finitePolicies ∧ finiteMass p π = q}
        (finiteA p m) (thresholdRule p j q) := by
      refine ⟨⟨ht, hmass⟩, ?_⟩
      intro π hπ
      calc
        finiteA p m π ≤ prefixA p m j + m j * (q - prefixMass p j) :=
          hupper π hπ.1 hπ.2
        _ = finiteA p m (thresholdRule p j q) := hvalue.symm
    calc
      finiteFrontier p m q = bestValue
          {π | π ∈ finitePolicies ∧ finiteMass p π = q} (finiteA p m) := rfl
      _ = finiteA p m (thresholdRule p j q) := bestValue_eq_local hbest
      _ = prefixA p m j + m j * (q - prefixMass p j) := hvalue
  obtain ⟨j₀, q₀, hlo₀, hhi₀, hglobal₀⟩ := hglobal
  have hq₀ : q₀ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hpref_nonneg j₀).trans hlo₀, hhi₀.trans (hright_le j₀)⟩
  obtain ⟨hthreshold, hmass₀, hvalue₀, hupper₀⟩ := hfront j₀ q₀ hlo₀ hhi₀
  have hfiber₀ : IsBest {π | π ∈ finitePolicies ∧ finiteMass p π = q₀}
      (finiteA p m) (thresholdRule p j₀ q₀) := by
    refine ⟨⟨hthreshold, hmass₀⟩, ?_⟩
    intro π hπ
    calc
      finiteA p m π ≤ prefixA p m j₀ + m j₀ * (q₀ - prefixMass p j₀) :=
        hupper₀ π hπ.1 hπ.2
      _ = finiteA p m (thresholdRule p j₀ q₀) := hvalue₀.symm
  have hvalue₀' : finiteFrontier p m q₀ =
      finiteA p m (thresholdRule p j₀ q₀) := by
    simpa [finiteFrontier] using bestValue_eq_local hfiber₀
  have hscalar₀ : IsBest (Set.Icc (0 : ℝ) 1)
      (fun q => emptyFactor n q * finiteFrontier p m q) q₀ := by
    refine ⟨hq₀, ?_⟩
    intro q hq
    obtain ⟨π, hπ⟩ := fiberBest q hq
    have hπvalue : finiteFrontier p m q = finiteA p m π := by
      simpa [finiteFrontier] using bestValue_eq_local hπ
    calc
      emptyFactor n q * finiteFrontier p m q =
          emptyFactor n q * finiteA p m π := by rw [hπvalue]
      _ = emptyFactor n (finiteMass p π) * finiteA p m π := by rw [hπ.1.2]
      _ ≤ emptyFactor n (finiteMass p (thresholdRule p j₀ q₀)) *
          finiteA p m (thresholdRule p j₀ q₀) := hglobal₀.2 π hπ.1.1
      _ = emptyFactor n q₀ * finiteFrontier p m q₀ := by
          rw [hmass₀, hvalue₀']
  have hobj₀ : emptyFactor n (finiteMass p (thresholdRule p j₀ q₀)) *
      finiteA p m (thresholdRule p j₀ q₀) =
      emptyFactor n q₀ * finiteFrontier p m q₀ := by
    rw [hmass₀, hvalue₀']
  refine ⟨?_, hfiber_affine, ⟨q₀, hscalar₀⟩, ?_⟩
  · intro q hq
    exact fiberBest q hq
  · calc
      bestValue finitePolicies
          (fun π => emptyFactor n (finiteMass p π) * finiteA p m π) =
          emptyFactor n (finiteMass p (thresholdRule p j₀ q₀)) *
            finiteA p m (thresholdRule p j₀ q₀) :=
        bestValue_eq_local hglobal₀
      _ = emptyFactor n q₀ * finiteFrontier p m q₀ := hobj₀
      _ = bestValue (Set.Icc (0 : ℝ) 1)
          (fun q => emptyFactor n q * finiteFrontier p m q) :=
        (bestValue_eq_local hscalar₀).symm
