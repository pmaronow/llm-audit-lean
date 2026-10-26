import AronowAudit.P037.P037_Sample
import AronowAudit.P037.P037_FiniteDesign

namespace AronowAudit.P037.Wave1
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Regard the supported law as a nonnegative finite design. -/
noncomputable def exposureMC_design {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) : FiniteDesign Ω where
  weight := P.mass
  nonneg := fun z => (P.positive z).le
  total := P.total

/-- The failure probability under the original assignment law. -/
lemma exposureMC_complement {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) :
    sampleProb P (fun z => ¬ E z) = 1 - sampleProb P E := by
  have h : sampleProb P (fun z => ¬ E z) + sampleProb P E = 1 := by
    unfold sampleProb
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ z, P.mass z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : E z <;> simp [hz]
      _ = 1 := P.total
  linarith

/-- Factor the probability of one exact set of successful draw indices. -/
lemma exposureMC_pattern {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) (J : ℕ) (A : Finset (Fin J)) :
    (∑ z : Fin J → Ω,
      (∏ j, P.mass (z j)) *
        (if Finset.univ.filter (fun j => E (z j)) = A then 1 else 0)) =
      (sampleProb P E)^A.card * (1 - sampleProb P E)^(J - A.card) := by
  have hpoint (z : Fin J → Ω) :
      (if Finset.univ.filter (fun j => E (z j)) = A then (1 : ℝ) else 0) =
        ∏ j, if E (z j) ↔ j ∈ A then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
    congr 1
    simp only [Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [hpoint, ← Finset.prod_mul_distrib]
  rw [finite_product_factorization (Ω := fun _ : Fin J => Ω)
    (fun j u => P.mass u * (if E u ↔ j ∈ A then (1 : ℝ) else 0))]
  have hfactor (j : Fin J) :
      (∑ u, P.mass u * (if E u ↔ j ∈ A then (1 : ℝ) else 0)) =
        if j ∈ A then sampleProb P E else 1 - sampleProb P E := by
    by_cases hj : j ∈ A
    · simp [hj, sampleProb]
    · simpa [hj, sampleProb] using exposureMC_complement P E
  simp_rw [hfactor]
  simpa only [Finset.piecewise, Finset.univ_inter, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.subset_univ A),
    Finset.card_univ, Fintype.card_fin] using
    (Finset.prod_piecewise (Finset.univ : Finset (Fin J)) A
      (fun _ => sampleProb P E) (fun _ => 1 - sampleProb P E))

/-- Partition actual draw sequences by their success-index sets. -/
lemma exposureMC_count {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) (J r : ℕ) :
    (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
      (if (Finset.univ.filter (fun j => E (z j))).card = r then 1 else 0)) =
      (Nat.choose J r : ℝ) * (sampleProb P E)^r *
        (1 - sampleProb P E)^(J - r) := by
  calc
    _ = ∑ z ∈ Finset.univ.filter
        (fun z : Fin J → Ω => (Finset.univ.filter (fun j => E (z j))).card = r),
          ∏ j, P.mass (z j) := by
      simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]
    _ = ∑ A ∈ (Finset.univ : Finset (Fin J)).powersetCard r,
        ∑ z ∈ Finset.univ.filter
          (fun z : Fin J → Ω => Finset.univ.filter (fun j => E (z j)) = A),
            ∏ j, P.mass (z j) := by
      symm
      simpa only [Finset.mem_powersetCard, Finset.subset_univ, true_and] using
        (Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (Fin J → Ω))
          ((Finset.univ : Finset (Fin J)).powersetCard r)
          (fun z => Finset.univ.filter (fun j => E (z j)))
          (fun z => ∏ j, P.mass (z j)))
    _ = ∑ _A ∈ (Finset.univ : Finset (Fin J)).powersetCard r,
        (sampleProb P E)^r * (1 - sampleProb P E)^(J - r) := by
      apply Finset.sum_congr rfl
      intro A hA
      have hcard := (Finset.mem_powersetCard.mp hA).2
      simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero, hcard] using
        exposureMC_pattern P E J A
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
      ring

/-- The empirical hit count is the sum of its binary indicators. -/
lemma exposureMC_hits_sum {Ω : Type*} (E : Ω → Prop) (J : ℕ) (z : Fin J → Ω) :
    ((Finset.univ.filter (fun j => E (z j))).card : ℝ) =
      ∑ j, if E (z j) then (1 : ℝ) else 0 := by
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Coordinate factorization supplies the two frequency moments. -/
lemma exposureMC_moments {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) (J : ℕ) (hJ : 0 < J) :
    (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
      (((Finset.univ.filter (fun j => E (z j))).card : ℝ) / J)) = sampleProb P E ∧
    (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
      ((((Finset.univ.filter (fun j => E (z j))).card : ℝ) / J - sampleProb P E)^2)) =
      sampleProb P E * (1 - sampleProb P E) / J := by
  let d := exposureMC_design P
  let D := productDesign (fun _ : Fin J => d)
  let X : Fin J → (Fin J → Ω) → ℝ := fun j z => if E (z j) then 1 else 0
  have hm (j : Fin J) : designMean D (X j) = sampleProb P E := by
    exact product_design_coordinate_mean (fun _ : Fin J => d) j
      (fun u => if E u then 1 else 0)
  have hp (j k : Fin J) (hjk : j ≠ k) :
      designMean D (fun z => X j z * X k z) = (sampleProb P E)^2 := by
    calc
      _ = designMean d (fun u => if E u then 1 else 0) *
          designMean d (fun u => if E u then 1 else 0) :=
        product_design_coordinate_pair (fun _ : Fin J => d) j k hjk
          (fun u => if E u then 1 else 0) (fun u => if E u then 1 else 0)
      _ = _ := by
        change sampleProb P E * sampleProb P E = (sampleProb P E)^2
        ring
  have hb (j : Fin J) (z : Fin J → Ω) : X j z = 0 ∨ X j z = 1 := by
    by_cases hz : E (z j) <;> simp [X, hz]
  obtain ⟨hmean, hvar, _⟩ := monte_carlo_frequency_moments D J hJ X
    (sampleProb P E) hb hm hp
  have hcenter := designVariance_centered D (fun z => (∑ j, X j z) / J)
  rw [hmean] at hcenter
  rw [hcenter] at hvar
  constructor
  · simpa only [designMean, D, d, productDesign, exposureMC_design, X,
      ← exposureMC_hits_sum E J] using hmean
  · simpa only [designMean, D, d, productDesign, exposureMC_design, X,
      ← exposureMC_hits_sum E J] using hvar

/-- Squared deviations control the tail including its boundary. -/
lemma exposureMC_tail {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) (J : ℕ) (hJ : 0 < J)
    (ε : ℝ) (hε : 0 < ε) :
    (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
      (if |((Finset.univ.filter (fun j => E (z j))).card : ℝ) / J -
        sampleProb P E| ≥ ε then 1 else 0)) ≤
      sampleProb P E * (1 - sampleProb P E) / (J * ε^2) ∧
    sampleProb P E * (1 - sampleProb P E) / (J * ε^2) ≤ 1 / (4 * J * ε^2) := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hεsq : 0 < ε^2 := sq_pos_of_pos hε
  constructor
  · calc
      _ ≤ (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
          ((((Finset.univ.filter (fun j => E (z j))).card : ℝ) / J -
            sampleProb P E)^2)) / ε^2 := by
        rw [le_div_iff₀ hεsq, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro z _
        have hw : 0 ≤ ∏ j, P.mass (z j) :=
          Finset.prod_nonneg (fun j _ => (P.positive (z j)).le)
        by_cases hz : |((Finset.univ.filter (fun j => E (z j))).card : ℝ) / J -
            sampleProb P E| ≥ ε
        · simp only [if_pos hz, mul_one]
          apply mul_le_mul_of_nonneg_left _ hw
          nlinarith [sq_abs (((Finset.univ.filter (fun j => E (z j))).card : ℝ) / J -
            sampleProb P E)]
        · simp only [if_neg hz, mul_zero, zero_mul]
          exact mul_nonneg hw (sq_nonneg _)
      _ = _ := by rw [(exposureMC_moments P E J hJ).2]; ring
  · have hquad : sampleProb P E * (1 - sampleProb P E) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (sampleProb P E - 1 / 2)]
    calc
      _ ≤ (1 / 4) / (J * ε^2) :=
        div_le_div_of_nonneg_right hquad (mul_nonneg hJpos.le hεsq.le)
      _ = _ := by ring

/-- Strictly positive supported states cannot occur in a probability-zero event. -/
lemma exposureMC_zero {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) (hp : sampleProb P E = 0) :
    ∀ u, ¬ E u := by
  intro u hu
  have hle : P.mass u ≤ sampleProb P E := by
    calc
      P.mass u = P.mass u * (if E u then 1 else 0) := by simp [hu]
      _ ≤ sampleProb P E := by
        apply Finset.single_le_sum _ (Finset.mem_univ u)
        intro z _
        exact mul_nonneg (P.positive z).le (by split_ifs <;> norm_num)
  linarith [P.positive u]

theorem exposure_monte_carlo_law_proof {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) (J : ℕ) (hJ : 0<J) :
    let p := sampleProb P E
    let hits := fun z : Fin J → Ω => (Finset.univ.filter (fun j => E (z j))).card
    let mass := fun z : Fin J → Ω => ∏ j, P.mass (z j)
    let phat := fun z => (hits z:ℝ)/J
    (∀ r : ℕ, r≤J →
      (∑ z, mass z*(if hits z=r then 1 else 0))=
        (Nat.choose J r:ℝ)*p^r*(1-p)^(J-r)) ∧
    (∑ z, mass z*phat z)=p ∧
    (∑ z, mass z*(phat z-p)^2)=p*(1-p)/J ∧
    (∑ z, mass z*(if hits z=0 then 1 else 0))=(1-p)^J ∧
    (∀ ε : ℝ, 0<ε →
      (∑ z, mass z*(if |phat z-p|≥ε then 1 else 0))≤p*(1-p)/(J*ε^2) ∧
      p*(1-p)/(J*ε^2)≤1/(4*J*ε^2)) ∧
    (∀ ε δ : ℝ, 0<ε → 0<δ → (J:ℝ)≥1/(4*δ*ε^2) →
      (∑ z, mass z*(if |phat z-p|≥ε then 1 else 0))≤δ) ∧
    (p=0 → ∀ z, hits z=0) ∧
    (0<p ∧ p<1 → 0<(1-p)^J ∧ 0<p*(1-p)/J) := by
  dsimp only
  obtain ⟨hmean, hvar⟩ := exposureMC_moments P E J hJ
  refine ⟨fun r _ => exposureMC_count P E J r, hmean, hvar, ?_,
    exposureMC_tail P E J hJ, ?_, ?_, ?_⟩
  · simpa only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
      using exposureMC_count P E J 0
  · intro ε δ hε hδ hsize
    have htail := exposureMC_tail P E J hJ ε hε
    refine htail.1.trans (htail.2.trans ?_)
    have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
    have hden : 0 < 4 * δ * ε^2 := by positivity
    have hmul : 1 ≤ (J : ℝ) * (4 * δ * ε^2) := (div_le_iff₀ hden).mp hsize
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * J * ε^2)).mpr
    nlinarith [hmul]
  · intro hp z
    have he := exposureMC_zero P E hp
    simp [he]
  · intro hp
    have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
    exact ⟨pow_pos (by linarith) J, div_pos (mul_pos hp.1 (by linarith)) hJpos⟩

end AronowAudit.P037.Wave1
