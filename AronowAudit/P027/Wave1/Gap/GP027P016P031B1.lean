import AronowAudit.P027.P027_Audit
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Cumulative endpoints, phase partitions, and systematic selection for the
periodic PPS design. -/

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable









/-! ## Periodic systematic selection -/

lemma periodic_prefix_sum (n j : ℕ) (hj : j ≤ n) (c : ℝ) :
    (∑ i : Fin n, if i.val < j then c else 0) = (j:ℝ)*c := by
  induction n generalizing j with
  | zero =>
      have : j = 0 := by omega
      subst j
      simp
  | succ n ih =>
      cases j with
      | zero => simp
      | succ j =>
          have hj' : j ≤ n := by omega
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Nat.zero_lt_succ, if_true, Fin.val_succ,
            Nat.succ_lt_succ_iff]
          rw [ih j hj']
          push_cast
          ring

/-- Base-Q comparison, used only with bounded within-block offsets. -/
lemma periodic_index_lex (Q a b i j : ℕ) (ha : a < Q) (hb : b < Q) :
    a+Q*i < b+Q*j ↔ i < j ∨ (i = j ∧ a < b) := by
  constructor
  · intro h
    by_cases hij : i < j
    · exact Or.inl hij
    · right
      have hji : j ≤ i := le_of_not_gt hij
      have heq : i = j := by
        by_contra hne
        have hstep : j+1 ≤ i := by omega
        have hmul : Q*(j+1) ≤ Q*i := Nat.mul_le_mul_left Q hstep
        nlinarith
      exact ⟨heq, by simpa [heq] using h⟩
  · rintro (hij | ⟨rfl, hab⟩)
    · have hstep : i+1 ≤ j := by omega
      have hmul : Q*(i+1) ≤ Q*j := Nat.mul_le_mul_left Q hstep
      nlinarith
    · omega

lemma periodic_offset_lt {r : ℕ} (g : Fin r × Fin 2) :
    2*g.1.val+g.2.val < 2*r := by
  have hi := g.1.isLt
  have hb := g.2.isLt
  omega

lemma periodic_block_term {r m : ℕ}
    (g : Fin r × Fin 2) (j : Fin m)
    (k : Σ _ : Fin r × Fin 2, Fin m) :
    (if phaseIndex ⟨g,j⟩ < phaseIndex k then phaseSize ⟨g,j⟩ else 0) =
      (if j.val < k.2.val then (if g.2 = 0 then (2:ℝ) else 10) else 0) +
      (if j = k.2 then
        (if 2*g.1.val+g.2.val < 2*k.1.1.val+k.1.2.val then
          (if g.2 = 0 then (2:ℝ) else 10) else 0) else 0) := by
  have hlex := periodic_index_lex (2*r) (2*g.1.val+g.2.val)
    (2*k.1.1.val+k.1.2.val) j.val k.2.val
    (periodic_offset_lt g) (periodic_offset_lt k.1)
  simp only [phaseIndex, phaseSize]
  simp only [hlex]
  by_cases hj : j.val < k.2.val
  · have hjne : j ≠ k.2 := by intro h; subst j; omega
    simp [hj, hjne]
  · by_cases heq : j = k.2
    · subst j
      simp
    · have hvne : j.val ≠ k.2.val := fun h => heq (Fin.ext h)
      simp [hj, heq, hvne]

lemma periodic_phase_prefix {r : ℕ} (g : Fin r × Fin 2) :
    (∑ h : Fin r × Fin 2,
      if 2*h.1.val+h.2.val < 2*g.1.val+g.2.val then
        (if h.2 = 0 then (2:ℝ) else 10) else 0) = phaseStartLeft g := by
  rcases g with ⟨i,b⟩
  have hpair (a : Fin r) :
      (∑ t : Fin 2,
        if 2*a.val+t.val < 2*i.val+b.val then
          (if t = 0 then (2:ℝ) else 10) else 0) =
        (if a.val < i.val then (12:ℝ) else 0) +
          (if a = i then (if b = 0 then (0:ℝ) else 2) else 0) := by
    fin_cases b <;> simp only [Fin.sum_univ_two] <;>
      norm_num <;> split_ifs <;> norm_num [Fin.ext_iff] at * <;> omega
  rw [Fintype.sum_prod_type]
  simp_rw [hpair]
  rw [Finset.sum_add_distrib, periodic_prefix_sum r i.val (Nat.le_of_lt i.isLt)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, phaseStartLeft]
  ring

lemma periodic_predecessor_sum {r m : ℕ}
    (k : Σ _ : Fin r × Fin 2, Fin m) :
    (∑ a : Σ _ : Fin r × Fin 2, Fin m,
      if phaseIndex a < phaseIndex k then phaseSize a else 0) =
        phaseStartLeft k.1+12*r*(k.2:ℝ) := by
  have hblock (g : Fin r × Fin 2) :
      (∑ j : Fin m,
        if phaseIndex ⟨g,j⟩ < phaseIndex k then phaseSize ⟨g,j⟩ else 0) =
      (k.2:ℝ)*(if g.2 = 0 then (2:ℝ) else 10) +
        (if 2*g.1.val+g.2.val < 2*k.1.1.val+k.1.2.val then
          (if g.2 = 0 then (2:ℝ) else 10) else 0) := by
    simp_rw [periodic_block_term]
    rw [Finset.sum_add_distrib,
      periodic_prefix_sum m k.2.val (Nat.le_of_lt k.2.isLt)]
    simp
  rw [Fintype.sum_sigma]
  simp_rw [hblock]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, periodic_phase_prefix]
  have htotal :
      (∑ g : Fin r × Fin 2, if g.2 = 0 then (2:ℝ) else 10) = 12*r := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
    <;> ring
  rw [htotal]
  ring

/-- Uniqueness of a block for a point in half-open consecutive grid intervals. -/
lemma periodic_grid_unique (Q x : ℝ) (hQ : 0 < Q) (i j : ℕ)
    (hi₀ : Q*(i:ℝ) ≤ x) (hi₁ : x < Q*((i:ℝ)+1))
    (hj₀ : Q*(j:ℝ) ≤ x) (hj₁ : x < Q*((j:ℝ)+1)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have hstep : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij)
    have hmul := mul_le_mul_of_nonneg_left hstep hQ.le
    nlinarith
  · exact hij
  · have hstep : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hji)
    have hmul := mul_le_mul_of_nonneg_left hstep hQ.le
    nlinarith

lemma periodic_pair_bounds {r : ℕ} (g : Fin r × Fin 2) :
    12*(g.1:ℝ) ≤ phaseStartLeft g ∧
    phaseStartLeft g+(if g.2 = 0 then (2:ℝ) else 10) ≤ 12*((g.1:ℝ)+1) := by
  rcases g with ⟨i,b⟩
  fin_cases b <;> norm_num [phaseStartLeft] <;> linarith

lemma periodic_interval_bounds {r : ℕ} (g : Fin r × Fin 2) :
    0 ≤ phaseStartLeft g ∧
    phaseStartLeft g+(if g.2 = 0 then (2:ℝ) else 10) ≤ 12*r := by
  have hpair := periodic_pair_bounds g
  have hi : (g.1:ℝ)+1 ≤ (r:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt g.1.isLt)
  constructor
  · exact le_trans (by positivity) hpair.1
  · linarith [hpair.2]

lemma periodic_start_unique {r : ℕ} (g h : Fin r × Fin 2) (u : ℝ)
    (hg₀ : phaseStartLeft g ≤ u)
    (hg₁ : u < phaseStartLeft g+(if g.2 = 0 then 2 else 10))
    (hh₀ : phaseStartLeft h ≤ u)
    (hh₁ : u < phaseStartLeft h+(if h.2 = 0 then 2 else 10)) : g = h := by
  have bg := periodic_pair_bounds g
  have bh := periodic_pair_bounds h
  have hi : g.1.val = h.1.val := periodic_grid_unique 12 u (by norm_num)
    g.1.val h.1.val (le_trans bg.1 hg₀) (lt_of_lt_of_le hg₁ bg.2)
    (le_trans bh.1 hh₀) (lt_of_lt_of_le hh₁ bh.2)
  rcases g with ⟨i,b⟩
  rcases h with ⟨j,c⟩
  have hij : i = j := Fin.ext hi
  subst j
  have hbc : b = c := by
    fin_cases b <;> fin_cases c <;>
      norm_num [phaseStartLeft] at hg₀ hg₁ hh₀ hh₁ ⊢ <;> linarith
  subst c
  rfl

lemma periodic_start_partition (r : ℕ) (hr : 0 < r) (u : ℝ)
    (hu₀ : 0 ≤ u) (hu₁ : u < 12*r) :
    ∃! g : Fin r × Fin 2,
      phaseStartLeft g ≤ u ∧
        u < phaseStartLeft g+(if g.2 = 0 then 2 else 10) := by
  have hu12 : 0 ≤ u/12 := div_nonneg hu₀ (by norm_num)
  have hfloor : ⌊u/12⌋₊ < r := (Nat.floor_lt hu12).mpr (by
    apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 12)).mpr
    nlinarith)
  let i : Fin r := ⟨⌊u/12⌋₊, hfloor⟩
  have hleft : 12*(i:ℝ) ≤ u := by
    have hf := Nat.floor_le hu12
    change (⌊u/12⌋₊:ℝ) ≤ u/12 at hf
    dsimp [i]
    linarith
  have hright : u < 12*((i:ℝ)+1) := by
    have hf := Nat.lt_floor_add_one (u/12)
    dsimp [i]
    linarith
  have hex : ∃ g : Fin r × Fin 2,
      phaseStartLeft g ≤ u ∧
        u < phaseStartLeft g+(if g.2 = 0 then 2 else 10) := by
    by_cases hlow : u < 12*(i:ℝ)+2
    · refine ⟨(i,0), ?_⟩
      simpa [phaseStartLeft] using And.intro hleft hlow
    · refine ⟨(i,1), ?_⟩
      norm_num [phaseStartLeft]
      constructor <;> linarith
  obtain ⟨g,hg⟩ := hex
  refine ⟨g,hg,?_⟩
  intro h hh
  exact periodic_start_unique h g u hh.1 hh.2 hg.1 hg.2

lemma periodic_selection_equivalence (r m : ℕ) (hr : 0 < r)
    (g : Fin r × Fin 2) (u : ℝ)
    (hg₀ : phaseStartLeft g ≤ u)
    (hg₁ : u < phaseStartLeft g+(if g.2 = 0 then 2 else 10))
    (k : Σ _ : Fin r × Fin 2, Fin m) :
    ((∃ j : Fin m,
      (∑ a : Σ _ : Fin r × Fin 2, Fin m,
        if phaseIndex a < phaseIndex k then phaseSize a else 0) ≤
          u+(j:ℝ)*(12*r) ∧
      u+(j:ℝ)*(12*r) <
        (∑ a : Σ _ : Fin r × Fin 2, Fin m,
          if phaseIndex a < phaseIndex k then phaseSize a else 0)+phaseSize k) ↔
      (phaseOriginal r m hr).selected g k = true) := by
  have hQ : (0:ℝ) < 12*r := by positivity
  have bg := periodic_interval_bounds g
  have bk := periodic_interval_bounds k.1
  have hu₀ : 0 ≤ u := le_trans bg.1 hg₀
  have hu₁ : u < 12*r := lt_of_lt_of_le hg₁ bg.2
  simp only [phaseOriginal, liftDesign, phaseGrouped, oneDraw]
  simp only [decide_eq_true_eq]
  simp only [periodic_predecessor_sum]
  constructor
  · rintro ⟨j,hj₀,hj₁⟩
    have hjblock₀ : (12*(r:ℝ))*(j:ℝ) ≤ u+(j:ℝ)*(12*r) := by nlinarith
    have hjblock₁ : u+(j:ℝ)*(12*r) < (12*(r:ℝ))*((j:ℝ)+1) := by nlinarith
    have hkblock₀ : (12*(r:ℝ))*(k.2:ℝ) ≤ u+(j:ℝ)*(12*r) := by
      nlinarith [bk.1]
    have hkblock₁ : u+(j:ℝ)*(12*r) < (12*(r:ℝ))*((k.2:ℝ)+1) := by
      change _ < phaseStartLeft k.1+12*r*(k.2:ℝ)+
        (if k.1.2 = 0 then (2:ℝ) else 10) at hj₁
      nlinarith [bk.2]
    have hjk : j = k.2 := Fin.ext (periodic_grid_unique (12*r)
      (u+(j:ℝ)*(12*r)) hQ j.val k.2.val
      hjblock₀ hjblock₁ hkblock₀ hkblock₁)
    subst j
    have hk₀ : phaseStartLeft k.1 ≤ u := by nlinarith [hj₀]
    have hk₁ : u < phaseStartLeft k.1+(if k.1.2 = 0 then 2 else 10) := by
      change _ < phaseStartLeft k.1+12*r*(k.2:ℝ)+
        (if k.1.2 = 0 then (2:ℝ) else 10) at hj₁
      nlinarith [hj₁]
    exact periodic_start_unique g k.1 u hg₀ hg₁ hk₀ hk₁
  · intro hgk
    refine ⟨k.2, ?_, ?_⟩
    · have h := hg₀
      rw [hgk] at h
      nlinarith
    · have h := hg₁
      rw [hgk] at h
      change _ < phaseStartLeft k.1+12*r*(k.2:ℝ)+
        (if k.1.2 = 0 then (2:ℝ) else 10)
      nlinarith

/-- Cumulative endpoints, unique phase intervals, systematic selection, and
phase probabilities for the periodic design. -/
theorem periodic_systematic_bridge_proof (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    (∀ k : Σ _ : Fin r × Fin 2, Fin m,
      (∑ a : Σ _ : Fin r × Fin 2, Fin m, if phaseIndex a < phaseIndex k then phaseSize a else 0) =
        phaseStartLeft k.1+12*r*(k.2:ℝ)) ∧
    (∀ u : ℝ, 0 ≤ u → u < 12*r → ∃! g : Fin r × Fin 2,
      phaseStartLeft g ≤ u ∧ u < phaseStartLeft g+(if g.2 = 0 then 2 else 10)) ∧
    (∀ (g : Fin r × Fin 2) (u : ℝ),
      phaseStartLeft g ≤ u → u < phaseStartLeft g+(if g.2 = 0 then 2 else 10) →
      ∀ k : Σ _ : Fin r × Fin 2, Fin m,
        ((∃ j : Fin m, (∑ a : Σ _ : Fin r × Fin 2, Fin m, if phaseIndex a < phaseIndex k then phaseSize a else 0) ≤
          u+(j:ℝ)*(12*r) ∧ u+(j:ℝ)*(12*r) <
          (∑ a : Σ _ : Fin r × Fin 2, Fin m, if phaseIndex a < phaseIndex k then phaseSize a else 0)+phaseSize k) ↔
          (phaseOriginal r m hr).selected g k = true)) ∧
    (∀ g, phaseProb r g = (if g.2 = 0 then 2 else 10)/(12*r)) := by
  refine ⟨periodic_predecessor_sum, periodic_start_partition r hr,
    periodic_selection_equivalence r m hr, ?_⟩
  intro g
  have hrr : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold phaseProb
  split_ifs <;> field_simp [hrr] <;> ring

end
end AronowAudit.P027.Wave1
