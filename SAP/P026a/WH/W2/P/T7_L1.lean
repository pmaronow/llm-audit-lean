import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W2.P.T7_L1

open Finset
open scoped BigOperators Matrix

noncomputable section

private def fitReal {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℝ)
    (b : Fin k → ℝ) (i : Fin 16) : ℝ := ∑ j, A i j * b j

private def gramReal {k : ℕ} (A : Matrix (Fin 16) (Fin k) ℝ)
    (q : Fin 16 → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun j l => ∑ i, q i * A i j * A i l

private theorem real_weighted_ls_unique {k : ℕ}
    (A : Matrix (Fin 16) (Fin k) ℝ) (q y : Fin 16 → ℝ) (c : Fin k → ℝ)
    (hq : ∀ i, 0 ≤ q i)
    (hdet : (gramReal A q).det ≠ 0)
    (hne : ∀ j, (∑ i, q i * A i j * (y i - fitReal A c i)) = 0) :
    (∀ d : Fin k → ℝ,
      (∑ i, q i * (y i - fitReal A c i)^2) ≤
        ∑ i, q i * (y i - fitReal A d i)^2) ∧
    (∀ d : Fin k → ℝ,
      (∑ i, q i * (y i - fitReal A d i)^2) =
        (∑ i, q i * (y i - fitReal A c i)^2) → d = c) := by
  classical
  let delta := fun (d : Fin k → ℝ) (i : Fin 16) => fitReal A d i - fitReal A c i
  have hdelta (d : Fin k → ℝ) (i : Fin 16) :
      delta d i = ∑ j, A i j * (d j - c j) := by
    simp only [delta, fitReal]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcross (d : Fin k → ℝ) :
      (∑ i, q i * delta d i * (y i - fitReal A c i)) = 0 := by
    calc
      (∑ i, q i * delta d i * (y i - fitReal A c i)) =
          ∑ j, (d j - c j) * (∑ i, q i * A i j * (y i - fitReal A c i)) := by
        rw [show (∑ i, q i * delta d i * (y i - fitReal A c i)) =
          ∑ i, q i * (∑ j, A i j * (d j - c j)) * (y i - fitReal A c i) by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hdelta]]
        calc
          _ = ∑ i, ∑ j, (d j - c j) * (q i * A i j * (y i - fitReal A c i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              q i * (∑ j, A i j * (d j - c j)) * (y i - fitReal A c i) =
                  ∑ j, q i * (A i j * (d j - c j)) * (y i - fitReal A c i) := by
                rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ j, (d j - c j) * (q i * A i j * (y i - fitReal A c i)) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = ∑ j, ∑ i, (d j - c j) * (q i * A i j * (y i - fitReal A c i)) := by
            rw [Finset.sum_comm]
          _ = ∑ j, (d j - c j) * (∑ i, q i * A i j * (y i - fitReal A c i)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
      _ = 0 := by simp [hne]
  have hdecomp (d : Fin k → ℝ) :
      (∑ i, q i * (y i - fitReal A d i)^2) =
        (∑ i, q i * (y i - fitReal A c i)^2) +
          (∑ i, q i * (delta d i)^2) := by
    calc
      (∑ i, q i * (y i - fitReal A d i)^2) =
          ∑ i, (q i * (y i - fitReal A c i)^2 +
            q i * (delta d i)^2 - 2 * (q i * delta d i * (y i - fitReal A c i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfit : fitReal A d i = fitReal A c i + delta d i := by
          dsimp [delta]
          ring
        rw [hfit]
        ring
      _ = (∑ i, q i * (y i - fitReal A c i)^2) +
            (∑ i, q i * (delta d i)^2) -
              2 * (∑ i, q i * delta d i * (y i - fitReal A c i)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ i, q i * (y i - fitReal A c i)^2) +
            (∑ i, q i * (delta d i)^2) := by rw [hcross d]; ring
  constructor
  · intro d
    rw [hdecomp d]
    exact le_add_of_nonneg_right <| Finset.sum_nonneg fun i hi => mul_nonneg (hq i) (sq_nonneg _)
  · intro d hloss
    have hsum : (∑ i, q i * (delta d i)^2) = 0 := by
      have := hdecomp d
      linarith
    have hterms : ∀ i, q i * (delta d i)^2 = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi => mul_nonneg (hq i) (sq_nonneg (delta d i)))).mp hsum
      exact hz i (Finset.mem_univ i)
    have hweighted : ∀ i, q i * delta d i = 0 := by
      intro i
      rcases mul_eq_zero.mp (hterms i) with hqi | hsq
      · simp [hqi]
      · have hdi : delta d i = 0 := (sq_eq_zero_iff).mp hsq
        simp [hdi]
    have hmul (j : Fin k) : (gramReal A q *ᵥ (fun l => d l - c l)) j = 0 := by
      have hexpand : (gramReal A q *ᵥ (fun l => d l - c l)) j =
          ∑ i, q i * A i j * (∑ l, A i l * (d l - c l)) := by
        rw [Matrix.mulVec_apply_eq_sum]
        simp only [gramReal]
        calc
          (∑ l, (∑ i, q i * A i j * A i l) * (d l - c l)) =
              ∑ l, ∑ i, (q i * A i j * A i l) * (d l - c l) := by
            simp only [Finset.sum_mul]
          _ = ∑ i, ∑ l, (q i * A i j * A i l) * (d l - c l) := by
            exact Finset.sum_comm
          _ = ∑ i, q i * A i j * (∑ l, A i l * (d l - c l)) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              (∑ l, (q i * A i j * A i l) * (d l - c l)) =
                  ∑ l, (q i * A i j) * (A i l * (d l - c l)) := by
                apply Finset.sum_congr rfl
                intro l hl
                ring
              _ = q i * A i j * (∑ l, A i l * (d l - c l)) := by rw [Finset.mul_sum]
      rw [hexpand]
      simp_rw [← hdelta d]
      apply Finset.sum_eq_zero
      intro i hi
      calc
        q i * A i j * delta d i = A i j * (q i * delta d i) := by ring
        _ = 0 := by rw [hweighted i, mul_zero]
    have hdiff : (fun l => d l - c l) = 0 := by
      have hinj := Matrix.mulVec_injective_of_det_ne_zero hdet
      apply hinj
      funext j
      simpa using hmul j
    funext j
    have := congrFun hdiff j
    exact sub_eq_zero.mp this

end

end SAP.P026a.WH.W2.P.T7_L1

open Finset
open scoped BigOperators Matrix

theorem SAP.P026a.WH.W2.T7_L1_proof : SAP.P026a.WH.W2.T7_L1 := by
  intro k A q y c hvalid
  rcases hvalid with ⟨hq, hdet, hne⟩
  let Ar : Matrix (Fin 16) (Fin k) ℝ := fun i j => (A i j : ℝ)
  let qr : Fin 16 → ℝ := fun i => (q i : ℝ)
  let yr : Fin 16 → ℝ := fun i => (y i : ℝ)
  let cr : Fin k → ℝ := fun j => (c j : ℝ)
  have hqR : ∀ i, 0 ≤ qr i := by
    intro i
    change (0 : ℝ) ≤ (q i : ℝ)
    exact_mod_cast hq i
  have hneR : ∀ j, (∑ i, qr i * Ar i j *
      (yr i - SAP.P026a.WH.W2.P.T7_L1.fitReal Ar cr i)) = 0 := by
    intro j
    have hc := congrArg (fun x : ℚ => (x : ℝ)) (hne j)
    simpa [qr, Ar, yr, SAP.P026a.WH.W2.P.T7_L1.fitReal,
      SAP.P026a.w2Predict, map_sum, map_mul, map_sub] using hc
  have hgram : SAP.P026a.WH.W2.P.T7_L1.gramReal Ar qr =
      (Rat.castHom ℝ).mapMatrix (SAP.P026a.w2Gram A q) := by
    ext j l
    simp [SAP.P026a.WH.W2.P.T7_L1.gramReal, Ar, qr,
      SAP.P026a.w2Gram, RingHom.mapMatrix_apply, map_sum, map_mul]
  have hdetR : (SAP.P026a.WH.W2.P.T7_L1.gramReal Ar qr).det ≠ 0 := by
    rw [hgram]
    have hmap := RingHom.map_det (Rat.castHom ℝ) (SAP.P026a.w2Gram A q)
    rw [← hmap]
    change ((SAP.P026a.w2Gram A q).det : ℝ) ≠ 0
    exact_mod_cast hdet
  have hresult := SAP.P026a.WH.W2.P.T7_L1.real_weighted_ls_unique
    Ar qr yr cr hqR hdetR hneR
  constructor
  · intro d
    change (∑ i, qr i * (yr i - ∑ j, Ar i j * cr j)^2) ≤
      ∑ i, qr i * (yr i - ∑ j, Ar i j * d j)^2
    exact hresult.1 d
  · intro d hloss
    change (∑ i, qr i * (yr i - ∑ j, Ar i j * d j)^2) =
      ∑ i, qr i * (yr i - ∑ j, Ar i j * cr j)^2 at hloss
    exact hresult.2 d hloss
