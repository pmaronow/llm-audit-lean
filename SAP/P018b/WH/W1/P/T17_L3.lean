import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W1.P.T17_L3

open Finset Matrix
open scoped BigOperators

def u0 {N : ℕ} (hN : 4 < N) : Fin N := ⟨0, by omega⟩
def u1 {N : ℕ} (hN : 4 < N) : Fin N := ⟨1, by omega⟩
def u2 {N : ℕ} (hN : 4 < N) : Fin N := ⟨2, by omega⟩
def u3 {N : ℕ} (hN : 4 < N) : Fin N := ⟨3, by omega⟩

def e01 {N : ℕ} (hN : 4 < N) : Dyad N :=
  AronowAudit.P018.Wave1.printed_mkDyad (u0 hN) (u1 hN) (by
    intro h
    have := congrArg Fin.val h
    simp [u0, u1] at this)
def e02 {N : ℕ} (hN : 4 < N) : Dyad N :=
  AronowAudit.P018.Wave1.printed_mkDyad (u0 hN) (u2 hN) (by
    intro h
    have := congrArg Fin.val h
    simp [u0, u2] at this)
def e13 {N : ℕ} (hN : 4 < N) : Dyad N :=
  AronowAudit.P018.Wave1.printed_mkDyad (u1 hN) (u3 hN) (by
    intro h
    have := congrArg Fin.val h
    simp [u1, u3] at this)
def e23 {N : ℕ} (hN : 4 < N) : Dyad N :=
  AronowAudit.P018.Wave1.printed_mkDyad (u2 hN) (u3 hN) (by
    intro h
    have := congrArg Fin.val h
    simp [u2, u3] at this)

def support {N : ℕ} (hN : 4 < N) : Finset (Dyad N) :=
  {e01 hN, e02 hN, e13 hN, e23 hN}

lemma endpoint_eq {N : ℕ} {d : Dyad N} {i j : Fin N}
    (hij : i < j) (hi : firstUnit d = i) (hj : secondUnit d = j) :
    d = AronowAudit.P018.Wave1.printed_mkDyad i j hij.ne := by
  apply Subtype.ext
  change members d = ({i, j} : Finset (Fin N))
  calc
    members d = {firstUnit d, secondUnit d} :=
      AronowAudit.P018.Wave1.printed_members_endpoints d
    _ = {i, j} := by rw [hi, hj]

lemma y_e01 {N : ℕ} (hN : 4 < N) : wholePaddedY (e01 hN) = 1 := by
  have he := AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u0 hN) (u1 hN) (by simp [u0, u1])
  rw [wholePaddedY, show firstUnit (e01 hN) = u0 hN from he.1,
      show secondUnit (e01 hN) = u1 hN from he.2]
  norm_num [wholePaddedY, u0, u1]

lemma y_e02 {N : ℕ} (hN : 4 < N) : wholePaddedY (e02 hN) = -1 := by
  have he := AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u0 hN) (u2 hN) (by simp [u0, u2])
  rw [wholePaddedY, show firstUnit (e02 hN) = u0 hN from he.1,
      show secondUnit (e02 hN) = u2 hN from he.2]
  norm_num [wholePaddedY, u0, u2]

lemma y_e13 {N : ℕ} (hN : 4 < N) : wholePaddedY (e13 hN) = -1 := by
  have he := AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u1 hN) (u3 hN) (by simp [u1, u3])
  rw [wholePaddedY, show firstUnit (e13 hN) = u1 hN from he.1,
      show secondUnit (e13 hN) = u3 hN from he.2]
  norm_num [wholePaddedY, u1, u3]

lemma y_e23 {N : ℕ} (hN : 4 < N) : wholePaddedY (e23 hN) = 1 := by
  have he := AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u2 hN) (u3 hN) (by simp [u2, u3])
  rw [wholePaddedY, show firstUnit (e23 hN) = u2 hN from he.1,
      show secondUnit (e23 hN) = u3 hN from he.2]
  norm_num [wholePaddedY, u2, u3]

lemma edge_ne_of_first {N : ℕ} {d e : Dyad N} {i j : Fin N}
    (hd : firstUnit d = i) (he : firstUnit e = j) (hij : i ≠ j) : d ≠ e := by
  intro h
  apply hij
  calc
    i = firstUnit d := hd.symm
    _ = firstUnit e := congrArg firstUnit h
    _ = j := he

lemma edge_ne_of_second {N : ℕ} {d e : Dyad N} {i j : Fin N}
    (hd : secondUnit d = i) (he : secondUnit e = j) (hij : i ≠ j) : d ≠ e := by
  intro h
  apply hij
  calc
    i = secondUnit d := hd.symm
    _ = secondUnit e := congrArg secondUnit h
    _ = j := he

lemma first_e01 {N : ℕ} (hN : 4 < N) : firstUnit (e01 hN) = u0 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u0 hN) (u1 hN) (by simp [u0, u1])).1
lemma second_e01 {N : ℕ} (hN : 4 < N) : secondUnit (e01 hN) = u1 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u0 hN) (u1 hN) (by simp [u0, u1])).2
lemma first_e02 {N : ℕ} (hN : 4 < N) : firstUnit (e02 hN) = u0 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u0 hN) (u2 hN) (by simp [u0, u2])).1
lemma second_e02 {N : ℕ} (hN : 4 < N) : secondUnit (e02 hN) = u2 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u0 hN) (u2 hN) (by simp [u0, u2])).2
lemma first_e13 {N : ℕ} (hN : 4 < N) : firstUnit (e13 hN) = u1 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u1 hN) (u3 hN) (by simp [u1, u3])).1
lemma second_e13 {N : ℕ} (hN : 4 < N) : secondUnit (e13 hN) = u3 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u1 hN) (u3 hN) (by simp [u1, u3])).2
lemma first_e23 {N : ℕ} (hN : 4 < N) : firstUnit (e23 hN) = u2 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u2 hN) (u3 hN) (by simp [u2, u3])).1
lemma second_e23 {N : ℕ} (hN : 4 < N) : secondUnit (e23 hN) = u3 hN :=
  (AronowAudit.P018.Wave1.printed_mkDyad_endpoints (u2 hN) (u3 hN) (by simp [u2, u3])).2

lemma u01_ne {N : ℕ} (hN : 4 < N) : u0 hN ≠ u1 hN := by
  intro h
  have hh := congrArg Fin.val h
  norm_num [u0, u1] at hh
lemma u02_ne {N : ℕ} (hN : 4 < N) : u0 hN ≠ u2 hN := by
  intro h
  have hh := congrArg Fin.val h
  norm_num [u0, u2] at hh
lemma u12_ne {N : ℕ} (hN : 4 < N) : u1 hN ≠ u2 hN := by
  intro h
  have hh := congrArg Fin.val h
  norm_num [u1, u2] at hh
lemma u03_ne {N : ℕ} (hN : 4 < N) : u0 hN ≠ u3 hN := by
  intro h
  have hh := congrArg Fin.val h
  norm_num [u0, u3] at hh
lemma u13_ne {N : ℕ} (hN : 4 < N) : u1 hN ≠ u3 hN := by
  intro h
  have hh := congrArg Fin.val h
  norm_num [u1, u3] at hh
lemma u23_ne {N : ℕ} (hN : 4 < N) : u2 hN ≠ u3 hN := by
  intro h
  have hh := congrArg Fin.val h
  norm_num [u2, u3] at hh

lemma e01_ne_e02 {N : ℕ} (hN : 4 < N) : e01 hN ≠ e02 hN :=
  edge_ne_of_second (second_e01 hN) (second_e02 hN) (u12_ne hN)
lemma e01_ne_e13 {N : ℕ} (hN : 4 < N) : e01 hN ≠ e13 hN :=
  edge_ne_of_first (first_e01 hN) (first_e13 hN) (u01_ne hN)
lemma e01_ne_e23 {N : ℕ} (hN : 4 < N) : e01 hN ≠ e23 hN :=
  edge_ne_of_first (first_e01 hN) (first_e23 hN) (u02_ne hN)
lemma e02_ne_e13 {N : ℕ} (hN : 4 < N) : e02 hN ≠ e13 hN :=
  edge_ne_of_first (first_e02 hN) (first_e13 hN) (u01_ne hN)
lemma e02_ne_e23 {N : ℕ} (hN : 4 < N) : e02 hN ≠ e23 hN :=
  edge_ne_of_first (first_e02 hN) (first_e23 hN) (u02_ne hN)
lemma e13_ne_e23 {N : ℕ} (hN : 4 < N) : e13 hN ≠ e23 hN :=
  edge_ne_of_first (first_e13 hN) (first_e23 hN) (u12_ne hN)

lemma support_mem01 {N : ℕ} (hN : 4 < N) : e01 hN ∈ support hN := by simp [support]
lemma support_mem02 {N : ℕ} (hN : 4 < N) : e02 hN ∈ support hN := by simp [support]
lemma support_mem13 {N : ℕ} (hN : 4 < N) : e13 hN ∈ support hN := by simp [support]
lemma support_mem23 {N : ℕ} (hN : 4 < N) : e23 hN ∈ support hN := by simp [support]

@[simp] lemma members_e01 {N : ℕ} (hN : 4 < N) : members (e01 hN) = {u0 hN, u1 hN} := by
  simp [members, e01, AronowAudit.P018.Wave1.printed_mkDyad]
@[simp] lemma members_e02 {N : ℕ} (hN : 4 < N) : members (e02 hN) = {u0 hN, u2 hN} := by
  simp [members, e02, AronowAudit.P018.Wave1.printed_mkDyad]
@[simp] lemma members_e13 {N : ℕ} (hN : 4 < N) : members (e13 hN) = {u1 hN, u3 hN} := by
  simp [members, e13, AronowAudit.P018.Wave1.printed_mkDyad]
@[simp] lemma members_e23 {N : ℕ} (hN : 4 < N) : members (e23 hN) = {u2 hN, u3 hN} := by
  simp [members, e23, AronowAudit.P018.Wave1.printed_mkDyad]

lemma padded_support {N : ℕ} (hN : 4 < N) (d : Dyad N)
    (hy : wholePaddedY d ≠ 0) : d ∈ support hN := by
  classical
  unfold wholePaddedY at hy
  split_ifs at hy with h01 h02 h13 h23
  · have hi : firstUnit d = u0 hN := Fin.ext (by simpa [u0] using h01.1)
    have hj : secondUnit d = u1 hN := Fin.ext (by simpa [u1] using h01.2)
    have he := endpoint_eq (d := d) (i := u0 hN) (j := u1 hN) (by simp [u0, u1]) hi hj
    rw [he]
    exact support_mem01 hN
  · have hi : firstUnit d = u0 hN := Fin.ext (by simpa [u0] using h02.1)
    have hj : secondUnit d = u2 hN := Fin.ext (by simpa [u2] using h02.2)
    have he := endpoint_eq (d := d) (i := u0 hN) (j := u2 hN) (by simp [u0, u2]) hi hj
    rw [he]
    exact support_mem02 hN
  · have hi : firstUnit d = u1 hN := Fin.ext (by simpa [u1] using h13.1)
    have hj : secondUnit d = u3 hN := Fin.ext (by simpa [u3] using h13.2)
    have he := endpoint_eq (d := d) (i := u1 hN) (j := u3 hN) (by simp [u1, u3]) hi hj
    rw [he]
    exact support_mem13 hN
  · have hi : firstUnit d = u2 hN := Fin.ext (by simpa [u2] using h23.1)
    have hj : secondUnit d = u3 hN := Fin.ext (by simpa [u3] using h23.2)
    have he := endpoint_eq (d := d) (i := u2 hN) (j := u3 hN) (by simp [u2, u3]) hi hj
    rw [he]
    exact support_mem23 hN
  · norm_num at hy

lemma sum_supported {N : ℕ} {α : Type*} [AddCommMonoid α]
    (S : Finset (Dyad N)) (f : Dyad N → α)
    (hz : ∀ d, d ∉ S → f d = 0) :
    (∑ d : Dyad N, f d) = ∑ d ∈ S, f d := by
  classical
  calc
    (∑ d : Dyad N, f d) = ∑ d ∈ (Finset.univ : Finset (Dyad N)), f d := by simp
    _ = ∑ d ∈ S, f d := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro d hd hnot
      exact hz d hnot

end SAP.P018b.WH.W1.P.T17_L3

open SAP.P018b.WH.W1.P.T17_L3

theorem SAP.P018b.WH.W1.T17_L3_proof : SAP.P018b.WH.W1.T17_L3 := by
  classical
  intro N hN
  let X : Dyad N → Vec 1 := wholeInterceptX (Dyad N)
  let Y : Dyad N → ℝ := wholePaddedY
  let S := support hN
  let q : Dyad N → Vec 1 := fun d => ![Y d]
  have hzero_out (d : Dyad N) (hd : d ∉ S) : Y d = 0 := by
    by_contra hy
    exact hd (padded_support hN d hy)
  have hsumY : (∑ d : Dyad N, Y d) = 0 := by
    rw [sum_supported S Y hzero_out]
    norm_num [S, support, Y, e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN,
      e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN, y_e01, y_e02, y_e13, y_e23]
  have hsumY2 : (∑ d : Dyad N, (Y d)^2) = 4 := by
    have hz2 (d : Dyad N) (hd : d ∉ S) : (Y d)^2 = 0 := by rw [hzero_out d hd]; norm_num
    rw [sum_supported S (fun d => (Y d)^2) hz2]
    norm_num [S, support, Y, e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN,
      e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN, y_e01, y_e02, y_e13, y_e23]
  have hgram : sampleGram X = Dreal N • (1 : Mat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [sampleGram, Matrix.sum_apply, outer, X, wholeInterceptX]
    have hc : (Fintype.card (Dyad N) : ℝ) = Dreal N := by
      simpa [Dyad, dyads, Dreal, AronowAudit.P018.Dreal, AronowAudit.P018.Dyad,
        AronowAudit.P018.dyads] using AronowAudit.P018.Wave1.printed_card_real N
    simpa [Finset.sum_const, nsmul_eq_mul, mul_one] using hc
  have hD : 0 < Dreal N := by
    simpa [Dreal, AronowAudit.P018.Dreal] using
      (AronowAudit.P018.Wave1.printed_Dpos (N := N) (by omega))
  have hdet : (sampleGram X).det = Dreal N := by
    rw [hgram]
    norm_num [Matrix.det_fin_one]
  have hinv : (sampleGram X)⁻¹ = (Dreal N)⁻¹ • (1 : Mat 1) := by
    rw [hgram, AronowAudit.P018.matrix_inverse_scale_total _ _ hD.ne']
    simp
  have hscore' : (∑ d : Dyad N, score (X d) (Y d)) = ∑ d : Dyad N, q d := by
    apply Finset.sum_congr rfl
    intro d hd
    ext i
    fin_cases i
    simp [q, X, score, wholeInterceptX]
  have hqsum : (∑ d : Dyad N, q d) = 0 := by
    ext i
    fin_cases i
    simp only [Finset.sum_apply, q, Matrix.cons_val_zero]
    exact hsumY
  have hscore : (∑ d : Dyad N, score (X d) (Y d)) = 0 := by rw [hscore', hqsum]
  have hfit : sampleOLS X Y = 0 := by
    unfold sampleOLS
    rw [hscore]
    simp
  have hres (d : Dyad N) : fittedResidual X Y d = Y d := by
    simp [fittedResidual, hfit, X, wholeInterceptX, dot]
  have hq : (fun d => score (X d) (fittedResidual X Y d)) = q := by
    funext d
    ext j
    fin_cases j
    simp [q, score, hres, X, wholeInterceptX]
  have hunit (i : Fin N) : unitScore members q i = 0 := by
    have hz (d : Dyad N) (hd : d ∉ S) : (if i ∈ members d then q d else 0) = 0 := by
      simp [q, hzero_out d hd]
    unfold unitScore
    rw [sum_supported S (fun d => if i ∈ members d then q d else 0) hz]
    by_cases hi0 : i = u0 hN
    · subst i
      simp [S, support, q, Y, u0, u1, u2, u3, y_e01, y_e02, y_e13, y_e23,
        u01_ne hN, u02_ne hN, u12_ne hN, u03_ne hN, u13_ne hN, u23_ne hN,
        (Ne.symm (u01_ne hN)), (Ne.symm (u02_ne hN)), (Ne.symm (u12_ne hN)),
        (Ne.symm (u03_ne hN)), (Ne.symm (u13_ne hN)), (Ne.symm (u23_ne hN)),
        e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN, e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN]
    · by_cases hi1 : i = u1 hN
      · subst i
        simp [S, support, q, Y, u0, u1, u2, u3, y_e01, y_e02, y_e13, y_e23,
          u01_ne hN, u02_ne hN, u12_ne hN, u03_ne hN, u13_ne hN, u23_ne hN,
          (Ne.symm (u01_ne hN)), (Ne.symm (u02_ne hN)), (Ne.symm (u12_ne hN)),
          (Ne.symm (u03_ne hN)), (Ne.symm (u13_ne hN)), (Ne.symm (u23_ne hN)),
          e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN, e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN]
      · by_cases hi2 : i = u2 hN
        · subst i
          simp [S, support, q, Y, u0, u1, u2, u3, y_e01, y_e02, y_e13, y_e23,
            u01_ne hN, u02_ne hN, u12_ne hN, u03_ne hN, u13_ne hN, u23_ne hN,
            (Ne.symm (u01_ne hN)), (Ne.symm (u02_ne hN)), (Ne.symm (u12_ne hN)),
            (Ne.symm (u03_ne hN)), (Ne.symm (u13_ne hN)), (Ne.symm (u23_ne hN)),
            e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN, e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN]
        · by_cases hi3 : i = u3 hN
          · subst i
            simp [S, support, q, Y, u0, u1, u2, u3, y_e01, y_e02, y_e13, y_e23,
              u01_ne hN, u02_ne hN, u12_ne hN, u03_ne hN, u13_ne hN, u23_ne hN,
              (Ne.symm (u01_ne hN)), (Ne.symm (u02_ne hN)), (Ne.symm (u12_ne hN)),
              (Ne.symm (u03_ne hN)), (Ne.symm (u13_ne hN)), (Ne.symm (u23_ne hN)),
              e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN, e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN]
          · simp [u0, u1, u2, u3] at hi0 hi1 hi2 hi3
            simp [S, support, q, Y, u0, u1, u2, u3, hi0, hi1, hi2, hi3, y_e01, y_e02, y_e13, y_e23,
              e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN, e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN]
  have hdyad : (dyadMeat q) 0 0 = 4 := by
    have hz (d : Dyad N) (hd : d ∉ S) : (outer (q d) (q d)) 0 0 = 0 := by
      simp [outer, q, hzero_out d hd]
    unfold dyadMeat
    simp only [Matrix.sum_apply]
    rw [sum_supported S (fun d => (outer (q d) (q d)) 0 0) hz]
    norm_num [S, support, q, Y, outer, e01_ne_e02 hN, e01_ne_e13 hN, e01_ne_e23 hN,
      e02_ne_e13 hN, e02_ne_e23 hN, e13_ne_e23 hN, y_e01, y_e02, y_e13, y_e23]
  have hmeat : (meat members q) 0 0 = -4 := by
    change (meat members q) 0 0 = -4
    have hid := AronowAudit.P018.overlap_meat_identity members members_card
      (fun d e h => Subtype.ext h) q
    have hid00 := congrFun (congrFun hid 0) 0
    have hid' : (meat members q) 0 0 =
        ((∑ i : Fin N, outer (unitScore members q i) (unitScore members q i)) - dyadMeat q) 0 0 := by
      dsimp [SAP.P018b.meat, SAP.P018b.unitScore, SAP.P018b.dyadMeat, SAP.P018b.outer,
        AronowAudit.P018.meat, AronowAudit.P018.unitScore, AronowAudit.P018.dyadMeat,
        AronowAudit.P018.outer] at hid00 ⊢
      exact hid00
    calc
      (meat members q) 0 0 =
          ((∑ i : Fin N, outer (unitScore members q i) (unitScore members q i)) -
            dyadMeat q) 0 0 := hid'
      _ = -4 := by
        simp only [Matrix.sub_apply, Matrix.sum_apply, outer, Matrix.of_apply]
        rw [hdyad]
        simp [hunit]
  refine ⟨hdet, hD, ?_, ?_, ?_⟩
  · simpa [X, Y] using hfit
  · intro d
    simpa [X, Y] using hres d
  · have hv : sampleVariance members X Y 0 0 = (Dreal N)⁻¹ * (-4) * (Dreal N)⁻¹ := by
      rw [sampleVariance, hq, hinv]
      simp [sandwich, Matrix.mul_apply, Fin.sum_univ_one, hmeat]
    rw [hv]
    field_simp
    <;> ring

