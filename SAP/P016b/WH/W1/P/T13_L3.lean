import SAP.P016b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b.WH.W1.P.T13_L3

open SAP.P016b.WH.W1
open SAP.P016b
open scoped BigOperators Classical

lemma zipWith3_map_range {α β γ δ : Type} (F : α → β → γ → δ)
    (f : ℕ → α) (g : ℕ → β) (h : ℕ → γ) : ∀ n : ℕ,
    List.zipWith3 F (List.map f (List.range n)) (List.map g (List.range n))
      (List.map h (List.range n)) = List.map (fun i => F (f i) (g i) (h i)) (List.range n) := by
  intro n
  induction n generalizing F f g h with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
    change F (f 0) (g 0) (h 0) ::
        List.zipWith3 F (List.map (fun i => f (i+1)) (List.range n))
          (List.map (fun i => g (i+1)) (List.range n))
          (List.map (fun i => h (i+1)) (List.range n)) =
      F (f 0) (g 0) (h 0) ::
        List.map (fun i => F (f (i+1)) (g (i+1)) (h (i+1))) (List.range n)
    apply congrArg (List.cons (F (f 0) (g 0) (h 0)))
    exact ih F (fun i => f (i+1)) (fun i => g (i+1)) (fun i => h (i+1))

lemma forall₂_zipWith3 {α β γ α' β' γ' δ δ' : Type}
    {R₁ : α → α' → Prop} {R₂ : β → β' → Prop} {R₃ : γ → γ' → Prop}
    {S : δ → δ' → Prop}
    (f : α → β → γ → δ) (g : α' → β' → γ' → δ')
    {as : List α} {as' : List α'} {bs : List β} {bs' : List β'}
    {cs : List γ} {cs' : List γ'}
    (h₁ : List.Forall₂ R₁ as as') (h₂ : List.Forall₂ R₂ bs bs')
    (h₃ : List.Forall₂ R₃ cs cs')
    (h : ∀ a a' b b' c c', R₁ a a' → R₂ b b' → R₃ c c' → S (f a b c) (g a' b' c')) :
    List.Forall₂ S (List.zipWith3 f as bs cs) (List.zipWith3 g as' bs' cs') := by
  induction h₁ generalizing bs bs' cs cs' with
  | nil =>
    cases h₂ <;> cases h₃ <;> simp [List.zipWith3]
  | cons hab htail ih =>
    cases h₂ with
    | nil => simp [List.zipWith3]
    | cons hbc hbt =>
      cases h₃ with
      | nil => simp [List.zipWith3]
      | cons hcd hct =>
        constructor
        · exact h _ _ _ _ _ _ hab hbc hcd
        · exact ih hbt hct

lemma sum_map_range_eq_finset {R : Type} [AddCommMonoid R] (f : ℕ → R) : ∀ n : ℕ,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, ih]
    simp [Finset.sum_range_succ]

lemma reverse_map_range (f : ℕ → ℝ) : ∀ n : ℕ,
    ((List.range (n+1)).map f).reverse =
      (List.range (n+1)).map (fun i => f (n-i)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ((List.range (n+1+1)).map f).reverse =
          [f (n+1)] ++ ((List.range (n+1)).map f).reverse := by
        rw [List.range_succ]
        simp
      _ = [f (n+1)] ++ (List.range (n+1)).map (fun i => f (n-i)) := by rw [ih]
      _ = (List.range (n+1+1)).map (fun i => f (n+1-i)) := by
        conv_rhs => rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map]
        change f (n+1) :: (List.range (n+1)).map (fun i => f (n-i)) =
          f (n+1) :: (List.range (n+1)).map (fun i => f (n+1-(i+1)))
        congr 1
        apply List.map_congr_left
        intro i hi
        have hip : i < n+1 := List.mem_range.mp hi
        congr 1
        omega

end SAP.P016b.WH.W1.P.T13_L3

open SAP.P016b.WH.W1.P.T13_L3

theorem SAP.P016b.WH.W1.T13_L3_proof : SAP.P016b.WH.W1.T13_L3 := by
  intro ha hp scale outScale M B c hscale hout hM hc
  rcases ha with ⟨hratio, hmul, hnatmul, hsum, hrescale⟩
  rcases hp with ⟨hpow, hpowers⟩
  classical
  let coeff : List ℕ := (List.range (c+1)).map (Nat.fast_choose B)
  let rindices := List.range M
  let rowBounds : List NatBounds := rindices.map fun i =>
    mixtureRowBounds scale M B c (i+1) coeff
  let rowValues : List ℝ := rindices.map fun i =>
    ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
      (((i+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(i+1))/M)^(B-k)
  have hrow : ∀ i : ℕ, i < M →
      Encloses scale (mixtureRowBounds scale M B c (i+1) coeff)
        (∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
          (((i+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(i+1))/M)^(B-k)) := by
    intro i hi
    let r := i+1
    have hr : r ≤ M := by dsimp [r]; omega
    let p := boundsRatio scale r M
    let q := boundsRatio scale (M-r) M
    let x : ℝ := (r : ℝ)/(M : ℝ)
    let y : ℝ := ((M : ℝ)-(r : ℝ))/(M : ℝ)
    have hpr : Encloses scale p x := by
      simpa [p, x] using hratio scale r M hscale hM
    have hqr : Encloses scale q y := by
      have h := hratio scale (M-r) M hscale hM
      simpa [q, y, Nat.cast_sub hr] using h
    have hseedP : Encloses scale (boundsOne scale) (1 : ℝ) := by
      simp [Encloses, boundsOne]
    let ps := boundsPowersFrom scale p (boundsOne scale) (c+1)
    let pPowers := (List.range (c+1)).map fun k => x^k
    have hps0 := hpowers scale p (boundsOne scale) x 1 (c+1) hscale hpr hseedP
    have hps : List.Forall₂ (Encloses scale)
        ps pPowers := by
      simpa only [one_mul] using hps0
    have hseedQ : Encloses scale (boundsPow scale q (B-c)) (y^(B-c)) :=
      hpow scale q y (B-c) hscale hqr
    let qs := boundsPowersFrom scale q (boundsPow scale q (B-c)) (c+1)
    let qsRev := qs.reverse
    have hqs0 := hpowers scale q (boundsPow scale q (B-c)) y (y^(B-c))
      (c+1) hscale hqr hseedQ
    let qIntermediate := (List.range (c+1)).map fun k => y^(B-c)*y^(c-k)
    let qPowers := (List.range (c+1)).map fun k => y^(B-k)
    have hqs : List.Forall₂ (Encloses scale)
        qs
        ((List.range (c+1)).map fun j => y^(B-c)*y^j) := by
      simpa using hqs0
    have hqrev0 : List.Forall₂ (Encloses scale) qsRev
        (((List.range (c+1)).map fun j => y^(B-c)*y^j).reverse) := by
      exact (List.forall₂_reverse_iff).mpr hqs
    have hqrev1 : List.Forall₂ (Encloses scale) qsRev qIntermediate := by
      simpa [qsRev, qIntermediate, reverse_map_range (fun j => y^(B-c)*y^j) c]
        using hqrev0
    have hqeq : qIntermediate = qPowers := by
      apply List.map_congr_left
      intro k hk
      have hkc : k ≤ c := by
        have := List.mem_range.mp hk
        omega
      have hexp : (B-c)+(c-k) = B-k := by omega
      calc
        y^(B-c)*y^(c-k) = y^((B-c)+(c-k)) := by rw [← pow_add]
        _ = y^(B-k) := by rw [hexp]
    have hqrev : List.Forall₂ (Encloses scale) qsRev qPowers := by
      simpa [hqeq] using hqrev1
    have hterms : List.Forall₂ (Encloses scale)
        (List.zipWith3 (fun n a b => boundsNatMul n (boundsMul scale a b))
          coeff ps qsRev)
        (List.zipWith3 (fun (n : ℕ) a b => (n : ℝ)*(a*b)) coeff pPowers qPowers) := by
      have hcoeff : List.Forall₂ (fun n n' : ℕ => n = n') coeff coeff :=
        List.forall₂_refl coeff
      apply forall₂_zipWith3
        (fun n a b => boundsNatMul n (boundsMul scale a b))
        (fun (n : ℕ) a b => (n : ℝ)*(a*b))
        hcoeff hps hqrev
      intro n n' a a' b b' hnn hp hq
      subst n'
      exact hnatmul scale n _ _ hscale (hmul scale _ _ _ _ hscale hp hq)
    let boundTerms := List.zipWith3
      (fun n a b => boundsNatMul n (boundsMul scale a b)) coeff ps qsRev
    let realTerms := List.zipWith3 (fun (n : ℕ) a b => (n : ℝ)*(a*b)) coeff pPowers qPowers
    have htermSum : Encloses scale (boundsSum boundTerms) realTerms.sum := by
      exact hsum scale boundTerms realTerms hscale hterms
    have hrealTerms : realTerms = (List.range (c+1)).map
        (fun k => (Nat.fast_choose B k : ℝ) * (x^k * y^(B-k))) := by
      change List.zipWith3 (fun (n : ℕ) a b => (n : ℝ)*(a*b))
        ((List.range (c+1)).map (Nat.fast_choose B))
        ((List.range (c+1)).map fun k => x^k)
        ((List.range (c+1)).map fun k => y^(B-k)) = _
      exact zipWith3_map_range (fun (n : ℕ) a b => (n : ℝ)*(a*b))
        (Nat.fast_choose B) (fun k => x^k) (fun k => y^(B-k)) (c+1)
    have hrealSum : realTerms.sum =
        ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
          (x^k * y^(B-k)) := by
      rw [hrealTerms]
      exact sum_map_range_eq_finset
        (fun k => (Nat.fast_choose B k : ℝ) * (x^k * y^(B-k))) (c+1)
    have hrowSum : Encloses scale
        (boundsSum (List.zipWith3
          (fun n a b => boundsNatMul n (boundsMul scale a b)) coeff ps qsRev))
        (∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
          (x^k * y^(B-k))) := by
      simpa [hrealSum, ps, pPowers, x, y, r, qsRev, p, q, coeff,
        mixtureRowBounds, List.zipWith_zipWith_right] using htermSum
    have hrowTarget : (∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
          (x^k * y^(B-k))) =
        ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
          (((r : ℝ)/M)^k) * (((M : ℝ)-r)/M)^(B-k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [x, y]
      ring
    have hrowRes : Encloses scale
        (mixtureRowBounds scale M B c (i+1) coeff)
        (∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
          (((i+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(i+1))/M)^(B-k)) := by
      have hbound : boundsSum boundTerms =
          mixtureRowBounds scale M B c (i+1) coeff := by
        simp [boundTerms, mixtureRowBounds, ps, qsRev, qs, p, q, r, coeff,
          List.zipWith_zipWith_right]
      rw [hrowTarget, hbound] at hrowSum
      simpa [r, x, y] using hrowSum
    simpa [r] using hrowRes
  have hrows : List.Forall₂ (Encloses scale) rowBounds rowValues := by
    change List.Forall₂ (Encloses scale)
      (rindices.map fun i => mixtureRowBounds scale M B c (i+1) coeff)
      (rindices.map fun i => ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
        (((i+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(i+1))/M)^(B-k))
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro i hi
    exact hrow i (List.mem_range.mp hi)
  have hrowsSum : Encloses scale (boundsSum rowBounds) rowValues.sum :=
    hsum scale rowBounds rowValues hscale hrows
  have houter : rowValues.sum = ∑ r : Fin M,
      ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
        (((r.val+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(r.val+1))/M)^(B-k) := by
    calc
      rowValues.sum = ∑ i ∈ Finset.range M,
          ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
            (((i+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(i+1))/M)^(B-k) := by
        simpa [rowValues, rindices] using sum_map_range_eq_finset
          (fun i => ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
            (((i+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(i+1))/M)^(B-k)) M
      _ = ∑ r : Fin M,
          ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
            (((r.val+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(r.val+1))/M)^(B-k) := by
        exact (Fin.sum_univ_eq_sum_range
          (fun i => ∑ k ∈ Finset.range (c+1), (Nat.fast_choose B k : ℝ) *
            (((i+1 : ℕ) : ℝ)/M)^k * (((M : ℝ)-(i+1))/M)^(B-k)) M).symm
  have hmixture : (2 : ℝ)/(M : ℝ) * rowValues.sum = binomialMixture M B c := by
    rw [houter]
    unfold binomialMixture
    simp [Nat.choose_eq_fast_choose]
  have hfactor : Encloses scale (boundsRatio scale 2 M) ((2 : ℝ)/(M : ℝ)) :=
    hratio scale 2 M hscale hM
  have hmulRows := hmul scale (boundsRatio scale 2 M) (boundsSum rowBounds)
    ((2 : ℝ)/(M : ℝ)) rowValues.sum hscale hfactor hrowsSum
  have hscaled := hrescale scale outScale
    (boundsMul scale (boundsRatio scale 2 M) (boundsSum rowBounds))
    (((2 : ℝ)/(M : ℝ))*rowValues.sum) hscale hout hmulRows
  rw [hmixture] at hscaled
  simpa [mixtureBounds, rowBounds, rowValues, rindices, coeff] using hscaled
