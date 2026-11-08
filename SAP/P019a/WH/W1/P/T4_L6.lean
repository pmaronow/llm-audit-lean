import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T4_L6

open SAP.P019a Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical
universe u

theorem whole_prob_congr {Ω : Type u} [MeasurableSpace Ω] (P : WholeMeasureLaw Ω)
    (D1 D2 : Ω → Prop) [DecidablePred D1] [DecidablePred D2]
    (hD : ∀ ω, D1 ω ↔ D2 ω) : P.prob D1 = P.prob D2 := by
  unfold WholeMeasureLaw.prob WholeMeasureLaw.mean
  apply congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂P.measure)
  funext ω
  by_cases h1 : D1 ω
  · have h2 : D2 ω := (hD ω).mp h1
    simp [h1, h2]
  · have h2 : ¬D2 ω := fun h2 => h1 ((hD ω).mpr h2)
    simp [h1, h2]

theorem finite_prob_congr {E : Type*} [Fintype E] (P : FiniteLaw E)
    (D1 D2 : E → Prop) [DecidablePred D1] [DecidablePred D2]
    (hD : ∀ ω, D1 ω ↔ D2 ω) : P.prob D1 = P.prob D2 := by
  unfold SAP.P019a.FiniteLaw.prob
  apply congrArg P.mean
  funext ω
  by_cases h1 : D1 ω
  · have h2 : D2 ω := (hD ω).mp h1
    simp [h1, h2]
  · have h2 : ¬D2 ω := fun h2 => h1 ((hD ω).mpr h2)
    simp [h1, h2]

theorem whole_ce_congr {Ω : Type u} [MeasurableSpace Ω] (P : WholeMeasureLaw Ω)
    (f1 f2 : Ω → ℝ) (D1 D2 : Ω → Prop) [DecidablePred D1] [DecidablePred D2]
    (hf : ∀ ω, f1 ω = f2 ω) (hD : ∀ ω, D1 ω ↔ D2 ω) :
    P.ce f1 D1 = P.ce f2 D2 := by
  unfold WholeMeasureLaw.ce
  have hn : P.mean (fun ω => if D1 ω then f1 ω else 0) =
      P.mean (fun ω => if D2 ω then f2 ω else 0) := by
    unfold WholeMeasureLaw.mean
    apply congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂P.measure)
    funext ω
    by_cases h1 : D1 ω
    · have h2 : D2 ω := (hD ω).mp h1
      simp [h1, h2, hf ω]
    · have h2 : ¬D2 ω := fun h2 => h1 ((hD ω).mpr h2)
      simp [h1, h2]
  rw [hn, whole_prob_congr P D1 D2 hD]

theorem finite_ce_congr {E : Type*} [Fintype E] (P : FiniteLaw E)
    (f1 f2 : E → ℝ) (D1 D2 : E → Prop) [DecidablePred D1] [DecidablePred D2]
    (hf : ∀ ω, f1 ω = f2 ω) (hD : ∀ ω, D1 ω ↔ D2 ω) :
    P.ce f1 D1 = P.ce f2 D2 := by
  unfold SAP.P019a.FiniteLaw.ce
  have hn : P.mean (fun ω => if D1 ω then f1 ω else 0) =
      P.mean (fun ω => if D2 ω then f2 ω else 0) := by
    apply congrArg P.mean
    funext ω
    by_cases h1 : D1 ω
    · have h2 : D2 ω := (hD ω).mp h1
      simp [h1, h2, hf ω]
    · have h2 : ¬D2 ω := fun h2 => h1 ((hD ω).mpr h2)
      simp [h1, h2]
  rw [hn, finite_prob_congr P D1 D2 hD]

theorem whole_ccov_congr {Ω : Type u} [MeasurableSpace Ω] (P : WholeMeasureLaw Ω)
    (f1 f2 g1 g2 : Ω → ℝ) (D1 D2 : Ω → Prop)
    [DecidablePred D1] [DecidablePred D2]
    (hf : ∀ ω, f1 ω = f2 ω) (hg : ∀ ω, g1 ω = g2 ω)
    (hD : ∀ ω, D1 ω ↔ D2 ω) : P.ccov f1 g1 D1 = P.ccov f2 g2 D2 := by
  unfold WholeMeasureLaw.ccov
  rw [whole_ce_congr P (fun ω => f1 ω*g1 ω) (fun ω => f2 ω*g2 ω) D1 D2
      (by intro ω; rw [hf ω, hg ω]) hD,
    whole_ce_congr P f1 f2 D1 D2 hf hD,
    whole_ce_congr P g1 g2 D1 D2 hg hD]

theorem finite_ccov_congr {E : Type*} [Fintype E] (P : FiniteLaw E)
    (f1 f2 g1 g2 : E → ℝ) (D1 D2 : E → Prop)
    [DecidablePred D1] [DecidablePred D2]
    (hf : ∀ ω, f1 ω = f2 ω) (hg : ∀ ω, g1 ω = g2 ω)
    (hD : ∀ ω, D1 ω ↔ D2 ω) : P.ccov f1 g1 D1 = P.ccov f2 g2 D2 := by
  unfold SAP.P019a.FiniteLaw.ccov
  rw [finite_ce_congr P (fun ω => f1 ω*g1 ω) (fun ω => f2 ω*g2 ω) D1 D2
      (by intro ω; rw [hf ω, hg ω]) hD,
    finite_ce_congr P f1 f2 D1 D2 hf hD,
    finite_ce_congr P g1 g2 D1 D2 hg hD]

def obsX (o : WholeObservation) : Bool := o.2.1
def obsY (o : WholeObservation) : Bool := o.2.2.1
def obsZ (o : WholeObservation) : Bool := o.2.2.2.1
def obsV (o : WholeObservation) : ℕ := o.2.2.2.2

def obsCell (z y : Bool) (o : WholeObservation) : Prop := obsZ o = z ∧ obsY o = y

def obsCellCount {n : ℕ} (x : Fin n → WholeObservation) (z y : Bool) : ℕ :=
  ∑ i, if obsCell z y (x i) then 1 else 0

def obsNegativeCount {n : ℕ} (x : Fin n → WholeObservation) : ℕ :=
  obsCellCount x true false + obsCellCount x false false

def obsYbar {n : ℕ} (x : Fin n → WholeObservation) : ℝ :=
  (∑ i, bitVal (obsY (x i))) / (n : ℝ)

def obsCellMean {n : ℕ} (x : Fin n → WholeObservation) (z y : Bool) (c : ℝ) : ℝ :=
  if obsCellCount x z y = 0 then c else
    (∑ i, if obsCell z y (x i) then (obsV (x i) : ℝ) else 0) /
      (obsCellCount x z y : ℝ)

def obsA {n : ℕ} (x : Fin n → WholeObservation) : ℝ := 1 - obsYbar x

def obsB {n : ℕ} (x : Fin n → WholeObservation) (c1 c0 : ℝ) : ℝ :=
  obsCellMean x true false c1 - obsCellMean x false false c0 - 1

def obsMuHat {n : ℕ} (x : Fin n → WholeObservation) (c1 c0 : ℝ) : ℝ :=
  obsYbar x + (1 - obsYbar x) *
    (obsCellMean x true false c1 - obsCellMean x false false c0)

def obsOccupied {n : ℕ} (x : Fin n → WholeObservation) : Prop :=
  0 < obsCellCount x true false ∧ 0 < obsCellCount x false false

def obsH {n : ℕ} (x : Fin n → WholeObservation) (v1 v0 : ℝ) : ℝ :=
  v1 / (obsCellCount x true false : ℝ) + v0 / (obsCellCount x false false : ℝ)

def gObsSample {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) : Fin n → WholeObservation := fun i => G.observable (s i)

def sObsSample {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) : Fin n → WholeObservation := fun i => S.wholeObservable (s i)

theorem sample_mean_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (n : ℕ) (f : (Fin n → WholeObservation) → ℝ) :
    (G.law.iid n).mean (fun s => f (gObsSample G s)) =
      (S.law.iid n).mean (fun s => f (sObsSample S s)) := by
  change (G.law.iid n).mean (fun s => f (fun i => G.observable (s i))) =
    (S.law.iid n).mean (fun s => f (fun i => S.wholeObservable (s i)))
  exact hrep.2 n f

theorem sample_prob_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (n : ℕ) (D : (Fin n → WholeObservation) → Prop)
    [DecidablePred (fun s => D (gObsSample G s))]
    [DecidablePred (fun s => D (sObsSample S s))] :
    (G.law.iid n).prob (fun s => D (gObsSample G s)) =
      (S.law.iid n).prob (fun s => D (sObsSample S s)) := by
  change (G.law.iid n).mean (fun s => if D (gObsSample G s) then (1 : ℝ) else 0) =
    (S.law.iid n).mean (fun s => if D (sObsSample S s) then (1 : ℝ) else 0)
  have hg : (fun s => if D (gObsSample G s) then (1 : ℝ) else 0) =
      (fun s => (fun x => if D x then (1 : ℝ) else 0) (gObsSample G s)) := by
    funext s
    by_cases hd : D (gObsSample G s) <;> simp [hd]
  have hs : (fun s => if D (sObsSample S s) then (1 : ℝ) else 0) =
      (fun s => (fun x => if D x then (1 : ℝ) else 0) (sObsSample S s)) := by
    funext s
    by_cases hd : D (sObsSample S s) <;> simp [hd]
  calc
    _ = (G.law.iid n).mean (fun s => (fun x => if D x then (1 : ℝ) else 0) (gObsSample G s)) :=
      congrArg (G.law.iid n).mean hg
    _ = (S.law.iid n).mean (fun s => (fun x => if D x then (1 : ℝ) else 0) (sObsSample S s)) :=
      sample_mean_eq G S hrep n (fun x => if D x then 1 else 0)
    _ = _ := congrArg (S.law.iid n).mean hs.symm

theorem sample_ce_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (n : ℕ) (f : (Fin n → WholeObservation) → ℝ)
    (D : (Fin n → WholeObservation) → Prop)
    [DecidablePred (fun s => D (gObsSample G s))]
    [DecidablePred (fun s => D (sObsSample S s))] :
    (G.law.iid n).ce (fun s => f (gObsSample G s)) (fun s => D (gObsSample G s)) =
      (S.law.iid n).ce (fun s => f (sObsSample S s)) (fun s => D (sObsSample S s)) := by
  have hg : (fun s => if D (gObsSample G s) then f (gObsSample G s) else 0) =
      (fun s => (fun x => if D x then f x else 0) (gObsSample G s)) := by
    funext s
    by_cases hd : D (gObsSample G s) <;> simp [hd]
  have hs : (fun s => if D (sObsSample S s) then f (sObsSample S s) else 0) =
      (fun s => (fun x => if D x then f x else 0) (sObsSample S s)) := by
    funext s
    by_cases hd : D (sObsSample S s) <;> simp [hd]
  have hn : (G.law.iid n).mean
        (fun s => if D (gObsSample G s) then f (gObsSample G s) else 0) =
      (S.law.iid n).mean
        (fun s => if D (sObsSample S s) then f (sObsSample S s) else 0) := by
    calc
      _ = (G.law.iid n).mean (fun s => (fun x => if D x then f x else 0) (gObsSample G s)) :=
        congrArg (G.law.iid n).mean hg
      _ = (S.law.iid n).mean (fun s => (fun x => if D x then f x else 0) (sObsSample S s)) :=
        sample_mean_eq G S hrep n (fun x => if D x then f x else 0)
      _ = _ := congrArg (S.law.iid n).mean hs.symm
  have hd := sample_prob_eq G S hrep n D
  change (G.law.iid n).mean
      (fun s => if D (gObsSample G s) then f (gObsSample G s) else 0) /
        (G.law.iid n).prob (fun s => D (gObsSample G s)) =
    (S.law.iid n).mean
      (fun s => if D (sObsSample S s) then f (sObsSample S s) else 0) /
        (S.law.iid n).prob (fun s => D (sObsSample S s))
  rw [hn]
  rw [hd]

theorem sample_variance_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (n : ℕ) (f : (Fin n → WholeObservation) → ℝ) :
    (G.law.iid n).variance (fun s => f (gObsSample G s)) =
      (S.law.iid n).variance (fun s => f (sObsSample S s)) := by
  unfold WholeMeasureLaw.variance SAP.P019a.FiniteLaw.variance
  rw [sample_mean_eq G S hrep n (fun x => (f x)^2), sample_mean_eq G S hrep n f]

theorem sample_ccov_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (n : ℕ) (f g : (Fin n → WholeObservation) → ℝ)
    (D : (Fin n → WholeObservation) → Prop) :
    (G.law.iid n).ccov (fun s => f (gObsSample G s)) (fun s => g (gObsSample G s))
      (fun s => D (gObsSample G s)) =
    (S.law.iid n).ccov (fun s => f (sObsSample S s)) (fun s => g (sObsSample S s))
      (fun s => D (sObsSample S s)) := by
  unfold WholeMeasureLaw.ccov SAP.P019a.FiniteLaw.ccov
  rw [sample_ce_eq G S hrep n (fun x => f x * g x) D,
    sample_ce_eq G S hrep n f D, sample_ce_eq G S hrep n g D]

theorem pop_mean_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (f : WholeObservation → ℝ) :
    G.law.mean (fun ω => f (G.observable ω)) =
      S.law.mean (fun ω => f (S.wholeObservable ω)) := by
  exact hrep.1 f

theorem pop_prob_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (D : WholeObservation → Prop)
    [DecidablePred (fun ω => D (G.observable ω))]
    [DecidablePred (fun ω => D (S.wholeObservable ω))] :
    G.law.prob (fun ω => D (G.observable ω)) =
      S.law.prob (fun ω => D (S.wholeObservable ω)) := by
  change G.law.mean (fun ω => if D (G.observable ω) then 1 else 0) =
    S.law.mean (fun ω => if D (S.wholeObservable ω) then 1 else 0)
  have hg : (fun ω => if D (G.observable ω) then 1 else 0) =
      (fun ω => (fun o => if D o then (1 : ℝ) else 0) (G.observable ω)) := by
    funext ω
    by_cases hd : D (G.observable ω) <;> simp [hd]
  have hs : (fun ω => if D (S.wholeObservable ω) then 1 else 0) =
      (fun ω => (fun o => if D o then (1 : ℝ) else 0) (S.wholeObservable ω)) := by
    funext ω
    by_cases hd : D (S.wholeObservable ω) <;> simp [hd]
  calc
    _ = G.law.mean (fun ω => (fun o => if D o then (1 : ℝ) else 0) (G.observable ω)) :=
      congrArg G.law.mean hg
    _ = S.law.mean (fun ω => (fun o => if D o then (1 : ℝ) else 0) (S.wholeObservable ω)) :=
      pop_mean_eq G S hrep (fun o => if D o then 1 else 0)
    _ = _ := congrArg S.law.mean hs.symm

theorem pop_ce_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (f : WholeObservation → ℝ) (D : WholeObservation → Prop)
    [DecidablePred (fun ω => D (G.observable ω))]
    [DecidablePred (fun ω => D (S.wholeObservable ω))] :
    G.law.ce (fun ω => f (G.observable ω)) (fun ω => D (G.observable ω)) =
      S.law.ce (fun ω => f (S.wholeObservable ω)) (fun ω => D (S.wholeObservable ω)) := by
  have hg : (fun ω => if D (G.observable ω) then f (G.observable ω) else 0) =
      (fun ω => (fun o => if D o then f o else 0) (G.observable ω)) := by
    funext ω
    by_cases hd : D (G.observable ω) <;> simp [hd]
  have hs : (fun ω => if D (S.wholeObservable ω) then f (S.wholeObservable ω) else 0) =
      (fun ω => (fun o => if D o then f o else 0) (S.wholeObservable ω)) := by
    funext ω
    by_cases hd : D (S.wholeObservable ω) <;> simp [hd]
  have hn : G.law.mean
      (fun ω => if D (G.observable ω) then f (G.observable ω) else 0) =
    S.law.mean (fun ω => if D (S.wholeObservable ω) then f (S.wholeObservable ω) else 0) := by
    calc
      _ = G.law.mean (fun ω => (fun o => if D o then f o else 0) (G.observable ω)) :=
        congrArg G.law.mean hg
      _ = S.law.mean (fun ω => (fun o => if D o then f o else 0) (S.wholeObservable ω)) :=
        pop_mean_eq G S hrep (fun o => if D o then f o else 0)
      _ = _ := congrArg S.law.mean hs.symm
  have hd := pop_prob_eq G S hrep D
  change G.law.mean (fun ω => if D (G.observable ω) then f (G.observable ω) else 0) /
      G.law.prob (fun ω => D (G.observable ω)) =
    S.law.mean (fun ω => if D (S.wholeObservable ω) then f (S.wholeObservable ω) else 0) /
      S.law.prob (fun ω => D (S.wholeObservable ω))
  rw [hn]
  rw [hd]

theorem pop_cv_eq {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {E : Type*} [Fintype E] (S : Study E) (hrep : wholeRepresentation G S)
    (f : WholeObservation → ℝ) (D : WholeObservation → Prop) :
    G.law.cv (fun ω => f (G.observable ω)) (fun ω => D (G.observable ω)) =
      S.law.cv (fun ω => f (S.wholeObservable ω)) (fun ω => D (S.wholeObservable ω)) := by
  unfold WholeMeasureLaw.cv SAP.P019a.FiniteLaw.cv
  rw [pop_ce_eq G S hrep (fun o => (f o)^2) D, pop_ce_eq G S hrep f D]

theorem obsCellCount_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) (z y : Bool) :
    G.cellCount s z y = obsCellCount (gObsSample G s) z y := by
  rfl

theorem obsCellCount_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) (z y : Bool) :
    S.cellCount s z y = obsCellCount (sObsSample S s) z y := by
  rfl

theorem obsNegativeCount_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) :
    G.negativeCount s = obsNegativeCount (gObsSample G s) := by
  simp [WholeMeasureStudy.negativeCount, obsNegativeCount, obsCellCount_G]

theorem obsNegativeCount_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) :
    S.negativeCount s = obsNegativeCount (sObsSample S s) := by
  simp [Study.negativeCount, obsNegativeCount, obsCellCount_S]

theorem obsCellMean_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) (z y : Bool) (c : ℝ) :
    G.cellMean s z y c = obsCellMean (gObsSample G s) z y c := by
  rfl

theorem obsCellMean_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) (z y : Bool) (c : ℝ) :
    S.cellMean s z y c = obsCellMean (sObsSample S s) z y c := by
  rfl

theorem obsA_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) : G.sampleA s = obsA (gObsSample G s) := by
  simp [WholeMeasureStudy.sampleA, WholeMeasureStudy.ybar, obsA, obsYbar, obsY,
    gObsSample, WholeMeasureStudy.observable]

theorem obsA_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) : S.sampleA s = obsA (sObsSample S s) := by
  simp [Study.sampleA, Study.ybar, obsA, obsYbar, obsY, sObsSample, Study.wholeObservable]

theorem obsB_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    G.sampleB s c1 c0 = obsB (gObsSample G s) c1 c0 := by
  simp [WholeMeasureStudy.sampleB, obsB, obsCellMean_G]

theorem obsB_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) (c1 c0 : ℝ) :
    S.sampleB s c1 c0 = obsB (sObsSample S s) c1 c0 := by
  simp [Study.sampleB, obsB, obsCellMean_S]

theorem obsMuHat_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    G.muHat s c1 c0 = obsMuHat (gObsSample G s) c1 c0 := by
  simp [WholeMeasureStudy.muHat, WholeMeasureStudy.ybar, obsMuHat, obsYbar,
    obsY, obsCellMean_G, gObsSample, WholeMeasureStudy.observable]

theorem obsMuHat_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) (c1 c0 : ℝ) :
    S.muHat s c1 c0 = obsMuHat (sObsSample S s) c1 c0 := by
  simp [Study.muHat, Study.ybar, obsMuHat, obsYbar, obsY, obsCellMean_S,
    sObsSample, Study.wholeObservable]

theorem obsOccupied_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) : G.occupied s = obsOccupied (gObsSample G s) := by
  simp [WholeMeasureStudy.occupied, obsOccupied, obsCellCount_G]

theorem obsOccupied_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) : S.occupied s = obsOccupied (sObsSample S s) := by
  simp [Study.occupied, obsOccupied, obsCellCount_S]

theorem obsH_G {Ω : Type u} [MeasurableSpace Ω] (G : WholeMeasureStudy Ω)
    {n : ℕ} (s : Fin n → Ω) :
    G.sampleH s = obsH (gObsSample G s)
      (G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell true false))
      (G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell false false)) := by
  simp [WholeMeasureStudy.sampleH, obsH, obsCellCount_G]

theorem obsH_S {E : Type*} [Fintype E] (S : Study E) {n : ℕ}
    (s : Fin n → E) :
    S.sampleH s = obsH (sObsSample S s)
      (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
      (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)) := by
  simp [Study.sampleH, obsH, obsCellCount_S]

end
end SAP.P019a.WH.W1.P.T4_L6

namespace SAP.P019a.WH.W1
open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open SAP.P019a.WH.W1.P.T4_L6
open scoped BigOperators Topology
noncomputable section
open Classical

theorem T4_L6_proof : SAP.P019a.WH.W1.T4_L6 := by
  intro Ω _ G N S hprob hmeas hbounded hstanding hsStanding hrep hcountsS hextrasS
  classical
  rcases hextrasS with
    ⟨hdetS, hresponseS, hmuPosS, hgammaPosS, hgammaLtS, hnonresponsePosS,
      hmomS, hlistS, hcontrastS, hremaindersS⟩
  have hmu : G.mu = S.mu := by
    unfold WholeMeasureStudy.mu Study.mu
    calc
      G.law.prob (fun ω => G.X ω = true) =
          G.law.prob (fun ω => obsX (G.observable ω) = true) :=
        whole_prob_congr G.law _ _ (by intro ω; simp [obsX, WholeMeasureStudy.observable])
      _ = S.law.prob (fun ω => obsX (S.wholeObservable ω) = true) :=
        pop_prob_eq G S hrep (fun o => obsX o = true)
      _ = S.law.prob (fun ω => S.X ω = true) :=
        finite_prob_congr S.law _ _ (by intro ω; simp [obsX, Study.wholeObservable])
  have htruth : G.truthRate = S.truthRate := by
    unfold WholeMeasureStudy.truthRate Study.truthRate
    calc
      G.law.ce (fun ω => bitVal (G.Y ω)) (fun ω => G.X ω = true) =
          G.law.ce (fun ω => bitVal (obsY (G.observable ω)))
            (fun ω => obsX (G.observable ω) = true) :=
        whole_ce_congr G.law _ _ _ _
          (by intro ω; simp [obsY, WholeMeasureStudy.observable])
          (by intro ω; simp [obsX, WholeMeasureStudy.observable])
      _ = S.law.ce (fun ω => bitVal (obsY (S.wholeObservable ω)))
            (fun ω => obsX (S.wholeObservable ω) = true) :=
        pop_ce_eq G S hrep (fun o => bitVal (obsY o)) (fun o => obsX o = true)
      _ = S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.X ω = true) :=
        finite_ce_congr S.law _ _ _ _
          (by intro ω; simp [obsY, Study.wholeObservable])
          (by intro ω; simp [obsX, Study.wholeObservable])
  have hgamma : G.gamma = S.gamma := by
    unfold WholeMeasureStudy.gamma Study.gamma
    calc
      G.law.prob (fun ω => G.Z ω = true) =
          G.law.prob (fun ω => obsZ (G.observable ω) = true) :=
        whole_prob_congr G.law _ _ (by intro ω; simp [obsZ, WholeMeasureStudy.observable])
      _ = S.law.prob (fun ω => obsZ (S.wholeObservable ω) = true) :=
        pop_prob_eq G S hrep (fun o => obsZ o = true)
      _ = S.law.prob (fun ω => S.Z ω = true) :=
        finite_prob_congr S.law _ _ (by intro ω; simp [obsZ, Study.wholeObservable])
  have hYprob : G.law.prob (fun ω => G.Y ω = true) =
      S.law.prob (fun ω => S.Y ω = true) := by
    calc
      G.law.prob (fun ω => G.Y ω = true) =
          G.law.prob (fun ω => obsY (G.observable ω) = true) :=
        whole_prob_congr G.law _ _ (by intro ω; simp [obsY, WholeMeasureStudy.observable])
      _ = S.law.prob (fun ω => obsY (S.wholeObservable ω) = true) :=
        pop_prob_eq G S hrep (fun o => obsY o = true)
      _ = S.law.prob (fun ω => S.Y ω = true) :=
        finite_prob_congr S.law _ _ (by intro ω; simp [obsY, Study.wholeObservable])
  have hresponse : G.law.prob (fun ω => G.Y ω = true) = G.mu*G.truthRate := by
    calc
      G.law.prob (fun ω => G.Y ω = true) = S.law.prob (fun ω => S.Y ω = true) := hYprob
      _ = S.mu*S.truthRate := hresponseS
      _ = G.mu*G.truthRate := by rw [hmu, htruth]
  have hlist (z y : Bool) : G.listMean z y = S.listMean z y := by
    unfold WholeMeasureStudy.listMean Study.listMean
    exact pop_ce_eq G S hrep (fun o => (obsV o : ℝ)) (fun o => obsCell z y o)
  have hcv (z y : Bool) :
      G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell z y) =
        S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y) := by
    exact pop_cv_eq G S hrep (fun o => (obsV o : ℝ)) (fun o => obsCell z y o)

  have hdet : ∀ (n : ℕ) (s : Fin n → Ω),
      (G.negativeCount s : ℝ) = (n : ℝ)*G.sampleA s ∧
        (∀ c1 c0 : ℝ, G.muHat s c1 c0 = 1+G.sampleA s*G.sampleB s c1 c0) := by
    intro n s
    have hcount : (G.negativeCount s : ℝ) =
        ∑ i, (1-bitVal (G.Y (s i))) := by
      unfold WholeMeasureStudy.negativeCount WholeMeasureStudy.cellCount
      simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      cases hy : G.Y (s i) <;> cases hz : G.Z (s i) <;>
        simp [WholeMeasureStudy.cell, bitVal, hy, hz]
    have hsum : (G.negativeCount s : ℝ) =
        (n : ℝ)-∑ i, bitVal (G.Y (s i)) := by
      calc
        _ = ∑ i, (1-bitVal (G.Y (s i))) := hcount
        _ = (n : ℝ)-∑ i, bitVal (G.Y (s i)) := by
          simp [Finset.sum_sub_distrib]
    constructor
    · by_cases hn : n = 0
      · subst n
        simp [WholeMeasureStudy.negativeCount, WholeMeasureStudy.cellCount,
          WholeMeasureStudy.sampleA, WholeMeasureStudy.ybar]
      · rw [hsum]
        unfold WholeMeasureStudy.sampleA WholeMeasureStudy.ybar
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        field_simp
    · intro c1 c0
      unfold WholeMeasureStudy.muHat WholeMeasureStudy.sampleA WholeMeasureStudy.sampleB
        WholeMeasureStudy.ybar
      ring

  have hcounts : wholeT4MeasureCounts G := by
    intro n k hk
    rcases hcountsS n k hk with ⟨hposS, hbinS, hsumTrueS, hsumFalseS⟩
    let KG : (Fin n → Ω) → Prop := fun s => G.negativeCount s = k
    let KS : (Fin n → Fin N) → Prop := fun s => S.negativeCount s = k
    have hKG (s : Fin n → Ω) : KG s ↔ obsNegativeCount (gObsSample G s) = k := by
      simp [KG, obsNegativeCount_G]
    have hKS (s : Fin n → Fin N) : KS s ↔ obsNegativeCount (sObsSample S s) = k := by
      simp [KS, obsNegativeCount_S]
    have hK : (G.law.iid n).prob KG = (S.law.iid n).prob KS := by
      calc
        (G.law.iid n).prob KG =
            (G.law.iid n).prob (fun s => obsNegativeCount (gObsSample G s) = k) :=
          whole_prob_congr (G.law.iid n) _ _ hKG
        _ = (S.law.iid n).prob (fun s => obsNegativeCount (sObsSample S s) = k) :=
          sample_prob_eq G S hrep n (fun x => obsNegativeCount x = k)
        _ = (S.law.iid n).prob KS :=
          finite_prob_congr (S.law.iid n) _ _ hKS
    have hCG (i : ℕ) (s : Fin n → Ω) :
        (if G.cellCount s true false = i then (1 : ℝ) else 0) =
          (if obsCellCount (gObsSample G s) true false = i then 1 else 0) := by
      rw [obsCellCount_G]
    have hCS (i : ℕ) (s : Fin n → Fin N) :
        (if S.cellCount s true false = i then (1 : ℝ) else 0) =
          (if obsCellCount (sObsSample S s) true false = i then 1 else 0) := by
      rw [obsCellCount_S]
    have hcell (i : ℕ) :
        (G.law.iid n).ce (fun s => if G.cellCount s true false = i then 1 else 0) KG =
          (S.law.iid n).ce (fun s => if S.cellCount s true false = i then 1 else 0) KS := by
      calc
        _ = (G.law.iid n).ce
            (fun s => if obsCellCount (gObsSample G s) true false = i then 1 else 0)
            (fun s => obsNegativeCount (gObsSample G s) = k) :=
          whole_ce_congr (G.law.iid n) _ _ _ _ (hCG i) hKG
        _ = (S.law.iid n).ce
            (fun s => if obsCellCount (sObsSample S s) true false = i then 1 else 0)
            (fun s => obsNegativeCount (sObsSample S s) = k) :=
          sample_ce_eq G S hrep n
            (fun x => if obsCellCount x true false = i then 1 else 0)
            (fun x => obsNegativeCount x = k)
        _ = (S.law.iid n).ce (fun s => if S.cellCount s true false = i then 1 else 0) KS :=
          (finite_ce_congr (S.law.iid n) _ _ _ _ (hCS i) hKS).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hK]
      exact hposS
    · intro i hi
      calc
        (G.law.iid n).ce (fun s => if G.cellCount s true false = i then 1 else 0) KG =
            (S.law.iid n).ce (fun s => if S.cellCount s true false = i then 1 else 0) KS := hcell i
        _ = (Nat.choose k i : ℝ)*G.gamma^i*(1-G.gamma)^(k-i) := by
          rw [hgamma]
          exact hbinS i hi
    · calc
        (∑ i ∈ Finset.Icc 1 k,
          (G.law.iid n).ce (fun s => if G.cellCount s true false = i then 1 else 0) KG) =
            ∑ i ∈ Finset.Icc 1 k,
              (S.law.iid n).ce (fun s => if S.cellCount s true false = i then 1 else 0) KS := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcell i
        _ = 1-(1-G.gamma)^k := by rw [hgamma]; exact hsumTrueS
    · have hcellFalse (i : ℕ) :
        (G.law.iid n).ce (fun s => if G.cellCount s false false = i then 1 else 0) KG =
          (S.law.iid n).ce (fun s => if S.cellCount s false false = i then 1 else 0) KS := by
        have hCgf (s : Fin n → Ω) :
            (if G.cellCount s false false = i then (1 : ℝ) else 0) =
              (if obsCellCount (gObsSample G s) false false = i then 1 else 0) := by
          rw [obsCellCount_G]
        have hCsf (s : Fin n → Fin N) :
            (if S.cellCount s false false = i then (1 : ℝ) else 0) =
              (if obsCellCount (sObsSample S s) false false = i then 1 else 0) := by
          rw [obsCellCount_S]
        calc
          _ = (G.law.iid n).ce
              (fun s => if obsCellCount (gObsSample G s) false false = i then 1 else 0)
              (fun s => obsNegativeCount (gObsSample G s) = k) :=
            whole_ce_congr (G.law.iid n) _ _ _ _ hCgf hKG
          _ = (S.law.iid n).ce
              (fun s => if obsCellCount (sObsSample S s) false false = i then 1 else 0)
              (fun s => obsNegativeCount (sObsSample S s) = k) :=
            sample_ce_eq G S hrep n
              (fun x => if obsCellCount x false false = i then 1 else 0)
              (fun x => obsNegativeCount x = k)
          _ = (S.law.iid n).ce (fun s => if S.cellCount s false false = i then 1 else 0) KS :=
            (finite_ce_congr (S.law.iid n) _ _ _ _ hCsf hKS).symm
      calc
        (∑ i ∈ Finset.Icc 1 k,
          (G.law.iid n).ce (fun s => if G.cellCount s false false = i then 1 else 0) KG) =
            ∑ i ∈ Finset.Icc 1 k,
              (S.law.iid n).ce (fun s => if S.cellCount s false false = i then 1 else 0) KS := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcellFalse i
        _ = 1-G.gamma^k := by rw [hgamma]; exact hsumFalseS

  have hExtras : wholeT4MeasureExtras G := by
    refine ⟨hdet, hresponse, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmu]
      exact hmuPosS
    · rw [hgamma]
      exact hgammaPosS
    · rw [hgamma]
      exact hgammaLtS
    · rw [hmu, htruth]
      exact hnonresponsePosS
    · intro n hn
      have hmA : (G.law.iid n).mean G.sampleA = (S.law.iid n).mean S.sampleA := by
        calc
          (G.law.iid n).mean G.sampleA =
              (G.law.iid n).mean (fun s => obsA (gObsSample G s)) :=
            congrArg (G.law.iid n).mean (funext fun s => obsA_G G s)
          _ = (S.law.iid n).mean (fun s => obsA (sObsSample S s)) :=
            sample_mean_eq G S hrep n obsA
          _ = (S.law.iid n).mean S.sampleA := by
            exact congrArg (S.law.iid n).mean (funext fun s => (obsA_S S s).symm)
      have hvA : (G.law.iid n).variance G.sampleA = (S.law.iid n).variance S.sampleA := by
        calc
          (G.law.iid n).variance G.sampleA =
              (G.law.iid n).variance (fun s => obsA (gObsSample G s)) :=
            congrArg (G.law.iid n).variance (funext fun s => obsA_G G s)
          _ = (S.law.iid n).variance (fun s => obsA (sObsSample S s)) :=
            sample_variance_eq G S hrep n obsA
          _ = (S.law.iid n).variance S.sampleA := by
            exact congrArg (S.law.iid n).variance (funext fun s => (obsA_S S s).symm)
      rcases hmomS n hn with ⟨hmS, hvS⟩
      constructor
      · calc
          (G.law.iid n).mean G.sampleA = (S.law.iid n).mean S.sampleA := hmA
          _ = 1-S.mu*S.truthRate := hmS
          _ = 1-G.mu*G.truthRate := by rw [hmu, htruth]
      · calc
          (G.law.iid n).variance G.sampleA = (S.law.iid n).variance S.sampleA := hvA
          _ = (S.mu*S.truthRate)*(1-S.mu*S.truthRate)/(n : ℝ) := hvS
          _ = (G.mu*G.truthRate)*(1-G.mu*G.truthRate)/(n : ℝ) := by rw [hmu, htruth]
    · calc
        G.listMean true false-G.listMean false false =
            S.listMean true false-S.listMean false false := by rw [hlist, hlist]
        _ = ((1-S.truthRate)*S.mu)/(1-S.mu*S.truthRate) := hlistS
        _ = ((1-G.truthRate)*G.mu)/(1-G.mu*G.truthRate) := by rw [hmu, htruth]
    · calc
        G.listMean true false-G.listMean false false-1 =
            S.listMean true false-S.listMean false false-1 := by rw [hlist, hlist]
        _ = -(1-S.mu)/(1-S.mu*S.truthRate) := hcontrastS
        _ = -(1-G.mu)/(1-G.mu*G.truthRate) := by rw [hmu, htruth]
    · rcases hremaindersS with ⟨hbigS, hlimS⟩
      have hRpoint (n : ℕ) :
          (G.law.iid n).ccov (fun s => (G.sampleA s)^2) G.sampleH G.occupied =
            (S.law.iid n).ccov (fun s => (S.sampleA s)^2) S.sampleH S.occupied := by
        have hH (s : Fin n → Ω) :
            G.sampleH s = obsH (gObsSample G s)
              (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
              (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)) := by
          rw [obsH_G, hcv true false, hcv false false]
        calc
          _ = (G.law.iid n).ccov (fun s => (obsA (gObsSample G s))^2)
                (fun s => obsH (gObsSample G s)
                  (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
                  (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)))
                (fun s => obsOccupied (gObsSample G s)) :=
            whole_ccov_congr (G.law.iid n)
              (fun s => (G.sampleA s)^2) (fun s => (obsA (gObsSample G s))^2)
              G.sampleH (fun s => obsH (gObsSample G s)
                (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
                (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)))
              (fun s => G.occupied s) (fun s => obsOccupied (gObsSample G s))
              (by intro s; rw [obsA_G]) hH
              (by intro s; rw [obsOccupied_G])
          _ = (S.law.iid n).ccov (fun s => (obsA (sObsSample S s))^2)
                (fun s => obsH (sObsSample S s)
                  (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
                  (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)))
                (fun s => obsOccupied (sObsSample S s)) :=
            sample_ccov_eq G S hrep n
            (fun x => (obsA x)^2)
            (fun x => obsH x
              (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
              (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)))
            obsOccupied
          _ = (S.law.iid n).ccov (fun s => (S.sampleA s)^2) S.sampleH S.occupied :=
            finite_ccov_congr (S.law.iid n)
              (fun s => (obsA (sObsSample S s))^2) (fun s => (S.sampleA s)^2)
              (fun s => obsH (sObsSample S s)
                (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
                (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false))) S.sampleH
              (fun s => obsOccupied (sObsSample S s)) (fun s => S.occupied s)
              (by intro s; rw [obsA_S])
              (by intro s; exact (obsH_S S s).symm)
              (by intro s; rw [obsOccupied_S])
      have hRseq :
          (fun n : ℕ => (G.law.iid n).ccov
            (fun s => (G.sampleA s)^2) G.sampleH G.occupied) =
          (fun n : ℕ => (S.law.iid n).ccov
            (fun s => (S.sampleA s)^2) S.sampleH S.occupied) := by
        funext n
        exact hRpoint n
      change (Asymptotics.IsBigO atTop
          (fun n : ℕ => (G.law.iid n).ccov
            (fun s => (G.sampleA s)^2) G.sampleH G.occupied)
          (fun n : ℕ => (1/(n : ℝ))^2) ∧
        Tendsto (fun n : ℕ => (n : ℝ)^2 * (G.law.iid n).ccov
            (fun s => (G.sampleA s)^2) G.sampleH G.occupied) atTop
          (nhds (-2*(G.mu*G.truthRate)*
            (G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell true false)/G.gamma +
             G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell false false)/(1-G.gamma)))))
      constructor
      · simpa only [hRpoint, hmu, htruth, hgamma, hcv] using hbigS
      · simpa only [hRpoint, hmu, htruth, hgamma, hcv] using hlimS
  exact ⟨hcounts, hExtras⟩

end
end SAP.P019a.WH.W1
