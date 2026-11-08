import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T4_L5
open SAP.P019a Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical

abbrev ObsSeq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) : Fin n → WholeObservation :=
  fun i => G.observable (s i)

abbrev FinObsSeq {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) : Fin n → WholeObservation :=
  fun i => S.wholeObservable (s i)

def oX (o : WholeObservation) : Bool := o.2.1
def oY (o : WholeObservation) : Bool := o.2.2.1
def oZ (o : WholeObservation) : Bool := o.2.2.2.1
def oV (o : WholeObservation) : ℕ := o.2.2.2.2

def oCell (o : WholeObservation) (z y : Bool) : Prop := oZ o = z ∧ oY o = y
def oCellCount {n : ℕ} (s : Fin n → WholeObservation) (z y : Bool) : ℕ :=
  ∑ i, if oCell (s i) z y then 1 else 0
def oCellMean {n : ℕ} (s : Fin n → WholeObservation) (z y : Bool) (c : ℝ) : ℝ :=
  if oCellCount s z y = 0 then c else
    (∑ i, if oCell (s i) z y then (oV (s i) : ℝ) else 0) / (oCellCount s z y : ℝ)
def oOccupied {n : ℕ} (s : Fin n → WholeObservation) : Prop :=
  0 < oCellCount s true false ∧ 0 < oCellCount s false false
def oA {n : ℕ} (s : Fin n → WholeObservation) : ℝ :=
  1 - (∑ i, bitVal (oY (s i))) / (n : ℝ)
def oB {n : ℕ} (s : Fin n → WholeObservation) (c1 c0 : ℝ) : ℝ :=
  oCellMean s true false c1 - oCellMean s false false c0 - 1
def oMuHat {n : ℕ} (s : Fin n → WholeObservation) (c1 c0 : ℝ) : ℝ :=
  (∑ i, bitVal (oY (s i))) / (n : ℝ) + oA s *
    (oCellMean s true false c1 - oCellMean s false false c0)
def oH {n : ℕ} (v1 v0 : ℝ) (s : Fin n → WholeObservation) : ℝ :=
  v1 / (oCellCount s true false : ℝ) + v0 / (oCellCount s false false : ℝ)
def oNegativeCount {n : ℕ} (s : Fin n → WholeObservation) : ℕ :=
  oCellCount s true false + oCellCount s false false
def oArmCount {n : ℕ} (s : Fin n → WholeObservation) (z : Bool) : ℕ :=
  ∑ i, if oZ (s i) = z then 1 else 0
def oPattern {n : ℕ} (s t : Fin n → WholeObservation) : Prop :=
  ∀ i, oY (t i) = oY (s i) ∧ oZ (t i) = oZ (s i)

theorem popProb_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F)
    (hr : wholeRepresentation G S) (D : WholeObservation → Prop)
    [DecidablePred (fun ω => D (G.observable ω))]
    [DecidablePred (fun e => D (S.wholeObservable e))] :
    G.law.prob (fun ω => D (G.observable ω)) =
      S.law.prob (fun e => D (S.wholeObservable e)) := by
  let ind : WholeObservation → ℝ := fun o => if D o then 1 else 0
  have hG : (fun ω => if D (G.observable ω) then 1 else 0) =
      (fun ω => ind (G.observable ω)) := by
    funext ω
    by_cases h : D (G.observable ω) <;> simp [ind, h]
  have hS : (fun e => if D (S.wholeObservable e) then 1 else 0) =
      (fun e => ind (S.wholeObservable e)) := by
    funext e
    by_cases h : D (S.wholeObservable e) <;> simp [ind, h]
  calc
    G.law.prob (fun ω => D (G.observable ω)) =
        G.law.mean (fun ω => if D (G.observable ω) then 1 else 0) := rfl
    _ = G.law.mean (fun ω => ind (G.observable ω)) := congrArg G.law.mean hG
    _ = S.law.mean (fun e => ind (S.wholeObservable e)) := hr.1 ind
    _ = S.law.mean (fun e => if D (S.wholeObservable e) then 1 else 0) :=
      congrArg S.law.mean hS.symm
    _ = S.law.prob (fun e => D (S.wholeObservable e)) := rfl

theorem popCE_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F)
    (hr : wholeRepresentation G S) (f : WholeObservation → ℝ)
    (D : WholeObservation → Prop)
    [DecidablePred (fun ω => D (G.observable ω))]
    [DecidablePred (fun e => D (S.wholeObservable e))] :
    G.law.ce (fun ω => f (G.observable ω)) (fun ω => D (G.observable ω)) =
      S.law.ce (fun e => f (S.wholeObservable e)) (fun e => D (S.wholeObservable e)) := by
  unfold WholeMeasureLaw.ce FiniteLaw.ce
  let integrand : WholeObservation → ℝ := fun o => if D o then f o else 0
  have hG : (fun ω => if D (G.observable ω) then f (G.observable ω) else 0) =
      (fun ω => integrand (G.observable ω)) := by
    funext ω
    by_cases h : D (G.observable ω) <;> simp [integrand, h]
  have hS : (fun e => if D (S.wholeObservable e) then f (S.wholeObservable e) else 0) =
      (fun e => integrand (S.wholeObservable e)) := by
    funext e
    by_cases h : D (S.wholeObservable e) <;> simp [integrand, h]
  rw [congrArg G.law.mean hG, hr.1 integrand, congrArg S.law.mean hS.symm,
    popProb_eq G S hr D]

theorem popCV_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F)
    (hr : wholeRepresentation G S) (f : WholeObservation → ℝ)
    (D : WholeObservation → Prop)
    [DecidablePred (fun ω => D (G.observable ω))]
    [DecidablePred (fun e => D (S.wholeObservable e))] :
    G.law.cv (fun ω => f (G.observable ω)) (fun ω => D (G.observable ω)) =
      S.law.cv (fun e => f (S.wholeObservable e)) (fun e => D (S.wholeObservable e)) := by
  unfold WholeMeasureLaw.cv FiniteLaw.cv
  rw [popCE_eq G S hr (fun o => f o ^ 2) D, popCE_eq G S hr f D]

theorem sampleProb_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (n : ℕ) (D : (Fin n → WholeObservation) → Prop)
    [DecidablePred (fun s => D (ObsSeq G s))]
    [DecidablePred (fun s => D (FinObsSeq S s))] :
    (G.law.iid n).prob (fun s => D (ObsSeq G s)) =
      (S.law.iid n).prob (fun s => D (FinObsSeq S s)) := by
  let ind : (Fin n → WholeObservation) → ℝ := fun v => if D v then 1 else 0
  have hG : (fun s => if D (ObsSeq G s) then 1 else 0) =
      (fun s => ind (ObsSeq G s)) := by
    funext s
    by_cases h : D (ObsSeq G s) <;> simp [ind, h]
  have hS : (fun s => if D (FinObsSeq S s) then 1 else 0) =
      (fun s => ind (FinObsSeq S s)) := by
    funext s
    by_cases h : D (FinObsSeq S s) <;> simp [ind, h]
  calc
    (G.law.iid n).prob (fun s => D (ObsSeq G s)) =
        (G.law.iid n).mean (fun s => if D (ObsSeq G s) then 1 else 0) := rfl
    _ = (G.law.iid n).mean (fun s => ind (ObsSeq G s)) :=
      congrArg (G.law.iid n).mean hG
    _ = (S.law.iid n).mean (fun s => ind (FinObsSeq S s)) := hr.2 n ind
    _ = (S.law.iid n).mean (fun s => if D (FinObsSeq S s) then 1 else 0) :=
      congrArg (S.law.iid n).mean hS.symm
    _ = (S.law.iid n).prob (fun s => D (FinObsSeq S s)) := rfl

theorem sampleMean_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (n : ℕ) (f : (Fin n → WholeObservation) → ℝ) :
    (G.law.iid n).mean (fun s => f (ObsSeq G s)) =
      (S.law.iid n).mean (fun s => f (FinObsSeq S s)) := hr.2 n f

theorem sampleCE_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (n : ℕ) (f : (Fin n → WholeObservation) → ℝ)
    (D : (Fin n → WholeObservation) → Prop)
    [DecidablePred (fun s => D (ObsSeq G s))]
    [DecidablePred (fun s => D (FinObsSeq S s))] :
    (G.law.iid n).ce (fun s => f (ObsSeq G s)) (fun s => D (ObsSeq G s)) =
      (S.law.iid n).ce (fun s => f (FinObsSeq S s)) (fun s => D (FinObsSeq S s)) := by
  unfold WholeMeasureLaw.ce FiniteLaw.ce
  let integrand : (Fin n → WholeObservation) → ℝ := fun v => if D v then f v else 0
  have hG : (fun s => if D (ObsSeq G s) then f (ObsSeq G s) else 0) =
      (fun s => integrand (ObsSeq G s)) := by
    funext s
    by_cases h : D (ObsSeq G s) <;> simp [integrand, h]
  have hS : (fun s => if D (FinObsSeq S s) then f (FinObsSeq S s) else 0) =
      (fun s => integrand (FinObsSeq S s)) := by
    funext s
    by_cases h : D (FinObsSeq S s) <;> simp [integrand, h]
  rw [congrArg (G.law.iid n).mean hG, sampleMean_eq G S hr n integrand,
    congrArg (S.law.iid n).mean hS.symm, sampleProb_eq G S hr n D]

theorem sampleCV_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (n : ℕ) (f : (Fin n → WholeObservation) → ℝ)
    (D : (Fin n → WholeObservation) → Prop)
    [DecidablePred (fun s => D (ObsSeq G s))]
    [DecidablePred (fun s => D (FinObsSeq S s))] :
    (G.law.iid n).cv (fun s => f (ObsSeq G s)) (fun s => D (ObsSeq G s)) =
      (S.law.iid n).cv (fun s => f (FinObsSeq S s)) (fun s => D (FinObsSeq S s)) := by
  unfold WholeMeasureLaw.cv FiniteLaw.cv
  rw [sampleCE_eq G S hr n (fun v => f v ^ 2) D, sampleCE_eq G S hr n f D]

theorem sampleCCov_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (n : ℕ) (f g : (Fin n → WholeObservation) → ℝ)
    (D : (Fin n → WholeObservation) → Prop)
    [DecidablePred (fun s => D (ObsSeq G s))]
    [DecidablePred (fun s => D (FinObsSeq S s))] :
    (G.law.iid n).ccov (fun s => f (ObsSeq G s)) (fun s => g (ObsSeq G s))
      (fun s => D (ObsSeq G s)) =
    (S.law.iid n).ccov (fun s => f (FinObsSeq S s)) (fun s => g (FinObsSeq S s))
      (fun s => D (FinObsSeq S s)) := by
  unfold WholeMeasureLaw.ccov FiniteLaw.ccov
  rw [sampleCE_eq G S hr n (fun v => f v * g v) D,
    sampleCE_eq G S hr n f D, sampleCE_eq G S hr n g D]

theorem wholeProb_congr {α : Type*} [MeasurableSpace α] (P : WholeMeasureLaw α)
    (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.prob D = P.prob D' := by
  unfold WholeMeasureLaw.prob
  congr 1
  funext x
  by_cases hx : D x
  · have hx' := (h x).mp hx
    simp [hx, hx']
  · have hx' : ¬ D' x := fun h' => hx ((h x).mpr h')
    simp [hx, hx']

theorem finiteProb_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.prob D = P.prob D' := by
  unfold FiniteLaw.prob
  congr 1
  funext x
  by_cases hx : D x
  · have hx' := (h x).mp hx
    simp [hx, hx']
  · have hx' : ¬ D' x := fun h' => hx ((h x).mpr h')
    simp [hx, hx']

theorem wholeCE_congr {α : Type*} [MeasurableSpace α] (P : WholeMeasureLaw α)
    (f : α → ℝ) (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.ce f D = P.ce f D' := by
  unfold WholeMeasureLaw.ce
  have hn : (fun x => if D x then f x else 0) = fun x => if D' x then f x else 0 := by
    funext x
    by_cases hx : D x
    · have hx' := (h x).mp hx
      simp [hx, hx']
    · have hx' : ¬ D' x := fun h' => hx ((h x).mpr h')
      simp [hx, hx']
  rw [hn, wholeProb_congr P D D' h]

theorem finiteCE_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.ce f D = P.ce f D' := by
  unfold FiniteLaw.ce
  have hn : (fun x => if D x then f x else 0) = fun x => if D' x then f x else 0 := by
    funext x
    by_cases hx : D x
    · have hx' := (h x).mp hx
      simp [hx, hx']
    · have hx' : ¬ D' x := fun h' => hx ((h x).mpr h')
      simp [hx, hx']
  rw [hn, finiteProb_congr P D D' h]

theorem wholeCV_congr {α : Type*} [MeasurableSpace α] (P : WholeMeasureLaw α)
    (f : α → ℝ) (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.cv f D = P.cv f D' := by
  unfold WholeMeasureLaw.cv
  rw [wholeCE_congr P (fun x => f x ^ 2) D D' h, wholeCE_congr P f D D' h]

theorem finiteCV_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.cv f D = P.cv f D' := by
  unfold FiniteLaw.cv
  rw [finiteCE_congr P (fun x => f x ^ 2) D D' h, finiteCE_congr P f D D' h]

theorem wholeCE_fun_congr {α : Type*} [MeasurableSpace α] (P : WholeMeasureLaw α)
    (f g : α → ℝ) (D : α → Prop) [DecidablePred D]
    (h : ∀ x, f x = g x) : P.ce f D = P.ce g D :=
  congrArg (fun f : α → ℝ => P.ce f D) (funext h)

theorem finiteCE_fun_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f g : α → ℝ) (D : α → Prop) [DecidablePred D]
    (h : ∀ x, f x = g x) : P.ce f D = P.ce g D :=
  congrArg (fun f : α → ℝ => P.ce f D) (funext h)

theorem wholeCV_fun_congr {α : Type*} [MeasurableSpace α] (P : WholeMeasureLaw α)
    (f g : α → ℝ) (D : α → Prop) [DecidablePred D]
    (h : ∀ x, f x = g x) : P.cv f D = P.cv g D :=
  congrArg (fun f : α → ℝ => P.cv f D) (funext h)

theorem finiteCV_fun_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f g : α → ℝ) (D : α → Prop) [DecidablePred D]
    (h : ∀ x, f x = g x) : P.cv f D = P.cv g D :=
  congrArg (fun f : α → ℝ => P.cv f D) (funext h)

theorem wholeCCov_fun_congr {α : Type*} [MeasurableSpace α] (P : WholeMeasureLaw α)
    (f f' g g' : α → ℝ) (D : α → Prop) [DecidablePred D]
    (hf : ∀ x, f x = f' x) (hg : ∀ x, g x = g' x) :
    P.ccov f g D = P.ccov f' g' D := by
  unfold WholeMeasureLaw.ccov
  rw [wholeCE_fun_congr P (fun x => f x * g x) (fun x => f' x * g' x) D
      (by intro x; rw [hf x, hg x]),
    wholeCE_fun_congr P f f' D hf, wholeCE_fun_congr P g g' D hg]

theorem finiteCCov_fun_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f f' g g' : α → ℝ) (D : α → Prop) [DecidablePred D]
    (hf : ∀ x, f x = f' x) (hg : ∀ x, g x = g' x) :
    P.ccov f g D = P.ccov f' g' D := by
  unfold FiniteLaw.ccov
  rw [finiteCE_fun_congr P (fun x => f x * g x) (fun x => f' x * g' x) D
      (by intro x; rw [hf x, hg x]),
    finiteCE_fun_congr P f f' D hf, finiteCE_fun_congr P g g' D hg]

theorem wholeCCov_event_congr {α : Type*} [MeasurableSpace α] (P : WholeMeasureLaw α)
    (f g : α → ℝ) (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.ccov f g D = P.ccov f g D' := by
  unfold WholeMeasureLaw.ccov
  rw [wholeCE_congr P (fun x => f x * g x) D D' h,
    wholeCE_congr P f D D' h, wholeCE_congr P g D D' h]

theorem finiteCCov_event_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f g : α → ℝ) (D D' : α → Prop) [DecidablePred D] [DecidablePred D']
    (h : ∀ x, D x ↔ D' x) : P.ccov f g D = P.ccov f g D' := by
  unfold FiniteLaw.ccov
  rw [finiteCE_congr P (fun x => f x * g x) D D' h,
    finiteCE_congr P f D D' h, finiteCE_congr P g D D' h]

theorem g_cellCount {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) (z y : Bool) :
    G.cellCount s z y = oCellCount (ObsSeq G s) z y := rfl
theorem s_cellCount {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) (z y : Bool) :
    S.cellCount s z y = oCellCount (FinObsSeq S s) z y := rfl
theorem g_cellMean {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) (z y : Bool) (c : ℝ) :
    G.cellMean s z y c = oCellMean (ObsSeq G s) z y c := rfl
theorem s_cellMean {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) (z y : Bool) (c : ℝ) :
    S.cellMean s z y c = oCellMean (FinObsSeq S s) z y c := rfl
theorem g_occupied {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) : G.occupied s = oOccupied (ObsSeq G s) := rfl
theorem s_occupied {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) : S.occupied s = oOccupied (FinObsSeq S s) := rfl
theorem g_pattern {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s t : Fin n → E) : G.patternFibre s t = oPattern (ObsSeq G s) (ObsSeq G t) := rfl
theorem s_pattern {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s t : Fin n → E) : S.patternFibre s t = oPattern (FinObsSeq S s) (FinObsSeq S t) := rfl
theorem g_sampleA {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) : G.sampleA s = oA (ObsSeq G s) := rfl
theorem s_sampleA {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) : S.sampleA s = oA (FinObsSeq S s) := rfl
theorem g_sampleB {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) (c1 c0 : ℝ) :
    G.sampleB s c1 c0 = oB (ObsSeq G s) c1 c0 := rfl
theorem s_sampleB {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) (c1 c0 : ℝ) :
    S.sampleB s c1 c0 = oB (FinObsSeq S s) c1 c0 := rfl
theorem g_sampleH {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) :
    G.sampleH s = oH
      (G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell true false))
      (G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell false false)) (ObsSeq G s) := rfl
theorem s_sampleH {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) :
    S.sampleH s = oH
      (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false))
      (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)) (FinObsSeq S s) := rfl
theorem g_muHat {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) (c1 c0 : ℝ) :
    G.muHat s c1 c0 = oMuHat (ObsSeq G s) c1 c0 := rfl
theorem s_muHat {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) (c1 c0 : ℝ) :
    S.muHat s c1 c0 = oMuHat (FinObsSeq S s) c1 c0 := rfl

theorem pop_gamma_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S) :
    G.gamma = S.gamma := by
  unfold WholeMeasureStudy.gamma Study.gamma
  calc
    G.law.prob (fun ω => G.Z ω = true) =
        G.law.prob (fun ω => oZ (G.observable ω) = true) :=
          wholeProb_congr G.law _ _ (by intro ω; simp [WholeMeasureStudy.observable, oZ])
    _ = G.law.prob (fun ω => oZ (G.observable ω) = true) :=
      wholeProb_congr G.law _ _ (by intro ω; rfl)
    _ = S.law.prob (fun e => oZ (S.wholeObservable e) = true) :=
      popProb_eq G S hr (fun o => oZ o = true)
    _ = S.law.prob (fun e => S.Z e = true) :=
      (finiteProb_congr S.law _ _ (by intro e; simp [Study.wholeObservable, oZ])).symm

theorem pop_mu_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S) :
    G.mu = S.mu := by
  unfold WholeMeasureStudy.mu Study.mu
  calc
    G.law.prob (fun ω => G.X ω = true) =
        G.law.prob (fun ω => oX (G.observable ω) = true) :=
          wholeProb_congr G.law _ _ (by intro ω; simp [WholeMeasureStudy.observable, oX])
    _ = G.law.prob (fun ω => oX (G.observable ω) = true) :=
      wholeProb_congr G.law _ _ (by intro ω; rfl)
    _ = S.law.prob (fun e => oX (S.wholeObservable e) = true) :=
      popProb_eq G S hr (fun o => oX o = true)
    _ = S.law.prob (fun e => S.X e = true) :=
      (finiteProb_congr S.law _ _ (by intro e; simp [Study.wholeObservable, oX])).symm

theorem pop_truthRate_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S) :
    G.truthRate = S.truthRate := by
  unfold WholeMeasureStudy.truthRate Study.truthRate
  calc
    G.law.ce (fun ω => bitVal (G.Y ω)) (fun ω => G.X ω = true) =
        G.law.ce (fun ω => bitVal (G.Y ω))
          (fun ω => oX (G.observable ω) = true) :=
            wholeCE_congr G.law _ _ _ (by intro ω; simp [WholeMeasureStudy.observable, oX])
    _ = G.law.ce (fun ω => bitVal (oY (G.observable ω)))
          (fun ω => oX (G.observable ω) = true) :=
      wholeCE_congr G.law _ _ _ (by intro ω; rfl)
    _ = S.law.ce (fun e => bitVal (oY (S.wholeObservable e)))
          (fun e => oX (S.wholeObservable e) = true) :=
      popCE_eq G S hr (fun o => bitVal (oY o)) (fun o => oX o = true)
    _ = S.law.ce (fun e => bitVal (S.Y e))
          (fun e => oX (S.wholeObservable e) = true) :=
      finiteCE_congr S.law _ _ _ (by intro e; simp [Study.wholeObservable])
    _ = S.law.ce (fun e => bitVal (S.Y e)) (fun e => S.X e = true) :=
      (finiteCE_congr S.law _ _ _ (by intro e; simp [Study.wholeObservable, oX])).symm

theorem pop_listMean_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (z y : Bool) : G.listMean z y = S.listMean z y := by
  unfold WholeMeasureStudy.listMean Study.listMean
  calc
    G.law.ce (fun ω => (G.V ω : ℝ)) (G.cell z y) =
        G.law.ce (fun ω => (G.V ω : ℝ)) (fun ω => oCell (G.observable ω) z y) :=
          wholeCE_congr G.law _ _ _ (by intro ω; simp [WholeMeasureStudy.cell,
            WholeMeasureStudy.observable, oCell, oY, oZ])
    _ = G.law.ce (fun ω => (oV (G.observable ω) : ℝ))
          (fun ω => oCell (G.observable ω) z y) :=
      wholeCE_congr G.law _ _ _ (by intro ω; simp [WholeMeasureStudy.observable])
    _ = S.law.ce (fun e => (oV (S.wholeObservable e) : ℝ))
          (fun e => oCell (S.wholeObservable e) z y) :=
      popCE_eq G S hr (fun o => (oV o : ℝ)) (fun o => oCell o z y)
    _ = S.law.ce (fun e => (S.V e : ℝ)) (fun e => oCell (S.wholeObservable e) z y) :=
      finiteCE_congr S.law _ _ _ (by intro e; simp [Study.wholeObservable])
    _ = S.law.ce (fun e => (S.V e : ℝ)) (S.cell z y) :=
      (finiteCE_congr S.law _ _ _ (by intro e; simp [Study.cell, Study.wholeObservable,
        oCell, oY, oZ])).symm

theorem pop_cellCV_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (z y : Bool) :
    G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell z y) =
      S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y) := by
  calc
    G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell z y) =
        G.law.cv (fun ω => (G.V ω : ℝ)) (fun ω => oCell (G.observable ω) z y) :=
          wholeCV_congr G.law _ _ _ (by intro ω; simp [WholeMeasureStudy.cell,
            WholeMeasureStudy.observable, oCell, oY, oZ])
    _ = G.law.cv (fun ω => (oV (G.observable ω) : ℝ))
          (fun ω => oCell (G.observable ω) z y) :=
      wholeCV_congr G.law _ _ _ (by intro ω; simp [WholeMeasureStudy.observable])
    _ = S.law.cv (fun e => (oV (S.wholeObservable e) : ℝ))
          (fun e => oCell (S.wholeObservable e) z y) :=
      popCV_eq G S hr (fun o => (oV o : ℝ)) (fun o => oCell o z y)
    _ = S.law.cv (fun e => (S.V e : ℝ)) (fun e => oCell (S.wholeObservable e) z y) :=
      finiteCV_congr S.law _ _ _ (by intro e; simp [Study.wholeObservable])
    _ = S.law.cv (fun e => (S.V e : ℝ)) (S.cell z y) :=
      (finiteCV_congr S.law _ _ _ (by intro e; simp [Study.cell, Study.wholeObservable,
        oCell, oY, oZ])).symm

theorem pop_cellProb_eq {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {F : Type*} [Fintype F] (S : Study F) (hr : wholeRepresentation G S)
    (z y : Bool) :
    G.law.prob (G.cell z y) = S.law.prob (S.cell z y) := by
  calc
    G.law.prob (G.cell z y) =
        G.law.prob (fun ω => oCell (G.observable ω) z y) :=
          wholeProb_congr G.law _ _ (by intro ω; simp [WholeMeasureStudy.cell,
            WholeMeasureStudy.observable, oCell, oY, oZ])
    _ = G.law.prob (fun ω => oCell (G.observable ω) z y) :=
      wholeProb_congr G.law _ _ (by intro ω; rfl)
    _ = S.law.prob (fun e => oCell (S.wholeObservable e) z y) :=
      popProb_eq G S hr (fun o => oCell o z y)
    _ = S.law.prob (fun e => S.cell z y e) :=
      finiteProb_congr S.law _ _ (by intro e; simp [Study.wholeObservable, Study.cell,
        oCell, oY, oZ])
    _ = S.law.prob (S.cell z y) := rfl

theorem cellCount_labels_eq {E : Type*} [MeasurableSpace E]
    (G : WholeMeasureStudy E) {F : Type*} [Fintype F] (S : Study F)
    {n : ℕ} (s : Fin n → E) (t : Fin n → F)
    (hlab : ∀ i, S.Y (t i) = G.Y (s i) ∧ S.Z (t i) = G.Z (s i))
    (z y : Bool) : G.cellCount s z y = S.cellCount t z y := by
  unfold WholeMeasureStudy.cellCount Study.cellCount
  apply Finset.sum_congr rfl
  intro i hi
  simp only [WholeMeasureStudy.cell, Study.cell]
  by_cases hg : G.Z (s i) = z ∧ G.Y (s i) = y
  · have hs : S.Z (t i) = z ∧ S.Y (t i) = y := by
      rcases hg with ⟨hz, hy⟩
      exact ⟨(hlab i).2.trans hz, (hlab i).1.trans hy⟩
    simp [hg, hs]
  · have hs : ¬ (S.Z (t i) = z ∧ S.Y (t i) = y) := by
      intro hs
      apply hg
      rcases hs with ⟨hz, hy⟩
      exact ⟨(hlab i).2.symm.trans hz, (hlab i).1.symm.trans hy⟩
    simp [hg, hs]

theorem cellCount_labels_eq' {E : Type*} [MeasurableSpace E]
    (G : WholeMeasureStudy E) {F : Type*} [Fintype F] (S : Study F)
    {n : ℕ} (s : Fin n → E) (t : Fin n → F)
    (hlab : ∀ i, S.Y (t i) = G.Y (s i) ∧ S.Z (t i) = G.Z (s i))
    (z y : Bool) : S.cellCount t z y = G.cellCount s z y :=
  (cellCount_labels_eq G S s t hlab z y).symm

theorem armCount_labels_eq {E : Type*} [MeasurableSpace E]
    (G : WholeMeasureStudy E) {F : Type*} [Fintype F] (S : Study F)
    {n : ℕ} (s : Fin n → E) (t : Fin n → F)
    (hlab : ∀ i, S.Z (t i) = G.Z (s i)) (z : Bool) :
    G.armCount s z = S.armCount t z := by
  unfold WholeMeasureStudy.armCount Study.armCount
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hg : G.Z (s i) = z
  · have hs : S.Z (t i) = z := (hlab i).trans hg
    simp [hg, hs]
  · have hs : S.Z (t i) ≠ z := by
      intro hs
      apply hg
      exact (hlab i).symm.trans hs
    simp [hg, hs]
theorem g_negativeCount {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) : G.negativeCount s = oNegativeCount (ObsSeq G s) := rfl
theorem s_negativeCount {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) : S.negativeCount s = oNegativeCount (FinObsSeq S s) := rfl
theorem g_armCount {E : Type*} [MeasurableSpace E] (G : WholeMeasureStudy E)
    {n : ℕ} (s : Fin n → E) (z : Bool) : G.armCount s z = oArmCount (ObsSeq G s) z := rfl
theorem s_armCount {E : Type*} [Fintype E] (S : Study E)
    {n : ℕ} (s : Fin n → E) (z : Bool) : S.armCount s z = oArmCount (FinObsSeq S s) z := rfl

end
end SAP.P019a.WH.W1.P.T4_L5

namespace SAP.P019a.WH.W1
open SAP.P019a Filter MeasureTheory ProbabilityTheory
open SAP.P019a.WH.W1.P.T4_L5
open scoped BigOperators Topology
noncomputable section
open Classical

theorem T4_L5_proof : SAP.P019a.WH.W1.T4_L5 := by
  intro E _ G N S hprob hmeas hbound hGstand hSstand hrep hcore
  have hgamma := SAP.P019a.WH.W1.P.T4_L5.pop_gamma_eq G S hrep
  have hmu := SAP.P019a.WH.W1.P.T4_L5.pop_mu_eq G S hrep
  have htruth := SAP.P019a.WH.W1.P.T4_L5.pop_truthRate_eq G S hrep
  have hlist (z y : Bool) := SAP.P019a.WH.W1.P.T4_L5.pop_listMean_eq G S hrep z y
  have hcellCV (z y : Bool) := SAP.P019a.WH.W1.P.T4_L5.pop_cellCV_eq G S hrep z y
  have hcellProb (z y : Bool) := SAP.P019a.WH.W1.P.T4_L5.pop_cellProb_eq G S hrep z y
  have hlabel (z y : Bool) : ∃ e : Fin N, S.Z e = z ∧ S.Y e = y := by
    have hp : 0 < S.law.prob (S.cell z y) := hSstand.2.2.2.1 z y |>.1
    by_contra hn
    have hfun : (fun e : Fin N => if S.cell z y e then (1 : ℝ) else 0) = fun _ => 0 := by
      funext e
      simp [Study.cell, not_exists.mp hn e]
    have hz : S.law.prob (S.cell z y) = 0 := by
      unfold FiniteLaw.prob FiniteLaw.mean
      rw [hfun]
      simp
    linarith
  let rep : Bool → Bool → Fin N := fun z y => Classical.choose (hlabel z y)
  have repZ (z y : Bool) : S.Z (rep z y) = z := (Classical.choose_spec (hlabel z y)).1
  have repY (z y : Bool) : S.Y (rep z y) = y := (Classical.choose_spec (hlabel z y)).2
  rcases hcore with ⟨hEmpty, hMain, hAsym, hTreat⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n z
    have hP : (G.law.iid n).prob (fun s => G.cellCount s z false = 0) =
        (S.law.iid n).prob (fun s => S.cellCount s z false = 0) := by
      change (G.law.iid n).prob
          (fun s => SAP.P019a.WH.W1.P.T4_L5.oCellCount
            (SAP.P019a.WH.W1.P.T4_L5.ObsSeq G s) z false = 0) =
        (S.law.iid n).prob
          (fun s => SAP.P019a.WH.W1.P.T4_L5.oCellCount
            (SAP.P019a.WH.W1.P.T4_L5.FinObsSeq S s) z false = 0)
      exact SAP.P019a.WH.W1.P.T4_L5.sampleProb_eq G S hrep n
        (fun q => SAP.P019a.WH.W1.P.T4_L5.oCellCount q z false = 0)
    rcases hEmpty n z with ⟨heq, hpos⟩
    constructor
    · calc
        _ = (S.law.iid n).prob (fun s => S.cellCount s z false = 0) := hP
        _ = (1 - S.law.prob (S.cell z false))^n := heq
        _ = (1 - G.law.prob (G.cell z false))^n := by rw [← hcellProb z false]
    · rw [hP]
      exact hpos
  · intro n hn c1 c0
    obtain ⟨hOcc, hCount, hPattern, hGivenA, hCovA, hCovCross,
      hVarMu, hVarAB, hPrinted, hDiff⟩ := hMain n hn c1 c0
    have hb : G.listMean true false - G.listMean false false - 1 =
        S.listMean true false - S.listMean false false - 1 := by
      rw [hlist true false, hlist false false]
    have hOccEventG (r : Fin n → E) :
        G.occupied r ↔ oOccupied (ObsSeq G r) := by rw [g_occupied]
    have hOccEventS (r : Fin n → Fin N) :
        S.occupied r ↔ oOccupied (FinObsSeq S r) := by rw [s_occupied]
    have liftCE (gG : (Fin n → E) → ℝ) (gS : (Fin n → Fin N) → ℝ)
        (f : (Fin n → WholeObservation) → ℝ)
        (hg : ∀ r, gG r = f (ObsSeq G r))
        (hs : ∀ r, gS r = f (FinObsSeq S r)) :
        (G.law.iid n).ce gG G.occupied = (S.law.iid n).ce gS S.occupied := by
      calc
        _ = (G.law.iid n).ce (fun r => f (ObsSeq G r)) G.occupied :=
          wholeCE_fun_congr (G.law.iid n) _ _ _ hg
        _ = (G.law.iid n).ce (fun r => f (ObsSeq G r))
              (fun r => oOccupied (ObsSeq G r)) :=
          wholeCE_congr (G.law.iid n) _ _ _ hOccEventG
        _ = (S.law.iid n).ce (fun r => f (FinObsSeq S r))
              (fun r => oOccupied (FinObsSeq S r)) :=
          sampleCE_eq G S hrep n f (fun q => oOccupied q)
        _ = (S.law.iid n).ce (fun r => f (FinObsSeq S r)) S.occupied :=
          (finiteCE_congr (S.law.iid n) _ _ _ hOccEventS).symm
        _ = (S.law.iid n).ce gS S.occupied :=
          finiteCE_fun_congr (S.law.iid n) _ _ _ (fun r => (hs r).symm)
    have liftCV (gG : (Fin n → E) → ℝ) (gS : (Fin n → Fin N) → ℝ)
        (f : (Fin n → WholeObservation) → ℝ)
        (hg : ∀ r, gG r = f (ObsSeq G r))
        (hs : ∀ r, gS r = f (FinObsSeq S r)) :
        (G.law.iid n).cv gG G.occupied = (S.law.iid n).cv gS S.occupied := by
      calc
        _ = (G.law.iid n).cv (fun r => f (ObsSeq G r)) G.occupied :=
          wholeCV_fun_congr (G.law.iid n) _ _ _ hg
        _ = (G.law.iid n).cv (fun r => f (ObsSeq G r))
              (fun r => oOccupied (ObsSeq G r)) :=
          wholeCV_congr (G.law.iid n) _ _ _ hOccEventG
        _ = (S.law.iid n).cv (fun r => f (FinObsSeq S r))
              (fun r => oOccupied (FinObsSeq S r)) :=
          sampleCV_eq G S hrep n f (fun q => oOccupied q)
        _ = (S.law.iid n).cv (fun r => f (FinObsSeq S r)) S.occupied :=
          (finiteCV_congr (S.law.iid n) _ _ _ hOccEventS).symm
        _ = (S.law.iid n).cv gS S.occupied :=
          finiteCV_fun_congr (S.law.iid n) _ _ _ (fun r => (hs r).symm)
    have liftCCov (gG hG : (Fin n → E) → ℝ) (gS hS : (Fin n → Fin N) → ℝ)
        (f g : (Fin n → WholeObservation) → ℝ)
        (hgf : ∀ r, gG r = f (ObsSeq G r)) (hgh : ∀ r, hG r = g (ObsSeq G r))
        (hsf : ∀ r, gS r = f (FinObsSeq S r)) (hsh : ∀ r, hS r = g (FinObsSeq S r)) :
        (G.law.iid n).ccov gG hG G.occupied =
          (S.law.iid n).ccov gS hS S.occupied := by
      calc
        _ = (G.law.iid n).ccov (fun r => f (ObsSeq G r))
              (fun r => g (ObsSeq G r)) G.occupied :=
          wholeCCov_fun_congr (G.law.iid n) _ _ _ _ _ hgf hgh
        _ = (G.law.iid n).ccov (fun r => f (ObsSeq G r))
              (fun r => g (ObsSeq G r)) (fun r => oOccupied (ObsSeq G r)) :=
          wholeCCov_event_congr (G.law.iid n) _ _ _ _ hOccEventG
        _ = (S.law.iid n).ccov (fun r => f (FinObsSeq S r))
              (fun r => g (FinObsSeq S r)) (fun r => oOccupied (FinObsSeq S r)) :=
          sampleCCov_eq G S hrep n f g (fun q => oOccupied q)
        _ = (S.law.iid n).ccov (fun r => f (FinObsSeq S r))
              (fun r => g (FinObsSeq S r)) S.occupied :=
          (finiteCCov_event_congr (S.law.iid n) _ _ _ _ hOccEventS).symm
        _ = (S.law.iid n).ccov gS hS S.occupied :=
          finiteCCov_fun_congr (S.law.iid n) _ _ _ _ _ (fun r => (hsf r).symm)
            (fun r => (hsh r).symm)
    let vT : ℝ := S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false)
    let vC : ℝ := S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)
    have hG_H (r : Fin n → E) : G.sampleH r = oH vT vC (ObsSeq G r) := by
      rw [g_sampleH, hcellCV true false, hcellCV false false]
    have hS_H (r : Fin n → Fin N) : S.sampleH r = oH vT vC (FinObsSeq S r) := by
      rw [s_sampleH]
    have hG_A (r : Fin n → E) : G.sampleA r = oA (ObsSeq G r) := g_sampleA G r
    have hS_A (r : Fin n → Fin N) : S.sampleA r = oA (FinObsSeq S r) := s_sampleA S r
    have hG_B (r : Fin n → E) : G.sampleB r c1 c0 = oB (ObsSeq G r) c1 c0 :=
      g_sampleB G r c1 c0
    have hS_B (r : Fin n → Fin N) : S.sampleB r c1 c0 = oB (FinObsSeq S r) c1 c0 :=
      s_sampleB S r c1 c0
    have hG_Mu (r : Fin n → E) : G.muHat r c1 c0 = oMuHat (ObsSeq G r) c1 c0 :=
      g_muHat G r c1 c0
    have hS_Mu (r : Fin n → Fin N) : S.muHat r c1 c0 = oMuHat (FinObsSeq S r) c1 c0 :=
      s_muHat S r c1 c0
    have hG_A2H (r : Fin n → E) : G.sampleA r ^ 2 * G.sampleH r =
        oA (ObsSeq G r)^2 * oH vT vC (ObsSeq G r) := by rw [hG_A r, hG_H r]
    have hS_A2H (r : Fin n → Fin N) : S.sampleA r ^ 2 * S.sampleH r =
        oA (FinObsSeq S r)^2 * oH vT vC (FinObsSeq S r) := by rw [hS_A r, hS_H r]
    have hG_AB (r : Fin n → E) : G.sampleA r * G.sampleB r c1 c0 =
        oA (ObsSeq G r) * oB (ObsSeq G r) c1 c0 := by rw [hG_A r, hG_B r]
    have hS_AB (r : Fin n → Fin N) : S.sampleA r * S.sampleB r c1 c0 =
        oA (FinObsSeq S r) * oB (FinObsSeq S r) c1 c0 := by rw [hS_A r, hS_B r]
    have hCEA := liftCE (fun r => G.sampleA r) (fun r => S.sampleA r) oA hG_A hS_A
    have hCEA2 := liftCE (fun r => G.sampleA r ^ 2) (fun r => S.sampleA r ^ 2)
      (fun q => oA q ^ 2) (fun r => by rw [hG_A r]) (fun r => by rw [hS_A r])
    have hCEH := liftCE (fun r => G.sampleH r) (fun r => S.sampleH r)
      (fun q => oH vT vC q) hG_H hS_H
    have hCEA2H := liftCE (fun r => G.sampleA r ^ 2 * G.sampleH r)
      (fun r => S.sampleA r ^ 2 * S.sampleH r)
      (fun q => oA q ^ 2 * oH vT vC q) hG_A2H hS_A2H
    have hCEB := liftCE (fun r => G.sampleB r c1 c0) (fun r => S.sampleB r c1 c0)
      (fun q => oB q c1 c0) hG_B hS_B
    have hCVA := liftCV (fun r => G.sampleA r) (fun r => S.sampleA r) oA hG_A hS_A
    have hCVB := liftCV (fun r => G.sampleB r c1 c0) (fun r => S.sampleB r c1 c0)
      (fun q => oB q c1 c0) hG_B hS_B
    have hCVMu := liftCV (fun r => G.muHat r c1 c0) (fun r => S.muHat r c1 c0)
      (fun q => oMuHat q c1 c0) hG_Mu hS_Mu
    have hCVAB := liftCV (fun r => G.sampleA r * G.sampleB r c1 c0)
      (fun r => S.sampleA r * S.sampleB r c1 c0)
      (fun q => oA q * oB q c1 c0) hG_AB hS_AB
    have hCCovA2H := liftCCov (fun r => G.sampleA r ^ 2) (fun r => G.sampleH r)
      (fun r => S.sampleA r ^ 2) (fun r => S.sampleH r)
      (fun q => oA q ^ 2) (fun q => oH vT vC q)
      (fun r => by rw [hG_A r]) hG_H (fun r => by rw [hS_A r]) hS_H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 < (G.law.iid n).prob (fun s => SAP.P019a.WH.W1.P.T4_L5.oOccupied
        (SAP.P019a.WH.W1.P.T4_L5.ObsSeq G s))
      have hp := SAP.P019a.WH.W1.P.T4_L5.sampleProb_eq G S hrep n
        (fun q => SAP.P019a.WH.W1.P.T4_L5.oOccupied q)
      rw [hp]
      exact hOcc
    · intro k hk hK
      have hPK : (G.law.iid n).prob (fun s => G.negativeCount s = k) =
          (S.law.iid n).prob (fun s => S.negativeCount s = k) := by
        change (G.law.iid n).prob (fun s => oNegativeCount (ObsSeq G s) = k) =
          (S.law.iid n).prob (fun s => oNegativeCount (FinObsSeq S s) = k)
        exact sampleProb_eq G S hrep n (fun q => oNegativeCount q = k)
      have hKfin : (S.law.iid n).prob (fun s => S.negativeCount s = k) ≠ 0 := by
        rw [← hPK]
        exact hK
      obtain ⟨hChoose, hTrue, hFalse⟩ := hCount k hk hKfin
      have hChooseEq (i : ℕ) :
          (G.law.iid n).ce (fun s => if G.cellCount s true false = i then (1 : ℝ) else 0)
              (fun s => G.negativeCount s = k) =
            (S.law.iid n).ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
              (fun s => S.negativeCount s = k) := by
        change (G.law.iid n).ce
            (fun s => if oCellCount (ObsSeq G s) true false = i then (1 : ℝ) else 0)
            (fun s => oNegativeCount (ObsSeq G s) = k) =
          (S.law.iid n).ce
            (fun s => if oCellCount (FinObsSeq S s) true false = i then (1 : ℝ) else 0)
            (fun s => oNegativeCount (FinObsSeq S s) = k)
        exact sampleCE_eq G S hrep n
          (fun q => if oCellCount q true false = i then (1 : ℝ) else 0)
          (fun q => oNegativeCount q = k)
      have hTrueEq :
          (G.law.iid n).ce (fun s => if 0 < G.cellCount s true false then (1 : ℝ) else 0)
              (fun s => G.negativeCount s = k) =
            (S.law.iid n).ce (fun s => if 0 < S.cellCount s true false then (1 : ℝ) else 0)
              (fun s => S.negativeCount s = k) := by
        change (G.law.iid n).ce
            (fun s => if 0 < oCellCount (ObsSeq G s) true false then (1 : ℝ) else 0)
            (fun s => oNegativeCount (ObsSeq G s) = k) =
          (S.law.iid n).ce
            (fun s => if 0 < oCellCount (FinObsSeq S s) true false then (1 : ℝ) else 0)
            (fun s => oNegativeCount (FinObsSeq S s) = k)
        exact sampleCE_eq G S hrep n
          (fun q => if 0 < oCellCount q true false then (1 : ℝ) else 0)
          (fun q => oNegativeCount q = k)
      have hFalseEq :
          (G.law.iid n).ce (fun s => if 0 < G.cellCount s false false then (1 : ℝ) else 0)
              (fun s => G.negativeCount s = k) =
            (S.law.iid n).ce (fun s => if 0 < S.cellCount s false false then (1 : ℝ) else 0)
              (fun s => S.negativeCount s = k) := by
        change (G.law.iid n).ce
            (fun s => if 0 < oCellCount (ObsSeq G s) false false then (1 : ℝ) else 0)
            (fun s => oNegativeCount (ObsSeq G s) = k) =
          (S.law.iid n).ce
            (fun s => if 0 < oCellCount (FinObsSeq S s) false false then (1 : ℝ) else 0)
            (fun s => oNegativeCount (FinObsSeq S s) = k)
        exact sampleCE_eq G S hrep n
          (fun q => if 0 < oCellCount q false false then (1 : ℝ) else 0)
          (fun q => oNegativeCount q = k)
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        calc
          _ = (S.law.iid n).ce (fun s => if S.cellCount s true false = i then (1 : ℝ) else 0)
                (fun s => S.negativeCount s = k) := hChooseEq i
          _ = (Nat.choose k i : ℝ) * G.gamma^i * (1-G.gamma)^(k-i) := by
                rw [hgamma]
                exact hChoose i hi
      · calc
          _ = (S.law.iid n).ce (fun s => if 0 < S.cellCount s true false then (1 : ℝ) else 0)
                (fun s => S.negativeCount s = k) := hTrueEq
          _ = 1-(1-G.gamma)^k := by rw [hgamma]; exact hTrue
      · calc
          _ = (S.law.iid n).ce (fun s => if 0 < S.cellCount s false false then (1 : ℝ) else 0)
                (fun s => S.negativeCount s = k) := hFalseEq
          _ = 1-G.gamma^k := by rw [hgamma]; exact hFalse
    · intro s hsOcc hsPat
      let t : Fin n → Fin N := fun i => rep (G.Z (s i)) (G.Y (s i))
      have hlabels : ∀ i, S.Y (t i) = G.Y (s i) ∧ S.Z (t i) = G.Z (s i) := by
        intro i
        exact ⟨repY (G.Z (s i)) (G.Y (s i)), repZ (G.Z (s i)) (G.Y (s i))⟩
      have hcounts (z y : Bool) : G.cellCount s z y = S.cellCount t z y :=
        cellCount_labels_eq G S s t hlabels z y
      have htOcc : S.occupied t := by
        rcases hsOcc with ⟨ht, hf⟩
        exact ⟨by rw [← hcounts true false]; exact ht,
          by rw [← hcounts false false]; exact hf⟩
      have hAnchor (i : Fin n) :
          oY (FinObsSeq S t i) = oY (ObsSeq G s i) ∧
          oZ (FinObsSeq S t i) = oZ (ObsSeq G s i) := by
        change S.Y (t i) = G.Y (s i) ∧ S.Z (t i) = G.Z (s i)
        exact hlabels i
      have hEvent (q : Fin n → WholeObservation) :
          oPattern (ObsSeq G s) q = oPattern (FinObsSeq S t) q := by
        apply propext
        unfold oPattern
        constructor <;> intro hp i
        · rcases hp i with ⟨hy, hz⟩
          exact ⟨hy.trans (hAnchor i).1.symm, hz.trans (hAnchor i).2.symm⟩
        · rcases hp i with ⟨hy, hz⟩
          exact ⟨hy.trans (hAnchor i).1, hz.trans (hAnchor i).2⟩
      have hPatEventG (r : Fin n → E) :
          G.patternFibre s r ↔ oPattern (ObsSeq G s) (ObsSeq G r) := by
        rw [g_pattern]
      have hPatEventS (r : Fin n → Fin N) :
          S.patternFibre t r ↔ oPattern (ObsSeq G s) (FinObsSeq S r) := by
        rw [s_pattern]
        exact (Iff.of_eq (hEvent (FinObsSeq S r))).symm
      have hPatProb : (G.law.iid n).prob (G.patternFibre s) =
          (S.law.iid n).prob (S.patternFibre t) := by
        calc
          _ = (G.law.iid n).prob (fun r => oPattern (ObsSeq G s) (ObsSeq G r)) :=
            wholeProb_congr (G.law.iid n) _ _ hPatEventG
          _ = (S.law.iid n).prob
              (fun r => oPattern (ObsSeq G s) (FinObsSeq S r)) :=
            sampleProb_eq G S hrep n (fun q => oPattern (ObsSeq G s) q)
          _ = (S.law.iid n).prob (S.patternFibre t) :=
            (finiteProb_congr (S.law.iid n) _ _ hPatEventS).symm
      have hPatFin : (S.law.iid n).prob (S.patternFibre t) ≠ 0 := by
        rw [← hPatProb]
        exact hsPat
      obtain ⟨hCells, hCrossPat, hCEB, hCVB⟩ := hPattern t htOcc hPatFin
      have hb : G.listMean true false - G.listMean false false - 1 =
          S.listMean true false - S.listMean false false - 1 := by
        rw [hlist true false, hlist false false]
      have hCellCE (z : Bool) :
          (G.law.iid n).ce (fun r => G.cellMean r z false (if z then c1 else c0))
              (G.patternFibre s) =
            (S.law.iid n).ce (fun r => S.cellMean r z false (if z then c1 else c0))
              (S.patternFibre t) := by
        calc
          _ = (G.law.iid n).ce
              (fun r => oCellMean (ObsSeq G r) z false (if z then c1 else c0))
              (G.patternFibre s) :=
                wholeCE_fun_congr (G.law.iid n) _ _ _
                  (fun r => g_cellMean G r z false (if z then c1 else c0))
          _ = (G.law.iid n).ce
              (fun r => oCellMean (ObsSeq G r) z false (if z then c1 else c0))
              (fun r => oPattern (ObsSeq G s) (ObsSeq G r)) :=
                wholeCE_congr (G.law.iid n) _ _ _ hPatEventG
          _ = (S.law.iid n).ce
              (fun r => oCellMean (FinObsSeq S r) z false (if z then c1 else c0))
              (fun r => oPattern (ObsSeq G s) (FinObsSeq S r)) :=
                sampleCE_eq G S hrep n
                  (fun q => oCellMean q z false (if z then c1 else c0))
                  (fun q => oPattern (ObsSeq G s) q)
          _ = (S.law.iid n).ce
              (fun r => oCellMean (FinObsSeq S r) z false (if z then c1 else c0))
              (S.patternFibre t) :=
                (finiteCE_congr (S.law.iid n) _ _ _ hPatEventS).symm
          _ = (S.law.iid n).ce
              (fun r => S.cellMean r z false (if z then c1 else c0))
              (S.patternFibre t) :=
                finiteCE_fun_congr (S.law.iid n) _ _ _
                  (fun r => (s_cellMean S r z false (if z then c1 else c0)).symm)
      have hCellCV (z : Bool) :
          (G.law.iid n).cv (fun r => G.cellMean r z false (if z then c1 else c0))
              (G.patternFibre s) =
            (S.law.iid n).cv (fun r => S.cellMean r z false (if z then c1 else c0))
              (S.patternFibre t) := by
        calc
          _ = (G.law.iid n).cv
              (fun r => oCellMean (ObsSeq G r) z false (if z then c1 else c0))
              (G.patternFibre s) :=
                wholeCV_fun_congr (G.law.iid n) _ _ _
                  (fun r => g_cellMean G r z false (if z then c1 else c0))
          _ = (G.law.iid n).cv
              (fun r => oCellMean (ObsSeq G r) z false (if z then c1 else c0))
              (fun r => oPattern (ObsSeq G s) (ObsSeq G r)) :=
                wholeCV_congr (G.law.iid n) _ _ _ hPatEventG
          _ = (S.law.iid n).cv
              (fun r => oCellMean (FinObsSeq S r) z false (if z then c1 else c0))
              (fun r => oPattern (ObsSeq G s) (FinObsSeq S r)) :=
                sampleCV_eq G S hrep n
                  (fun q => oCellMean q z false (if z then c1 else c0))
                  (fun q => oPattern (ObsSeq G s) q)
          _ = (S.law.iid n).cv
              (fun r => oCellMean (FinObsSeq S r) z false (if z then c1 else c0))
              (S.patternFibre t) :=
                (finiteCV_congr (S.law.iid n) _ _ _ hPatEventS).symm
          _ = (S.law.iid n).cv
              (fun r => S.cellMean r z false (if z then c1 else c0))
              (S.patternFibre t) :=
                finiteCV_fun_congr (S.law.iid n) _ _ _
                  (fun r => (s_cellMean S r z false (if z then c1 else c0)).symm)
      have hCrossEq :
          (G.law.iid n).ccov (fun r => G.cellMean r true false c1)
              (fun r => G.cellMean r false false c0) (G.patternFibre s) =
            (S.law.iid n).ccov (fun r => S.cellMean r true false c1)
              (fun r => S.cellMean r false false c0) (S.patternFibre t) := by
        calc
          _ = (G.law.iid n).ccov
              (fun r => oCellMean (ObsSeq G r) true false c1)
              (fun r => oCellMean (ObsSeq G r) false false c0) (G.patternFibre s) :=
                wholeCCov_fun_congr (G.law.iid n) _ _ _ _ _
                  (fun r => g_cellMean G r true false c1)
                  (fun r => g_cellMean G r false false c0)
          _ = (G.law.iid n).ccov
              (fun r => oCellMean (ObsSeq G r) true false c1)
              (fun r => oCellMean (ObsSeq G r) false false c0)
              (fun r => oPattern (ObsSeq G s) (ObsSeq G r)) :=
                wholeCCov_event_congr (G.law.iid n) _ _ _ _ hPatEventG
          _ = (S.law.iid n).ccov
              (fun r => oCellMean (FinObsSeq S r) true false c1)
              (fun r => oCellMean (FinObsSeq S r) false false c0)
              (fun r => oPattern (ObsSeq G s) (FinObsSeq S r)) :=
                sampleCCov_eq G S hrep n
                  (fun q => oCellMean q true false c1)
                  (fun q => oCellMean q false false c0)
                  (fun q => oPattern (ObsSeq G s) q)
          _ = (S.law.iid n).ccov
              (fun r => oCellMean (FinObsSeq S r) true false c1)
              (fun r => oCellMean (FinObsSeq S r) false false c0) (S.patternFibre t) :=
                (finiteCCov_event_congr (S.law.iid n) _ _ _ _ hPatEventS).symm
          _ = (S.law.iid n).ccov
              (fun r => S.cellMean r true false c1)
              (fun r => S.cellMean r false false c0) (S.patternFibre t) :=
                finiteCCov_fun_congr (S.law.iid n) _ _ _ _ _
                  (fun r => (s_cellMean S r true false c1).symm)
                  (fun r => (s_cellMean S r false false c0).symm)
      have hBCE :
          (G.law.iid n).ce (fun r => G.sampleB r c1 c0) (G.patternFibre s) =
            (S.law.iid n).ce (fun r => S.sampleB r c1 c0) (S.patternFibre t) := by
        calc
          _ = (G.law.iid n).ce (fun r => oB (ObsSeq G r) c1 c0) (G.patternFibre s) :=
            wholeCE_fun_congr (G.law.iid n) _ _ _ (fun r => g_sampleB G r c1 c0)
          _ = (G.law.iid n).ce (fun r => oB (ObsSeq G r) c1 c0)
              (fun r => oPattern (ObsSeq G s) (ObsSeq G r)) :=
            wholeCE_congr (G.law.iid n) _ _ _ hPatEventG
          _ = (S.law.iid n).ce (fun r => oB (FinObsSeq S r) c1 c0)
              (fun r => oPattern (ObsSeq G s) (FinObsSeq S r)) :=
            sampleCE_eq G S hrep n (fun q => oB q c1 c0)
              (fun q => oPattern (ObsSeq G s) q)
          _ = (S.law.iid n).ce (fun r => oB (FinObsSeq S r) c1 c0)
              (S.patternFibre t) := (finiteCE_congr (S.law.iid n) _ _ _ hPatEventS).symm
          _ = (S.law.iid n).ce (fun r => S.sampleB r c1 c0) (S.patternFibre t) :=
            finiteCE_fun_congr (S.law.iid n) _ _ _ (fun r => (s_sampleB S r c1 c0).symm)
      have hcountsT (z : Bool) : G.cellCount s z false = S.cellCount t z false :=
        hcounts z false
      have hSampleH : G.sampleH s = S.sampleH t := by
        change G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell true false) /
              (G.cellCount s true false : ℝ) +
            G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell false false) /
              (G.cellCount s false false : ℝ) =
          S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) /
              (S.cellCount t true false : ℝ) +
            S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) /
              (S.cellCount t false false : ℝ)
        rw [hcellCV true false, hcellCV false false,
          hcountsT true, hcountsT false]
      have hBCV :
          (G.law.iid n).cv (fun r => G.sampleB r c1 c0) (G.patternFibre s) =
            (S.law.iid n).cv (fun r => S.sampleB r c1 c0) (S.patternFibre t) := by
        calc
          _ = (G.law.iid n).cv (fun r => oB (ObsSeq G r) c1 c0) (G.patternFibre s) :=
            wholeCV_fun_congr (G.law.iid n) _ _ _ (fun r => g_sampleB G r c1 c0)
          _ = (G.law.iid n).cv (fun r => oB (ObsSeq G r) c1 c0)
              (fun r => oPattern (ObsSeq G s) (ObsSeq G r)) :=
            wholeCV_congr (G.law.iid n) _ _ _ hPatEventG
          _ = (S.law.iid n).cv (fun r => oB (FinObsSeq S r) c1 c0)
              (fun r => oPattern (ObsSeq G s) (FinObsSeq S r)) :=
            sampleCV_eq G S hrep n (fun q => oB q c1 c0)
              (fun q => oPattern (ObsSeq G s) q)
          _ = (S.law.iid n).cv (fun r => oB (FinObsSeq S r) c1 c0)
              (S.patternFibre t) := (finiteCV_congr (S.law.iid n) _ _ _ hPatEventS).symm
          _ = (S.law.iid n).cv (fun r => S.sampleB r c1 c0) (S.patternFibre t) :=
            finiteCV_fun_congr (S.law.iid n) _ _ _ (fun r => (s_sampleB S r c1 c0).symm)
      refine ⟨?_, ?_, ?_⟩
      · intro z
        refine ⟨?_, ?_⟩
        · calc
            _ = (S.law.iid n).ce
                (fun r => S.cellMean r z false (if z then c1 else c0)) (S.patternFibre t) :=
                  hCellCE z
            _ = S.listMean z false := (hCells z).1
            _ = G.listMean z false := (hlist z false).symm
        · calc
            _ = (S.law.iid n).cv
                (fun r => S.cellMean r z false (if z then c1 else c0)) (S.patternFibre t) :=
                  hCellCV z
            _ = S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z false) /
                (S.cellCount t z false : ℝ) := (hCells z).2
            _ = G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell z false) /
                (G.cellCount s z false : ℝ) := by
                  rw [← hcellCV z false, ← hcounts z false]
      · calc
          _ = (S.law.iid n).ccov (fun r => S.cellMean r true false c1)
                (fun r => S.cellMean r false false c0) (S.patternFibre t) := hCrossEq
          _ = 0 := hCrossPat
      · refine ⟨?_, ?_⟩
        · calc
            _ = (S.law.iid n).ce (fun r => S.sampleB r c1 c0) (S.patternFibre t) := hBCE
            _ = S.listMean true false - S.listMean false false - 1 := hCEB
            _ = G.listMean true false - G.listMean false false - 1 := hb.symm
        · calc
            _ = (S.law.iid n).cv (fun r => S.sampleB r c1 c0) (S.patternFibre t) := hBCV
            _ = S.sampleH t := hCVB
            _ = G.sampleH s := hSampleH.symm
    · intro a hApos z
      have hPA : (G.law.iid n).prob (fun r => G.occupied r ∧ G.sampleA r = a) =
          (S.law.iid n).prob (fun r => S.occupied r ∧ S.sampleA r = a) := by
        change (G.law.iid n).prob
            (fun r => oOccupied (ObsSeq G r) ∧ oA (ObsSeq G r) = a) =
          (S.law.iid n).prob
            (fun r => oOccupied (FinObsSeq S r) ∧ oA (FinObsSeq S r) = a)
        exact sampleProb_eq G S hrep n (fun q => oOccupied q ∧ oA q = a)
      have hAposFin :
          (S.law.iid n).prob (fun r => S.occupied r ∧ S.sampleA r = a) ≠ 0 := by
        rw [← hPA]
        exact hApos
      have hMeanEq :
          (G.law.iid n).ce (fun r => G.cellMean r z false (if z then c1 else c0))
              (fun r => G.occupied r ∧ G.sampleA r = a) =
            (S.law.iid n).ce (fun r => S.cellMean r z false (if z then c1 else c0))
              (fun r => S.occupied r ∧ S.sampleA r = a) := by
        change (G.law.iid n).ce
            (fun r => oCellMean (ObsSeq G r) z false (if z then c1 else c0))
            (fun r => oOccupied (ObsSeq G r) ∧ oA (ObsSeq G r) = a) =
          (S.law.iid n).ce
            (fun r => oCellMean (FinObsSeq S r) z false (if z then c1 else c0))
            (fun r => oOccupied (FinObsSeq S r) ∧ oA (FinObsSeq S r) = a)
        exact sampleCE_eq G S hrep n
          (fun q => oCellMean q z false (if z then c1 else c0))
          (fun q => oOccupied q ∧ oA q = a)
      calc
        _ = (S.law.iid n).ce (fun r => S.cellMean r z false (if z then c1 else c0))
              (fun r => S.occupied r ∧ S.sampleA r = a) := hMeanEq
        _ = S.listMean z false := hGivenA a hAposFin z
        _ = G.listMean z false := (hlist z false).symm
    · intro z
      have hCovEq :
          (G.law.iid n).ccov (fun r => G.cellMean r z false (if z then c1 else c0))
              G.sampleA G.occupied =
            (S.law.iid n).ccov (fun r => S.cellMean r z false (if z then c1 else c0))
              S.sampleA S.occupied := by
        change (G.law.iid n).ccov
            (fun r => oCellMean (ObsSeq G r) z false (if z then c1 else c0))
            (fun r => oA (ObsSeq G r)) (fun r => oOccupied (ObsSeq G r)) =
          (S.law.iid n).ccov
            (fun r => oCellMean (FinObsSeq S r) z false (if z then c1 else c0))
            (fun r => oA (FinObsSeq S r)) (fun r => oOccupied (FinObsSeq S r))
        exact sampleCCov_eq G S hrep n
          (fun q => oCellMean q z false (if z then c1 else c0)) (fun q => oA q)
          (fun q => oOccupied q)
      calc
        _ = (S.law.iid n).ccov
              (fun r => S.cellMean r z false (if z then c1 else c0)) S.sampleA S.occupied := hCovEq
        _ = 0 := hCovA z
    · have hCovEq :
          (G.law.iid n).ccov (fun r => G.cellMean r true false c1)
              (fun r => G.cellMean r false false c0) G.occupied =
            (S.law.iid n).ccov (fun r => S.cellMean r true false c1)
              (fun r => S.cellMean r false false c0) S.occupied := by
        change (G.law.iid n).ccov
            (fun r => oCellMean (ObsSeq G r) true false c1)
            (fun r => oCellMean (ObsSeq G r) false false c0) (fun r => oOccupied (ObsSeq G r)) =
          (S.law.iid n).ccov
            (fun r => oCellMean (FinObsSeq S r) true false c1)
            (fun r => oCellMean (FinObsSeq S r) false false c0) (fun r => oOccupied (FinObsSeq S r))
        exact sampleCCov_eq G S hrep n
          (fun q => oCellMean q true false c1) (fun q => oCellMean q false false c0)
          (fun q => oOccupied q)
      calc
        _ = (S.law.iid n).ccov (fun r => S.cellMean r true false c1)
              (fun r => S.cellMean r false false c0) S.occupied := hCovEq
        _ = 0 := hCovCross
    · calc
        _ = (S.law.iid n).cv (fun r => S.muHat r c1 c0) S.occupied := hCVMu
        _ = (S.listMean true false - S.listMean false false - 1)^2 *
              (S.law.iid n).cv S.sampleA S.occupied +
            (S.law.iid n).ce (fun r => S.sampleA r ^ 2 * S.sampleH r) S.occupied := hVarMu
        _ = (G.listMean true false - G.listMean false false - 1)^2 *
              (G.law.iid n).cv G.sampleA G.occupied +
            (G.law.iid n).ce (fun r => G.sampleA r ^ 2 * G.sampleH r) G.occupied := by
              rw [← hb, ← hCVA, ← hCEA2H]
    · calc
        _ = (S.law.iid n).cv (fun r => S.sampleA r * S.sampleB r c1 c0) S.occupied := hCVAB
        _ = (S.listMean true false - S.listMean false false - 1)^2 *
              (S.law.iid n).cv S.sampleA S.occupied +
            (S.law.iid n).ce (fun r => S.sampleA r ^ 2 * S.sampleH r) S.occupied := hVarAB
        _ = (G.listMean true false - G.listMean false false - 1)^2 *
              (G.law.iid n).cv G.sampleA G.occupied +
            (G.law.iid n).ce (fun r => G.sampleA r ^ 2 * G.sampleH r) G.occupied := by
              rw [← hb, ← hCVA, ← hCEA2H]
    · rw [hCEA, hCVB, hCVA, hCEB, hCEA2, hCEH, hb]
      exact hPrinted
    · rw [hCVAB, hCEA, hCVB, hCEB, hCVA, hCCovA2H]
      exact hDiff
  · let Rg : ℕ → ℝ := fun n =>
      (G.law.iid (n+2)).ccov (fun s => G.sampleA s ^ 2) G.sampleH G.occupied
    let Rs : ℕ → ℝ := fun n =>
      (S.law.iid (n+2)).ccov (fun s => S.sampleA s ^ 2) S.sampleH S.occupied
    let vT : ℝ := S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false)
    let vC : ℝ := S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)
    have hR (n : ℕ) : Rg n = Rs n := by
      let m := n+2
      have hG_A (r : Fin m → E) : G.sampleA r ^ 2 = oA (ObsSeq G r)^2 := by
        rw [g_sampleA]
      have hS_A (r : Fin m → Fin N) : S.sampleA r ^ 2 = oA (FinObsSeq S r)^2 := by
        rw [s_sampleA]
      have hG_H (r : Fin m → E) : G.sampleH r = oH vT vC (ObsSeq G r) := by
        rw [g_sampleH, hcellCV true false, hcellCV false false]
      have hS_H (r : Fin m → Fin N) : S.sampleH r = oH vT vC (FinObsSeq S r) := by
        rw [s_sampleH]
      calc
        _ = (G.law.iid m).ccov (fun r => oA (ObsSeq G r)^2)
              (fun r => oH vT vC (ObsSeq G r)) G.occupied :=
          wholeCCov_fun_congr (G.law.iid m) _ _ _ _ _ hG_A hG_H
        _ = (G.law.iid m).ccov (fun r => oA (ObsSeq G r)^2)
              (fun r => oH vT vC (ObsSeq G r))
              (fun r => oOccupied (ObsSeq G r)) :=
          wholeCCov_event_congr (G.law.iid m) _ _ _ _ (by intro r; rw [g_occupied])
        _ = (S.law.iid m).ccov (fun r => oA (FinObsSeq S r)^2)
              (fun r => oH vT vC (FinObsSeq S r))
              (fun r => oOccupied (FinObsSeq S r)) :=
          sampleCCov_eq G S hrep m (fun q => oA q^2) (fun q => oH vT vC q)
            (fun q => oOccupied q)
        _ = (S.law.iid m).ccov (fun r => oA (FinObsSeq S r)^2)
              (fun r => oH vT vC (FinObsSeq S r)) S.occupied :=
          (finiteCCov_event_congr (S.law.iid m) _ _ _ _
            (by intro r; rw [s_occupied])).symm
        _ = (S.law.iid m).ccov (fun r => S.sampleA r ^ 2) S.sampleH S.occupied :=
          finiteCCov_fun_congr (S.law.iid m) _ _ _ _ _
            (fun r => (hS_A r).symm) (fun r => (hS_H r).symm)
    have hSeq : Rg = Rs := funext hR
    have hSeqMul : (fun n => ((n+2:ℕ):ℝ)^2 * Rg n) =
        (fun n => ((n+2:ℕ):ℝ)^2 * Rs n) := by
      funext n
      rw [hR n]
    have hTarget :
        -2 * (G.mu * G.truthRate) *
          (G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell true false) / G.gamma +
            G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell false false) / (1-G.gamma)) =
        -2 * (S.mu * S.truthRate) *
          (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / S.gamma +
            S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (1-S.gamma)) := by
      rw [hmu, htruth, hcellCV true false, hcellCV false false, hgamma]
    change Asymptotics.IsBigO atTop Rg (fun n => (1/((n+2:ℕ):ℝ))^2) ∧
      Tendsto (fun n => ((n+2:ℕ):ℝ)^2 * Rg n) atTop
        (nhds (-2*(G.mu*G.truthRate)*
          (G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell true false)/G.gamma +
            G.law.cv (fun ω => (G.V ω : ℝ)) (G.cell false false)/(1-G.gamma))))
    refine ⟨?_, ?_⟩
    · have hBig : Asymptotics.IsBigO atTop Rs (fun n => (1/((n+2:ℕ):ℝ))^2) := hAsym.1
      rw [hSeq]
      exact hBig
    · have hLim := hAsym.2
      rw [hSeqMul, hTarget]
      exact hLim
  · intro n hn
    rcases hTreat n hn with ⟨hmean, hpoint⟩
    have hArmMean : (G.law.iid n).mean (fun s => (G.armCount s true : ℝ)) =
        (S.law.iid n).mean (fun s => (S.armCount s true : ℝ)) := by
      change (G.law.iid n).mean (fun s => (oArmCount (ObsSeq G s) true : ℝ)) =
        (S.law.iid n).mean (fun s => (oArmCount (FinObsSeq S s) true : ℝ))
      exact sampleMean_eq G S hrep n (fun q => (oArmCount q true : ℝ))
    refine ⟨?_, ?_⟩
    · calc
        _ = (S.law.iid n).mean (fun s => (S.armCount s true : ℝ)) := hArmMean
        _ = (n : ℝ)*G.gamma := by rw [hgamma]; exact hmean
    · intro s
      let t : Fin n → Fin N := fun i => rep (G.Z (s i)) (G.Y (s i))
      have hZ (i : Fin n) : S.Z (t i) = G.Z (s i) := repZ (G.Z (s i)) (G.Y (s i))
      have hCount := armCount_labels_eq G S s t hZ true
      calc
        (G.armCount s true : ℝ) = (S.armCount t true : ℝ) := by exact_mod_cast hCount
        _ = (n : ℝ)*S.gammaHat t := hpoint t
        _ = (n : ℝ)*G.gammaHat s := by
          unfold WholeMeasureStudy.gammaHat Study.gammaHat
          rw [← hCount]

end
end SAP.P019a.WH.W1
