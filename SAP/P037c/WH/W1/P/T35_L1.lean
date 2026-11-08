import SAP.P037c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.WH.W1.P.T35_L1

open SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev LocalStudent := Fin 5 × Bool

def localFiber (z : Finset Whole35Student) (h : Fin 4) : Finset LocalStudent :=
  (z.filter (fun i => i.1 = h)).image Prod.snd

theorem mem_localFiber (z : Finset Whole35Student) (h : Fin 4) (x : LocalStudent) :
    x ∈ localFiber z h ↔ (h, x) ∈ z := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, hix⟩
    rcases i with ⟨h', x'⟩
    simp only [Finset.mem_filter] at hi
    have hx' : x' = x := hix
    subst x'
    rcases hi with ⟨hi, hh⟩
    simpa [hh] using hi
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨(h, x), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hx, rfl⟩

theorem localFiber_card_of_support (z : Finset Whole35Student)
    (hz : z ∈ whole35Support) (h : Fin 4) : (localFiber z h).card = 5 := by
  have hinj : Set.InjOn Prod.snd (↑(z.filter (fun i => i.1 = h)) : Set Whole35Student) := by
    intro i hi j hj heq
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    have hi' : (i₁, i₂) ∈ z.filter (fun i => i.1 = h) := hi
    have hj' : (j₁, j₂) ∈ z.filter (fun i => i.1 = h) := hj
    have hif := (Finset.mem_filter.mp hi').2
    have hjf := (Finset.mem_filter.mp hj').2
    have hif' : i₁ = h := hif
    have hjf' : j₁ = h := hjf
    apply Prod.ext
    · exact hif'.trans hjf'.symm
    · exact heq
  have hcard : (localFiber z h).card = (z.filter (fun i => i.1 = h)).card :=
    Finset.card_image_iff.mpr hinj
  have hz' := (Finset.mem_filter.mp hz).2 h
  rw [hcard]
  exact hz'

def encode (z : {z : Finset Whole35Student // z ∈ whole35Support}) :
    Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport} :=
  fun h => ⟨localFiber z.1 h, by
    change localFiber z.1 h ∈ Finset.univ.powersetCard 5
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, localFiber_card_of_support z.1 z.2 h⟩⟩

def assemble (f : Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport}) :
    Finset Whole35Student :=
  Finset.univ.biUnion (fun h => (f h).1.image (fun x => (h, x)))

theorem mem_assemble (f : Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport})
    (h : Fin 4) (x : LocalStudent) :
    (h, x) ∈ assemble f ↔ x ∈ (f h).1 := by
  simp [assemble]

theorem assemble_fiber_eq (f : Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport})
    (h : Fin 4) :
    (assemble f).filter (fun i => i.1 = h) = (f h).1.image (fun x => (h, x)) := by
  ext i
  rcases i with ⟨h', x⟩
  simp only [Finset.mem_filter, mem_assemble, Finset.mem_image]
  constructor
  · rintro ⟨hx, hh⟩
    change h' = h at hh
    subst h'
    exact ⟨x, hx, rfl⟩
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    have hh : h = h' := congrArg Prod.fst hxy
    have hyy : y = x := congrArg Prod.snd hxy
    subst h'
    subst y
    exact ⟨hy, rfl⟩

theorem assemble_mem_support (f : Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport}) :
    assemble f ∈ whole35Support := by
  change assemble f ∈ Finset.univ.powerset.filter (fun z => ∀ h : Fin 4,
    (z.filter (fun i => i.1 = h)).card = 5)
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact Finset.subset_univ _
  · intro h
    rw [assemble_fiber_eq]
    have hinj : Set.InjOn (fun x : LocalStudent => (h, x))
        (↑(f h).1 : Set LocalStudent) := by
      intro x hx y hy hxy
      exact congrArg Prod.snd hxy
    rw [Finset.card_image_iff.mpr hinj]
    exact (Finset.mem_powersetCard.mp (f h).2).2

def decode (f : Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport}) :
    {z : Finset Whole35Student // z ∈ whole35Support} :=
  ⟨assemble f, assemble_mem_support f⟩

theorem assemble_localFiber (f : Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport})
    (h : Fin 4) : localFiber (assemble f) h = (f h).1 := by
  ext x
  rw [mem_localFiber, mem_assemble]

def supportEquiv :
    {z : Finset Whole35Student // z ∈ whole35Support} ≃
      (Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport}) where
  toFun := encode
  invFun := decode
  left_inv := by
    intro z
    apply Subtype.ext
    ext i
    rcases i with ⟨h, x⟩
    change (h, x) ∈ assemble (encode z) ↔ (h, x) ∈ z.1
    rw [mem_assemble]
    change x ∈ localFiber z.1 h ↔ (h, x) ∈ z.1
    exact mem_localFiber z.1 h x
  right_inv := by
    intro f
    funext h
    apply Subtype.ext
    exact assemble_localFiber f h

end SAP.P037c.WH.W1.P.T35_L1

namespace SAP.P037c.WH.W1

open SAP.P037c
open SAP.P037c.WH.W1.P.T35_L1

theorem T35_L1_proof : SAP.P037c.WH.W1.T35_L1 := by
  classical
  have hwhole : Fintype.card {z : Finset Whole35Student // z ∈ whole35Support} =
      whole35Support.card := Fintype.card_coe whole35Support
  have hlocal : Fintype.card {s : Finset LocalStudent // s ∈ pairedSupport} =
      pairedSupport.card := Fintype.card_coe pairedSupport
  calc
    whole35Support.card =
        Fintype.card {z : Finset Whole35Student // z ∈ whole35Support} := hwhole.symm
    _ = Fintype.card (Fin 4 → {s : Finset LocalStudent // s ∈ pairedSupport}) :=
      Fintype.card_congr supportEquiv
    _ = (Fintype.card {s : Finset LocalStudent // s ∈ pairedSupport}) ^ 4 := by
      rw [Fintype.card_fun, Fintype.card_fin]
    _ = 252 ^ 4 := by rw [hlocal, SAP.P037c.Bridge.paired_certificate.1]

end SAP.P037c.WH.W1
