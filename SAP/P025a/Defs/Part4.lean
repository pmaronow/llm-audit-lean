import SAP.P025a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

def T5Statement : Prop :=
  ((48 : ℝ)/(48+16) = 3/4 ∧ (864 : ℝ)/(864+288) = 3/4 ∧
    (48 : ℝ)/(48+12) = 4/5 ∧ (1156 : ℝ)/(1156+289) = 4/5 ∧
    ((44:ℕ)+4 = 48) ∧ ((291:ℕ)+288 = 579) ∧
    (1/4 : ℝ) ≤ 11/12 ∧ (11/12 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 97/288 ∧ (97/288 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 1/3 ∧ (1/4 : ℝ) ≤ 291/1156 ∧ (291/1156 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 288/289 ∧ (288/289 : ℝ) ≤ 1 ∧
    reweightedPrevalence (44/48) (11/12) (1/4) = 3/4 ∧
    reweightedPrevalence (291/579) (97/288) 1 = 3/4 ∧
    reweightedPrevalence (44/48) (11/12) (1/3) = 4/5 ∧
    reweightedPrevalence (291/579) (291/1156) (288/289) = 4/5 ∧
    ((11/12 : ℝ)/(1/4) = 11/3) ∧ (3 : ℝ) < 11/3 ∧
    ((1:ℝ)/(97/288) = 288/97) ∧ (288/97 : ℝ) < 3 ∧
    ((11/12 : ℝ)/(1/3) = 11/4) ∧ (11/4 : ℝ) < 3 ∧
    ((288/289 : ℝ)/(291/1156) = 384/97) ∧ (3 : ℝ) < 384/97 ∧
    (11/3 : ℝ)*(288/97) = 1056/97 ∧
    (11/4 : ℝ)*(384/97) = 1056/97 ∧
    binaryLower (44/48) 4 ≤ 3/4 ∧ (3/4 : ℝ) < 4/5 ∧
    (4/5 : ℝ) ≤ binaryUpper (291/579) 4) ∧
  ((1/4 : ℝ) ≤ 249/917 ∧ (249/917 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 503/1491 ∧ (503/1491 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 332/917 ∧ (332/917 : ℝ) ≤ 1 ∧
    (1/4 : ℝ) ≤ 503/1988 ∧ (503/1988 : ℝ) ≤ 1 ∧
    ((3/4 : ℝ)*1/((3/4)*1+(1-3/4)*(249/917)) = 917/1000) ∧
    ((3/4 : ℝ)*(503/1491)/((3/4)*(503/1491)+(1-3/4)*1) = 503/1000) ∧
    (1491/503 : ℝ) < 3 ∧
    ((4/5 : ℝ)*1/((4/5)*1+(1-4/5)*(332/917)) = 917/1000) ∧
    ((4/5 : ℝ)*(503/1988)/((4/5)*(503/1988)+(1-4/5)*1) = 503/1000) ∧
    (917/332 : ℝ) < 3) ∧
  ((quotaDraws 48 44).Nonempty ∧ (quotaDraws 16 4).Nonempty ∧
    (quotaDraws 864 291).Nonempty ∧ (quotaDraws 288 288).Nonempty ∧
    (quotaDraws 12 4).Nonempty ∧ (quotaDraws 1156 291).Nonempty ∧
    (quotaDraws 289 288).Nonempty ∧
    (∀ i : Fin 48, quotaMarginal 48 44 i = 11/12) ∧
    (∀ i : Fin 16, quotaMarginal 16 4 i = 1/4) ∧
    (∀ i : Fin 864, quotaMarginal 864 291 i = 97/288) ∧
    (∀ i : Fin 288, quotaMarginal 288 288 i = 1) ∧
    (∀ i : Fin 12, quotaMarginal 12 4 i = 1/3) ∧
    (∀ i : Fin 1156, quotaMarginal 1156 291 i = 291/1156) ∧
    (∀ i : Fin 289, quotaMarginal 289 288 i = 288/289)) ∧
  (∀ N s : ℕ, (N,s) ∈ applicationStrata →
    (quotaDraws N s).Nonempty ∧
    (∑ t ∈ quotaDraws N s, (1 : ℝ)/((quotaDraws N s).card : ℝ)) = 1 ∧
    (∀ t ∈ quotaDraws N s, t.card = s)) ∧
  ((917/10 : ℝ)-1/20 ≤ 100*(44/48) ∧ 100*(44/48) < 917/10+1/20 ∧
   (503/10 : ℝ)-1/20 ≤ 100*(291/579) ∧ 100*(291/579) < 503/10+1/20) ∧
  (3/4 : ℝ) ∈ binaryInterval (44/48) 4 ∧ (3/4 : ℝ) ∈ binaryInterval (291/579) 4 ∧
  (4/5 : ℝ) ∈ binaryInterval (44/48) 4 ∧ (4/5 : ℝ) ∈ binaryInterval (291/579) 4

end
end SAP.P025a
