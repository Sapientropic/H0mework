import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualBraContactData1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualBraContactDualContraction
open ActualCandidateBra ActualContactDualImaginary MixedSpectatorContactExchange MixedSpectatorPairedSourceFrame
open scoped Matrix BigOperators

private theorem starEnd_nat (n : ℕ) : (starRingEnd ℂ) (n : ℂ) = n := map_natCast (starRingEnd ℂ) n

private theorem starEnd_ofNat (n : ℕ) [n.AtLeastTwo] : (starRingEnd ℂ) (ofNat(n) : ℂ) = ofNat(n) := map_ofNat (starRingEnd ℂ) n

private theorem sqrt2_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt15_sq : (Real.sqrt 15 : ℂ)^2 = 15 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt30_sq : (Real.sqrt 30 : ℂ)^2 = 30 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

theorem actual_contact_bra_row0 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 0 b)*pairPoint dual 0 b) = contactBraRow0 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow0]

theorem actual_contact_bra_row1 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 1 b)*pairPoint dual 1 b) = contactBraRow1 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow1]

theorem actual_contact_bra_row2 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 2 b)*pairPoint dual 2 b) = contactBraRow2 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow2]

theorem actual_contact_bra_row3 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 3 b)*pairPoint dual 3 b) = contactBraRow3 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow3]

theorem actual_contact_bra_row4 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 4 b)*pairPoint dual 4 b) = contactBraRow4 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow4]

theorem actual_contact_bra_row5 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 5 b)*pairPoint dual 5 b) = contactBraRow5 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow5]

theorem actual_contact_bra_row6 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 6 b)*pairPoint dual 6 b) = contactBraRow6 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow6]

theorem actual_contact_bra_row7 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 7 b)*pairPoint dual 7 b) = contactBraRow7 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow7]

theorem actual_contact_bra_row8 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 8 b)*pairPoint dual 8 b) = contactBraRow8 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow8]

private theorem original_row9 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 9 b = sourceContactRow9 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row9 (b : Fin 97) :
    sourceContactRow9 contactValue b = pointContactRow9 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row9 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 9 b)*pairPoint dual 9 b) = contactBraRow9 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row9,hp,point_row9]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow9 b)*pairRow9 b) = 0
    norm_num [pointContactRow9,pairRow9,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient1,pairCoefficient2,pairCoefficient3]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow9 b)*star (pairRow9 b)) = 0
    norm_num [pointContactRow9,pairRow9,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient1,pairCoefficient2,pairCoefficient3]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row10 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 10 b = sourceContactRow10 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row10 (b : Fin 97) :
    sourceContactRow10 contactValue b = pointContactRow10 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row10 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 10 b)*pairPoint dual 10 b) = contactBraRow10 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row10,hp,point_row10]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow10 b)*pairRow10 b) = 0
    norm_num [pointContactRow10,pairRow10,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient3,pairCoefficient4,pairCoefficient5]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow10 b)*star (pairRow10 b)) = 0
    norm_num [pointContactRow10,pairRow10,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient3,pairCoefficient4,pairCoefficient5]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row11 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 11 b = sourceContactRow11 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row11 (b : Fin 97) :
    sourceContactRow11 contactValue b = pointContactRow11 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row11 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 11 b)*pairPoint dual 11 b) = contactBraRow11 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row11,hp,point_row11]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow11 b)*pairRow11 b) = ((-13/500) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow11,pairRow11,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient1]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow11 b)*star (pairRow11 b)) = ((-7/500) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow11,pairRow11,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient1]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row12 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 12 b = sourceContactRow12 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row12 (b : Fin 97) :
    sourceContactRow12 contactValue b = pointContactRow12 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row12 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 12 b)*pairPoint dual 12 b) = contactBraRow12 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row12,hp,point_row12]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow12 b)*pairRow12 b) = ((-13/500) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow12,pairRow12,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient4]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow12 b)*star (pairRow12 b)) = ((-7/500) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow12,pairRow12,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient4]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row13 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 13 b = sourceContactRow13 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row13 (b : Fin 97) :
    sourceContactRow13 contactValue b = pointContactRow13 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row13 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 13 b)*pairPoint dual 13 b) = contactBraRow13 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row13,hp,point_row13]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow13 b)*pairRow13 b) = ((-1/50) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow13,pairRow13,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient6]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow13 b)*star (pairRow13 b)) = ((-1/50) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow13,pairRow13,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient6]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row14 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 14 b = sourceContactRow14 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row14 (b : Fin 97) :
    sourceContactRow14 contactValue b = pointContactRow14 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row14 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 14 b)*pairPoint dual 14 b) = contactBraRow14 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row14,hp,point_row14]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow14 b)*pairRow14 b) = ((-1/50) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow14,pairRow14,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient6]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow14 b)*star (pairRow14 b)) = ((-1/50) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow14,pairRow14,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient6]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row15 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 15 b = sourceContactRow15 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row15 (b : Fin 97) :
    sourceContactRow15 contactValue b = pointContactRow15 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row15 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 15 b)*pairPoint dual 15 b) = contactBraRow15 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row15,hp,point_row15]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow15 b)*pairRow15 b) = ((-1/50) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow15,pairRow15,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient7,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient11,pairCoefficient12,pairCoefficient13,pairCoefficient14,pairCoefficient15,pairCoefficient16,pairCoefficient17,pairCoefficient18,pairCoefficient19]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow15 b)*star (pairRow15 b)) = ((-1/50) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow15,pairRow15,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient7,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient11,pairCoefficient12,pairCoefficient13,pairCoefficient14,pairCoefficient15,pairCoefficient16,pairCoefficient17,pairCoefficient18,pairCoefficient19]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row16 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 16 b = sourceContactRow16 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row16 (b : Fin 97) :
    sourceContactRow16 contactValue b = pointContactRow16 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row16 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 16 b)*pairPoint dual 16 b) = contactBraRow16 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row16,hp,point_row16]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow16 b)*pairRow16 b) = 0
    norm_num [pointContactRow16,pairRow16,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient6,pairCoefficient7,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient11,pairCoefficient12,pairCoefficient16,pairCoefficient20,pairCoefficient21]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow16 b)*star (pairRow16 b)) = 0
    norm_num [pointContactRow16,pairRow16,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient0,pairCoefficient6,pairCoefficient7,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient11,pairCoefficient12,pairCoefficient16,pairCoefficient20,pairCoefficient21]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

theorem actual_contact_bra_row17 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 17 b)*pairPoint dual 17 b) = contactBraRow17 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow17]

theorem actual_contact_bra_row18 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 18 b)*pairPoint dual 18 b) = contactBraRow18 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow18]

private theorem original_row19 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 19 b = sourceContactRow19 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row19 (b : Fin 97) :
    sourceContactRow19 contactValue b = pointContactRow19 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row19 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 19 b)*pairPoint dual 19 b) = contactBraRow19 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row19,hp,point_row19]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow19 b)*pairRow19 b) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow19,pairRow19,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient22,pairCoefficient23,pairCoefficient24,pairCoefficient25]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow19 b)*star (pairRow19 b)) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow19,pairRow19,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient22,pairCoefficient23,pairCoefficient24,pairCoefficient25]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row20 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 20 b = sourceContactRow20 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row20 (b : Fin 97) :
    sourceContactRow20 contactValue b = pointContactRow20 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row20 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 20 b)*pairPoint dual 20 b) = contactBraRow20 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row20,hp,point_row20]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow20 b)*pairRow20 b) = ((9/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow20,pairRow20,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient7,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient13,pairCoefficient14,pairCoefficient17,pairCoefficient18,pairCoefficient19,pairCoefficient20,pairCoefficient22,pairCoefficient26,pairCoefficient27,pairCoefficient28,pairCoefficient29,pairCoefficient30]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow20 b)*star (pairRow20 b)) = ((9/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow20,pairRow20,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient7,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient13,pairCoefficient14,pairCoefficient17,pairCoefficient18,pairCoefficient19,pairCoefficient20,pairCoefficient22,pairCoefficient26,pairCoefficient27,pairCoefficient28,pairCoefficient29,pairCoefficient30]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row21 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 21 b = sourceContactRow21 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row21 (b : Fin 97) :
    sourceContactRow21 contactValue b = pointContactRow21 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row21 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 21 b)*pairPoint dual 21 b) = contactBraRow21 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row21,hp,point_row21]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow21 b)*pairRow21 b) = 0
    norm_num [pointContactRow21,pairRow21,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow21 b)*star (pairRow21 b)) = 0
    norm_num [pointContactRow21,pairRow21,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row22 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 22 b = sourceContactRow22 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row22 (b : Fin 97) :
    sourceContactRow22 contactValue b = pointContactRow22 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row22 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 22 b)*pairPoint dual 22 b) = contactBraRow22 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row22,hp,point_row22]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow22 b)*pairRow22 b) = 0
    norm_num [pointContactRow22,pairRow22,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow22 b)*star (pairRow22 b)) = 0
    norm_num [pointContactRow22,pairRow22,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

theorem actual_contact_bra_row23 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 23 b)*pairPoint dual 23 b) = contactBraRow23 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow23]

theorem actual_contact_bra_row24 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 24 b)*pairPoint dual 24 b) = contactBraRow24 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow24]

end LowEnergy.ActualBraContactDualContraction
