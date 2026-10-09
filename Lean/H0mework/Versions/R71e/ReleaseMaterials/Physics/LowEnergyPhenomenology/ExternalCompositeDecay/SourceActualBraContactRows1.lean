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

private theorem original_row25 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 25 b = sourceContactRow25 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row25 (b : Fin 97) :
    sourceContactRow25 contactValue b = pointContactRow25 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row25 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 25 b)*pairPoint dual 25 b) = contactBraRow25 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row25,hp,point_row25]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow25 b)*pairRow25 b) = 0
    norm_num [pointContactRow25,pairRow25,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35,pairCoefficient36]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow25 b)*star (pairRow25 b)) = 0
    norm_num [pointContactRow25,pairRow25,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35,pairCoefficient36]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row26 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 26 b = sourceContactRow26 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row26 (b : Fin 97) :
    sourceContactRow26 contactValue b = pointContactRow26 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row26 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 26 b)*pairPoint dual 26 b) = contactBraRow26 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row26,hp,point_row26]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow26 b)*pairRow26 b) = 0
    norm_num [pointContactRow26,pairRow26,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow26 b)*star (pairRow26 b)) = 0
    norm_num [pointContactRow26,pairRow26,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row27 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 27 b = sourceContactRow27 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row27 (b : Fin 97) :
    sourceContactRow27 contactValue b = pointContactRow27 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row27 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 27 b)*pairPoint dual 27 b) = contactBraRow27 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row27,hp,point_row27]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow27 b)*pairRow27 b) = 0
    norm_num [pointContactRow27,pairRow27,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient32,pairCoefficient37,pairCoefficient38,pairCoefficient39,pairCoefficient40,pairCoefficient41,pairCoefficient42,pairCoefficient43,pairCoefficient44,pairCoefficient45,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow27 b)*star (pairRow27 b)) = 0
    norm_num [pointContactRow27,pairRow27,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient32,pairCoefficient37,pairCoefficient38,pairCoefficient39,pairCoefficient40,pairCoefficient41,pairCoefficient42,pairCoefficient43,pairCoefficient44,pairCoefficient45,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row28 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 28 b = sourceContactRow28 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row28 (b : Fin 97) :
    sourceContactRow28 contactValue b = pointContactRow28 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row28 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 28 b)*pairPoint dual 28 b) = contactBraRow28 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row28,hp,point_row28]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow28 b)*pairRow28 b) = 0
    norm_num [pointContactRow28,pairRow28,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient33,pairCoefficient35,pairCoefficient37,pairCoefficient39,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient51,pairCoefficient53,pairCoefficient54,pairCoefficient55,pairCoefficient56,pairCoefficient57,pairCoefficient58,pairCoefficient59,pairCoefficient60,pairCoefficient61,pairCoefficient62,pairCoefficient63,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient67]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow28 b)*star (pairRow28 b)) = 0
    norm_num [pointContactRow28,pairRow28,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient33,pairCoefficient35,pairCoefficient37,pairCoefficient39,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient51,pairCoefficient53,pairCoefficient54,pairCoefficient55,pairCoefficient56,pairCoefficient57,pairCoefficient58,pairCoefficient59,pairCoefficient60,pairCoefficient61,pairCoefficient62,pairCoefficient63,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient67]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

theorem actual_contact_bra_row29 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 29 b)*pairPoint dual 29 b) = contactBraRow29 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow29]

theorem actual_contact_bra_row30 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 30 b)*pairPoint dual 30 b) = contactBraRow30 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow30]

private theorem original_row31 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 31 b = sourceContactRow31 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row31 (b : Fin 97) :
    sourceContactRow31 contactValue b = pointContactRow31 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row31 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 31 b)*pairPoint dual 31 b) = contactBraRow31 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row31,hp,point_row31]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow31 b)*pairRow31 b) = 0
    norm_num [pointContactRow31,pairRow31,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient13,pairCoefficient18,pairCoefficient19,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient68,pairCoefficient69,pairCoefficient70,pairCoefficient71,pairCoefficient72,pairCoefficient73,pairCoefficient74,pairCoefficient75,pairCoefficient76]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow31 b)*star (pairRow31 b)) = 0
    norm_num [pointContactRow31,pairRow31,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient13,pairCoefficient18,pairCoefficient19,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient68,pairCoefficient69,pairCoefficient70,pairCoefficient71,pairCoefficient72,pairCoefficient73,pairCoefficient74,pairCoefficient75,pairCoefficient76]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row32 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 32 b = sourceContactRow32 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row32 (b : Fin 97) :
    sourceContactRow32 contactValue b = pointContactRow32 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row32 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 32 b)*pairPoint dual 32 b) = contactBraRow32 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row32,hp,point_row32]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow32 b)*pairRow32 b) = 0
    norm_num [pointContactRow32,pairRow32,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient10,pairCoefficient13,pairCoefficient19,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient68,pairCoefficient70,pairCoefficient72,pairCoefficient76,pairCoefficient77,pairCoefficient78,pairCoefficient79,pairCoefficient80]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow32 b)*star (pairRow32 b)) = 0
    norm_num [pointContactRow32,pairRow32,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient10,pairCoefficient13,pairCoefficient19,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient68,pairCoefficient70,pairCoefficient72,pairCoefficient76,pairCoefficient77,pairCoefficient78,pairCoefficient79,pairCoefficient80]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row33 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 33 b = sourceContactRow33 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row33 (b : Fin 97) :
    sourceContactRow33 contactValue b = pointContactRow33 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row33 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 33 b)*pairPoint dual 33 b) = contactBraRow33 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row33,hp,point_row33]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow33 b)*pairRow33 b) = 0
    norm_num [pointContactRow33,pairRow33,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow33 b)*star (pairRow33 b)) = 0
    norm_num [pointContactRow33,pairRow33,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row34 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 34 b = sourceContactRow34 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row34 (b : Fin 97) :
    sourceContactRow34 contactValue b = pointContactRow34 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row34 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 34 b)*pairPoint dual 34 b) = contactBraRow34 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row34,hp,point_row34]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow34 b)*pairRow34 b) = 0
    norm_num [pointContactRow34,pairRow34,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow34 b)*star (pairRow34 b)) = 0
    norm_num [pointContactRow34,pairRow34,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient31,pairCoefficient32]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

theorem actual_contact_bra_row35 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 35 b)*pairPoint dual 35 b) = contactBraRow35 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow35]

theorem actual_contact_bra_row36 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 36 b)*pairPoint dual 36 b) = contactBraRow36 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow36]

private theorem original_row37 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 37 b = sourceContactRow37 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row37 (b : Fin 97) :
    sourceContactRow37 contactValue b = pointContactRow37 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row37 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 37 b)*pairPoint dual 37 b) = contactBraRow37 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row37,hp,point_row37]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow37 b)*pairRow37 b) = 0
    norm_num [pointContactRow37,pairRow37,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow37 b)*star (pairRow37 b)) = 0
    norm_num [pointContactRow37,pairRow37,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row38 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 38 b = sourceContactRow38 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row38 (b : Fin 97) :
    sourceContactRow38 contactValue b = pointContactRow38 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row38 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 38 b)*pairPoint dual 38 b) = contactBraRow38 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row38,hp,point_row38]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow38 b)*pairRow38 b) = 0
    norm_num [pointContactRow38,pairRow38,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35,pairCoefficient36]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow38 b)*star (pairRow38 b)) = 0
    norm_num [pointContactRow38,pairRow38,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient35,pairCoefficient36]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row39 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 39 b = sourceContactRow39 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row39 (b : Fin 97) :
    sourceContactRow39 contactValue b = pointContactRow39 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row39 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 39 b)*pairPoint dual 39 b) = contactBraRow39 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row39,hp,point_row39]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow39 b)*pairRow39 b) = 0
    norm_num [pointContactRow39,pairRow39,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient32,pairCoefficient37,pairCoefficient40,pairCoefficient41,pairCoefficient44,pairCoefficient46,pairCoefficient47,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient59,pairCoefficient81,pairCoefficient82,pairCoefficient83,pairCoefficient84]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow39 b)*star (pairRow39 b)) = 0
    norm_num [pointContactRow39,pairRow39,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient32,pairCoefficient37,pairCoefficient40,pairCoefficient41,pairCoefficient44,pairCoefficient46,pairCoefficient47,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient59,pairCoefficient81,pairCoefficient82,pairCoefficient83,pairCoefficient84]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row40 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 40 b = sourceContactRow40 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row40 (b : Fin 97) :
    sourceContactRow40 contactValue b = pointContactRow40 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row40 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 40 b)*pairPoint dual 40 b) = contactBraRow40 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row40,hp,point_row40]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow40 b)*pairRow40 b) = 0
    norm_num [pointContactRow40,pairRow40,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient33,pairCoefficient35,pairCoefficient37,pairCoefficient38,pairCoefficient43,pairCoefficient46,pairCoefficient48,pairCoefficient49,pairCoefficient51,pairCoefficient56,pairCoefficient57,pairCoefficient58,pairCoefficient60,pairCoefficient63,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient67,pairCoefficient68,pairCoefficient77,pairCoefficient81,pairCoefficient82,pairCoefficient85,pairCoefficient86]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow40 b)*star (pairRow40 b)) = 0
    norm_num [pointContactRow40,pairRow40,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient33,pairCoefficient35,pairCoefficient37,pairCoefficient38,pairCoefficient43,pairCoefficient46,pairCoefficient48,pairCoefficient49,pairCoefficient51,pairCoefficient56,pairCoefficient57,pairCoefficient58,pairCoefficient60,pairCoefficient63,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient67,pairCoefficient68,pairCoefficient77,pairCoefficient81,pairCoefficient82,pairCoefficient85,pairCoefficient86]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

theorem actual_contact_bra_row41 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 41 b)*pairPoint dual 41 b) = contactBraRow41 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow41]

theorem actual_contact_bra_row42 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 42 b)*pairPoint dual 42 b) = contactBraRow42 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow42]

private theorem original_row43 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 43 b = sourceContactRow43 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row43 (b : Fin 97) :
    sourceContactRow43 contactValue b = pointContactRow43 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row43 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 43 b)*pairPoint dual 43 b) = contactBraRow43 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row43,hp,point_row43]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow43 b)*pairRow43 b) = 0
    norm_num [pointContactRow43,pairRow43,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient14,pairCoefficient18,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient69,pairCoefficient71,pairCoefficient72,pairCoefficient74,pairCoefficient76,pairCoefficient87,pairCoefficient88,pairCoefficient89]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow43 b)*star (pairRow43 b)) = 0
    norm_num [pointContactRow43,pairRow43,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient14,pairCoefficient18,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient69,pairCoefficient71,pairCoefficient72,pairCoefficient74,pairCoefficient76,pairCoefficient87,pairCoefficient88,pairCoefficient89]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row44 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 44 b = sourceContactRow44 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row44 (b : Fin 97) :
    sourceContactRow44 contactValue b = pointContactRow44 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row44 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 44 b)*pairPoint dual 44 b) = contactBraRow44 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row44,hp,point_row44]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow44 b)*pairRow44 b) = 0
    norm_num [pointContactRow44,pairRow44,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient9,pairCoefficient14,pairCoefficient18,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient55,pairCoefficient68,pairCoefficient72,pairCoefficient76,pairCoefficient78,pairCoefficient87,pairCoefficient90,pairCoefficient91]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow44 b)*star (pairRow44 b)) = 0
    norm_num [pointContactRow44,pairRow44,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient9,pairCoefficient14,pairCoefficient18,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient55,pairCoefficient68,pairCoefficient72,pairCoefficient76,pairCoefficient78,pairCoefficient87,pairCoefficient90,pairCoefficient91]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row45 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 45 b = sourceContactRow45 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row45 (b : Fin 97) :
    sourceContactRow45 contactValue b = pointContactRow45 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row45 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 45 b)*pairPoint dual 45 b) = contactBraRow45 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row45,hp,point_row45]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow45 b)*pairRow45 b) = 0
    norm_num [pointContactRow45,pairRow45,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient4,pairCoefficient5,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow45 b)*star (pairRow45 b)) = 0
    norm_num [pointContactRow45,pairRow45,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient4,pairCoefficient5,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row46 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 46 b = sourceContactRow46 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row46 (b : Fin 97) :
    sourceContactRow46 contactValue b = pointContactRow46 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row46 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 46 b)*pairPoint dual 46 b) = contactBraRow46 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row46,hp,point_row46]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow46 b)*pairRow46 b) = 0
    norm_num [pointContactRow46,pairRow46,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient2,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow46 b)*star (pairRow46 b)) = 0
    norm_num [pointContactRow46,pairRow46,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient2,pairCoefficient33,pairCoefficient34]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row47 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 47 b = sourceContactRow47 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row47 (b : Fin 97) :
    sourceContactRow47 contactValue b = pointContactRow47 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row47 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 47 b)*pairPoint dual 47 b) = contactBraRow47 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row47,hp,point_row47]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow47 b)*pairRow47 b) = ((39/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow47,pairRow47,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient4,pairCoefficient33]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow47 b)*star (pairRow47 b)) = ((-21/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow47,pairRow47,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient4,pairCoefficient33]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row48 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 48 b = sourceContactRow48 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row48 (b : Fin 97) :
    sourceContactRow48 contactValue b = pointContactRow48 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row48 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 48 b)*pairPoint dual 48 b) = contactBraRow48 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row48,hp,point_row48]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow48 b)*pairRow48 b) = ((39/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow48,pairRow48,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient33]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow48 b)*star (pairRow48 b)) = ((-21/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow48,pairRow48,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient33]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row49 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 49 b = sourceContactRow49 (contactPolynomial q) b := by
  fin_cases b <;> rfl

private theorem point_row49 (b : Fin 97) :
    sourceContactRow49 contactValue b = pointContactRow49 b := by
  fin_cases b <;> rfl

theorem actual_contact_bra_row49 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 49 b)*pairPoint dual 49 b) = contactBraRow49 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row49,hp,point_row49]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow49 b)*pairRow49 b) = ((-9/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow49,pairRow49,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient6,pairCoefficient31]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow49 b)*star (pairRow49 b)) = ((-9/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow49,pairRow49,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient6,pairCoefficient31]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

end LowEnergy.ActualBraContactDualContraction
