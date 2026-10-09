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

private theorem original_row50 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 50 b = sourceContactRow50 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row50 (b : Fin 97) :
    sourceContactRow50 contactValue b = pointContactRow50 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row50 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 50 b)*pairPoint dual 50 b) = contactBraRow50 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row50,hp,point_row50]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow50 b)*pairRow50 b) = ((-9/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow50,pairRow50,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient6,pairCoefficient31]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow50 b)*star (pairRow50 b)) = ((-9/5000) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow50,pairRow50,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient6,pairCoefficient31]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row51 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 51 b = sourceContactRow51 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row51 (b : Fin 97) :
    sourceContactRow51 contactValue b = pointContactRow51 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row51 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 51 b)*pairPoint dual 51 b) = contactBraRow51 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row51,hp,point_row51]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow51 b)*pairRow51 b) = 0
    norm_num [pointContactRow51,pairRow51,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient19,pairCoefficient26,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient73,pairCoefficient76,pairCoefficient88,pairCoefficient92,pairCoefficient93,pairCoefficient94,pairCoefficient95]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow51 b)*star (pairRow51 b)) = 0
    norm_num [pointContactRow51,pairRow51,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient19,pairCoefficient26,pairCoefficient33,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient54,pairCoefficient73,pairCoefficient76,pairCoefficient88,pairCoefficient92,pairCoefficient93,pairCoefficient94,pairCoefficient95]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row52 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 52 b = sourceContactRow52 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row52 (b : Fin 97) :
    sourceContactRow52 contactValue b = pointContactRow52 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row52 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 52 b)*pairPoint dual 52 b) = contactBraRow52 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row52,hp,point_row52]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow52 b)*pairRow52 b) = 0
    norm_num [pointContactRow52,pairRow52,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient6,pairCoefficient9,pairCoefficient10,pairCoefficient31,pairCoefficient37,pairCoefficient76,pairCoefficient95,pairCoefficient96,pairCoefficient97,pairCoefficient98,pairCoefficient99]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow52 b)*star (pairRow52 b)) = 0
    norm_num [pointContactRow52,pairRow52,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient6,pairCoefficient9,pairCoefficient10,pairCoefficient31,pairCoefficient37,pairCoefficient76,pairCoefficient95,pairCoefficient96,pairCoefficient97,pairCoefficient98,pairCoefficient99]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

theorem actual_contact_bra_row53 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 53 b)*pairPoint dual 53 b) = contactBraRow53 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow53]

theorem actual_contact_bra_row54 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 54 b)*pairPoint dual 54 b) = contactBraRow54 dual := by
  cases dual <;> simp [pairPoint,primalPairPoint,contactBraRow54]

private theorem original_row55 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 55 b = sourceContactRow55 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row55 (b : Fin 97) :
    sourceContactRow55 contactValue b = pointContactRow55 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row55 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 55 b)*pairPoint dual 55 b) = contactBraRow55 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row55,hp,point_row55]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow55 b)*pairRow55 b) = 0
    norm_num [pointContactRow55,pairRow55,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient27,pairCoefficient37,pairCoefficient53,pairCoefficient76,pairCoefficient100,pairCoefficient101,pairCoefficient102]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow55 b)*star (pairRow55 b)) = 0
    norm_num [pointContactRow55,pairRow55,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient27,pairCoefficient37,pairCoefficient53,pairCoefficient76,pairCoefficient100,pairCoefficient101,pairCoefficient102]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row56 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 56 b = sourceContactRow56 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row56 (b : Fin 97) :
    sourceContactRow56 contactValue b = pointContactRow56 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row56 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 56 b)*pairPoint dual 56 b) = contactBraRow56 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row56,hp,point_row56]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow56 b)*pairRow56 b) = 0
    norm_num [pointContactRow56,pairRow56,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient19,pairCoefficient31,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient73,pairCoefficient76,pairCoefficient88,pairCoefficient97,pairCoefficient103]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow56 b)*star (pairRow56 b)) = 0
    norm_num [pointContactRow56,pairRow56,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient19,pairCoefficient31,pairCoefficient37,pairCoefficient38,pairCoefficient53,pairCoefficient73,pairCoefficient76,pairCoefficient88,pairCoefficient97,pairCoefficient103]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row57 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 57 b = sourceContactRow57 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row57 (b : Fin 97) :
    sourceContactRow57 contactValue b = pointContactRow57 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row57 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 57 b)*pairPoint dual 57 b) = contactBraRow57 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row57,hp,point_row57]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow57 b)*pairRow57 b) = 0
    norm_num [pointContactRow57,pairRow57,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient11,pairCoefficient23,pairCoefficient28,pairCoefficient57,pairCoefficient92,pairCoefficient96,pairCoefficient100,pairCoefficient104,pairCoefficient105,pairCoefficient106,pairCoefficient107,pairCoefficient108,pairCoefficient109,pairCoefficient110,pairCoefficient111,pairCoefficient112,pairCoefficient113,pairCoefficient114,pairCoefficient115,pairCoefficient116,pairCoefficient117]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow57 b)*star (pairRow57 b)) = 0
    norm_num [pointContactRow57,pairRow57,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient11,pairCoefficient23,pairCoefficient28,pairCoefficient57,pairCoefficient92,pairCoefficient96,pairCoefficient100,pairCoefficient104,pairCoefficient105,pairCoefficient106,pairCoefficient107,pairCoefficient108,pairCoefficient109,pairCoefficient110,pairCoefficient111,pairCoefficient112,pairCoefficient113,pairCoefficient114,pairCoefficient115,pairCoefficient116,pairCoefficient117]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row58 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 58 b = sourceContactRow58 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row58 (b : Fin 97) :
    sourceContactRow58 contactValue b = pointContactRow58 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row58 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 58 b)*pairPoint dual 58 b) = contactBraRow58 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row58,hp,point_row58]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow58 b)*pairRow58 b) = 0
    norm_num [pointContactRow58,pairRow58,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient39,pairCoefficient56,pairCoefficient69,pairCoefficient81,pairCoefficient87,pairCoefficient97,pairCoefficient118,pairCoefficient119,pairCoefficient120,pairCoefficient121,pairCoefficient122,pairCoefficient123,pairCoefficient124]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow58 b)*star (pairRow58 b)) = 0
    norm_num [pointContactRow58,pairRow58,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient39,pairCoefficient56,pairCoefficient69,pairCoefficient81,pairCoefficient87,pairCoefficient97,pairCoefficient118,pairCoefficient119,pairCoefficient120,pairCoefficient121,pairCoefficient122,pairCoefficient123,pairCoefficient124]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row59 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 59 b = sourceContactRow59 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row59 (b : Fin 97) :
    sourceContactRow59 contactValue b = pointContactRow59 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row59 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 59 b)*pairPoint dual 59 b) = contactBraRow59 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row59,hp,point_row59]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow59 b)*pairRow59 b) = 0
    norm_num [pointContactRow59,pairRow59,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient20,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient39,pairCoefficient56,pairCoefficient69,pairCoefficient70,pairCoefficient81,pairCoefficient97,pairCoefficient118,pairCoefficient119,pairCoefficient120,pairCoefficient121,pairCoefficient122,pairCoefficient123]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow59 b)*star (pairRow59 b)) = 0
    norm_num [pointContactRow59,pairRow59,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient20,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient39,pairCoefficient56,pairCoefficient69,pairCoefficient70,pairCoefficient81,pairCoefficient97,pairCoefficient118,pairCoefficient119,pairCoefficient120,pairCoefficient121,pairCoefficient122,pairCoefficient123]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row60 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 60 b = sourceContactRow60 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row60 (b : Fin 97) :
    sourceContactRow60 contactValue b = pointContactRow60 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row60 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 60 b)*pairPoint dual 60 b) = contactBraRow60 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row60,hp,point_row60]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow60 b)*pairRow60 b) = 0
    norm_num [pointContactRow60,pairRow60,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient5,pairCoefficient20,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient39,pairCoefficient81,pairCoefficient97,pairCoefficient105,pairCoefficient118,pairCoefficient121,pairCoefficient122,pairCoefficient123,pairCoefficient125,pairCoefficient126]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow60 b)*star (pairRow60 b)) = 0
    norm_num [pointContactRow60,pairRow60,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient5,pairCoefficient20,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient39,pairCoefficient81,pairCoefficient97,pairCoefficient105,pairCoefficient118,pairCoefficient121,pairCoefficient122,pairCoefficient123,pairCoefficient125,pairCoefficient126]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row61 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 61 b = sourceContactRow61 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row61 (b : Fin 97) :
    sourceContactRow61 contactValue b = pointContactRow61 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row61 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 61 b)*pairPoint dual 61 b) = contactBraRow61 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row61,hp,point_row61]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow61 b)*pairRow61 b) = 0
    norm_num [pointContactRow61,pairRow61,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient3,pairCoefficient5,pairCoefficient6,pairCoefficient14,pairCoefficient19,pairCoefficient40,pairCoefficient42,pairCoefficient57,pairCoefficient71,pairCoefficient82,pairCoefficient119,pairCoefficient127,pairCoefficient128,pairCoefficient129,pairCoefficient130,pairCoefficient131,pairCoefficient132,pairCoefficient133,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow61 b)*star (pairRow61 b)) = 0
    norm_num [pointContactRow61,pairRow61,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient3,pairCoefficient5,pairCoefficient6,pairCoefficient14,pairCoefficient19,pairCoefficient40,pairCoefficient42,pairCoefficient57,pairCoefficient71,pairCoefficient82,pairCoefficient119,pairCoefficient127,pairCoefficient128,pairCoefficient129,pairCoefficient130,pairCoefficient131,pairCoefficient132,pairCoefficient133,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row62 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 62 b = sourceContactRow62 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row62 (b : Fin 97) :
    sourceContactRow62 contactValue b = pointContactRow62 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row62 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 62 b)*pairPoint dual 62 b) = contactBraRow62 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row62,hp,point_row62]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow62 b)*pairRow62 b) = 0
    norm_num [pointContactRow62,pairRow62,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient12,pairCoefficient24,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient74,pairCoefficient88,pairCoefficient93,pairCoefficient98,pairCoefficient101,pairCoefficient106,pairCoefficient122,pairCoefficient129,pairCoefficient135,pairCoefficient136,pairCoefficient137,pairCoefficient138,pairCoefficient139,pairCoefficient140,pairCoefficient141,pairCoefficient142,pairCoefficient143,pairCoefficient144]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow62 b)*star (pairRow62 b)) = 0
    norm_num [pointContactRow62,pairRow62,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient12,pairCoefficient24,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient74,pairCoefficient88,pairCoefficient93,pairCoefficient98,pairCoefficient101,pairCoefficient106,pairCoefficient122,pairCoefficient129,pairCoefficient135,pairCoefficient136,pairCoefficient137,pairCoefficient138,pairCoefficient139,pairCoefficient140,pairCoefficient141,pairCoefficient142,pairCoefficient143,pairCoefficient144]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row63 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 63 b = sourceContactRow63 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row63 (b : Fin 97) :
    sourceContactRow63 contactValue b = pointContactRow63 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row63 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 63 b)*pairPoint dual 63 b) = contactBraRow63 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row63,hp,point_row63]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow63 b)*pairRow63 b) = 0
    norm_num [pointContactRow63,pairRow63,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient13,pairCoefficient32,pairCoefficient41,pairCoefficient43,pairCoefficient59,pairCoefficient82,pairCoefficient88,pairCoefficient107,pairCoefficient123,pairCoefficient134,pairCoefficient136,pairCoefficient145,pairCoefficient146,pairCoefficient147,pairCoefficient148,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow63 b)*star (pairRow63 b)) = 0
    norm_num [pointContactRow63,pairRow63,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient13,pairCoefficient32,pairCoefficient41,pairCoefficient43,pairCoefficient59,pairCoefficient82,pairCoefficient88,pairCoefficient107,pairCoefficient123,pairCoefficient134,pairCoefficient136,pairCoefficient145,pairCoefficient146,pairCoefficient147,pairCoefficient148,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row64 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 64 b = sourceContactRow64 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row64 (b : Fin 97) :
    sourceContactRow64 contactValue b = pointContactRow64 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row64 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 64 b)*pairPoint dual 64 b) = contactBraRow64 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row64,hp,point_row64]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow64 b)*pairRow64 b) = 0
    norm_num [pointContactRow64,pairRow64,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient6,pairCoefficient34,pairCoefficient41,pairCoefficient43,pairCoefficient58,pairCoefficient59,pairCoefficient71,pairCoefficient72,pairCoefficient78,pairCoefficient82,pairCoefficient88,pairCoefficient90,pairCoefficient120,pairCoefficient123,pairCoefficient150,pairCoefficient151,pairCoefficient152,pairCoefficient153,pairCoefficient154,pairCoefficient155,pairCoefficient156]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow64 b)*star (pairRow64 b)) = 0
    norm_num [pointContactRow64,pairRow64,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient6,pairCoefficient34,pairCoefficient41,pairCoefficient43,pairCoefficient58,pairCoefficient59,pairCoefficient71,pairCoefficient72,pairCoefficient78,pairCoefficient82,pairCoefficient88,pairCoefficient90,pairCoefficient120,pairCoefficient123,pairCoefficient150,pairCoefficient151,pairCoefficient152,pairCoefficient153,pairCoefficient154,pairCoefficient155,pairCoefficient156]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row65 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 65 b = sourceContactRow65 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row65 (b : Fin 97) :
    sourceContactRow65 contactValue b = pointContactRow65 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row65 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 65 b)*pairPoint dual 65 b) = contactBraRow65 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row65,hp,point_row65]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow65 b)*pairRow65 b) = 0
    norm_num [pointContactRow65,pairRow65,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient3,pairCoefficient6,pairCoefficient13,pairCoefficient18,pairCoefficient30,pairCoefficient40,pairCoefficient42,pairCoefficient57,pairCoefficient71,pairCoefficient82,pairCoefficient119,pairCoefficient127,pairCoefficient129,pairCoefficient130,pairCoefficient132,pairCoefficient133,pairCoefficient134,pairCoefficient151]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow65 b)*star (pairRow65 b)) = 0
    norm_num [pointContactRow65,pairRow65,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient2,pairCoefficient3,pairCoefficient6,pairCoefficient13,pairCoefficient18,pairCoefficient30,pairCoefficient40,pairCoefficient42,pairCoefficient57,pairCoefficient71,pairCoefficient82,pairCoefficient119,pairCoefficient127,pairCoefficient129,pairCoefficient130,pairCoefficient132,pairCoefficient133,pairCoefficient134,pairCoefficient151]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row66 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 66 b = sourceContactRow66 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row66 (b : Fin 97) :
    sourceContactRow66 contactValue b = pointContactRow66 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row66 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 66 b)*pairPoint dual 66 b) = contactBraRow66 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row66,hp,point_row66]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow66 b)*pairRow66 b) = 0
    norm_num [pointContactRow66,pairRow66,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient14,pairCoefficient32,pairCoefficient40,pairCoefficient41,pairCoefficient42,pairCoefficient43,pairCoefficient59,pairCoefficient73,pairCoefficient108,pairCoefficient121,pairCoefficient137,pairCoefficient145,pairCoefficient146,pairCoefficient149,pairCoefficient157,pairCoefficient158]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow66 b)*star (pairRow66 b)) = 0
    norm_num [pointContactRow66,pairRow66,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient14,pairCoefficient32,pairCoefficient40,pairCoefficient41,pairCoefficient42,pairCoefficient43,pairCoefficient59,pairCoefficient73,pairCoefficient108,pairCoefficient121,pairCoefficient137,pairCoefficient145,pairCoefficient146,pairCoefficient149,pairCoefficient157,pairCoefficient158]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row67 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 67 b = sourceContactRow67 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row67 (b : Fin 97) :
    sourceContactRow67 contactValue b = pointContactRow67 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row67 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 67 b)*pairPoint dual 67 b) = contactBraRow67 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row67,hp,point_row67]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow67 b)*pairRow67 b) = 0
    norm_num [pointContactRow67,pairRow67,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient12,pairCoefficient24,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient74,pairCoefficient88,pairCoefficient93,pairCoefficient98,pairCoefficient101,pairCoefficient106,pairCoefficient122,pairCoefficient129,pairCoefficient135,pairCoefficient136,pairCoefficient137,pairCoefficient138,pairCoefficient139,pairCoefficient140,pairCoefficient141,pairCoefficient142,pairCoefficient143,pairCoefficient144]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow67 b)*star (pairRow67 b)) = 0
    norm_num [pointContactRow67,pairRow67,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient12,pairCoefficient24,pairCoefficient29,pairCoefficient32,pairCoefficient34,pairCoefficient74,pairCoefficient88,pairCoefficient93,pairCoefficient98,pairCoefficient101,pairCoefficient106,pairCoefficient122,pairCoefficient129,pairCoefficient135,pairCoefficient136,pairCoefficient137,pairCoefficient138,pairCoefficient139,pairCoefficient140,pairCoefficient141,pairCoefficient142,pairCoefficient143,pairCoefficient144]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row68 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 68 b = sourceContactRow68 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row68 (b : Fin 97) :
    sourceContactRow68 contactValue b = pointContactRow68 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row68 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 68 b)*pairPoint dual 68 b) = contactBraRow68 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row68,hp,point_row68]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow68 b)*pairRow68 b) = 0
    norm_num [pointContactRow68,pairRow68,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient5,pairCoefficient6,pairCoefficient34,pairCoefficient41,pairCoefficient42,pairCoefficient43,pairCoefficient57,pairCoefficient58,pairCoefficient59,pairCoefficient71,pairCoefficient72,pairCoefficient73,pairCoefficient78,pairCoefficient79,pairCoefficient120,pairCoefficient121,pairCoefficient128,pairCoefficient150,pairCoefficient152,pairCoefficient155,pairCoefficient156,pairCoefficient159]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow68 b)*star (pairRow68 b)) = 0
    norm_num [pointContactRow68,pairRow68,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient5,pairCoefficient6,pairCoefficient34,pairCoefficient41,pairCoefficient42,pairCoefficient43,pairCoefficient57,pairCoefficient58,pairCoefficient59,pairCoefficient71,pairCoefficient72,pairCoefficient73,pairCoefficient78,pairCoefficient79,pairCoefficient120,pairCoefficient121,pairCoefficient128,pairCoefficient150,pairCoefficient152,pairCoefficient155,pairCoefficient156,pairCoefficient159]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row69 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 69 b = sourceContactRow69 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row69 (b : Fin 97) :
    sourceContactRow69 contactValue b = pointContactRow69 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row69 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 69 b)*pairPoint dual 69 b) = contactBraRow69 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row69,hp,point_row69]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow69 b)*pairRow69 b) = 0
    norm_num [pointContactRow69,pairRow69,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient15,pairCoefficient16,pairCoefficient21,pairCoefficient25,pairCoefficient30,pairCoefficient42,pairCoefficient94,pairCoefficient99,pairCoefficient103,pairCoefficient109,pairCoefficient125,pairCoefficient129,pairCoefficient134,pairCoefficient147,pairCoefficient157,pairCoefficient160,pairCoefficient161,pairCoefficient162,pairCoefficient163,pairCoefficient164,pairCoefficient165]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow69 b)*star (pairRow69 b)) = 0
    norm_num [pointContactRow69,pairRow69,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient15,pairCoefficient16,pairCoefficient21,pairCoefficient25,pairCoefficient30,pairCoefficient42,pairCoefficient94,pairCoefficient99,pairCoefficient103,pairCoefficient109,pairCoefficient125,pairCoefficient129,pairCoefficient134,pairCoefficient147,pairCoefficient157,pairCoefficient160,pairCoefficient161,pairCoefficient162,pairCoefficient163,pairCoefficient164,pairCoefficient165]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row70 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 70 b = sourceContactRow70 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row70 (b : Fin 97) :
    sourceContactRow70 contactValue b = pointContactRow70 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row70 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 70 b)*pairPoint dual 70 b) = contactBraRow70 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row70,hp,point_row70]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow70 b)*pairRow70 b) = 0
    norm_num [pointContactRow70,pairRow70,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient18,pairCoefficient42,pairCoefficient43,pairCoefficient44,pairCoefficient59,pairCoefficient60,pairCoefficient72,pairCoefficient74,pairCoefficient83,pairCoefficient85,pairCoefficient89,pairCoefficient91,pairCoefficient121,pairCoefficient122,pairCoefficient126,pairCoefficient129,pairCoefficient140,pairCoefficient141,pairCoefficient143,pairCoefficient152,pairCoefficient159,pairCoefficient166,pairCoefficient167,pairCoefficient168,pairCoefficient169,pairCoefficient170,pairCoefficient171]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow70 b)*star (pairRow70 b)) = 0
    norm_num [pointContactRow70,pairRow70,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient18,pairCoefficient42,pairCoefficient43,pairCoefficient44,pairCoefficient59,pairCoefficient60,pairCoefficient72,pairCoefficient74,pairCoefficient83,pairCoefficient85,pairCoefficient89,pairCoefficient91,pairCoefficient121,pairCoefficient122,pairCoefficient126,pairCoefficient129,pairCoefficient140,pairCoefficient141,pairCoefficient143,pairCoefficient152,pairCoefficient159,pairCoefficient166,pairCoefficient167,pairCoefficient168,pairCoefficient169,pairCoefficient170,pairCoefficient171]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row71 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 71 b = sourceContactRow71 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row71 (b : Fin 97) :
    sourceContactRow71 contactValue b = pointContactRow71 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row71 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 71 b)*pairPoint dual 71 b) = contactBraRow71 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row71,hp,point_row71]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow71 b)*pairRow71 b) = 0
    norm_num [pointContactRow71,pairRow71,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient19,pairCoefficient43,pairCoefficient44,pairCoefficient45,pairCoefficient59,pairCoefficient60,pairCoefficient61,pairCoefficient72,pairCoefficient74,pairCoefficient75,pairCoefficient80,pairCoefficient82,pairCoefficient122,pairCoefficient123,pairCoefficient126,pairCoefficient129,pairCoefficient140,pairCoefficient141,pairCoefficient143,pairCoefficient152,pairCoefficient153,pairCoefficient166,pairCoefficient168,pairCoefficient169,pairCoefficient170,pairCoefficient171,pairCoefficient172]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow71 b)*star (pairRow71 b)) = 0
    norm_num [pointContactRow71,pairRow71,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient19,pairCoefficient43,pairCoefficient44,pairCoefficient45,pairCoefficient59,pairCoefficient60,pairCoefficient61,pairCoefficient72,pairCoefficient74,pairCoefficient75,pairCoefficient80,pairCoefficient82,pairCoefficient122,pairCoefficient123,pairCoefficient126,pairCoefficient129,pairCoefficient140,pairCoefficient141,pairCoefficient143,pairCoefficient152,pairCoefficient153,pairCoefficient166,pairCoefficient168,pairCoefficient169,pairCoefficient170,pairCoefficient171,pairCoefficient172]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row72 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 72 b = sourceContactRow72 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row72 (b : Fin 97) :
    sourceContactRow72 contactValue b = pointContactRow72 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row72 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 72 b)*pairPoint dual 72 b) = contactBraRow72 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row72,hp,point_row72]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow72 b)*pairRow72 b) = 0
    norm_num [pointContactRow72,pairRow72,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient16,pairCoefficient25,pairCoefficient74,pairCoefficient75,pairCoefficient89,pairCoefficient95,pairCoefficient102,pairCoefficient110,pairCoefficient126,pairCoefficient135,pairCoefficient148,pairCoefficient158,pairCoefficient161,pairCoefficient173,pairCoefficient174,pairCoefficient175]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow72 b)*star (pairRow72 b)) = 0
    norm_num [pointContactRow72,pairRow72,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient16,pairCoefficient25,pairCoefficient74,pairCoefficient75,pairCoefficient89,pairCoefficient95,pairCoefficient102,pairCoefficient110,pairCoefficient126,pairCoefficient135,pairCoefficient148,pairCoefficient158,pairCoefficient161,pairCoefficient173,pairCoefficient174,pairCoefficient175]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row73 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 73 b = sourceContactRow73 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row73 (b : Fin 97) :
    sourceContactRow73 contactValue b = pointContactRow73 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row73 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 73 b)*pairPoint dual 73 b) = contactBraRow73 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row73,hp,point_row73]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow73 b)*pairRow73 b) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow73,pairRow73,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient2,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient20,pairCoefficient30,pairCoefficient46,pairCoefficient48,pairCoefficient57,pairCoefficient63,pairCoefficient84,pairCoefficient86,pairCoefficient130,pairCoefficient166,pairCoefficient172,pairCoefficient176,pairCoefficient177,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow73 b)*star (pairRow73 b)) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow73,pairRow73,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient2,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient20,pairCoefficient30,pairCoefficient46,pairCoefficient48,pairCoefficient57,pairCoefficient63,pairCoefficient84,pairCoefficient86,pairCoefficient130,pairCoefficient166,pairCoefficient172,pairCoefficient176,pairCoefficient177,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row74 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 74 b = sourceContactRow74 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row74 (b : Fin 97) :
    sourceContactRow74 contactValue b = pointContactRow74 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row74 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 74 b)*pairPoint dual 74 b) = contactBraRow74 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row74,hp,point_row74]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow74 b)*pairRow74 b) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow74,pairRow74,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient2,pairCoefficient7,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient62,pairCoefficient63,pairCoefficient124,pairCoefficient130,pairCoefficient131,pairCoefficient154,pairCoefficient166,pairCoefficient167,pairCoefficient176,pairCoefficient177,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow74 b)*star (pairRow74 b)) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow74,pairRow74,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient2,pairCoefficient7,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient62,pairCoefficient63,pairCoefficient124,pairCoefficient130,pairCoefficient131,pairCoefficient154,pairCoefficient166,pairCoefficient167,pairCoefficient176,pairCoefficient177,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

end LowEnergy.ActualBraContactDualContraction
