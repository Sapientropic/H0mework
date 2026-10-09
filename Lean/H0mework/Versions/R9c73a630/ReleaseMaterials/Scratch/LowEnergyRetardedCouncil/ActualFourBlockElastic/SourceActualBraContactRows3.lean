import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraContactData1
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

private theorem original_row75 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 75 b = sourceContactRow75 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row75 (b : Fin 97) :
    sourceContactRow75 contactValue b = pointContactRow75 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row75 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 75 b)*pairPoint dual 75 b) = contactBraRow75 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row75,hp,point_row75]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow75 b)*pairRow75 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow75,pairRow75,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient5,pairCoefficient17,pairCoefficient19,pairCoefficient40,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient84,pairCoefficient111,pairCoefficient134,pairCoefficient139,pairCoefficient162,pairCoefficient173,pairCoefficient179,pairCoefficient180]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow75 b)*star (pairRow75 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow75,pairRow75,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient5,pairCoefficient17,pairCoefficient19,pairCoefficient40,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient84,pairCoefficient111,pairCoefficient134,pairCoefficient139,pairCoefficient162,pairCoefficient173,pairCoefficient179,pairCoefficient180]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row76 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 76 b = sourceContactRow76 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row76 (b : Fin 97) :
    sourceContactRow76 contactValue b = pointContactRow76 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row76 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 76 b)*pairPoint dual 76 b) = contactBraRow76 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row76,hp,point_row76]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow76 b)*pairRow76 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow76,pairRow76,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient7,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient29,pairCoefficient42,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient63,pairCoefficient71,pairCoefficient82,pairCoefficient84,pairCoefficient132,pairCoefficient140,pairCoefficient177,pairCoefficient181]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow76 b)*star (pairRow76 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow76,pairRow76,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient7,pairCoefficient9,pairCoefficient10,pairCoefficient18,pairCoefficient29,pairCoefficient42,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient63,pairCoefficient71,pairCoefficient82,pairCoefficient84,pairCoefficient132,pairCoefficient140,pairCoefficient177,pairCoefficient181]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row77 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 77 b = sourceContactRow77 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row77 (b : Fin 97) :
    sourceContactRow77 contactValue b = pointContactRow77 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row77 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 77 b)*pairPoint dual 77 b) = contactBraRow77 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row77,hp,point_row77]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow77 b)*pairRow77 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow77,pairRow77,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient19,pairCoefficient29,pairCoefficient42,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient63,pairCoefficient71,pairCoefficient82,pairCoefficient84,pairCoefficient132,pairCoefficient140,pairCoefficient177,pairCoefficient181]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow77 b)*star (pairRow77 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow77,pairRow77,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient19,pairCoefficient29,pairCoefficient42,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient63,pairCoefficient71,pairCoefficient82,pairCoefficient84,pairCoefficient132,pairCoefficient140,pairCoefficient177,pairCoefficient181]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row78 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 78 b = sourceContactRow78 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row78 (b : Fin 97) :
    sourceContactRow78 contactValue b = pointContactRow78 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row78 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 78 b)*pairPoint dual 78 b) = contactBraRow78 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row78,hp,point_row78]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow78 b)*pairRow78 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow78,pairRow78,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient8,pairCoefficient10,pairCoefficient29,pairCoefficient42,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient82,pairCoefficient84,pairCoefficient112,pairCoefficient140,pairCoefficient163,pairCoefficient174,pairCoefficient180,pairCoefficient181]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow78 b)*star (pairRow78 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow78,pairRow78,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient8,pairCoefficient10,pairCoefficient29,pairCoefficient42,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient82,pairCoefficient84,pairCoefficient112,pairCoefficient140,pairCoefficient163,pairCoefficient174,pairCoefficient180,pairCoefficient181]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row79 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 79 b = sourceContactRow79 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row79 (b : Fin 97) :
    sourceContactRow79 contactValue b = pointContactRow79 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row79 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 79 b)*pairPoint dual 79 b) = contactBraRow79 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row79,hp,point_row79]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow79 b)*pairRow79 b) = ((-3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow79,pairRow79,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient18,pairCoefficient39,pairCoefficient41,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient54,pairCoefficient65,pairCoefficient75,pairCoefficient84,pairCoefficient88,pairCoefficient113,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow79 b)*star (pairRow79 b)) = ((-3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow79,pairRow79,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient18,pairCoefficient39,pairCoefficient41,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient54,pairCoefficient65,pairCoefficient75,pairCoefficient84,pairCoefficient88,pairCoefficient113,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row80 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 80 b = sourceContactRow80 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row80 (b : Fin 97) :
    sourceContactRow80 contactValue b = pointContactRow80 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row80 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 80 b)*pairPoint dual 80 b) = contactBraRow80 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row80,hp,point_row80]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow80 b)*pairRow80 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow80,pairRow80,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient25,pairCoefficient32,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient47,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient114,pairCoefficient141,pairCoefficient175]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow80 b)*star (pairRow80 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow80,pairRow80,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient25,pairCoefficient32,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient47,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient114,pairCoefficient141,pairCoefficient175]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row81 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 81 b = sourceContactRow81 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row81 (b : Fin 97) :
    sourceContactRow81 contactValue b = pointContactRow81 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row81 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 81 b)*pairPoint dual 81 b) = contactBraRow81 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row81,hp,point_row81]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow81 b)*pairRow81 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow81,pairRow81,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient38,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient66,pairCoefficient72,pairCoefficient76,pairCoefficient84,pairCoefficient134,pairCoefficient143]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow81 b)*star (pairRow81 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow81,pairRow81,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient38,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient66,pairCoefficient72,pairCoefficient76,pairCoefficient84,pairCoefficient134,pairCoefficient143]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row82 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 82 b = sourceContactRow82 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row82 (b : Fin 97) :
    sourceContactRow82 contactValue b = pointContactRow82 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row82 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 82 b)*pairPoint dual 82 b) = contactBraRow82 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row82,hp,point_row82]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow82 b)*pairRow82 b) = ((1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow82,pairRow82,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient57,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow82 b)*star (pairRow82 b)) = ((1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow82,pairRow82,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient57,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row83 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 83 b = sourceContactRow83 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row83 (b : Fin 97) :
    sourceContactRow83 contactValue b = pointContactRow83 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row83 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 83 b)*pairPoint dual 83 b) = contactBraRow83 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row83,hp,point_row83]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow83 b)*pairRow83 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow83,pairRow83,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient18,pairCoefficient38,pairCoefficient39,pairCoefficient41,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient75,pairCoefficient115,pairCoefficient142,pairCoefficient149,pairCoefficient164]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow83 b)*star (pairRow83 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow83,pairRow83,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient18,pairCoefficient38,pairCoefficient39,pairCoefficient41,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient75,pairCoefficient115,pairCoefficient142,pairCoefficient149,pairCoefficient164]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row84 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 84 b = sourceContactRow84 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row84 (b : Fin 97) :
    sourceContactRow84 contactValue b = pointContactRow84 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row84 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 84 b)*pairPoint dual 84 b) = contactBraRow84 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row84,hp,point_row84]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow84 b)*pairRow84 b) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow84,pairRow84,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient37,pairCoefficient38,pairCoefficient39,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient54,pairCoefficient63,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient76,pairCoefficient97,pairCoefficient133,pairCoefficient155,pairCoefficient168,pairCoefficient171]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow84 b)*star (pairRow84 b)) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow84,pairRow84,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient37,pairCoefficient38,pairCoefficient39,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient54,pairCoefficient63,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient76,pairCoefficient97,pairCoefficient133,pairCoefficient155,pairCoefficient168,pairCoefficient171]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row85 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 85 b = sourceContactRow85 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row85 (b : Fin 97) :
    sourceContactRow85 contactValue b = pointContactRow85 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row85 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 85 b)*pairPoint dual 85 b) = contactBraRow85 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row85,hp,point_row85]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow85 b)*pairRow85 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow85,pairRow85,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient16,pairCoefficient34,pairCoefficient43,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient116,pairCoefficient143]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow85 b)*star (pairRow85 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow85,pairRow85,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient16,pairCoefficient34,pairCoefficient43,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient116,pairCoefficient143]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row86 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 86 b = sourceContactRow86 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row86 (b : Fin 97) :
    sourceContactRow86 contactValue b = pointContactRow86 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row86 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 86 b)*pairPoint dual 86 b) = contactBraRow86 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row86,hp,point_row86]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow86 b)*pairRow86 b) = ((-3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow86,pairRow86,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient18,pairCoefficient39,pairCoefficient41,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient54,pairCoefficient65,pairCoefficient75,pairCoefficient84,pairCoefficient88,pairCoefficient113,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow86 b)*star (pairRow86 b)) = ((-3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow86,pairRow86,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient18,pairCoefficient39,pairCoefficient41,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient54,pairCoefficient65,pairCoefficient75,pairCoefficient84,pairCoefficient88,pairCoefficient113,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row87 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 87 b = sourceContactRow87 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row87 (b : Fin 97) :
    sourceContactRow87 contactValue b = pointContactRow87 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row87 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 87 b)*pairPoint dual 87 b) = contactBraRow87 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row87,hp,point_row87]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow87 b)*pairRow87 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow87,pairRow87,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient32,pairCoefficient37,pairCoefficient38,pairCoefficient40,pairCoefficient43,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient65,pairCoefficient76,pairCoefficient78,pairCoefficient141]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow87 b)*star (pairRow87 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow87,pairRow87,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient32,pairCoefficient37,pairCoefficient38,pairCoefficient40,pairCoefficient43,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient59,pairCoefficient65,pairCoefficient76,pairCoefficient78,pairCoefficient141]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row88 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 88 b = sourceContactRow88 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row88 (b : Fin 97) :
    sourceContactRow88 contactValue b = pointContactRow88 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row88 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 88 b)*pairPoint dual 88 b) = contactBraRow88 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row88,hp,point_row88]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow88 b)*pairRow88 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow88,pairRow88,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient19,pairCoefficient41,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient81,pairCoefficient84,pairCoefficient89,pairCoefficient117,pairCoefficient144,pairCoefficient149,pairCoefficient165]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow88 b)*star (pairRow88 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow88,pairRow88,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient19,pairCoefficient41,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient81,pairCoefficient84,pairCoefficient89,pairCoefficient117,pairCoefficient144,pairCoefficient149,pairCoefficient165]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row89 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 89 b = sourceContactRow89 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row89 (b : Fin 97) :
    sourceContactRow89 contactValue b = pointContactRow89 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row89 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 89 b)*pairPoint dual 89 b) = contactBraRow89 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row89,hp,point_row89]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow89 b)*pairRow89 b) = ((1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow89,pairRow89,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient57,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow89 b)*star (pairRow89 b)) = ((1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow89,pairRow89,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient57,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row90 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 90 b = sourceContactRow90 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row90 (b : Fin 97) :
    sourceContactRow90 contactValue b = pointContactRow90 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row90 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 90 b)*pairPoint dual 90 b) = contactBraRow90 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row90,hp,point_row90]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow90 b)*pairRow90 b) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow90,pairRow90,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient37,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient53,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient68,pairCoefficient76,pairCoefficient81,pairCoefficient82,pairCoefficient97,pairCoefficient133,pairCoefficient155,pairCoefficient168,pairCoefficient169,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow90 b)*star (pairRow90 b)) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow90,pairRow90,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient10,pairCoefficient37,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient53,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient68,pairCoefficient76,pairCoefficient81,pairCoefficient82,pairCoefficient97,pairCoefficient133,pairCoefficient155,pairCoefficient168,pairCoefficient169,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row91 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 91 b = sourceContactRow91 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row91 (b : Fin 97) :
    sourceContactRow91 contactValue b = pointContactRow91 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row91 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 91 b)*pairPoint dual 91 b) = contactBraRow91 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row91,hp,point_row91]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow91 b)*pairRow91 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow91,pairRow91,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient32,pairCoefficient37,pairCoefficient40,pairCoefficient43,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient59,pairCoefficient65,pairCoefficient76,pairCoefficient78,pairCoefficient141]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow91 b)*star (pairRow91 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow91,pairRow91,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient32,pairCoefficient37,pairCoefficient40,pairCoefficient43,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient59,pairCoefficient65,pairCoefficient76,pairCoefficient78,pairCoefficient141]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row92 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 92 b = sourceContactRow92 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row92 (b : Fin 97) :
    sourceContactRow92 contactValue b = pointContactRow92 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row92 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 92 b)*pairPoint dual 92 b) = contactBraRow92 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row92,hp,point_row92]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow92 b)*pairRow92 b) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow92,pairRow92,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient59,pairCoefficient66,pairCoefficient72,pairCoefficient76,pairCoefficient84,pairCoefficient134,pairCoefficient143]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow92 b)*star (pairRow92 b)) = ((-1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow92,pairRow92,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient59,pairCoefficient66,pairCoefficient72,pairCoefficient76,pairCoefficient84,pairCoefficient134,pairCoefficient143]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row93 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 93 b = sourceContactRow93 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row93 (b : Fin 97) :
    sourceContactRow93 contactValue b = pointContactRow93 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row93 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 93 b)*pairPoint dual 93 b) = contactBraRow93 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row93,hp,point_row93]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow93 b)*pairRow93 b) = ((-3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow93,pairRow93,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient18,pairCoefficient39,pairCoefficient41,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient54,pairCoefficient65,pairCoefficient75,pairCoefficient84,pairCoefficient88,pairCoefficient113,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow93 b)*star (pairRow93 b)) = ((-3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow93,pairRow93,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient1,pairCoefficient18,pairCoefficient39,pairCoefficient41,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient54,pairCoefficient65,pairCoefficient75,pairCoefficient84,pairCoefficient88,pairCoefficient113,pairCoefficient149]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row94 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 94 b = sourceContactRow94 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row94 (b : Fin 97) :
    sourceContactRow94 contactValue b = pointContactRow94 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row94 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 94 b)*pairPoint dual 94 b) = contactBraRow94 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row94,hp,point_row94]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow94 b)*pairRow94 b) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow94,pairRow94,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient37,pairCoefficient46,pairCoefficient49,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient65,pairCoefficient66,pairCoefficient67,pairCoefficient68,pairCoefficient69,pairCoefficient71,pairCoefficient76,pairCoefficient81,pairCoefficient82,pairCoefficient156,pairCoefficient169,pairCoefficient170,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow94 b)*star (pairRow94 b)) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow94,pairRow94,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient37,pairCoefficient46,pairCoefficient49,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient65,pairCoefficient66,pairCoefficient67,pairCoefficient68,pairCoefficient69,pairCoefficient71,pairCoefficient76,pairCoefficient81,pairCoefficient82,pairCoefficient156,pairCoefficient169,pairCoefficient170,pairCoefficient178]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row95 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 95 b = sourceContactRow95 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row95 (b : Fin 97) :
    sourceContactRow95 contactValue b = pointContactRow95 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row95 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 95 b)*pairPoint dual 95 b) = contactBraRow95 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row95,hp,point_row95]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow95 b)*pairRow95 b) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow95,pairRow95,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient37,pairCoefficient38,pairCoefficient39,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient51,pairCoefficient52,pairCoefficient54,pairCoefficient63,pairCoefficient65,pairCoefficient66,pairCoefficient67,pairCoefficient69,pairCoefficient71,pairCoefficient76,pairCoefficient156,pairCoefficient170,pairCoefficient171]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow95 b)*star (pairRow95 b)) = ((3/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow95,pairRow95,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient37,pairCoefficient38,pairCoefficient39,pairCoefficient42,pairCoefficient48,pairCoefficient49,pairCoefficient51,pairCoefficient52,pairCoefficient54,pairCoefficient63,pairCoefficient65,pairCoefficient66,pairCoefficient67,pairCoefficient69,pairCoefficient71,pairCoefficient76,pairCoefficient156,pairCoefficient170,pairCoefficient171]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

private theorem original_row96 (q : Fin 4 → ℂ) (b : Fin 97) :
    contactCoefficient q 96 b = sourceContactRow96 (contactPolynomial q) b := by
  first | rfl | (fin_cases b <;> rfl)

private theorem point_row96 (b : Fin 97) :
    sourceContactRow96 contactValue b = pointContactRow96 b := by
  first | rfl | (fin_cases b <;> rfl)

theorem actual_contact_bra_row96 (dual : Bool) :
    (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) 96 b)*pairPoint dual 96 b) = contactBraRow96 dual := by
  have hp : contactPolynomial (worldTransfer Complex.I 0) = contactValue := funext actual_contact_polynomial_point
  simp only [original_row96,hp,point_row96]
  cases dual
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow96 b)*pairRow96 b) = ((1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow96,pairRow96,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient57,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)
  · change (∑b : Fin 97,((-1/2 : ℂ)*pointContactRow96 b)*star (pairRow96 b)) = ((1/200) * (Real.sqrt 30 : ℂ))
    norm_num [pointContactRow96,pairRow96,Fin.sum_univ_succ,starEnd_nat,starEnd_ofNat,pairCoefficient9,pairCoefficient10,pairCoefficient34,pairCoefficient37,pairCoefficient43,pairCoefficient46,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient57,pairCoefficient59,pairCoefficient74,pairCoefficient76,pairCoefficient84,pairCoefficient134]
    all_goals (ring_nf <;> norm_num [sqrt2_sq,sqrt15_sq,sqrt30_sq,Complex.I_sq] <;> ring)

end LowEnergy.ActualBraContactDualContraction
