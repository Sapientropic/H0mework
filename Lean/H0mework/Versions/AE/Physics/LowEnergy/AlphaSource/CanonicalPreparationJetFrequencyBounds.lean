import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationJetRapid
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationTaylorPoint

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumJetDecay
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumMomentumFirst PreparationVacuumTaylor PreparationVacuumRemainder
open CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace BigOperators
attribute [local irreducible] partialFourier

theorem partialFourierJet_eval_bound (n : ℕ) (p k : PhysicalMomentum) (v : Fin n → PhysicalMomentum) :
    (1+‖k‖)^104*‖partialFourierJet n p k v‖  ≤
      (sourceRapidJetBound n*sourceJetWeight n p)*(∏ i : Fin n,‖v i‖) := by
  calc
    _  ≤  (1+‖k‖)^104*(‖partialFourierJet n p k‖*(∏ i : Fin n,‖v i‖)) :=
      mul_le_mul_of_nonneg_left ((partialFourierJet n p k).le_opNorm v) (by positivity)
    _ = ((1+‖k‖)^104*‖partialFourierJet n p k‖)*(∏ i : Fin n,‖v i‖) := by rw [mul_assoc]
    _  ≤  _ := mul_le_mul_of_nonneg_right (partialFourierJet_rapid_bound n p k) (by positivity)

theorem source_first_fourier_104 (p k v : PhysicalMomentum) :
    (1+‖k‖)^104*‖fderiv ℝ (fun q : PhysicalMomentum => partialFourier q k) p v‖  ≤
      sourceRapidJetBound 1*‖v‖ := by
  have actual := partialFourierJet_eval_bound 1 p k (fun _ : Fin 1 => v)
  rw [partialFourierJet_readback] at actual
  simpa only [iteratedFDeriv_one_apply,sourceJetWeight,pow_zero,inv_one,mul_one,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one] using actual

theorem source_second_fourier_104 (p k v w : PhysicalMomentum) :
    (1+‖k‖)^104*‖fderiv ℝ (fderiv ℝ (fun q : PhysicalMomentum => partialFourier q k)) p v w‖  ≤
      (sourceRapidJetBound 2/(1+‖p‖))*(‖v‖*‖w‖) := by
  have actual := partialFourierJet_eval_bound 2 p k ![v,w]
  rw [partialFourierJet_readback] at actual
  simpa only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    sourceJetWeight,pow_one,div_eq_mul_inv,Fin.prod_univ_two] using actual

theorem shifted_first_104 (p v k : PhysicalMomentum) (t : ℝ) :
    (1+‖k‖)^104*‖shiftedFirst p v k t‖  ≤  sourceRapidJetBound 1*‖v‖ :=
  source_first_fourier_104 _ _ _

theorem shifted_second_104 (p v k : PhysicalMomentum) (t : ℝ) :
    (1+‖k‖)^104*‖shiftedSecond p v k t‖  ≤
      (sourceRapidJetBound 2/(1+‖p+t • v‖))*‖v‖^2 := by
  simpa only [shiftedSecond,pow_two] using source_second_fourier_104 (p+t • v) k v v

theorem source_frequency_distance (t : ℝ) (xi eta : PhysicalMomentum) (unit : |t| ≤ 1) :
    1+‖(t*Real.pi) • (xi+eta)‖  ≤  (1+Real.pi)*(1+‖xi‖)*(1+‖eta‖) := by
  have coeff : |t*Real.pi| ≤ Real.pi := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    simpa using mul_le_mul_of_nonneg_right unit Real.pi_pos.le
  have distance : ‖(t*Real.pi) • (xi+eta)‖ ≤ Real.pi*(‖xi‖+‖eta‖) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul coeff (norm_add_le xi eta) (norm_nonneg _) Real.pi_pos.le
  have peetre : 1+Real.pi*(‖xi‖+‖eta‖) ≤ (1+Real.pi)*(1+‖xi‖)*(1+‖eta‖) := by
    nlinarith [Real.pi_pos,norm_nonneg xi,norm_nonneg eta,
      mul_nonneg (norm_nonneg xi) (norm_nonneg eta),
      mul_nonneg Real.pi_pos.le (mul_nonneg (norm_nonneg xi) (norm_nonneg eta))]
  exact (add_le_add_right distance 1).trans (by simpa only [add_comm] using peetre)

theorem actual_shift_peetre (t : ℝ) (p xi eta : PhysicalMomentum) (unit : |t| ≤ 1) :
    1+‖p-(t*Real.pi) • xi‖  ≤
      (1+‖p+(t*Real.pi) • eta‖)*((1+Real.pi)*(1+‖xi‖)*(1+‖eta‖)) := by
  have peetre := frequency_peetre (p-(t*Real.pi) • xi) (p+(t*Real.pi) • eta)
  have difference : (p-(t*Real.pi) • xi)-(p+(t*Real.pi) • eta)=
      -((t*Real.pi) • (xi+eta)) := by rw [smul_add]; abel
  rw [difference,norm_neg] at peetre
  have bound := mul_le_mul_of_nonneg_right (source_frequency_distance t xi eta unit)
    (by positivity : 0 ≤ 1+‖p+(t*Real.pi) • eta‖)
  exact peetre.trans (bound.trans_eq (mul_comm _ _))

theorem actual_shift_peetre_reverse (t : ℝ) (p xi eta : PhysicalMomentum) (unit : |t| ≤ 1) :
    1+‖p+(t*Real.pi) • eta‖  ≤
      (1+‖p-(t*Real.pi) • xi‖)*((1+Real.pi)*(1+‖xi‖)*(1+‖eta‖)) := by
  have peetre := frequency_peetre (p+(t*Real.pi) • eta) (p-(t*Real.pi) • xi)
  have difference : (p+(t*Real.pi) • eta)-(p-(t*Real.pi) • xi)=
      (t*Real.pi) • (xi+eta) := by rw [smul_add]; abel
  rw [difference] at peetre
  have bound := mul_le_mul_of_nonneg_right (source_frequency_distance t xi eta unit)
    (by positivity : 0 ≤ 1+‖p-(t*Real.pi) • xi‖)
  exact peetre.trans (bound.trans_eq (mul_comm _ _))

theorem shifted_factor_104 (p v k : PhysicalMomentum) (t : ℝ) :
    (1+‖k‖)^104*‖shiftedFactor p v k t‖  ≤  sourceRapidJetBound 0*(1+‖p+t • v‖) := by
  simpa only [shiftedFactor,mul_comm] using
    (le_div_iff₀ (by positivity)).mp (actual_partialFourier_104_bound (p+t • v) k)

private theorem weighted_product_cancel (a b s d v m n : ℝ)
    (hn : 0  ≤  n) (hs : 0<s) (hv : 0  ≤  v)
    (ha : a ≤ (n/s)*v) (hb : b ≤ m*(s*d)) (hb0 : 0 ≤ b) :
    a*b ≤ n*m*d*v := by
  have product := mul_le_mul ha hb hb0 (mul_nonneg (div_nonneg hn hs.le) hv)
  apply product.trans_eq
  field_simp [hs.ne']

theorem second_zero_product_104 (t : ℝ) (p xi eta : PhysicalMomentum) (unit : |t| ≤ 1) :
    ((1+‖xi‖)^104*(1+‖eta‖)^104)*
      ‖shiftedSecond p (Real.pi • eta) xi t*shiftedFactor p (-Real.pi • xi) eta t‖  ≤
      (sourceRapidJetBound 2*sourceRapidJetBound 0)*
        ((1+Real.pi)*(1+‖xi‖)*(1+‖eta‖))*(Real.pi^2*‖eta‖^2) := by
  have left := shifted_second_104 p (Real.pi • eta) xi t
  have right := (shifted_factor_104 p (-Real.pi • xi) eta t).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [smul_neg,smul_smul,mul_neg,neg_smul,sub_eq_add_neg] using actual_shift_peetre t p xi eta unit)
      (sourceRapidJetBound_nonnegative 0))
  have product := weighted_product_cancel
    ((1+‖xi‖)^104*‖shiftedSecond p (Real.pi • eta) xi t‖)
    ((1+‖eta‖)^104*‖shiftedFactor p (-Real.pi • xi) eta t‖)
    (1+‖p+t • (Real.pi • eta)‖)
    ((1+Real.pi)*(1+‖xi‖)*(1+‖eta‖)) (‖Real.pi • eta‖^2)
    (sourceRapidJetBound 0) (sourceRapidJetBound 2)
    (sourceRapidJetBound_nonnegative 2) (by positivity) (by positivity) left
    (by simpa only [smul_neg,smul_smul,mul_neg,neg_smul,sub_eq_add_neg] using right) (by positivity)
  calc
    _ = ((1+‖xi‖)^104*‖shiftedSecond p (Real.pi • eta) xi t‖)*
      ((1+‖eta‖)^104*‖shiftedFactor p (-Real.pi • xi) eta t‖) := by rw [norm_mul]; ac_rfl
    _  ≤  _ := product
    _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_pow]

theorem zero_second_product_104 (t : ℝ) (p xi eta : PhysicalMomentum) (unit : |t| ≤ 1) :
    ((1+‖xi‖)^104*(1+‖eta‖)^104)*
      ‖shiftedFactor p (Real.pi • eta) xi t*shiftedSecond p (-Real.pi • xi) eta t‖  ≤
      (sourceRapidJetBound 2*sourceRapidJetBound 0)*
        ((1+Real.pi)*(1+‖xi‖)*(1+‖eta‖))*(Real.pi^2*‖xi‖^2) := by
  have left := (shifted_factor_104 p (Real.pi • eta) xi t).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [smul_neg,smul_smul,mul_neg,neg_smul,sub_eq_add_neg] using actual_shift_peetre_reverse t p xi eta unit)
      (sourceRapidJetBound_nonnegative 0))
  have right := shifted_second_104 p (-Real.pi • xi) eta t
  have product := weighted_product_cancel
    ((1+‖eta‖)^104*‖shiftedSecond p (-Real.pi • xi) eta t‖)
    ((1+‖xi‖)^104*‖shiftedFactor p (Real.pi • eta) xi t‖)
    (1+‖p+t • (-Real.pi • xi)‖)
    ((1+Real.pi)*(1+‖xi‖)*(1+‖eta‖)) (‖-Real.pi • xi‖^2)
    (sourceRapidJetBound 0) (sourceRapidJetBound 2)
    (sourceRapidJetBound_nonnegative 2) (by positivity) (by positivity) right
    (by simpa only [smul_neg,smul_smul,mul_neg,neg_smul,sub_eq_add_neg] using left) (by positivity)
  calc
    _ = ((1+‖eta‖)^104*‖shiftedSecond p (-Real.pi • xi) eta t‖)*
      ((1+‖xi‖)^104*‖shiftedFactor p (Real.pi • eta) xi t‖) := by rw [norm_mul]; ac_rfl
    _  ≤  _ := product
    _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos Real.pi_pos,mul_pow]

theorem first_first_product_104 (t : ℝ) (p xi eta : PhysicalMomentum) :
    ((1+‖xi‖)^104*(1+‖eta‖)^104)*
      ‖shiftedFirst p (Real.pi • eta) xi t*shiftedFirst p (-Real.pi • xi) eta t‖  ≤
      (sourceRapidJetBound 1)^2*Real.pi^2*(‖xi‖*‖eta‖) := by
  have product := mul_le_mul (shifted_first_104 p (Real.pi • eta) xi t)
    (shifted_first_104 p (-Real.pi • xi) eta t) (by positivity)
    (mul_nonneg (sourceRapidJetBound_nonnegative 1) (norm_nonneg _))
  calc
    _ = ((1+‖xi‖)^104*‖shiftedFirst p (Real.pi • eta) xi t‖)*
      ((1+‖eta‖)^104*‖shiftedFirst p (-Real.pi • xi) eta t‖) := by rw [norm_mul]; ac_rfl
    _  ≤  _ := product
    _ = _ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg,abs_of_pos Real.pi_pos]
      ring

def sourceSecondCompositionBound : ℝ :=
  2*Real.pi^2*((1+Real.pi)*sourceRapidJetBound 0*sourceRapidJetBound 2+(sourceRapidJetBound 1)^2)

theorem sourceSecondCompositionBound_nonnegative : 0  ≤  sourceSecondCompositionBound := by
  unfold sourceSecondCompositionBound
  exact mul_nonneg (by positivity) (add_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (sourceRapidJetBound_nonnegative 0))
      (sourceRapidJetBound_nonnegative 2)) (sq_nonneg _))

theorem compositionSecondIntegrand_101_bound (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) (unit : |t| ≤ 1) :
    ((1+‖w.1‖)^101*(1+‖w.2‖)^101)*‖compositionSecondIntegrand t z p w‖  ≤
      sourceSecondCompositionBound := by
  let x := 1+‖w.1‖
  let y := 1+‖w.2‖
  have xpos : 0<x := by dsimp [x]; positivity
  have ypos : 0<y := by dsimp [y]; positivity
  have xone : 1 ≤ x := by dsimp [x]; linarith [norm_nonneg w.1]
  have yone : 1 ≤ y := by dsimp [y]; linarith [norm_nonneg w.2]
  have nx : ‖w.1‖ ≤ x := by dsimp [x]; linarith
  have ny : ‖w.2‖ ≤ y := by dsimp [y]; linarith
  have xc : x ≤ x^3 := by simpa only [pow_one] using pow_le_pow_right₀ xone (show 1 ≤ 3 by norm_num)
  have yc : y ≤ y^3 := by simpa only [pow_one] using pow_le_pow_right₀ yone (show 1 ≤ 3 by norm_num)
  have powers : x*y ≤ x^3*y^3 := mul_le_mul xc yc ypos.le (by positivity)
  have left := second_zero_product_104 t p w.1 w.2 unit
  have middle := first_first_product_104 t p w.1 w.2
  have right := zero_second_product_104 t p w.1 w.2 unit
  have coefficient_nonnegative : 0 ≤
      Real.pi^2*(1+Real.pi)*sourceRapidJetBound 0*sourceRapidJetBound 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg Real.pi) (by positivity))
      (sourceRapidJetBound_nonnegative 0)) (sourceRapidJetBound_nonnegative 2)
  have outer : (sourceRapidJetBound 2*sourceRapidJetBound 0)*
      ((1+Real.pi)*x*y)*(Real.pi^2*‖w.2‖^2)  ≤
      (Real.pi^2*(1+Real.pi)*sourceRapidJetBound 0*sourceRapidJetBound 2)*(x^3*y^3) := by
    have geometric : x*y*‖w.2‖^2 ≤ x^3*y^3 := by
      calc
        _  ≤  x*y*y^2 := by gcongr
        _ = x*y^3 := by ring
        _  ≤  x^3*y^3 := mul_le_mul_of_nonneg_right xc (by positivity)
    calc
      _ = (Real.pi^2*(1+Real.pi)*sourceRapidJetBound 0*sourceRapidJetBound 2)*
        (x*y*‖w.2‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left geometric coefficient_nonnegative
  have outer' : (sourceRapidJetBound 2*sourceRapidJetBound 0)*
      ((1+Real.pi)*x*y)*(Real.pi^2*‖w.1‖^2)  ≤
      (Real.pi^2*(1+Real.pi)*sourceRapidJetBound 0*sourceRapidJetBound 2)*(x^3*y^3) := by
    have geometric : x*y*‖w.1‖^2 ≤ x^3*y^3 := by
      calc
        _  ≤  x*y*x^2 := by gcongr
        _ = x^3*y := by ring
        _  ≤  x^3*y^3 := mul_le_mul_of_nonneg_left yc (by positivity)
    calc
      _ = (Real.pi^2*(1+Real.pi)*sourceRapidJetBound 0*sourceRapidJetBound 2)*
        (x*y*‖w.1‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left geometric coefficient_nonnegative
  have inner : (sourceRapidJetBound 1)^2*Real.pi^2*(‖w.1‖*‖w.2‖)  ≤
      ((sourceRapidJetBound 1)^2*Real.pi^2)*(x^3*y^3) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact (mul_le_mul nx ny (norm_nonneg _) xpos.le).trans powers
  have triangle : ‖compositionSecondIntegrand t z p w‖  ≤
      ‖shiftedSecond p (Real.pi • w.2) w.1 t*shiftedFactor p (-Real.pi • w.1) w.2 t‖+
      2*‖shiftedFirst p (Real.pi • w.2) w.1 t*shiftedFirst p (-Real.pi • w.1) w.2 t‖+
      ‖shiftedFactor p (Real.pi • w.2) w.1 t*shiftedSecond p (-Real.pi • w.1) w.2 t‖ := by
    rw [compositionSecondIntegrand,Circle.norm_smul]
    apply (norm_add_le _ _).trans
    apply add_le_add _ le_rfl
    calc
      _ ≤ _ := norm_add_le _ _
      _ = _ := by rw [norm_mul]; norm_num
  have weighted : (x^104*y^104)*‖compositionSecondIntegrand t z p w‖  ≤
      sourceSecondCompositionBound*(x^3*y^3) := by
    calc
      _  ≤  (x^104*y^104)*(_+2*_+_) := mul_le_mul_of_nonneg_left triangle (by positivity)
      _ = (x^104*y^104)*‖shiftedSecond p (Real.pi • w.2) w.1 t*shiftedFactor p (-Real.pi • w.1) w.2 t‖+
          2*((x^104*y^104)*‖shiftedFirst p (Real.pi • w.2) w.1 t*shiftedFirst p (-Real.pi • w.1) w.2 t‖)+
          (x^104*y^104)*‖shiftedFactor p (Real.pi • w.2) w.1 t*shiftedSecond p (-Real.pi • w.1) w.2 t‖ := by
          rw [mul_add,mul_add,mul_left_comm (x^104*y^104) 2]
      _  ≤  _ := add_le_add (add_le_add (left.trans outer)
        (mul_le_mul_of_nonneg_left (middle.trans inner) (by norm_num))) (right.trans outer')
      _ = _ := by rw [sourceSecondCompositionBound]; ring
  have cancelled : (x^3*y^3)*((x^101*y^101)*‖compositionSecondIntegrand t z p w‖)  ≤
      (x^3*y^3)*sourceSecondCompositionBound := by
    convert weighted using 1
    · rw [show (104 : ℕ)=101+3 from rfl,pow_add,pow_add]; ac_rfl
    · ac_rfl
  exact (mul_le_mul_iff_right₀ (by positivity : 0<x^3*y^3)).mp cancelled

end LowEnergy.PreparationVacuumJetDecay
