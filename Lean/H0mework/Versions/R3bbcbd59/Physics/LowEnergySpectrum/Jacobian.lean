import H0mework.Versions.AB.Physics.LowEnergyEvolution.Balance

/-! Exact derivative of the original lapse-constrained homogeneous generator. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spectrum
open Evolution Stage9C.Material.SpinPair
noncomputable section

def variationPath (v : State) (t : ℝ) : State := Evolution.seed 0 + t • v

theorem variationPath_zero (v : State) : variationPath v 0 = Evolution.seed 0 := by simp [variationPath]

theorem variationPath_derivative (v : State) : HasDerivAt (variationPath v) v 0 := by
  convert! ((hasDerivAt_id (x := (0 : ℝ))).smul_const v).const_add (Evolution.seed 0) using 1
  simp

theorem coordinate_derivative (v : State) (i : Fin 7) :
    HasDerivAt (fun t => variationPath v t i) (v i) 0 :=
  hasDerivAt_pi.mp (variationPath_derivative v) i

theorem clock_origin : clock (Evolution.seed 0) = lapse := by rw [clock_seed, Contact.Slice.clock_zero]

theorem denominator_origin : denominator (Evolution.seed 0) = 9/5 := by
  norm_num [denominator, Evolution.seed, contorsion, Contact.Slice.impulse, gaugeScale,
    div_pow, mul_pow, spinScale_sq]
  nlinarith [spinScale_sq]

theorem torsion_derivative (v : State) :
    HasDerivAt (fun t => contorsion (variationPath v t)) (-2*spinScale*v 0) 0 := by
  have derivative := (hasDerivAt_const (x := (0 : ℝ)) spinScale).div
    ((coordinate_derivative v 0).pow 2) (by simp [variationPath_zero, Evolution.seed])
  convert! derivative using 1
  simp [variationPath_zero, Evolution.seed]
  ring

theorem energy_derivative (v : State) :
    HasDerivAt (fun t => gaugeEnergy (variationPath v t)) (4*gaugeScale^3*v 2) 0 := by
  have derivative := ((coordinate_derivative v 3).pow 2).add ((coordinate_derivative v 2).pow 4)
  convert! derivative using 1
  simp [variationPath_zero, Evolution.seed]

theorem denominator_derivative (v : State) :
    HasDerivAt (fun t => denominator (variationPath v t)) (-(9/5)*v 0-6*spinScale*v 2) 0 := by
  have dx := coordinate_derivative v
  have dk := torsion_derivative v
  have first := ((dk.sub (dx 2)).const_mul (6*spinScale)).div (dx 0)
    (by simp [variationPath_zero, Evolution.seed])
  have scalar := (((dx 0).pow 3).const_mul Contact.Stress.weight).mul
    (((dx 4).pow 2).sub (((dx 5).pow 2).div_const 2))
  have cosmological := ((dx 0).pow 3).const_mul 3
  have extrinsic := ((dx 0).const_mul 3).mul ((dx 1).pow 2)
  have torsion := ((dx 0).const_mul 3).mul (dk.pow 2)
  have derivative := (((first.add scalar).add cosmological).add extrinsic).sub torsion
  convert! derivative using 1
  simp [variationPath_zero, Evolution.seed, contorsion, Contact.Slice.impulse, gaugeScale]
  ring_nf
  rw [spinScale_sq]
  ring

def clockResponse (v : State) : ℝ := lapse*(v 0+(10*spinScale/3)*v 2)

private theorem spin_cube : spinScale^3 = 2*spinScale := by
  calc
    _ = spinScale^2*spinScale := by ring
    _ = _ := by rw [spinScale_sq]

private theorem spin_fourth : spinScale^4 = 4 := by
  calc
    _ = (spinScale^2)^2 := by ring
    _ = _ := by rw [spinScale_sq]; norm_num

private theorem spin_fifth : spinScale^5 = 4*spinScale := by
  calc
    _ = spinScale^4*spinScale := by ring
    _ = _ := by rw [spin_fourth]

theorem clock_derivative (v : State) :
    HasDerivAt (fun t => clock (variationPath v t)) (clockResponse v) 0 := by
  have numerator := ((coordinate_derivative v 0).const_mul 3).mul (energy_derivative v)
  have denominatorDifferential := (denominator_derivative v).const_mul (4*sourceCoupling)
  have denominatorNonzero : 4*sourceCoupling*denominator (variationPath v 0) ≠ 0 := by
    rw [variationPath_zero, denominator_origin, sourceCoupling_eq]
    norm_num
  have quotient := numerator.div denominatorDifferential denominatorNonzero
  have quotientNonzero : 3*variationPath v 0 0*gaugeEnergy (variationPath v 0) /
      (4*sourceCoupling*denominator (variationPath v 0)) ≠ 0 := by
    simp [variationPath_zero, Evolution.seed, gaugeEnergy, denominator_origin, sourceCoupling_eq,
      ne_of_gt gaugeScale_pos]
  have derivative := quotient.sqrt quotientNonzero
  convert! derivative using 1
  change clockResponse v = _ / (2*clock (variationPath v 0))
  rw [variationPath_zero, clock_origin, denominator_origin]
  simp [Evolution.seed, gaugeEnergy, Pi.mul_apply, variationPath_zero]
  unfold clockResponse
  rw [sourceCoupling_eq]
  field_simp [ne_of_gt lapse_pos]
  unfold gaugeScale
  ring_nf
  simp only [spin_cube, spin_fourth, spin_fifth, lapse_sq]
  ring

def linearResponse (v : State) (i : Fin 7) : ℝ :=
  match i.val with
  | 0 => lapse*v 1
  | 1 => -12*lapse*v 0
  | 2 => v 3/lapse
  | 3 => (50/3)*lapse*v 2
  | 4 => lapse*v 5
  | 5 => 2*lapse*v 4
  | _ => -3*lapse*spinScale*v 0+(5/2)*lapse*v 2

theorem generator_path_derivative (v : State) :
    HasDerivAt (fun t => generator (variationPath v t)) (linearResponse v) 0 := by
  have dx := coordinate_derivative v
  have dn := clock_derivative v
  have dk := torsion_derivative v
  have energy := energy_derivative v
  have hn : clock (variationPath v 0) ≠ 0 := by rw [variationPath_zero, clock_origin]; exact ne_of_gt lapse_pos
  have ha : variationPath v 0 0 ≠ 0 := by simp [variationPath_zero, Evolution.seed]
  have hs : 4*sourceCoupling*clock (variationPath v 0) ≠ 0 := by
    rw [sourceCoupling_eq]
    exact mul_ne_zero (by norm_num) hn
  have h2a : 2*variationPath v 0 0 ≠ 0 := mul_ne_zero (by norm_num) ha
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! dn.mul (dx 1) using 1
    simp [linearResponse, variationPath_zero, Evolution.seed, clock_origin]
  · have first := (energy.div (dn.const_mul (4*sourceCoupling)) hs).neg
    have spin := ((dk.sub (dx 2)).const_mul (2*spinScale)).div ((dx 0).pow 2) (pow_ne_zero _ ha)
    have scalar := (((dx 0).pow 2).const_mul Contact.Stress.weight).mul
      (((dx 4).pow 2).add (((dx 5).pow 2).div_const 2))
    have inner := (((spin.sub scalar).sub (((dx 0).pow 2).const_mul 3)).sub ((dx 1).pow 2)).add (dk.pow 2)
    have derivative := (first.add (dn.mul inner)).div ((dx 0).const_mul 2) h2a
    convert! derivative using 1
    · funext t
      simp [generator]
      ring
    ·
      simp [linearResponse, variationPath_zero, Evolution.seed, clock_origin, contorsion, gaugeEnergy,
        Contact.Slice.impulse, clockResponse]
      rw [sourceCoupling_eq]
      field_simp [ne_of_gt lapse_pos]
      unfold gaugeScale
      ring_nf
      simp only [spinScale_sq, spin_cube, spin_fourth, spin_fifth, lapse_sq]
      ring
  · convert! ((dx 0).mul (dx 3)).div dn hn using 1
    simp [linearResponse, variationPath_zero, Evolution.seed, clock_origin]
    field_simp [ne_of_gt lapse_pos]
  · have first := ((dn.const_mul (4*sourceCoupling)).mul_const spinScale).div (dx 0) ha
    have second := (((dx 0).mul ((dx 2).pow 3)).const_mul 2).div dn hn
    convert! first.sub second using 1
    · funext t
      simp [generator]
      ring
    · simp [linearResponse, variationPath_zero, Evolution.seed, clock_origin, clockResponse]
      rw [sourceCoupling_eq]
      field_simp [ne_of_gt lapse_pos]
      unfold gaugeScale
      ring_nf
      simp only [spinScale_sq, spin_fourth, lapse_sq]
      ring
  · convert! dn.mul (dx 5) using 1
    simp [linearResponse, variationPath_zero, Evolution.seed, clock_origin, Contact.Slice.impulse]
  · have expansion := (((dx 1).const_mul 3).mul (dx 5)).div (dx 0) ha
    convert! dn.mul (((dx 4).const_mul 2).sub expansion) using 1
    simp [linearResponse, variationPath_zero, Evolution.seed, clock_origin, Contact.Slice.impulse]
    ring
  · convert! (((dn.mul (dk.sub (dx 2))).const_mul 3).div ((dx 0).const_mul 2) h2a) using 1
    · funext t
      simp [generator]
      ring
    · simp [linearResponse, variationPath_zero, Evolution.seed, clock_origin, contorsion, clockResponse]
      unfold gaugeScale
      ring_nf
      rw [spinScale_sq]
      ring

theorem generator_fderiv (v : State) :
    fderiv ℝ generator (Evolution.seed 0) v = linearResponse v := by
  have differentiable := (generator_contDiffAt (Evolution.seed 0) (seed_admissible 0)).differentiableAt (by simp)
  have differentiable' : HasFDerivAt generator (fderiv ℝ generator (Evolution.seed 0)) (variationPath v 0) := by
    simpa only [variationPath_zero] using differentiable.hasFDerivAt
  have derivative := differentiable'.comp_hasDerivAt 0 (variationPath_derivative v)
  exact derivative.unique (generator_path_derivative v)

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spectrum
