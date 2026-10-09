import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Trajectory

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open Force.Interface
noncomputable section

def translationSpeed (t : ℝ) : ℝ := (displacementQ : ℝ)*FiniteActuation.progressRate t

theorem shift_velocity (t : ℝ) (i : Coordinate) :
    shiftRate .drive t i=translationSpeed t*(axisQ i.2 : ℝ) := by
  unfold shiftRate displacement translationSpeed
  ring

theorem translation_speed_formula (t : ℝ) : translationSpeed t=
    (3/4 : ℝ)*((FiniteContinuation.gainQ input : ℝ)/((totalMassQ : ℝ)+1))*
      (t/duration)*(1-t/duration) := by
  unfold translationSpeed displacementQ translationRateQ FiniteActuation.progressRate duration
  push_cast
  field_simp [ne_of_gt (Rat.cast_pos.mpr Propagation.Producer.nativeClockStep_positive :
    (0 : ℝ)<(Propagation.Producer.nativeClockStep : ℝ))]
  ring

theorem translation_speed_bound (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    0 ≤ translationSpeed t ∧ translationSpeed t ≤ (FiniteContinuation.gainQ input : ℝ)/((totalMassQ : ℝ)+1) := by
  have dp := FiniteActuation.duration_positive
  have u0 : 0 ≤ t/duration := div_nonneg lo dp.le
  have u1 : t/duration ≤ 1 := (div_le_one dp).mpr hi
  have parabola0 : 0 ≤ (t/duration)*(1-t/duration) := mul_nonneg u0 (by linarith)
  have parabola1 : (t/duration)*(1-t/duration) ≤ 1 := by nlinarith [sq_nonneg (t/duration)]
  have gp : 0 < (FiniteContinuation.gainQ input : ℝ) :=
    Rat.cast_pos.mpr (FiniteContinuation.gain_positive input input_admissible)
  have mp : 0 < (totalMassQ : ℝ) := Rat.cast_pos.mpr total_mass_positive
  have ap := div_pos gp (by linarith : 0<(totalMassQ : ℝ)+1)
  rw [translation_speed_formula]
  constructor
  · nlinarith [mul_nonneg ap.le parabola0]
  · nlinarith [mul_le_mul_of_nonneg_left parabola1 ap.le]

theorem translation_kinetic (t : ℝ) :
    nuclearKinetic (fun i => mass i*shiftRate .drive t i)=(totalMassQ : ℝ)*(translationSpeed t)^2/2 := by
  unfold nuclearKinetic
  rw [Fintype.sum_prod_type]
  have atom (a : Atom) :
      (∑ k : Axis, (mass (a,k)*shiftRate .drive t (a,k))^2/(2*mass (a,k)))=
        (Reentry.Source.stepReadout.nuclear.masses a : ℝ)*(translationSpeed t)^2/2 := by
    rw [Fin.sum_univ_three]
    simp only [shift_velocity,axisQ,ite_true,show (1 : Fin 3)≠0 from by decide,
      show (2 : Fin 3)≠0 from by decide,ite_false,Rat.cast_one,Rat.cast_zero,mul_one,mul_zero,
      zero_pow (by decide : (2 : Nat)≠0),zero_div,add_zero]
    unfold mass
    have positive : (0 : ℝ)<(Reentry.Source.stepReadout.nuclear.masses a : ℝ) := mass_positive (a,0)
    field_simp [positive.ne']
  simp_rw [atom]
  simp only [totalMassQ,Rat.cast_sum,Finset.sum_div,Finset.sum_mul]

theorem gain_below_reserve : FiniteContinuation.gainQ input < input.reserve := by
  have gp := FiniteContinuation.gain_positive input input_admissible
  have balance := FiniteContinuation.gain_balance input input_admissible
  have excess : 0 < FiniteContinuation.gainQ input*(8*(input.body.frame.kinetic+input.reserve+1)-1) :=
    mul_pos gp (by linarith only [input_admissible.positiveKinetic,input_admissible.positiveReserve])
  nlinarith only [excess,balance]

theorem translation_kinetic_paid (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    nuclearKinetic (fun i => mass i*shiftRate .drive t i)<(input.reserve : ℝ)/2 := by
  have gp : 0 < (FiniteContinuation.gainQ input : ℝ) :=
    Rat.cast_pos.mpr (FiniteContinuation.gain_positive input input_admissible)
  have g1 : (FiniteContinuation.gainQ input : ℝ)<1 := by
    exact_mod_cast FiniteContinuation.gain_lt_one input input_admissible
  have gr : (FiniteContinuation.gainQ input : ℝ)<(input.reserve : ℝ) := Rat.cast_lt.mpr gain_below_reserve
  have mp : 0 < (totalMassQ : ℝ) := Rat.cast_pos.mpr total_mass_positive
  let a := (FiniteContinuation.gainQ input : ℝ)/((totalMassQ : ℝ)+1)
  have ap : 0 < a := div_pos gp (by linarith)
  have ab : a*((totalMassQ : ℝ)+1)=(FiniteContinuation.gainQ input : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt (by linarith : 0<(totalMassQ : ℝ)+1))
  have mBound : (totalMassQ : ℝ)≤((totalMassQ : ℝ)+1)^2 := by nlinarith [sq_nonneg (totalMassQ : ℝ)]
  have bound := mul_le_mul_of_nonneg_right mBound (sq_nonneg a)
  have identity : ((totalMassQ : ℝ)+1)^2*a^2=(FiniteContinuation.gainQ input : ℝ)^2 := by
    rw [← mul_pow,mul_comm,ab]
  rw [identity] at bound
  have velocityBound := translation_speed_bound t lo hi
  have velocitySquare : (translationSpeed t)^2≤a^2 := by nlinarith
  have kineticBound := mul_le_mul_of_nonneg_left velocitySquare mp.le
  rw [translation_kinetic]
  nlinarith

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
