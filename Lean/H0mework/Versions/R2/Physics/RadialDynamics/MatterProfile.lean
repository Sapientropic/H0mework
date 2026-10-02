import H0mework.Versions.R2.Physics.RadialDynamics.Matter

/-! A generated phase primitive follows the radial Jacobi profile. The
matter time jet is the derivative of the original occupied coefficients. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDiracKineticLocalSpinDensity
open DiracCliffordRepresentation Stage9C.Material.SpinPair

noncomputable section

def impulsePrimitive (time : ℝ) : ℝ :=
  (1-impulseMomentum time)/(inertia*responseFrequency^2)

theorem impulsePrimitive_hasDerivAt (time : ℝ) :
    HasDerivAt impulsePrimitive (impulse time) time := by
  unfold impulsePrimitive
  have raw := ((impulseMomentum_hasDerivAt time).const_sub 1).div_const (inertia*responseFrequency^2)
  convert raw using 1
  all_goals try rfl
  have square := responseFrequency_sq
  field_simp [ne_of_gt inertia_pos] at square
  rw [← square]
  field_simp [ne_of_gt inertia_pos, ne_of_gt responseFrequency_pos]

def responseProfile (parameter time : ℝ) : ℝ := gaugeScale+parameter*impulse time
def responseVelocity (parameter time : ℝ) : ℝ := parameter*(impulseMomentum time/inertia)
def responseAngle (parameter time : ℝ) : ℝ :=
  frequency*time - (3*lapse/2)*parameter*impulsePrimitive time

theorem responseProfile_hasDerivAt (parameter time : ℝ) :
    HasDerivAt (responseProfile parameter) (responseVelocity parameter time) time :=
  (impulse_hasDerivAt time).const_mul parameter |>.const_add gaugeScale

theorem responseVelocity_hasDerivAt (parameter time : ℝ) :
    HasDerivAt (responseVelocity parameter) (parameter*impulseAcceleration time) time :=
  (impulseVelocity_hasDerivAt time).const_mul parameter

theorem responseAngle_hasDerivAt (parameter time : ℝ) :
    HasDerivAt (responseAngle parameter) (3*lapse/2*(spinScale-responseProfile parameter time)) time := by
  have raw := ((hasDerivAt_id time).const_mul frequency).sub
    ((impulsePrimitive_hasDerivAt time).const_mul ((3*lapse/2)*parameter))
  convert raw using 1
  all_goals first | rfl | simp only [responseProfile, frequency]; ring

theorem responseAngle_background (point : BasePoint) :
    unitPhase (responseAngle 0 (point 0)) = upperPhase point ∧
      unitPhase (-responseAngle 0 (point 0)) = lowerPhase point := by
  simp only [responseAngle, mul_zero, zero_mul, sub_zero]
  constructor <;> simp only [unitPhase, upperPhase, lowerPhase, phase] <;>
    congr 1 <;> push_cast <;> ring

theorem coefficients_hasDerivAt (angle : ℝ → ℝ) (time rate : ℝ)
    (derivative : HasDerivAt angle rate time) :
    HasDerivAt (fun t => spinPairCoefficients (unitPhase (angle t)) (unitPhase (-angle t)))
      (spinPairCoefficients (Complex.I*(rate : ℂ)*unitPhase (angle time))
        (-Complex.I*(rate : ℂ)*unitPhase (-angle time))) time := by
  have positive := (unitPhase_hasDerivAt (angle time)).hasFDerivAt.comp_hasDerivAt time derivative
  have negative := (unitPhase_hasDerivAt (-angle time)).hasFDerivAt.comp_hasDerivAt time derivative.neg
  apply hasDerivAt_pi.mpr
  intro row
  apply hasDerivAt_pi.mpr
  intro column
  fin_cases row <;> fin_cases column
  all_goals simp only [spinPairCoefficients]
  · exact hasDerivAt_const time 0
  · convert positive using 1 <;> first | rfl | simp [Complex.real_smul]; ring
  · convert positive.neg using 1 <;> first | rfl | simp [Complex.real_smul]; ring
  · exact hasDerivAt_const time 0
  · exact hasDerivAt_const time 0
  · convert negative using 1 <;> first | rfl | simp [Complex.real_smul]; ring
  · convert negative.neg using 1 <;> first | rfl | simp [Complex.real_smul]; ring
  · exact hasDerivAt_const time 0

theorem movingMatterCoordinates_hasDerivAt (angle : ℝ → ℝ) (time rate : ℝ)
    (derivative : HasDerivAt angle rate time) :
    HasDerivAt (fun t => matterCoordinateEquiv (movingMatter (angle t)))
      (matterCoordinateEquiv (temporalMatter rate (angle time))) time := by
  let linear := (sourceColorMatterCoordinateLinear.restrictScalars ℝ).toContinuousLinearMap
  exact linear.hasFDerivAt.comp_hasDerivAt time (coefficients_hasDerivAt angle time rate derivative)

theorem responseMatter_kinetic_zero (parameter time : ℝ) :
    generatedContinuumMatterKineticVector
      StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource 0 0
      (matterJet (responseProfile parameter time)
        (deriv (responseAngle parameter) time) (responseAngle parameter time)) = 0 := by
  rw [(responseAngle_hasDerivAt parameter time).deriv]
  exact kineticVector_closed _ _

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
