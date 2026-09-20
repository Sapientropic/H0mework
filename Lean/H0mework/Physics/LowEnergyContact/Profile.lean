import H0mework.Physics.LowEnergyResponse.Radial
import H0mework.Physics.SpinPair.Coframe

/-! Contact-preserving radial test family through the original actual.
No new source, curvature coordinate, or on-shell certificate is an input. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Contact.Profile
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair
open StageNineP286GaugeConnectionVariationDensity Response.Radial
noncomputable section

def wave (point : BasePoint) : ℝ := Real.sinh (growthRate * point 0)
def testField (parameter : ℝ) : StageNineHolonomicConfiguration :=
  { actual with scalar := fun point =>
      actual.scalar point + (parameter * wave point) • direction }

theorem wave_zero : wave 0 = 0 := by simp [wave]
theorem scalar_origin (parameter : ℝ) :
    (testField parameter).scalar 0 = actual.scalar 0 := by
  simp [testField, wave_zero]

theorem family_zero : testField 0 = actual := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  funext point
  simp [testField]

def timeProjection : BasePoint →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 4)

theorem wave_hasFDerivAt (point : BasePoint) :
    HasFDerivAt wave ((growthRate * Real.cosh (growthRate * point 0)) • timeProjection) point := by
  have linear := ((timeProjection.hasFDerivAt (x := point)).const_mul growthRate)
  convert! linear.sinh using 1
  change (growthRate * Real.cosh (growthRate * point 0)) • timeProjection =
    Real.cosh (growthRate * point 0) • growthRate • timeProjection
  rw [smul_smul, mul_comm]


theorem scalar_derivative (parameter : ℝ) (point : BasePoint) (mu : LorentzianIndex) :
    fieldDirectionalDerivative (testField parameter).scalar point mu =
      (parameter * Real.cosh (growthRate * point 0) * growthRate *
        (if mu = 0 then 1 else 0)) • direction := by
  unfold fieldDirectionalDerivative
  have d := (hasFDerivAt_const (𝕜 := ℝ) direction point).add
    (((wave_hasFDerivAt point).const_mul parameter).smul_const direction)
  have eqField : (testField parameter).scalar = fun p => direction + (parameter * wave p) • direction := by
    funext p
    rw [testField, actual_scalar]
    rfl
  rw [eqField]
  change fderiv ℝ ((fun _ : BasePoint => direction) +
    (fun p => (parameter * wave p) • direction)) point _ = _
  rw [d.fderiv]
  simp [timeProjection, coordinateDirection, mul_comm, mul_left_comm, eq_comm]

theorem covariant_derivative (parameter : ℝ) (point : BasePoint) (mu : LorentzianIndex) :
    holonomicScalarCovariantDerivative (testField parameter) point mu =
      (parameter * Real.cosh (growthRate * point 0) * growthRate *
        (if mu = 0 then 1 else 0)) • direction := by
  rw [holonomicScalarCovariantDerivative, scalar_derivative]
  change _ + scalarMotherLieAction _ (actual.scalar point + _ • direction) = _
  rw [actual_scalar]
  change _ + scalarMotherLieAction
    (SU7MotherLieAlgebra.p286LieBlockEmbed (actual.gaugeConnection point mu))
    (direction + _ • direction) = _
  rw [scalarMotherLieAction_add_right, scalarMotherLieAction_real_smul_right,
    background_action_zero, smul_zero, add_zero, add_zero]

theorem covariant_origin (parameter : ℝ) :
    holonomicScalarCovariantDerivative (testField parameter) 0 =
      fun mu => if mu = 0 then (parameter * growthRate) • direction else 0 := by
  funext mu
  rw [covariant_derivative]
  by_cases h : mu = 0 <;> simp [h]

private theorem scalar_update_pointField (configuration : StageNineHolonomicConfiguration)
    (scalar : BasePoint → ScalarCoordinateCarrier) (point : BasePoint) :
    toContinuumPointField { configuration with scalar := scalar } point =
      { toContinuumPointField configuration point with
        scalar := scalar point
        scalarCovariantDerivative :=
          holonomicScalarCovariantDerivative { configuration with scalar := scalar } point } := by
  rfl

/-- All curvature and matter jets below come from the primitive field. -/
theorem pointField_origin (parameter : ℝ) :
    toContinuumPointField (testField parameter) 0 =
      { toContinuumPointField actual 0 with
        scalarCovariantDerivative := fun mu =>
          if mu = 0 then (parameter * growthRate) • direction else 0 } := by
  have generated := scalar_update_pointField actual (testField parameter).scalar 0
  change toContinuumPointField (testField parameter) 0 =
    { toContinuumPointField actual 0 with
      scalar := (testField parameter).scalar 0
      scalarCovariantDerivative := holonomicScalarCovariantDerivative (testField parameter) 0 } at generated
  rw [scalar_origin, covariant_origin] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.Contact.Profile
