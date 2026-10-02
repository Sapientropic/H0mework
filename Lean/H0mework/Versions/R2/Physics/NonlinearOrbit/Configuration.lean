import H0mework.Versions.R2.Physics.NonlinearOrbit.Flow

/-! The generated orbit writes the original primitive connection and both
Dirac fields; the source constitutive action generates its auxiliary. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineDiracKineticLocalSpinDensity StageNineMatterCovariantDerivativeAffine
open StageNineCoframeFirstJet StageNineCoframeLocalDifferentiability StageNineMatterVariation
open StageNineLorentzConnectionVariation SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineLorentzConnectionVariationDensity
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open Stage9C.Dynamics.Homogeneous StageNineEnrichedProofFreeSource

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

def LocalOrbit.configuration (flow : LocalOrbit initial initialTime) : StageNineHolonomicConfiguration :=
  { radialReadout flow.amplitude with
    matter := fun point => movingMatter (flow.angle (point 0))
    conjugateMatter := fun point => movingDual (flow.angle (point 0)) }

private theorem curvature_congr (first second : StageNineHolonomicConfiguration)
    (same : first.gaugeConnection = second.gaugeConnection) (point : BasePoint) :
    holonomicGaugeCurvature first point = holonomicGaugeCurvature second point := by
  funext pair
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [same]

theorem LocalOrbit.curvature (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) :
    holonomicGaugeCurvature flow.configuration point = radialCurvature (flow.amplitude (point 0)) (flow.velocity (point 0)) := by
  rw [curvature_congr flow.configuration (radialWrite flow.amplitude) rfl]
  exact radialWrite_curvature _ _ _ (flow.amplitude_derivative _ inside)

theorem LocalOrbit.auxiliary (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) :
    flow.configuration.gaugeAuxiliary point = radialAuxiliary (flow.amplitude (point 0)) (flow.velocity (point 0)) := by
  rw [show flow.configuration.gaugeAuxiliary = (radialReadout flow.amplitude).gaugeAuxiliary from rfl]
  exact radialReadout_auxiliary _ _ _ (flow.amplitude_derivative _ inside)

theorem LocalOrbit.matterCoordinateDerivative (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (direction : LorentzianIndex) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv (flow.configuration.matter candidate)) point direction) =
      if direction = 0 then temporalMatter (3*lapse/2*(spinScale-flow.amplitude (point 0))) (flow.angle (point 0)) else 0 := by
  have derivative := movingMatterCoordinates_hasDerivAt flow.angle (point 0) _ (flow.angle_derivative _ inside)
  have composed := derivative.hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun candidate : BasePoint =>
    matterCoordinateEquiv (flow.configuration.matter candidate)) _ point at composed
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  change matterCoordinateEquiv.symm ((coordinateDirection direction) 0 •
    matterCoordinateEquiv (temporalMatter (3*lapse/2*(spinScale-flow.amplitude (point 0))) (flow.angle (point 0)))) = _
  by_cases same : direction = 0
  · simp [same, coordinateDirection]
  · simp [same, Ne.symm same, coordinateDirection]

theorem LocalOrbit.matterCovariantDerivative (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) :
    holonomicMatterCovariantDerivative flow.configuration point =
      ![temporalMatter (3*lapse/2*(spinScale-flow.amplitude (point 0))) (flow.angle (point 0)),
        spatialMatter (flow.amplitude (point 0)) (flow.angle (point 0)) 0,
        spatialMatter (flow.amplitude (point 0)) (flow.angle (point 0)) 1,
        spatialMatter (flow.amplitude (point 0)) (flow.angle (point 0)) 2] := by
  have gravity : flow.configuration.gravityConnection = fun _ => homogeneousConnection spinScale := by
    change Runtime.configuration.gravityConnection = _
    rw [Runtime.configuration_eq, actual_gravityConnection]
  have timeSpin : diracSpinConnectionLift (homogeneousConnection spinScale) 0 = 0 := by
    simp only [diracSpinConnectionLift, homogeneousConnection,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm]
    simp [homogeneousContorsion, Fin.sum_univ_six]
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [flow.matterCoordinateDerivative point inside direction, gravity]
  rw [show flow.configuration.gaugeConnection = fun p => gaugePotential (flow.amplitude (p 0)) from rfl]
  rw [show flow.configuration.matter = fun p => movingMatter (flow.angle (p 0)) from rfl]
  fin_cases direction <;>
    simp [timeSpin, spatialMatter, gaugePotential, diracMatrixMatterAction_zero_matrix,
      p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix]

theorem LocalOrbit.primalKinetic_zero (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) = 0 := by
  have frame : flow.configuration.coframe point = homogeneousCoframe lapse := by
    change Runtime.configuration.coframe point = _
    rw [Runtime.configuration_eq, actual_coframe]
  have actualJet := flow.matterCovariantDerivative point inside
  have closed := kineticVector_closed (flow.amplitude (point 0)) (flow.angle (point 0))
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum at closed ⊢
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField] at closed ⊢
  rw [frame, actualJet]
  exact closed

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
