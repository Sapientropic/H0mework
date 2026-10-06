import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Action

/-! The time component of the existing charged Euler three-form on the complete temporal family. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
namespace SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality StageNineP286GaugeAuxiliaryVariation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineCoframeLocalDifferentiability StageNineMatterVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def temporalTest (data : P286LieBlockData) : P286GaugeOneForm :=
  fun direction => if direction = 0 then p286CoordinateEquiv data else 0

theorem scalar_test (potential : Potential) (point : BasePoint) (data : P286LieBlockData) :
    pointwiseScalarP286GaugeConnectionVariation (toContinuumPointField (primitive potential) point)
      (temporalTest data) = fun direction => if direction = 0 then scalarCharge data else 0 := by
  funext direction
  simp only [pointwiseScalarP286GaugeConnectionVariation, pointwiseP286GaugeConnectionMotherVariation,
    temporalTest, toContinuumPointField, primitive]
  split_ifs
  · simp only [LinearEquiv.symm_apply_apply, Stage10.Runtime.configuration_eq, actual_scalar]
    rw [scalarCharge, Stage10.Runtime.source_eq]
  · simp [p286LieBlockEmbed_zero, scalarMotherLieAction]

theorem matter_test (potential : Potential) (point : BasePoint) (data : P286LieBlockData) :
    pointwiseMatterP286GaugeConnectionVariation (toContinuumPointField (primitive potential) point)
      (temporalTest data) = fun direction => if direction = 0 then matterCharge data point else 0 := by
  funext direction
  simp only [pointwiseMatterP286GaugeConnectionVariation, pointwiseP286GaugeConnectionMotherVariation,
    temporalTest, toContinuumPointField, primitive]
  split_ifs
  · simp only [LinearEquiv.symm_apply_apply, matterCharge]
  · simp [p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix]

theorem scalar_pair_symmetric (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second = scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re]
  ring

theorem charged_scalar_time (potential : Potential) (point : BasePoint) (data : P286LieBlockData) :
    scalarGaugeConnectionKineticFirstVariationDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point)
      (pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField (primitive potential) point) (temporalTest data)) =
      -scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point)) / lapse^2 := by
  have derivative : holonomicScalarCovariantDerivative (primitive potential) point =
      fun direction => if direction = 0 then scalarCharge (potential point) else 0 :=
    funext (scalar_derivative potential point)
  rw [scalar_test, Stage10.Runtime.source_eq]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField]
  rw [derivative]
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart]
  have coframe : (primitive potential).coframe point = actual.coframe point := by
    simp only [primitive, Stage10.Runtime.configuration_eq]
  rw [coframe, LowEnergy.Response.ScalarSignature.actual_metric_inverse]
  have zeroPair : scalarCoordinatePairingRe 0 0 = 0 := by simp [scalarCoordinatePairingRe]
  simp [Matrix.diagonal_apply, Fin.sum_univ_four, zeroPair]
  rw [scalar_pair_symmetric (scalarCharge (potential point))]
  ring

theorem charged_dirac_time (potential : Potential) (point : BasePoint) (data : P286LieBlockData) :
    matterGaugeConnectionFirstVariationDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point)
      (pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField (primitive potential) point) (temporalTest data)) = 0 := by
  rw [matter_test, Stage10.Runtime.source_eq]
  unfold matterGaugeConnectionFirstVariationDensity matterGaugeConnectionVariationVector
    matterGaugeKineticSum
  simp only [toContinuumPointField, primitive, matterDualFrameRelative_chartZero,
    matterDerivativeFrameRelative_zeroChart]
  have coframe : Stage10.Runtime.configuration.coframe point = homogeneousCoframe lapse := by
    rw [Stage10.Runtime.configuration_eq, actual_coframe]
  rw [coframe]
  simp only [Fin.sum_univ_four, show (1 : LorentzianIndex) ≠ 0 by decide,
    show (2 : LorentzianIndex) ≠ 0 by decide, show (3 : LorentzianIndex) ≠ 0 by decide,
    if_true, if_false, map_zero, add_zero]
  rw [homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
  simp only [coframeDiracMatrixMatterAction_smul_matrix]
  rw [smul_comm, map_smul, temporal_dual_zero, smul_zero]
  rfl

theorem charged_time_coefficient (potential : Potential) (point : BasePoint) (data : P286LieBlockData) :
    formNativeChargedGaugeFirstCoefficient Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) (temporalTest data) =
      -scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point)) / lapse := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [charged_scalar_time, charged_dirac_time, add_zero]
  simp only [generatedVolumeDensity, toContinuumPointField, primitive]
  rw [Stage10.Runtime.configuration_eq, actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  field_simp [ne_of_gt lapse_pos]

theorem charged_gauss_projection (potential : Potential) (point : BasePoint) (data : P286LieBlockData) :
    p286CoordinateLiePairing (p286CoordinateEquiv data)
      (formNativeChargedGaugeThreeForm Stage10.Runtime.source 0 point
        (toContinuumPointField (primitive potential) point) 3) =
      -scalarCoordinatePairingRe (scalarCharge data) (scalarCharge (potential point)) / lapse := by
  have result := formNativeChargedGaugeThreeForm_evaluation Stage10.Runtime.source 0 point
    (toContinuumPointField (primitive potential) point) (temporalTest data)
  rw [charged_time_coefficient] at result
  have zeroPair (value : P286CoordinateCarrier) : p286CoordinateLiePairing 0 value = 0 := by
    simp [p286CoordinateLiePairing, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]
  simpa [p286GaugeOneFormThreeFormWedgeCoefficient, temporalTest,
    Fin.sum_univ_four, oneWedgeThreeSign, missingTripleOfOneForm, zeroPair] using result

end
end SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
