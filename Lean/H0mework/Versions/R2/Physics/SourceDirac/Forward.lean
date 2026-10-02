import H0mework.Versions.R2.Physics.SourceDirac.Material
import H0mework.Versions.R2.Physics.SourceFamily.Scalar

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Dirac

open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariation
open StageNineLorentzConnectionVariationDensity StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariationDensity
open StageNineDiracDualFormNativeJointResidualCarrier SU7MotherLieAlgebra SU7MotherGaugeTheory Gauge

noncomputable section

theorem homogeneous_spin_time (spin : ℝ) :
    diracSpinConnectionLift (homogeneousConnection spin) 0 = 0 := by
  simp only [diracSpinConnectionLift, homogeneousConnection,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  simp [homogeneousContorsion, Fin.sum_univ_six]

theorem matter_covariant_time (step : ℕ) (point : BasePoint) :
    holonomicMatterCovariantDerivative (fieldAt step) point 0 =
      spinPairMatter (Complex.I * (phaseRate step : ℂ) * upper step point)
        (-Complex.I * (phaseRate step : ℂ) * lower step point) := by
  unfold holonomicMatterCovariantDerivative
  rw [matter_coordinate_derivative, field_matter, field_gravityConnection, field_connection]
  simp only [ite_true, homogeneous_spin_time, diracMatrixMatterAction_zero_matrix, add_zero]
  have gaugeZero : gaugePotential gaugeScale 0 = 0 := rfl
  rw [gaugeZero, p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix, add_zero]
  congr 1 <;> ring

theorem matter_covariant_spatial (step : ℕ) (point : BasePoint) (direction : Fin 3) :
    holonomicMatterCovariantDerivative (fieldAt step) point direction.succ =
      (((spinScale - gaugeScale : ℝ) : ℂ) / 2) •
        diracMatrixMatterAction (spinRotation direction) (spinPairMatter (upper step point) (lower step point)) := by
  unfold holonomicMatterCovariantDerivative
  rw [matter_coordinate_derivative, field_matter, field_gravityConnection, field_connection]
  simp only [Fin.succ_ne_zero, ite_false, zero_add]
  have gauge : gaugePotential gaugeScale direction.succ = gaugeScale • sourceColorP286Generator direction := by
    fin_cases direction <;> rfl
  rw [gauge, spinPair_spatialCovariantTerm]

private theorem time_kinetic (step : ℕ) (point : BasePoint) :
    Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := (fieldAt step).coframe point, derivative := 0 } 0)
      (holonomicMatterCovariantDerivative (fieldAt step) point 0) =
      ((phaseRate step : ℂ) / (clock step : ℂ)) • spinPairMatter (lower step point) (upper step point) := by
  rw [field_coframe, homogeneousInverseGamma (clock step) (ne_of_gt (clock_pos step)), matter_covariant_time]
  simp only [ite_true, coframeDiracMatrixMatterAction_smul_matrix]
  rw [smul_comm, spinPair_temporalKinetic, smul_smul]
  congr 1
  push_cast
  ring

private theorem spatial_kinetic (step : ℕ) (point : BasePoint) (direction : Fin 3) :
    Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := (fieldAt step).coframe point, derivative := 0 } direction.succ)
      (holonomicMatterCovariantDerivative (fieldAt step) point direction.succ) =
      (-((spinScale - gaugeScale : ℝ) : ℂ) / 2) • spinPairMatter (lower step point) (upper step point) := by
  rw [field_coframe, homogeneousInverseGamma (clock step) (ne_of_gt (clock_pos step)), matter_covariant_spatial]
  simp only [Fin.succ_ne_zero, ite_false, one_smul]
  have closed := spinPair_spatialKinetic spinScale gaugeScale direction (upper step point) (lower step point)
  rw [spinPair_spatialCovariantTerm] at closed
  exact closed

/-- The original kinetic operator consumes the actual phase derivative and
the generated Cartan/color locking at every physical spacetime point. -/
theorem kinetic_zero (step : ℕ) (point : BasePoint) :
    generatedContinuumMatterKineticVector (sourceAt step) 0 point
      (toContinuumPointField (fieldAt step) point) = 0 := by
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField]
  rw [Finset.smul_sum, Fin.sum_univ_succ, time_kinetic]
  simp_rw [spatial_kinetic]
  rw [Fin.sum_univ_three]
  have frequencyRatio : (phaseRate step : ℂ) / (clock step : ℂ) =
      3 * ((spinScale - gaugeScale : ℝ) : ℂ) / 2 := by
    unfold phaseRate
    push_cast
    have nonzero : (clock step : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (clock_pos step)
    field_simp
  rw [frequencyRatio]
  module

theorem conjugate_directional_zero (step : ℕ) (point : BasePoint) (variation : MatterCoordinateCarrier) :
    diracDualConjugateMatterDirectionalCoefficient (sourceAt step) (fieldAt step) variation point = 0 := by
  unfold diracDualConjugateMatterDirectionalCoefficient generatedContinuumDiracDualMatterVector
  rw [kinetic_zero, Scalar.yukawa_vector_zero]
  simp

theorem conjugate_channel_zero (step : ℕ) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual (sourceAt step) (fieldAt step) point).conjugateMatter = 0 :=
  funext (conjugate_directional_zero step point)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Dirac
