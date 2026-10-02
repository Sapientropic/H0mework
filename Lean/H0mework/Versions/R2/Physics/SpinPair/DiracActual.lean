import H0mework.Physics.SpinPair.Dirac
import H0mework.Versions.R2.Physics.SpinPair.Scalar
import H0mework.Versions.R2.Physics.SpinPair.Derivatives
import H0mework.Versions.R2.Physics.Homogeneous.CartanActual

/-! The original primal Dirac Euler vector vanishes on the shared actual.
Both its phase derivative and source Cartan connection are consumed here. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariation
open StageNineLorentzConnectionVariationDensity StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariationDensity
open SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

theorem homogeneousInverseGamma (scale : ℝ) (nonzero : scale ≠ 0) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma { coframe := homogeneousCoframe scale, derivative := 0 } direction =
      (if direction = 0 then ((scale⁻¹ : ℝ) : ℂ) else 1) • diracGamma direction := by
  unfold inverseCoframeDiracGamma
  rw [homogeneousCoframe_inv scale nonzero]
  fin_cases direction <;> simp [homogeneousCoframe, Fin.sum_univ_four]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  exact map_inv₀ (algebraMap ℝ ℂ) scale

private theorem homogeneousSpinLift_time (spin : ℝ) :
    diracSpinConnectionLift (homogeneousConnection spin) 0 = 0 := by
  simp only [diracSpinConnectionLift, homogeneousConnection,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  simp [homogeneousContorsion, Fin.sum_univ_six]

theorem actual_matterCovariant_time (point : BasePoint) :
    holonomicMatterCovariantDerivative actual point 0 =
      spinPairMatter (Complex.I*(frequency : ℂ)*upperPhase point)
        (-Complex.I*(frequency : ℂ)*lowerPhase point) := by
  unfold holonomicMatterCovariantDerivative
  rw [actual_matterCoordinateDerivative, actual_matter, actual_gravityConnection, actual_gaugeConnection]
  simp only [ite_true, homogeneousSpinLift_time, diracMatrixMatterAction_zero_matrix, add_zero]
  have gaugeZero : gaugePotential gaugeScale 0 = 0 := rfl
  rw [gaugeZero, p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix, add_zero]
  congr 1 <;> ring

theorem actual_matterCovariant_spatial (point : BasePoint) (direction : Fin 3) :
    holonomicMatterCovariantDerivative actual point direction.succ =
      (((spinScale-gaugeScale : ℝ) : ℂ) / 2) •
        diracMatrixMatterAction (spinRotation direction) (spinPairMatter (upperPhase point) (lowerPhase point)) := by
  unfold holonomicMatterCovariantDerivative
  rw [actual_matterCoordinateDerivative, actual_matter, actual_gravityConnection, actual_gaugeConnection]
  simp only [Fin.succ_ne_zero, ite_false, zero_add]
  have gauge : gaugePotential gaugeScale direction.succ = gaugeScale • sourceColorP286Generator direction := by
    fin_cases direction <;> rfl
  rw [gauge, spinPair_spatialCovariantTerm]

theorem actual_matterTimeKinetic (point : BasePoint) :
    Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } 0)
      (holonomicMatterCovariantDerivative actual point 0) =
      ((frequency : ℂ) / (lapse : ℂ)) • spinPairMatter (lowerPhase point) (upperPhase point) := by
  rw [actual_coframe, homogeneousInverseGamma lapse (ne_of_gt lapse_pos), actual_matterCovariant_time]
  simp only [ite_true, coframeDiracMatrixMatterAction_smul_matrix]
  rw [smul_comm, spinPair_temporalKinetic, smul_smul]
  congr 1
  push_cast
  ring

theorem actual_matterSpatialKinetic (point : BasePoint) (direction : Fin 3) :
    Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } direction.succ)
      (holonomicMatterCovariantDerivative actual point direction.succ) =
      (-((spinScale-gaugeScale : ℝ) : ℂ) / 2) • spinPairMatter (lowerPhase point) (upperPhase point) := by
  rw [actual_coframe, homogeneousInverseGamma lapse (ne_of_gt lapse_pos), actual_matterCovariant_spatial]
  simp only [Fin.succ_ne_zero, ite_false, one_smul]
  have closed := spinPair_spatialKinetic spinScale gaugeScale direction (upperPhase point) (lowerPhase point)
  rw [spinPair_spatialCovariantTerm] at closed
  exact closed

theorem actual_kineticVector_zero (point : BasePoint) :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField actual point) = 0 := by
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField]
  rw [Finset.smul_sum, Fin.sum_univ_succ, actual_matterTimeKinetic]
  simp_rw [actual_matterSpatialKinetic]
  rw [Fin.sum_univ_three]
  have frequencyRatio : (frequency : ℂ) / (lapse : ℂ) =
      3 * ((spinScale-gaugeScale : ℝ) : ℂ) / 2 := by
    unfold frequency
    push_cast
    have nonzero : (lapse : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt lapse_pos
    field_simp
  rw [frequencyRatio]
  module

theorem actual_conjugateMatterEuler_zero (point : BasePoint) (variation : MatterCoordinateCarrier) :
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource actual variation point = 0 := by
  unfold diracDualConjugateMatterDirectionalCoefficient generatedContinuumDiracDualMatterVector
  rw [actual_kineticVector_zero, actual_yukawaVector_zero]
  simp

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
