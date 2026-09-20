import H0mework.Physics.LowEnergyMatterSpace.GaugeLift
import H0mework.Physics.LowEnergyMatterSpace.Spatial
import H0mework.Physics.SpinPair.Scalar

/-! Smooth occupied test fields enter the original holonomic differential operator. -/
set_option autoImplicit false
open scoped Matrix Kronecker
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction ActiveSector
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineP286GaugeConnectionVariationDensity
open StageNineDiracDualFormNativeMotherAction StageNineDynamicBreakingVacuum
open PointwiseDiracSpinConnectionLift SU7MotherLieAlgebra Stage9C.Material.SpinPair
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
noncomputable section

def tripletCoordinateMap : MatterFiber →L[ℂ] MatterCoordinateCarrier :=
  LinearMap.toContinuousLinearMap ((matterCoordinateEquiv.toLinearMap.comp tripletLift).comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : SourceIndex => ℂ)).toLinearEquiv.toLinearMap)

def tripletField (profile : BasePoint → MatterFiber) : StageNineHolonomicConfiguration :=
  { actual with matter := fun point => tripletLift (profile point) }

theorem tripletField_directional (profile : BasePoint → MatterFiber)
    (derivative : BasePoint →L[ℝ] MatterFiber) (point : BasePoint)
    (differentiates : HasFDerivAt profile derivative point) (mu : LorentzianIndex) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun p => matterCoordinateEquiv ((tripletField profile).matter p)) point mu)=
      tripletLift (derivative (coordinateDirection mu)) := by
  have generated := (tripletCoordinateMap.restrictScalars ℝ).hasFDerivAt.comp point differentiates
  change HasFDerivAt (fun p => matterCoordinateEquiv (tripletLift (profile p))) _ point at generated
  unfold fieldDirectionalDerivative tripletField
  rw [generated.fderiv]
  simp [tripletCoordinateMap]
  rfl

def sourceConnectionMatrix (point : BasePoint) (mu : LorentzianIndex) : SourceMatrix :=
  (diracSpinConnectionLift (actual.gravityConnection point) mu) ⊗ₖ
    (1 : Matrix (Fin 3) (Fin 3) ℂ)+
      (1 : DiracMatrix) ⊗ₖ tripletGaugeMatrix (actual.gaugeConnection point mu)

theorem sourceConnectionMatrix_lift (point : BasePoint) (mu : LorentzianIndex)
    (v : SourceIndex → ℂ) :
    tripletLift (sourceConnectionMatrix point mu*ᵥv)=
      diracMatrixMatterAction (diracSpinConnectionLift (actual.gravityConnection point) mu)
        (tripletLift v)+
      diracExteriorMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) (tripletLift v) := by
  rw [sourceConnectionMatrix,Matrix.add_mulVec,map_add,tripletLift_tensor,tripletLift_spin_gauge]
  simp [tripletLift,Matrix.one_apply,diracMatrixMatterAction]

theorem tripletField_covariant (profile : BasePoint → MatterFiber)
    (derivative : BasePoint →L[ℝ] MatterFiber) (point : BasePoint)
    (differentiates : HasFDerivAt profile derivative point) (mu : LorentzianIndex) :
    holonomicMatterCovariantDerivative (tripletField profile) point mu=
      tripletLift ((fun index => derivative (coordinateDirection mu) index)+
        sourceConnectionMatrix point mu*ᵥ(fun index => profile point index)) := by
  unfold holonomicMatterCovariantDerivative
  rw [tripletField_directional profile derivative point differentiates mu,map_add,
    sourceConnectionMatrix_lift]
  exact add_assoc _ _ _

theorem tripletField_yukawa_zero (profile : BasePoint → MatterFiber) (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (tripletField profile) point)=0 := by
  unfold generatedContinuumDiracDualYukawaVector
  change diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm
      (scalarFrameRelativeCoordinates positiveSmoothUnifiedSource 0 point (actual.scalar point)))
    (matterFrameRelative positiveSmoothUnifiedSource 0 point (tripletLift (profile point)))=0
  rw [actual_scalar,scalarFrameRelativeCoordinates_zeroChart,matterFrameRelative_zeroChart]
  simp only [sourceGeneratedVacuumCoordinates,LinearEquiv.symm_apply_apply]
  exact triplet_yukawa_zero _

def primalJet (profile : BasePoint → MatterFiber) (derivative : BasePoint →L[ℝ] MatterFiber)
    (point : BasePoint) : SourceIndex → ℂ :=
  Complex.I • ∑ mu, (sourceInverseGamma mu ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))*ᵥ
    ((fun index => derivative (coordinateDirection mu) index)+
      sourceConnectionMatrix point mu*ᵥ(fun index => profile point index))

theorem original_primal_differential (profile : BasePoint → MatterFiber)
    (derivative : BasePoint →L[ℝ] MatterFiber) (point : BasePoint)
    (differentiates : HasFDerivAt profile derivative point) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (tripletField profile) point)=tripletLift (primalJet profile derivative point) := by
  rw [generatedContinuumDiracDualMatterVector,tripletField_yukawa_zero,add_zero]
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart,toContinuumPointField]
  simp_rw [tripletField_covariant profile derivative point differentiates]
  rw [primalJet,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  rw [tripletLift_tensor]
  simp [tripletLift,Matrix.one_apply,sourceInverseGamma_original point,tripletField]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
