import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedChargeCore
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationWeightedChargePreparedActionReturn

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedGaussBalance
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumWeightedChargeActionWard GaussDiagonalHistory

/-- All native scalar and gauge derivatives remain in this source torque. -/
def sourceLockedNativeTorque : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussNativeForm.nativeAction.comp sourceLockedChargeCore-sourceLockedChargeCore.comp GaussNativeForm.nativeAction

def sourceLockedCoframeTorque : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussCoframeForm.coframeAction.comp sourceLockedChargeCore-sourceLockedChargeCore.comp GaussCoframeForm.coframeAction

def sourceLockedMatterTorque : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussMatterCore.matterAction.comp sourceLockedChargeCore-sourceLockedChargeCore.comp GaussMatterCore.matterAction

def sourceLockedYukawaTorque : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussYukawaOperator.originalAction.comp sourceLockedChargeCore-sourceLockedChargeCore.comp GaussYukawaOperator.originalAction

/-- The spin part can torque the complete physical momentum, so this term is retained. -/
def sourceLockedMomentumTorque (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest:=
  (momentumAction p).comp sourceLockedChargeCore-sourceLockedChargeCore.comp (momentumAction p)

/-- The momentum-transfer current includes every CAR and occupation contribution. -/
def sourceLockedMomentumCurrent (k : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest:=
  (momentumAction k).comp sourceLockedChargeCore

def sourceLockedWardCore (p k : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest:=
  sourceLockedNativeTorque+sourceLockedCoframeTorque+sourceLockedMatterTorque+
    sourceLockedMomentumTorque p+sourceLockedMomentumCurrent k+sourceLockedYukawaTorque

theorem sourceLockedFullSourceWard_generated (p k : PhysicalMomentum) (f : QuantumTest) :
    fullSourceAction (p+k) (sourceLockedChargeCore f)-sourceLockedChargeCore (fullSourceAction p f)=
      sourceLockedWardCore p k f := by
  simp only [fullSourceAction,physicalAction,momentumAction_add,diagonalAction,
    sourceLockedWardCore,sourceLockedNativeTorque,sourceLockedCoframeTorque,sourceLockedMatterTorque,
    sourceLockedMomentumTorque,sourceLockedMomentumCurrent,sourceLockedYukawaTorque,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,map_add]
  abel

def sourceLockedPairTorque (p k : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest:=
  (fullSourceAction (p+k)).comp sourceLockedPairCore-sourceLockedPairCore.comp (fullSourceAction p)

def sourceLockedWeightedWard (p k : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest:=
  weightCore.comp (sourceLockedWardCore p k)+(weightActionTorque (p+k)).comp sourceLockedChargeCore-
    sourceLockedPairTorque p k

/-- The actual raw temporal mode consumes the full source Ward and the complete normal-ordering pair torque. -/
theorem sourceLockedRawActionWard_generated (p k : PhysicalMomentum) (f : QuantumTest) :
    fullSourceAction (p+k) (sourceLockedRawChargeCore f)-
      sourceLockedRawChargeCore (fullSourceAction p f)=sourceLockedWeightedWard p k f := by
  have generated:=sourceLockedFullSourceWard_generated p k f
  simp only [sourceLockedRawCore_generated,sourceLockedWeightedWard,weightActionTorque,sourceLockedPairTorque,
    LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,map_sub]
  rw [←generated,map_sub]
  abel

/-- This is the original full Hamiltonian decomposition, with its retained subtraction and Yukawa unchanged. -/
theorem sourceLockedOriginalActionWard (p k : PhysicalMomentum) (f : QuantumTest) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
      PreparationVacuumActionDecomposition.actualCore (p+k)-PreparationVacuumActionDecomposition.retainedCore)
        (sourceLockedRawChargeCore f)-sourceLockedRawChargeCore
      ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
        PreparationVacuumActionDecomposition.actualCore p-PreparationVacuumActionDecomposition.retainedCore) f)=
          sourceLockedWeightedWard p k f := by
  rw [←PreparationVacuumActionDecomposition.physical_action_decomposition,
    ←PreparationVacuumActionDecomposition.physical_action_decomposition]
  exact sourceLockedRawActionWard_generated p k f

end LowEnergy.PreparationVacuumPhysicalLockedGaussBalance
