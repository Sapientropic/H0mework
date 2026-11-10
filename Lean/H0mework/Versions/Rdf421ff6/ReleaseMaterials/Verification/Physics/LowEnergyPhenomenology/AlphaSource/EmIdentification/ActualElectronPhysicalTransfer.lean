import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronAmputatedCharge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronPhysicalNormalization
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource CanonicalGradedCharge SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert PreparationPhysicalPhaseGaugeRealization
open GaussFockPair
open GaussCoreHilbert ActualCompositeFieldCurrent ActualCompositeGaugeBand ActualCompositeOriginWard
open ActualEMOriginWard PhysicalEMGaugeRealization
open PreparationVacuumFieldConstraintResponse PreparationVacuumActionDecomposition
open PreparationVacuumFullElectricWard CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open scoped InnerProductSpace

/-- Both independent physical momenta consume the same amputated complete N3 event. -/
theorem actual_electron_amputated_physical_ward (p k : PhysicalMomentum) (leg : CompositeLeg) :
    (if leg.dual then (-1:ℂ) else 1) •
      ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (p+k)-retainedCore)
        (actualElectronAmputatedLeg leg))-
      compositeChargeCore ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore)
        (actualElectronAmputatedLeg leg))=
    configurationTorque sourcePhaseGaugeLie (actualElectronAmputatedLeg leg)+
      CanonicalPhysicalWardCore.currentAction k sourcePhaseGaugeLie (actualElectronAmputatedLeg leg)+
      pairCurrent k sourcePhaseGaugeLie (actualElectronAmputatedLeg leg)+
      yukawaTorque sourcePhaseGaugeLie (actualElectronAmputatedLeg leg) := by
  have original := em_origin_original_action_ward p k (actualElectronAmputatedLeg leg)
  rw [←composite_charge_original,actual_electron_amputated_charge,map_smul] at original
  exact original

/-- This is the original transferred current, distinct from the Fourier parameter of rawForm. -/
def actualElectronTransferredCurrent (k : PhysicalMomentum) (left right : CompositeLeg) : ℂ :=
  sourcePair (actualElectronAmputatedLeg left)
    (CanonicalPhysicalWardCore.currentAction k sourcePhaseGaugeLie (actualElectronAmputatedLeg right))

/-- Configuration, full CAR pair current, Yukawa torque and both physical action operators remain in the vertex. -/
theorem actual_electron_transferred_current_source (p k : PhysicalMomentum) (left right : CompositeLeg) :
    actualElectronTransferredCurrent k left right=
      sourcePair (actualElectronAmputatedLeg left)
        ((if right.dual then (-1:ℂ) else 1) •
          ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (p+k)-retainedCore)
            (actualElectronAmputatedLeg right))-
          compositeChargeCore ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore)
            (actualElectronAmputatedLeg right))-
          configurationTorque sourcePhaseGaugeLie (actualElectronAmputatedLeg right)-
          pairCurrent k sourcePhaseGaugeLie (actualElectronAmputatedLeg right)-
          yukawaTorque sourcePhaseGaugeLie (actualElectronAmputatedLeg right)) := by
  have original := actual_electron_amputated_physical_ward p k right
  unfold actualElectronTransferredCurrent
  congr 1
  rw [original]
  abel

end LowEnergy.GaussComposite.ActualElectronPhysicalNormalization
