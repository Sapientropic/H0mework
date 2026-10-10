import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMSourceLockedCarrier
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.IndependentLockedConsumer
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineDynamicBreakingVacuum
open StageNineHolonomicField Stage9C.Material.SpinPair DiracExteriorMatterAction DiracCliffordRepresentation
open SourceQuantumScalarChart SourceQuantumResidualGaugeSlice SourceQuantumScalarOrbitDimensions
open PreparationVacuumPhysicalElectromagneticDirection PreparationPhysicalElectromagneticDirectionReturn
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily PreparationVacuumNativeFieldInjection
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationCoordinates
open PhysicalEMGaugeRealization ActualEMCompleteOrbit
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open scoped Matrix BigOperators

open LowEnergy.GaussComposite.ActualEMSourceDirection
example (mu : Fin 4) (n : Fin 3→ℝ) (i : Fin 3) :
    lockedAmplitude mu n (lorentzSlot mu (sourceSpinSlot i))=(n i:ℂ) := locked_amplitude_lorentz_read mu n i

example (n : Fin 3→ℝ) (point : BasePoint) :
    orbit (sourceBackgroundColor n)=0 ∧
    (∀j : Fin 3,sourceBackgroundBracket (sourceBackgroundColor n) (gaugeCoordinates sourceGauge j)+
      ∑k : Fin 3,sourceBackgroundIndex n j k • gaugeCoordinates sourceGauge k=0) ∧
    sourceBackgroundMatterAction n (actual.matter point)=0 ∧
    (actual.conjugateMatter point).comp (sourceBackgroundMatterAction n)=0 ∧
    sourceBackgroundFrame n*actual.coframe point-actual.coframe point*sourceBackgroundFrame n=0 := locked_actual_background n point

example : sourceRestLockedMixing 0 2 (0,1) (0,1)=(-1:ℂ) := locked_actual_charged_read 

end LowEnergy.GaussComposite.IndependentLockedConsumer
#print axioms LowEnergy.GaussComposite.ActualEMSourceDirection.locked_amplitude_lorentz_read
#print axioms LowEnergy.GaussComposite.ActualEMSourceDirection.locked_actual_background
#print axioms LowEnergy.GaussComposite.ActualEMSourceDirection.locked_actual_charged_read
