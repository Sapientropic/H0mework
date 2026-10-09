import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUnitSchur

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedConstraintWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open scoped Matrix BigOperators
attribute [local irreducible] originalChange originalReadback originalJacobi dressedWindowPolarization nativeHessian

/-- The original left null identity removes the classical block and retains the actual quantum constraint. -/
theorem source_cokernel_actual_pencil (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) :
    sourceCokernel p (dressedNativeWindowPencil event transfer p lambda T*ᵥa)=
      -sourceCokernel p (dressedWindowPolarization event transfer p lambda T*ᵥa) := by
  have classical : sourceCokernel p (nativeFourierHessian nativeHessian p*ᵥa)=0 := by
    rw [nativeActionFourierHessian_original]
    exact (source_compatibility_nine p _).mp (source_compatibility_euler p a)
  rw [dressedNativeWindowPencil,Matrix.sub_mulVec,Matrix.smul_mulVec,map_sub,map_smul,classical,smul_zero,zero_sub]

end LowEnergy.GaussComposite.ActualDressedConstraintWard
