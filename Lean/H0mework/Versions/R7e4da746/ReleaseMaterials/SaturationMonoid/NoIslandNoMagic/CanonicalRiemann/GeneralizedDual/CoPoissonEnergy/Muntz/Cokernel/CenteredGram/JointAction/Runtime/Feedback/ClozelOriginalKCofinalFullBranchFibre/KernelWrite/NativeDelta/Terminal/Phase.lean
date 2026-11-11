import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open private collapse_native_sub from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Source
namespace WB
export NativeSigma.Writeback (nativeInverseValue nativeFace ReceiptAt original_sigma_root_consumer)
end WB
namespace Next
export BornInstalledJoint.MacroNext (nextNative nextPhase nextRootRead born_whole born_next_current)
end Next
local instance phaseGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
attribute [local irreducible] AS.localNativeReceipt
private theorem collapsed_zero (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket) :
 NativeSigma.collapseNative factory packet 0=0 := by
 simpa only [sub_self] using (collapse_native_sub factory packet 0 0)

private theorem receipt_unsound (native : NativeSigma.NativePacket) (constraint : Prop)
 (phase : ResidualDispositionOutcome (WB.nativeFace native))
 (receipt : WB.ReceiptAt native constraint phase) (refutes : ¬constraint) :
 ∃ (obstruction : GeneratedUnsoundRelationObstructionAt (WB.nativeFace native))
   (coordinate : GeneratedRelationResidualCoordinateAt (WB.nativeFace native)),
 phase=.unsound obstruction coordinate := by
 cases phase with
 | faithful _ _ _ => exact False.elim (refutes receipt.1.down)
 | unsound obstruction coordinate => exact ⟨obstruction,coordinate,rfl⟩
 | kernelResidual _ _ _ => exact False.elim (refutes receipt.1.down)
 | coverageResidual _ _ _ => exact False.elim (refutes receipt.1.down)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The complete native inverse is nonzero by the independent original physical terminal. -/
theorem actual_native_inverse_nonzero :
 WB.nativeInverseValue (originalNative observation nontrivial half depth (ordinal+1)) ≠ 0 := by
 intro zero
 have branchZero : inverseBranches observation nontrivial half depth (ordinal+1)=0 := by
  exact (congrArg (NativeSigma.collapseNative (NativeSigma.originalFactory observation nontrivial half)
   (NativeSigma.originalPacket observation nontrivial half depth (ordinal+1))) zero).trans
   (collapsed_zero _ _)
 have read := actual_inverse_source_readback observation nontrivial half depth (ordinal+1)
 rw [branchZero, map_zero] at read
 have difference : D.input observation nontrivial half depth (ordinal+1)-
  D.input observation nontrivial half depth ordinal=0 :=
  (actual_increment_successor observation nontrivial half depth ordinal).symm.trans read.symm
 exact actual_input_fixed_terminal observation nontrivial half depth ordinal (sub_eq_zero.mp difference)

/-- The original installed phase generates its own unsound obstruction and full coordinate. -/
theorem actual_next_phase_unsound : type_of% (receipt_unsound _ _ _
 (WB.original_sigma_root_consumer observation nontrivial half depth (ordinal+1))
 (actual_native_inverse_nonzero observation nontrivial half depth ordinal)) :=
 receipt_unsound _ _ _
  (WB.original_sigma_root_consumer observation nontrivial half depth (ordinal+1))
  (actual_native_inverse_nonzero observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
