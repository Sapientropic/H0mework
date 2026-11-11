import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.Reentry.Splice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordReentryConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open private total from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Source
namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice (nextFullValue next_full_value)
end SP
namespace W
export NativeSigma.Writeback (admissionValue)
end W
local instance reentryGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

def fullValue (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 W.admissionValue factory (AS.bornAfterNative native)
  (SP.nextFullValue (V:=L.Value (PairValue C.Value) (AS.bornAfterNative native).1)
   (WordNative.sourceFrame factory native) (WordNative.sourceBase factory native)
   (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory native))

theorem full_value (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 fullValue factory native=Recurrence.actualUpdatedValue factory native :=
 (congrArg (W.admissionValue factory (AS.bornAfterNative native))
  (SP.next_full_value (V:=L.Value (PairValue C.Value) (AS.bornAfterNative native).1)
   (WordNative.sourceFrame factory native) (WordNative.sourceBase factory native)
   (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory native))).trans
  (WordNative.full_value factory native)

attribute [local irreducible] AS.localNativeReceipt L.Value
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def originalFullValue := fullValue (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1))

theorem original_full_value : originalFullValue observation nontrivial half depth ordinal=
 Recurrence.actualUpdatedValue (D.factory observation nontrivial half)
  (originalNative observation nontrivial half depth (ordinal+1)) := full_value _ _

def physical := total
 (NativeSigma.collapseNative (D.factory observation nontrivial half)
  (AS.bornAfterNative (originalNative observation nontrivial half depth (ordinal+1)))
  (originalFullValue observation nontrivial half depth ordinal))

theorem physical_read : physical observation nontrivial half depth ordinal=
 Recurrence.physicalUpdated observation nontrivial half depth ordinal :=
 congrArg (fun value=>total
  (NativeSigma.collapseNative (D.factory observation nontrivial half)
   (AS.bornAfterNative (originalNative observation nontrivial half depth (ordinal+1))) value))
  (original_full_value observation nontrivial half depth ordinal)

/-- The actual common-source successor retains the original complete physical update. -/
theorem independent_original_R_square : physical observation nontrivial half depth ordinal≠0 := by
 rw [physical_read]
 exact Recurrence.original_updated_physical_nonzero observation nontrivial half depth ordinal

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordReentryConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
