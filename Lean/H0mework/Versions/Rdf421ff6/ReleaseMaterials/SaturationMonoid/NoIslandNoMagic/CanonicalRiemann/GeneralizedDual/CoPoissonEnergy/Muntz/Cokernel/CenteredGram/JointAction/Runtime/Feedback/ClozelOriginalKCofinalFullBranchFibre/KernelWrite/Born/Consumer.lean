import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.QueryReceipt

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.MacroNext
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
attribute [local irreducible] AS.localNativeReceipt
local instance consumerGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The actual admission input consumes the installed Joint's complete written stock. -/
theorem actual_written_source_stock :
 ∃ carried,
  (bornPacket observation nontrivial half depth ordinal).2.2.1.nextPairInventory
   (bornPacket observation nontrivial half depth ordinal).2.1.1=some carried ∧
  ∀ event∈(installedWritten observation nontrivial half depth ordinal).trace,event∈carried.trace := by
 obtain ⟨carried,written,preserved⟩:=
  original_native_seed_installed observation nontrivial half depth ordinal
   (writerBorn observation nontrivial half depth ordinal)
 refine ⟨carried,written,?_⟩
 intro event belongs
 apply preserved event
 apply J.Past.current_written_preserved
 exact Eq.mp
  (congrArg (fun inventory => event∈inventory.trace)
   (installed_written observation nontrivial half depth ordinal)) belongs

/-- The complete source inventory enters the literal seed created by this admission. -/
theorem actual_written_native_seed :
 ∀ event∈(installedWritten observation nontrivial half depth ordinal).trace,
 admissionEvent (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal) event∈
  (nextSeed observation nontrivial half depth ordinal).trace := by
 obtain ⟨carried,written,preserved⟩:=actual_written_source_stock observation nontrivial half depth ordinal
 intro event belongs
 exact native_seed_query_receipt (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal) carried written event (preserved event belongs)

/-- The actual new primary face reads the complete old source receipt, at the canonical next occurrence. -/
theorem actual_written_next_primary :
 ∀ event∈(installedWritten observation nontrivial half depth ordinal).trace,
 admissionEvent (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal) event∈
  (nextRootRead observation nontrivial half depth ordinal).1.1.1.1.2.1.trace := by
 intro event belongs
 exact native_seed_root_receipt (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal)
  (FR.jointCode (RSource.code observation nontrivial half)) rfl
  (nextFrame observation nontrivial half depth ordinal) _
  (actual_written_native_seed observation nontrivial half depth ordinal event belongs)

/-- Every paid event of the actual executed born query is consumed by that next primary inventory. -/
theorem actual_query_next_primary :
 ∀ event∈(SourceOperationPaidRelations.exposure
  (RelationAction.bornResult observation nontrivial half depth ordinal).2.1.2).trace,
 admissionEvent (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal) event∈
  (nextRootRead observation nontrivial half depth ordinal).1.1.1.1.2.1.trace := by
 intro event belongs
 exact actual_written_next_primary observation nontrivial half depth ordinal event
  (installed_paid_trace observation nontrivial half depth ordinal event belongs)

/-- The real next Joint writes the entire original inventory, through its existing physical lift. -/
theorem actual_written_next_joint :
 ∀ event∈(installedWritten observation nontrivial half depth ordinal).trace,
 ReceiptLift.liftEvent (admissionEvent (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal) event)∈
  (nextWritten observation nontrivial half depth ordinal).trace := by
 intro event belongs
 exact native_seed_joint_receipt (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal)
  (FR.jointCode (RSource.code observation nontrivial half)) rfl
  (nextFrame observation nontrivial half depth ordinal) _
  (actual_written_native_seed observation nontrivial half depth ordinal event belongs)

/-- Its actual complete write-back consumes every paid event of the executed source query. -/
theorem actual_query_next_joint :
 ∀ event∈(SourceOperationPaidRelations.exposure
  (RelationAction.bornResult observation nontrivial half depth ordinal).2.1.2).trace,
 ReceiptLift.liftEvent (admissionEvent (D.factory observation nontrivial half)
  (bornPacket observation nontrivial half depth ordinal) event)∈
  (nextWritten observation nontrivial half depth ordinal).trace := by
 intro event belongs
 exact actual_written_next_joint observation nontrivial half depth ordinal event
  (installed_paid_trace observation nontrivial half depth ordinal event belongs)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.MacroNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
