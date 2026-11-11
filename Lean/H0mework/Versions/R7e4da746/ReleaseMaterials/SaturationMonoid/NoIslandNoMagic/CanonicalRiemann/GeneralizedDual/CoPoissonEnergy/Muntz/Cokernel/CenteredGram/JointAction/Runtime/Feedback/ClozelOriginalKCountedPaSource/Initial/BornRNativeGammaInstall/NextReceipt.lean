import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.BoundaryFeedback
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalGammaNextReceipt"

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory)
export BornRCanonicalMethodRuntime.Lower (Value groups)
end A
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace Cfa
export ActualCofinalSourceAction
  (sourceBorn nativePacket selected bornStock born_inventory packetTransport actual_next_packet)
export ActualCofinalSourceAction.D (packetAt)
export ActualCofinalSourceAction.AS (AdmissionPacket)
end Cfa
namespace Q
export PhysicalGammaActionQuery (environment request receipt)
end Q
namespace BF
export PhysicalGammaBoundaryFeedback (StepIndex bornStep receiptSegment)
end BF
namespace R
export ActualCofinalSourceAction.SourceReceiptOccurrence
  (ExecutionAt atBirth atBirth_request_position atBirth_segment_position)
export ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt (reindex reindex_length reindex_step reindex_positions)
end R
namespace P
export SourceOperationPaidRelations (words)
end P
namespace RF
export BornRWordPaWriteback.RelationFeedback (RelationAt jointRelation_member)
end RF
namespace Cx
export CofinalRelationGeneratedComplex (natComplex completion_kills_generated_differential)
end Cx

open private born_packet_literal from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.BoundaryFeedback
open private jointHistoryAt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Transport

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance levelGroups (grade : Nat) : ∀ target, AddCommGroup (A.Value A.W grade target) :=
  A.groups A.W grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (depth ordinal : Nat)
local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

private def originalBirth : R.ExecutionAt (Cfa.sourceBorn factory method.source) :=
  ⟨Cfa.bornStock factory method.source, Cfa.born_inventory factory method.source,
    Q.environment observation nontrivial half method.source,
    ActualNativeRelationTransport.decoded_environment
      (Cfa.selected factory method.source) (Cfa.nativePacket factory method.source).2.2.1,
    Q.request observation nontrivial half method.source, Q.receipt observation nontrivial half method.source,
    BF.receiptSegment observation nontrivial half method.source⟩

local notation "original" => originalBirth observation nontrivial half depth ordinal method
local notation "recognition" => born_packet_literal observation nontrivial half depth ordinal method
local notation "sourceBorn" => Cfa.sourceBorn factory method.source
local notation "sourceSite" => site (update+2)

/-- Carry the original paid physical Gamma block into its already identified cofinal packet. -/
def actualBirth : R.ExecutionAt (site (update+2)) :=
  R.reindex sourceBorn sourceSite method.source.2.2.2.down recognition original

local notation "birth" => actualBirth observation nontrivial half depth ordinal method
local notation "AtomIndex" => BF.StepIndex observation nontrivial half method.source

private def actualIndex (index : AtomIndex) : Fin (P.words (birth).paid).length :=
  Fin.cast (R.reindex_length sourceBorn sourceSite method.source.2.2.2.down recognition original).symm index

def actualStep (index : AtomIndex) :=
  (birth).step (actualIndex observation nontrivial half depth ordinal method index)

theorem actualStep_literal (index : AtomIndex) :
    HEq (actualStep observation nontrivial half depth ordinal method index)
      (BF.bornStep observation nontrivial half method.source index) :=
  R.reindex_step sourceBorn sourceSite method.source.2.2.2.down recognition original index

abbrev SupportIndex (index : AtomIndex) :=
  ActualCofinalSourceAction.SourceReceiptOccurrence.SupportIndex factory sourceSite
    (birth).stock (birth).installed (actualStep observation nontrivial half depth ordinal method index)

local notation "sourceAtom" => actualStep observation nontrivial half depth ordinal method

local notation "nextSite" => site ((update+2)+1)
local notation "nextBorn" => Cfa.sourceBorn factory sourceSite

private theorem following_literal :
    Cfa.packetTransport (sourceSite).2.2.2.down nextBorn = nextSite :=
  (Cfa.actual_next_packet factory initial programme rfl (update+2)).symm

def nativeNextReceipt (index : AtomIndex) (item : SupportIndex observation nontrivial half depth ordinal method index) :
    R.ExecutionAt nextBorn :=
  R.atBirth factory sourceSite (birth).stock (birth).installed (sourceAtom index) item

local notation "nextNative" => nativeNextReceipt observation nontrivial half depth ordinal method
local notation "nextRecognition" => following_literal observation nontrivial half depth ordinal (update := update)

/-- The next receiver executes the support item at the transported paid atom's exact address. -/
def actualNextReceipt (index : AtomIndex) (item : SupportIndex observation nontrivial half depth ordinal method index) :
    R.ExecutionAt nextSite :=
  R.reindex nextBorn nextSite (sourceSite).2.2.2.down nextRecognition (nextNative index item)

local notation "execution" => actualNextReceipt observation nontrivial half depth ordinal method

theorem actualNextReceipt_position (index : AtomIndex) (item : SupportIndex observation nontrivial half depth ordinal method index) :
    (execution index item).request.position =
      (ActualNativeRelationTransport.SourceInventoryBlock.source factory sourceSite
        (birth).stock (birth).installed).before.length + (sourceAtom index).before.length :=
  (R.reindex_positions nextBorn nextSite (sourceSite).2.2.2.down nextRecognition (nextNative index item)).1.trans
    (R.atBirth_request_position factory sourceSite (birth).stock (birth).installed (sourceAtom index) item)

theorem actualNextReceipt_segment_position (index : AtomIndex) (item : SupportIndex observation nontrivial half depth ordinal method index) :
    (execution index item).segment.before.length = (nextNative index item).segment.before.length :=
  (R.reindex_positions nextBorn nextSite (sourceSite).2.2.2.down nextRecognition (nextNative index item)).2

attribute [local irreducible] actualNextReceipt actualBirth actualStep

private def relationFromExecution
    {packet : Cfa.AdmissionPacket (W := A.W) (X := A.X) (s := slot)}
    (receipt : R.ExecutionAt packet) : RF.RelationAt packet where
  inventory := receipt.stock
  installed := receipt.installed
  val := Finsupp.single receipt.request.expression 1 -
    Finsupp.single (.const (receipt.request.expression.eval receipt.decoder)) 1
  member := receipt.boundary_written

def nextReceiptRelation (index : AtomIndex) (item : SupportIndex observation nontrivial half depth ordinal method index) :
    RF.RelationAt nextSite :=
  relationFromExecution (execution index item)

private def jointFromRelation
    {packet : Cfa.AdmissionPacket (W := A.W) (X := A.X) (s := slot)}
    (relation : RF.RelationAt packet) : (jointHistoryAt packet).relationClosure :=
  ⟨liftMap (R := ℤ) relation.val, by
    simpa only [jointHistoryAt, SourceInventoryExecutionFeed.history_relation_space] using
      RF.jointRelation_member packet relation⟩

local notation "nextJoint" => jointHistoryAt nextSite

def nextReceiptJointBoundary (index : AtomIndex)
    (item : SupportIndex observation nontrivial half depth ordinal method index) :
    (nextJoint).relationClosure :=
  jointFromRelation (nextReceiptRelation observation nontrivial half depth ordinal method index item)

theorem actual_next_receipt_completion (index : AtomIndex) (item : SupportIndex observation nontrivial half depth ordinal method index) :
    (nextJoint).completionProjection (((Cx.natComplex nextJoint).d 0 1).hom
      (nextReceiptJointBoundary observation nontrivial half depth ordinal method index item)) = 0 :=
  Cx.completion_kills_generated_differential nextJoint
    (nextReceiptJointBoundary observation nontrivial half depth ordinal method index item)

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
