import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Runtime
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Outgoing.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Target.Coface

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation
 (epoch targetCoface optionalTargetCoface)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (datum query query_unique actualOccurrence root visit queryLaw resultLaw consumerLaw compilationLaw)
end Shared
end A
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
 (programme runtime frameAt)
end R
namespace O
export SourceOperationInquiry.Context.Outgoing (scalarStock pairStock material)
end O
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target, AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
abbrev lowBareInitial := SourceGeneratedInquiryReceiptAction.bornFrame frame configuration
abbrev lowStock := SourceOperationPaidRelations.exposure (actualMaterial frame configuration).state.2
abbrev outgoingMaterial := O.material frame configuration
abbrev outgoingScalar := O.scalarStock frame configuration
abbrev outgoingPair := O.pairStock frame configuration
def lowWritten := SourceHistoryCommon.seed (lowStock frame configuration) (outgoingScalar frame configuration)
def lowPairWritten := match (lowBareInitial frame configuration).pairInventory with
 | none => outgoingPair frame configuration
 | some prior => SourceHistoryCommon.seed prior (outgoingPair frame configuration)
def lowInitial := {lowBareInitial frame configuration with
 inventory:=some (lowWritten frame configuration)
 pairInventory:=some (lowPairWritten frame configuration)}
def lowSeed := SourceHistoryCommon.seed (lowWritten frame configuration)
 (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (lowInitial frame configuration).registered.input.expression))
abbrev lowProgramme := R.programme (lowSeed frame configuration)
abbrev lowRuntime := R.runtime (lowSeed frame configuration) (lowInitial frame configuration)
abbrev lowFrameAt := R.frameAt (lowSeed frame configuration) (lowInitial frame configuration)
abbrev bareGeneratedAction := SourceGeneratedInquiryReceiptAction.generatedAction frame configuration
abbrev Event := ExactTemporalCausalRootEventAt (old frame configuration).root.toAuthoritativeRoot.toLedgerRoot
 (old frame configuration).visit

def targetAt (event : Event frame configuration) : type_of%
 ((SourceGeneratedInquiryReceiptAction.birthProgram frame configuration).targetAt event) :=
 let receiver := lowInitial frame configuration
 let programme := lowProgramme frame configuration
 let original := (SourceGeneratedInquiryReceiptAction.birthProgram frame configuration).targetAt event
 let material := A.targetCoface original (SourceOperationInquiry.Context.Installation.component (A.epoch receiver))
 let configured := A.optionalTargetCoface material (A.Shared.datum receiver programme).component
 let withQuery := A.targetCoface configured (A.Shared.queryLaw (A.epoch receiver) programme)
 let withResult := A.targetCoface withQuery (A.Shared.resultLaw (A.epoch receiver) programme)
 let withConsumer := A.targetCoface withResult (A.Shared.consumerLaw (A.epoch receiver) programme)
 A.targetCoface withConsumer (A.Shared.compilationLaw (A.epoch receiver) programme)

def birthProgram : type_of% (SourceGeneratedInquiryReceiptAction.birthProgram frame configuration) where
 targetAt := targetAt frame configuration
abbrev generatedAction := (birthProgram frame configuration).generate (sourceEvent frame configuration)

def compilation (candidate : (old frame configuration).Query) : SourceNativeInquiryCompilationProgramAt
 (old frame configuration).root (old frame configuration).visit (old frame configuration).U7 (old frame configuration).calculus
 (old frame configuration).root.source.base.lawSurface candidate ((old frame configuration).emitInquiry candidate)
 ((old frame configuration).entryAt candidate) ((old frame configuration).authorityAt candidate) where
 compile := fun event => by
  cases A.Shared.query_unique frame configuration candidate
  exact .debtAdmission ((birthProgram frame configuration).generate event)

def state : RootInquiryStateAt
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered)
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt) where
 root := (old frame configuration).root
 visit := (old frame configuration).visit
 U7 := (old frame configuration).U7
 calculus := (old frame configuration).calculus
 Query := (old frame configuration).Query
 entryAt := (old frame configuration).entryAt
 authorityAt := (old frame configuration).authorityAt
 compilationProgramAt := compilation frame configuration
 compilationFaceAt := fun candidate => by
  cases A.Shared.query_unique frame configuration candidate
  exact { projection := ((old frame configuration).compilationFaceAt (A.Shared.query frame configuration)).projection
          active := ((old frame configuration).compilationFaceAt (A.Shared.query frame configuration)).active
          classifier_eq := ((old frame configuration).compilationFaceAt (A.Shared.query frame configuration)).classifier_eq
          project_heq := HEq.rfl }
 u7RootDisposition_commutes := by
  intro candidate _ _ impossible
  cases A.Shared.query_unique frame configuration candidate
  exact nomatch impossible

def sourcePresentation : RootInquiryStatePresentation where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
 state := .create (state frame configuration)
abbrev targetPresentation := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation
 (lowInitial frame configuration) (lowProgramme frame configuration)
abbrev sourceMaterial := (actualMaterial frame configuration,outgoingMaterial frame configuration,
 lowStock frame configuration,lowWritten frame configuration,lowPairWritten frame configuration,lowSeed frame configuration)

end SourceGeneratedInquiryReceiptAction.Configured
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
