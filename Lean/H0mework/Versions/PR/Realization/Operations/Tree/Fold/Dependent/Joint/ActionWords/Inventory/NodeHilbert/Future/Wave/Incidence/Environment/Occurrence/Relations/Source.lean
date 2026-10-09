import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Consumer
import H0mework.Realization.Operations.Execution.Coefficients.Words
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedOccurrenceRelations
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {S : Type u} {A X : S → Type u} [∀ slot,AddCommGroup (A slot)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=A) (Var:=X) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
abbrev physical := SourceOperationInquiry.Context.Installation.materialAt frame occurrence
abbrev paid := (physical frame occurrence).paid
abbrev before := (paid frame occurrence).environment
abbrev increment := (physical frame occurrence).nextRaw.environment-(before frame occurrence)
abbrev relations := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.relations (R:=ℤ) (paid frame occurrence)
abbrev word := relationMap (R:=ℤ) (before frame occurrence) (relations frame occurrence)
abbrev expression := SourceOperationExecution.Coefficients.expression (word frame occurrence)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue A) (Var:=X) (sort:=slot) :=
 ⟨pairEnvironment (before frame occurrence) (increment frame occurrence),liftExpr (expression frame occurrence)⟩
abbrev inverse := canonicalResidual
 (evaluation (R:=ℤ) ((before frame occurrence)+(increment frame occurrence))) (word frame occurrence)
end SourceGeneratedOccurrenceRelations
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable (frame : Frame.{u})
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
abbrev paid := SourceGeneratedOccurrenceRelations.paid frame occurrence
abbrev before := SourceGeneratedOccurrenceRelations.before frame occurrence
abbrev increment := SourceGeneratedOccurrenceRelations.increment frame occurrence
abbrev relations := SourceGeneratedOccurrenceRelations.relations frame occurrence
abbrev word := SourceGeneratedOccurrenceRelations.word frame occurrence
abbrev expression := SourceGeneratedOccurrenceRelations.expression frame occurrence
abbrev raw := SourceGeneratedOccurrenceRelations.raw frame occurrence
def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) := raw frame supplied
def result {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot (reader frame) supplied
abbrev inverse := SourceGeneratedOccurrenceRelations.inverse frame occurrence
abbrev paidInventory := (SourceOperationPaidRelations.exposure (paid frame occurrence).state.2).map
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent
def written := SourceHistoryCommon.seed (Occurrence.written frame occurrence)
 (SourceHistoryCommon.seed (paidInventory frame occurrence)
  (SourceOperationPaidRelations.exposure (result frame occurrence).2.1.2))
def material := (Occurrence.material frame occurrence,relations frame occurrence,word frame occurrence,
 inverse frame occurrence,raw frame occurrence,result frame occurrence,written frame occurrence)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
