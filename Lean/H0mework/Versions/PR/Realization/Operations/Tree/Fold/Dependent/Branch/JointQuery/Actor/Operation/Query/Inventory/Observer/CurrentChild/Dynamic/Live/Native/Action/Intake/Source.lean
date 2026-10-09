import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Root

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
namespace R
export SourceGeneratedInquiryReceiptAction (old birthProgram sourceEvent)
end R
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (targetCoface optionalTargetCoface epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (datum root visit queryLaw resultLaw consumerLaw compilationLaw)
end Shared
end A
namespace Owned
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.RootOwned
 (sourceFrame sourceProgramme sourceInitial sourceSeed configuration runtime)
end Owned
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor sourceStage stage : Nat)
abbrev sourceFrame := Owned.sourceFrame root visit rec U7 calculus anchor sourceStage stage
abbrev sourceProgramme := Owned.sourceProgramme root visit rec U7 calculus anchor sourceStage
abbrev receiver := Owned.sourceInitial root visit rec U7 calculus anchor sourceStage stage
abbrev receiverProgramme := Owned.configuration root visit rec U7 calculus anchor sourceStage stage
abbrev Event := ExactTemporalCausalRootEventAt
 (R.old (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (sourceProgramme root visit rec U7 calculus anchor sourceStage)).root.toAuthoritativeRoot.toLedgerRoot
 (R.old (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (sourceProgramme root visit rec U7 calculus anchor sourceStage)).visit
namespace Lower
variable {S : Type u} {Value Var : S → Type u} [∀ s, AddCommGroup (Value s)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=s))
variable (programme : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue Value) (PhysicalVar:=cfg.LowVar) (sort:=s))
def targetAt (event : SourceGeneratedInquiryReceiptAction.Configured.Event frame cfg) :
 type_of% ((R.birthProgram frame cfg).targetAt event) :=
 let initial := SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg
 let original := (R.birthProgram frame cfg).targetAt event
 let material := A.targetCoface original (SourceOperationInquiry.Context.Installation.component (A.epoch initial))
 let configured := A.optionalTargetCoface material (A.Shared.datum initial programme).component
 let withQuery := A.targetCoface configured (A.Shared.queryLaw (A.epoch initial) programme)
 let withResult := A.targetCoface withQuery (A.Shared.resultLaw (A.epoch initial) programme)
 let withConsumer := A.targetCoface withResult (A.Shared.consumerLaw (A.epoch initial) programme)
 A.targetCoface withConsumer (A.Shared.compilationLaw (A.epoch initial) programme)
def birthProgram : type_of% (R.birthProgram frame cfg) where
 targetAt := targetAt frame cfg programme
abbrev generatedAction := (birthProgram frame cfg programme).generate (R.sourceEvent frame cfg)
def compilation (candidate : (R.old frame cfg).Query) : SourceNativeInquiryCompilationProgramAt
 (R.old frame cfg).root (R.old frame cfg).visit (R.old frame cfg).U7 (R.old frame cfg).calculus
 (R.old frame cfg).root.source.base.lawSurface candidate ((R.old frame cfg).emitInquiry candidate)
 ((R.old frame cfg).entryAt candidate) ((R.old frame cfg).authorityAt candidate) where
 compile := fun event => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique frame cfg candidate
  exact .debtAdmission ((birthProgram frame cfg programme).generate event)
def state : type_of% (SourceGeneratedInquiryReceiptAction.Configured.state frame cfg) where
 root := (R.old frame cfg).root
 visit := (R.old frame cfg).visit
 U7 := (R.old frame cfg).U7
 calculus := (R.old frame cfg).calculus
 Query := (R.old frame cfg).Query
 entryAt := (R.old frame cfg).entryAt
 authorityAt := (R.old frame cfg).authorityAt
 compilationProgramAt := compilation frame cfg programme
 compilationFaceAt := fun candidate => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique frame cfg candidate
  exact { projection := ((R.old frame cfg).compilationFaceAt (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame cfg)).projection
          active := ((R.old frame cfg).compilationFaceAt (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame cfg)).active
          classifier_eq := ((R.old frame cfg).compilationFaceAt (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame cfg)).classifier_eq
          project_heq := HEq.rfl }
 u7RootDisposition_commutes := by
  intro candidate _ _ impossible
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique frame cfg candidate
  exact nomatch impossible
def sourcePresentation : RootInquiryStatePresentation where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
 state := .create (state frame cfg programme)
abbrev targetPresentation := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation
 (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg) programme
end Lower
abbrev targetAt := Lower.targetAt
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)
abbrev birthProgram := Lower.birthProgram
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)
abbrev generatedAction := Lower.generatedAction
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)
abbrev state := Lower.state
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)
abbrev sourcePresentation := Lower.sourcePresentation
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)
abbrev targetPresentation := Lower.targetPresentation
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)
abbrev actualSourceEvent := R.sourceEvent
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
