import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
local instance : ∀ s,AddCommGroup (Value root visit recognition s) := inferInstance
abbrev Event := SourceGeneratedInquiryReceiptAction.Configured.Event
 (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
 (configuration root visit recognition U7 calculus anchor sourceStage)
abbrev old := SourceGeneratedInquiryReceiptAction.old
 (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
 (configuration root visit recognition U7 calculus anchor sourceStage)
-- The receiver inventories are source data, and this exact body is assembled before emission.
def targetAt (event : Event root visit recognition U7 calculus anchor sourceStage stage) : type_of%
 ((SourceGeneratedInquiryReceiptAction.birthProgram
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
  (configuration root visit recognition U7 calculus anchor sourceStage)).targetAt event) :=
 let initial := receiver root visit recognition U7 calculus anchor sourceStage stage
 let programme := receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage
 let original := (SourceGeneratedInquiryReceiptAction.birthProgram
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
  (configuration root visit recognition U7 calculus anchor sourceStage)).targetAt event
 let material := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface original
  (SourceOperationInquiry.Context.Installation.component (A.epoch initial))
 let configured := SourceOperationInquiry.Context.Faces.Execution.Activation.optionalTargetCoface material
  (A.Shared.datum initial programme).component
 let withQuery := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface configured
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw (A.epoch initial) programme)
 let withResult := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface withQuery
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw (A.epoch initial) programme)
 let withConsumer := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface withResult
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw (A.epoch initial) programme)
 SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface withConsumer
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw (A.epoch initial) programme)
def birthProgram : type_of% (SourceGeneratedInquiryReceiptAction.birthProgram
 (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
 (configuration root visit recognition U7 calculus anchor sourceStage)) where
 targetAt:=targetAt root visit recognition U7 calculus anchor sourceStage stage
abbrev generatedAction := (birthProgram root visit recognition U7 calculus anchor sourceStage stage).generate
 (SourceGeneratedInquiryReceiptAction.sourceEvent
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
  (configuration root visit recognition U7 calculus anchor sourceStage))
def compilation (candidate : (old root visit recognition U7 calculus anchor sourceStage stage).Query) : SourceNativeInquiryCompilationProgramAt
 (old root visit recognition U7 calculus anchor sourceStage stage).root
 (old root visit recognition U7 calculus anchor sourceStage stage).visit
 (old root visit recognition U7 calculus anchor sourceStage stage).U7
 (old root visit recognition U7 calculus anchor sourceStage stage).calculus
 (old root visit recognition U7 calculus anchor sourceStage stage).root.source.base.lawSurface candidate
 ((old root visit recognition U7 calculus anchor sourceStage stage).emitInquiry candidate)
 ((old root visit recognition U7 calculus anchor sourceStage stage).entryAt candidate)
 ((old root visit recognition U7 calculus anchor sourceStage stage).authorityAt candidate) where
 compile:=fun event => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique
   (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage) candidate
  exact .debtAdmission ((birthProgram root visit recognition U7 calculus anchor sourceStage stage).generate event)
def state : type_of% (SourceGeneratedInquiryReceiptAction.Configured.state
 (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
 (configuration root visit recognition U7 calculus anchor sourceStage)) where
 root:=(old root visit recognition U7 calculus anchor sourceStage stage).root
 visit:=(old root visit recognition U7 calculus anchor sourceStage stage).visit
 U7:=(old root visit recognition U7 calculus anchor sourceStage stage).U7
 calculus:=(old root visit recognition U7 calculus anchor sourceStage stage).calculus
 Query:=(old root visit recognition U7 calculus anchor sourceStage stage).Query
 entryAt:=(old root visit recognition U7 calculus anchor sourceStage stage).entryAt
 authorityAt:=(old root visit recognition U7 calculus anchor sourceStage stage).authorityAt
 compilationProgramAt:=compilation root visit recognition U7 calculus anchor sourceStage stage
 compilationFaceAt:=fun candidate => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique
   (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage) candidate
  exact { projection:=((old root visit recognition U7 calculus anchor sourceStage stage).compilationFaceAt
           (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
            (configuration root visit recognition U7 calculus anchor sourceStage))).projection
          active:=((old root visit recognition U7 calculus anchor sourceStage stage).compilationFaceAt
           (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
            (configuration root visit recognition U7 calculus anchor sourceStage))).active
          classifier_eq:=((old root visit recognition U7 calculus anchor sourceStage stage).compilationFaceAt
           (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
            (configuration root visit recognition U7 calculus anchor sourceStage))).classifier_eq
          project_heq:=HEq.rfl }
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique
   (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage) candidate
  exact nomatch impossible
def sourcePresentation : RootInquiryStatePresentation where
 N:=RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).registered
 V:=RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).registered
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).packetAt
 state:=.create (state root visit recognition U7 calculus anchor sourceStage stage)
abbrev targetPresentation := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation
 (receiver root visit recognition U7 calculus anchor sourceStage stage)
 (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage)
abbrev actualGenerated := (generatedAction root visit recognition U7 calculus anchor sourceStage stage,
 runtime root visit recognition U7 calculus anchor sourceStage stage)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
