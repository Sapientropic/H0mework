import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Consumer
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Rep
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay
 (receiver seed configuration sourceFrame sourceMaterial Event old receiver_strict)
end Rep
namespace Cat
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
 (LowFrame configuration UniformAt nextCount uniform_next actor_word_of_uniform support actorWord restriction queryRaw scalarWritten pairWritten)
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic
 (coreSlot actorAtCount)
namespace Parent
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live
 (birthCount)
namespace Origin
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin
 (uniform_origin)
end Origin
end Parent
end D
end Cat
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
 (PhysicalValue)
end Act
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch targetCoface optionalTargetCoface)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (runtime frames next nextBorn query actualOccurrence datum queryLaw resultLaw consumerLaw compilationLaw root visit query_unique actual_query actual_next)
end Shared
end A
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
abbrev initial : Cat.LowFrame root visit rec := Rep.receiver root visit rec U7 calculus anchor sourceStage stage
abbrev sourceSeed := Rep.seed root visit rec U7 calculus anchor sourceStage stage
abbrev configuration := Cat.configuration root visit rec U7 calculus anchor
 (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
abbrev runtime := A.Shared.runtime (initial root visit rec U7 calculus anchor sourceStage stage)
 (configuration root visit rec U7 calculus anchor sourceStage stage)
abbrev frameAt : Nat → Cat.LowFrame root visit rec := A.Shared.frames
 (initial root visit rec U7 calculus anchor sourceStage stage)
 (configuration root visit rec U7 calculus anchor sourceStage stage)
def rawSource (state : (runtime root visit rec U7 calculus anchor sourceStage stage).State) :
 SourceOperationInquiry.Context.RawAt
 (PhysicalValue:=SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.LowValue root visit rec)
 (PhysicalVar:=SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.LowVar root visit rec)
 (sort:=SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.sort root rec)
 (runtime root visit rec U7 calculus anchor sourceStage stage) state := by
 rcases state with ⟨⟨count⟩,activation⟩
 exact Cat.restriction root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
  (frameAt root visit rec U7 calculus anchor sourceStage stage count.down)

def targetAt (event : Rep.Event root visit rec U7 calculus anchor sourceStage stage) : type_of%
 ((SourceGeneratedInquiryReceiptAction.birthProgram (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (Rep.configuration root visit rec U7 calculus anchor sourceStage)).targetAt event) :=
 let initial := initial root visit rec U7 calculus anchor sourceStage stage
 let programme := configuration root visit rec U7 calculus anchor sourceStage stage
 let original := (SourceGeneratedInquiryReceiptAction.birthProgram
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (Rep.configuration root visit rec U7 calculus anchor sourceStage)).targetAt event
 let material := A.targetCoface original (SourceOperationInquiry.Context.Installation.component (A.epoch initial))
 let configured := A.optionalTargetCoface material (A.Shared.datum initial programme).component
 let withQuery := A.targetCoface configured (A.Shared.queryLaw (A.epoch initial) programme)
 let withResult := A.targetCoface withQuery (A.Shared.resultLaw (A.epoch initial) programme)
 let withConsumer := A.targetCoface withResult (A.Shared.consumerLaw (A.epoch initial) programme)
 A.targetCoface withConsumer (A.Shared.compilationLaw (A.epoch initial) programme)

def birthProgram : type_of% (SourceGeneratedInquiryReceiptAction.birthProgram
 (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (Rep.configuration root visit rec U7 calculus anchor sourceStage)) where
 targetAt:=targetAt root visit rec U7 calculus anchor sourceStage stage

abbrev generatedAction := (birthProgram root visit rec U7 calculus anchor sourceStage stage).generate
 (SourceGeneratedInquiryReceiptAction.sourceEvent (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (Rep.configuration root visit rec U7 calculus anchor sourceStage))

def compilation (candidate : (Rep.old root visit rec U7 calculus anchor sourceStage stage).Query) : SourceNativeInquiryCompilationProgramAt
 (Rep.old root visit rec U7 calculus anchor sourceStage stage).root
 (Rep.old root visit rec U7 calculus anchor sourceStage stage).visit
 (Rep.old root visit rec U7 calculus anchor sourceStage stage).U7
 (Rep.old root visit rec U7 calculus anchor sourceStage stage).calculus
 (Rep.old root visit rec U7 calculus anchor sourceStage stage).root.source.base.lawSurface candidate
 ((Rep.old root visit rec U7 calculus anchor sourceStage stage).emitInquiry candidate)
 ((Rep.old root visit rec U7 calculus anchor sourceStage stage).entryAt candidate)
 ((Rep.old root visit rec U7 calculus anchor sourceStage stage).authorityAt candidate) where
 compile:=fun event => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique
   (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
   (Rep.configuration root visit rec U7 calculus anchor sourceStage) candidate
  exact .debtAdmission ((birthProgram root visit rec U7 calculus anchor sourceStage stage).generate event)

def state : type_of% (SourceGeneratedInquiryReceiptAction.Configured.state
 (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (Rep.configuration root visit rec U7 calculus anchor sourceStage)) where
 root:=(Rep.old root visit rec U7 calculus anchor sourceStage stage).root
 visit:=(Rep.old root visit rec U7 calculus anchor sourceStage stage).visit
 U7:=(Rep.old root visit rec U7 calculus anchor sourceStage stage).U7
 calculus:=(Rep.old root visit rec U7 calculus anchor sourceStage stage).calculus
 Query:=(Rep.old root visit rec U7 calculus anchor sourceStage stage).Query
 entryAt:=(Rep.old root visit rec U7 calculus anchor sourceStage stage).entryAt
 authorityAt:=(Rep.old root visit rec U7 calculus anchor sourceStage stage).authorityAt
 compilationProgramAt:=compilation root visit rec U7 calculus anchor sourceStage stage
 compilationFaceAt:=fun candidate => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique
   (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
   (Rep.configuration root visit rec U7 calculus anchor sourceStage) candidate
  exact { projection:=((Rep.old root visit rec U7 calculus anchor sourceStage stage).compilationFaceAt
           (A.Shared.query (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
            (Rep.configuration root visit rec U7 calculus anchor sourceStage))).projection
          active:=((Rep.old root visit rec U7 calculus anchor sourceStage stage).compilationFaceAt
           (A.Shared.query (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
            (Rep.configuration root visit rec U7 calculus anchor sourceStage))).active
          classifier_eq:=((Rep.old root visit rec U7 calculus anchor sourceStage stage).compilationFaceAt
           (A.Shared.query (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
            (Rep.configuration root visit rec U7 calculus anchor sourceStage))).classifier_eq
          project_heq:=HEq.rfl }
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique
   (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
   (Rep.configuration root visit rec U7 calculus anchor sourceStage) candidate
  exact nomatch impossible

def sourcePresentation : RootInquiryStatePresentation where
 N:=RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage).registered
 V:=RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage).registered
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage).packetAt
 state:=.create (state root visit rec U7 calculus anchor sourceStage stage)

abbrev targetPresentation := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation
 (initial root visit rec U7 calculus anchor sourceStage stage)
 (configuration root visit rec U7 calculus anchor sourceStage stage)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
