import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Action.Source
import H0mework.Realization.Operations.Execution.Substitution.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence)
end Shared
end E
namespace C
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end C
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)

def queryBinding : ∀ slot : Inventory.OldSlot.{u}, Query.Variable root visit recognition slot →
    Expr (Query.Value root visit recognition) (Query.Variable root visit recognition) slot
  | .inl slot, name => Actor.Extension.embed (Actor.Value root visit recognition) (Actor.Variable root visit recognition)
      (Query.Output root visit recognition) (Actor.Action.binding root visit recognition slot name)
  | .inr _, absent => PEmpty.elim absent

def binding : ∀ slot, Inventory.Variable root visit recognition slot →
    Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition) slot
  | .inl slot, name => Inventory.embed root visit recognition (queryBinding root visit recognition slot name)
  | .inr (.inl index), name => Inventory.childEmbed root visit recognition index
      (InventoryVector.expression
        (Inventory.P.Index root recognition index.1 index.2 (Inventory.childData root recognition index))
        (Operation.SomePacket.binding root recognition index.1 index.2 (Inventory.childData root recognition index)
          PUnit.unit name))
  | .inr (.inr _), absent => PEmpty.elim absent

abbrev Frame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Inventory.Value root visit recognition) (Var:=Inventory.Variable root visit recognition)
  (sort:=Inventory.resultSlot root recognition)
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : C.Occurrence frame (current:=current))

abbrev environmentAt := frame.environment
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
    frame.registered frame.packetAt occurrence)
abbrev generatedEnvironmentAt := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
  (binding root visit recognition) (environmentAt root visit recognition frame occurrence)
abbrev incrementAt := generatedEnvironmentAt root visit recognition frame occurrence -
  environmentAt root visit recognition frame occurrence

def rawAt : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Inventory.Value root visit recognition) (Var:=Inventory.Variable root visit recognition)
    (sort:=Inventory.resultSlot root recognition) :=
  ⟨environmentAt root visit recognition frame occurrence,
    (Inventory.expression root visit recognition).subst (binding root visit recognition)⟩
def sourceTraceAt := execution (generatedEnvironmentAt root visit recognition frame occurrence)
  (Inventory.expression root visit recognition)
def fullTraceAt := (sourceTraceAt root visit recognition frame occurrence).substitutedTrace
  (binding root visit recognition) (environmentAt root visit recognition frame occurrence)
abbrev paidAt := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (E.Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} supplied => rawAt root visit recognition frame supplied) occurrence
def writtenAt := SourceHistoryCommon.seed
  (SourceOperationPaidRelations.exposure (paidAt root visit recognition frame occurrence).2.1.2)
  (SourceOperationPaidRelations.exposure (fullTraceAt root visit recognition frame occurrence))
def materialAt := (C.materialAt frame occurrence, binding root visit recognition,
  rawAt root visit recognition frame occurrence,paidAt root visit recognition frame occurrence,
  fullTraceAt root visit recognition frame occurrence,generatedEnvironmentAt root visit recognition frame occurrence)
abbrev generatedEnvironment := generatedEnvironmentAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev increment := incrementAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev raw := rawAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev sourceTrace := sourceTraceAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev fullTrace := fullTraceAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev paid := paidAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev written := writtenAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev material := materialAt root visit recognition frame (E.Shared.actualOccurrence frame)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
