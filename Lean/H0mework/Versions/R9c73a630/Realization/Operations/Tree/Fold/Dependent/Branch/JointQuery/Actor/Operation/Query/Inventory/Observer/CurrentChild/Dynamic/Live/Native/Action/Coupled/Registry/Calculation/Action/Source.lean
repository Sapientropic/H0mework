import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Query.Moving
import H0mework.Realization.Operations.Execution.Relations.History.Laws
import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Exposure
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Acted
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
 (PhysicalValue LowValue LowVar sort pairBinding)
end Act
namespace Cat
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
 (configuration pairWritten queryRaw)
end Cat
namespace P
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled
 (sourceSeed initial)
end P
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch optionalSourceRoot)
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base root query actualOccurrence datum nextBorn queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw visit)
end S
end A
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ.Lower
 (deltaRaw deltaExpression deltaWord delta_eval moving_eval)
end D
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
abbrev seed := P.sourceSeed root visit rec U7 calculus anchor sourceStage stage
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
def original := Cat.queryRaw root visit rec U7 calculus anchor (seed root visit rec U7 calculus anchor sourceStage stage) frame actual
def acted : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (Act.LowValue root visit rec)) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec) :=
 ⟨(original root visit rec U7 calculus anchor sourceStage stage frame actual).environment,
  (original root visit rec U7 calculus anchor sourceStage stage frame actual).expression.subst (Act.pairBinding root visit rec)⟩
def delta := D.deltaRaw (original root visit rec U7 calculus anchor sourceStage stage frame actual)
 (acted root visit rec U7 calculus anchor sourceStage stage frame actual)
def deltaTrace := execution (delta root visit rec U7 calculus anchor sourceStage stage frame actual).environment
 (delta root visit rec U7 calculus anchor sourceStage stage frame actual).expression
def replayEnvironment := SourceSubstitution.sourceEnvironment (Act.pairBinding root visit rec)
 (original root visit rec U7 calculus anchor sourceStage stage frame actual).environment
def replayTrace := (execution (replayEnvironment root visit rec U7 calculus anchor sourceStage stage frame actual)
 (original root visit rec U7 calculus anchor sourceStage stage frame actual).expression).substitutedTrace
 (Act.pairBinding root visit rec) (original root visit rec U7 calculus anchor sourceStage stage frame actual).environment
def added := SourceHistoryCommon.seed
 (SourceOperationPaidRelations.exposure (replayTrace root visit rec U7 calculus anchor sourceStage stage frame actual))
 (SourceOperationPaidRelations.exposure (deltaTrace root visit rec U7 calculus anchor sourceStage stage frame actual))
def written := SourceHistoryCommon.seed
 (Cat.pairWritten root visit rec U7 calculus anchor (seed root visit rec U7 calculus anchor sourceStage stage) frame actual)
 (added root visit rec U7 calculus anchor sourceStage stage frame actual)
def material := (original root visit rec U7 calculus anchor sourceStage stage frame actual,
 acted root visit rec U7 calculus anchor sourceStage stage frame actual,
 delta root visit rec U7 calculus anchor sourceStage stage frame actual,
 deltaTrace root visit rec U7 calculus anchor sourceStage stage frame actual,
 replayEnvironment root visit rec U7 calculus anchor sourceStage stage frame actual,
 replayTrace root visit rec U7 calculus anchor sourceStage stage frame actual,
 written root visit rec U7 calculus anchor sourceStage stage frame actual)
def component : SourceNativeProjectionLaw (A.S.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit.{u+1}
 ActiveAt:=fun _ {_current} _ => PUnit.{u+1}
 InactiveAt:=fun _ {_current} _ => PEmpty.{u+1}
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun _ {_current} supplied _ => type_of% (material root visit rec U7 calculus anchor sourceStage stage frame supplied)
 project:=fun _ {_current} supplied _ => material root visit rec U7 calculus anchor sourceStage stage frame supplied
abbrev baseline := Cat.configuration root visit rec U7 calculus anchor (seed root visit rec U7 calculus anchor sourceStage stage)
def combined := (A.optionalSourceRoot (A.S.base frame).root
 ((baseline root visit rec U7 calculus anchor sourceStage stage).datum frame).component).source.base.withProjectionCoface
 (component root visit rec U7 calculus anchor sourceStage stage frame) |>.projectionLaw
def configuration := {baseline root visit rec U7 calculus anchor sourceStage stage with
 datum:=fun sourceFrame => {(baseline root visit rec U7 calculus anchor sourceStage stage).datum sourceFrame with
  component:=some (combined root visit rec U7 calculus anchor sourceStage stage sourceFrame)}
 nextPairInventory:=fun sourceFrame => some ((component root visit rec U7 calculus anchor sourceStage stage (A.epoch sourceFrame)).project PUnit.unit
  (A.S.actualOccurrence sourceFrame) PUnit.unit).2.2.2.2.2.2}


def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (A.S.base frame).root.source.base (combined root visit rec U7 calculus anchor sourceStage stage (A.epoch frame))).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame (configuration root visit rec U7 calculus anchor sourceStage stage)).source.base
  (A.S.queryLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor sourceStage stage))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (A.S.queryRoot frame (configuration root visit rec U7 calculus anchor sourceStage stage)).source.base
  (A.S.resultLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor sourceStage stage))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (A.S.resultRoot frame (configuration root visit rec U7 calculus anchor sourceStage stage)).source.base
  (A.S.consumerLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor sourceStage stage))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (A.S.consumerRoot frame (configuration root visit rec U7 calculus anchor sourceStage stage)).source.base
  (A.S.compilationLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor sourceStage stage)))
def calculationFace : SourceNativeRootSemanticFaceAt (A.S.root frame (configuration root visit rec U7 calculus anchor sourceStage stage))
 (A.S.visit frame (configuration root visit rec U7 calculus anchor sourceStage stage)) where
 projection := (installation root visit rec U7 calculus anchor sourceStage stage frame).embed (.component PUnit.unit)
 active:=PUnit.unit
 classifier_eq:=rfl
theorem actual_material : (calculationFace root visit rec U7 calculus anchor sourceStage stage frame).rootRead=
 material root visit rec U7 calculus anchor sourceStage stage (A.epoch frame) (A.S.actualOccurrence frame) := rfl
theorem actual_written : (A.S.nextBorn frame (configuration root visit rec U7 calculus anchor sourceStage stage)).pairInventory=
 some ((calculationFace root visit rec U7 calculus anchor sourceStage stage frame).rootRead.2.2.2.2.2.2) := rfl
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Acted
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
