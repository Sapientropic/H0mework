import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Root
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Epoch.Consumer
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
 (PhysicalValue PhysicalVar LowValue LowVar sort actualEnvironment rightOldEnvironment rightEffectEnvironment lowBinding physicalNext raw component configuration scalarWritten pairWritten right_core_action)
namespace Owned
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.RootOwned
 (sourceInitial sourceSeed sourceFrame sourceProgramme)
end Owned
end Act
namespace Child
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
 (Value Variable Output resultSlot SourceActor actorTerm programme oldTerm oldOutputEmbed indices samples observationOutput gramOutput)
end Child
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic
 (coreSlot actorAtCount actor_projection_eval orbitPair actorMaterial)
namespace Parent
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live
 (birthCount)
namespace Origin
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin
 (pairAt uniform_origin)
end Origin
end Parent
namespace Low
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow
 (right)
end Low
end D
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base actualOccurrence root visit datum baseRoot queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw query resultFace nextBorn next frames runtime process actual_node actual_query actual_next)
end Shared
end A
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Act.LowValue root visit rec) (Act.LowVar root visit rec) (Act.sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
def actorRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=Act.PhysicalValue root visit rec) (Var:=Act.PhysicalVar root visit rec) (sort:=Act.sort root rec) :=
 ⟨Act.rightOldEnvironment root visit rec frame actual,Child.actorTerm root visit rec⟩
def actorPaid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (A.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} supplied => actorRaw root visit rec frame supplied) actual
def actorWord := (actorPaid root visit rec frame actual).2.2.1.2.1.2.1+
 (actorPaid root visit rec frame actual).2.2.1.2.1.2.2
def support := (actorWord root visit rec frame actual).support.toList
def indices := (support root visit rec frame actual).flatMap (Child.indices root rec)
def samples := (support root visit rec frame actual).flatMap (Child.samples root rec)
def childTerm (source : Child.SourceActor root rec) := Child.oldOutputEmbed root visit rec
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.oldOutputEmbed root visit rec
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.childExpressionAtCode root visit rec source.1.1))
def childTerms := (support root visit rec frame actual).map (childTerm root visit rec)
def observationTerms := ((indices root visit rec frame actual).map
 (fun index => List.ofFn (fun kind : Fin 4 => Child.observationOutput root visit rec index kind))).flatten
def gramTerms := (samples root visit rec frame actual).flatMap
 (fun first => (samples root visit rec frame actual).map (fun second => Child.gramOutput root visit rec first second))
def terms := Child.oldTerm root visit rec U7 calculus anchor::Child.actorTerm root visit rec::
 (childTerms root visit rec frame actual ++ observationTerms root visit rec frame actual ++ gramTerms root visit rec frame actual)
def expression := Child.programme root visit rec (terms root visit rec U7 calculus anchor frame actual)
def lowExpression := D.Low.right (liftExpr (expression root visit rec U7 calculus anchor frame actual))
def lowRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec) :=
 ⟨Act.actualEnvironment root visit rec frame actual,lowExpression root visit rec U7 calculus anchor frame actual⟩
def lowPaid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (A.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} supplied => lowRaw root visit rec U7 calculus anchor frame supplied) actual
def lowTrace := execution (lowRaw root visit rec U7 calculus anchor frame actual).environment
 (lowRaw root visit rec U7 calculus anchor frame actual).expression
def queryRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (Act.LowValue root visit rec)) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec) :=
 ⟨(Act.raw root visit rec seed frame actual).environment,
  (Act.raw root visit rec seed frame actual).expression.add
   (liftExpr (lowExpression root visit rec U7 calculus anchor frame actual))⟩
def queryPaid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (A.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} supplied => queryRaw root visit rec U7 calculus anchor seed frame supplied) actual
def queryTrace := execution (queryRaw root visit rec U7 calculus anchor seed frame actual).environment
 (queryRaw root visit rec U7 calculus anchor seed frame actual).expression
def scalarAdded := SourceHistoryCommon.seed
 (SourceOperationPaidRelations.exposure (lowPaid root visit rec U7 calculus anchor frame actual).2.1.2)
 (SourceOperationPaidRelations.exposure (lowTrace root visit rec U7 calculus anchor frame actual))
def pairAdded := SourceHistoryCommon.seed
 (SourceOperationPaidRelations.exposure (queryPaid root visit rec U7 calculus anchor seed frame actual).2.1.2)
 (SourceOperationPaidRelations.exposure (queryTrace root visit rec U7 calculus anchor seed frame actual))
def scalarWritten := SourceHistoryCommon.seed (Act.scalarWritten root visit rec seed frame actual)
 (scalarAdded root visit rec U7 calculus anchor frame actual)
def pairWritten := SourceHistoryCommon.seed (Act.pairWritten root visit rec seed frame actual)
 (pairAdded root visit rec U7 calculus anchor seed frame actual)
def material := (actorRaw root visit rec frame actual,actorPaid root visit rec frame actual,
 actorWord root visit rec frame actual,support root visit rec frame actual,
 (support root visit rec frame actual).map (D.actorMaterial root rec),
 indices root visit rec frame actual,samples root visit rec frame actual,
 terms root visit rec U7 calculus anchor frame actual,expression root visit rec U7 calculus anchor frame actual,
 lowRaw root visit rec U7 calculus anchor frame actual,lowPaid root visit rec U7 calculus anchor frame actual,
 queryRaw root visit rec U7 calculus anchor seed frame actual,queryPaid root visit rec U7 calculus anchor seed frame actual,
 scalarWritten root visit rec U7 calculus anchor seed frame actual,pairWritten root visit rec U7 calculus anchor seed frame actual)
def component : SourceNativeProjectionLaw (A.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit.{u+1}
 ActiveAt:=fun _ {_current} _ => PUnit.{u+1}
 InactiveAt:=fun _ {_current} _ => PEmpty.{u+1}
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun _ {_current} supplied _ => type_of% (material root visit rec U7 calculus anchor seed frame supplied)
 project:=fun _ {_current} supplied _ => material root visit rec U7 calculus anchor seed frame supplied

def combined : SourceNativeProjectionLaw (A.Shared.base frame).root.source.base.restructuringSource.toLedgerSource :=
 ({(A.Shared.base frame).root.source.base with projectionLaw:=Act.component root visit rec seed frame}.withProjectionCoface
  (component root visit rec U7 calculus anchor seed frame)).projectionLaw
def configuration := {Act.configuration root visit rec seed with
 datum:=fun sourceFrame => {(Act.configuration root visit rec seed).datum sourceFrame with
  component:=some (combined root visit rec U7 calculus anchor seed sourceFrame)
  reader:=fun {_current} supplied => queryRaw root visit rec U7 calculus anchor seed sourceFrame supplied}
 nextInventory:=fun sourceFrame => some (scalarWritten root visit rec U7 calculus anchor seed sourceFrame (A.Shared.actualOccurrence sourceFrame))
 nextPairInventory:=fun sourceFrame => some (pairWritten root visit rec U7 calculus anchor seed sourceFrame (A.Shared.actualOccurrence sourceFrame))}

theorem actor_value : (actorPaid root visit rec frame actual).2.2.1 =
 (Child.actorTerm root visit rec).eval (Act.rightOldEnvironment root visit rec frame actual) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
abbrev LowFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
