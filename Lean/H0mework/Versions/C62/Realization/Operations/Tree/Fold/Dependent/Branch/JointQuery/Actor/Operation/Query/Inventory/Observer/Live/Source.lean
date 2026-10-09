import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController CofinalHistorySettlement
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
  (programme component material)
end R
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base actualOccurrence runtime frames baseRoot queryRoot resultRoot consumerRoot root visit baseInstallation queryLaw resultLaw consumerLaw compilationLaw)
end Shared
end E
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor : Nat)
variable (frame : Action.Frame root visit recognition)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) (Observer.resultSlot root recognition))))
def material {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Action.C.Occurrence frame (current:=current)) :=
  (R.material seed frame occurrence,Action.materialAt root visit recognition U7 calculus anchor frame occurrence)
def actionLaw : SourceNativeProjectionLaw (E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection:=PUnit.{u+1}
  ActiveAt:=fun _ {_current} _ => PUnit.{u+1}
  InactiveAt:=fun _ {_current} _ => PEmpty.{u+1}
  classify:=fun _ {_current} _ => .inl PUnit.unit
  PayloadAt:=fun _ {_current} supplied _ => type_of% (material root visit recognition U7 calculus anchor frame seed supplied)
  project:=fun _ {_current} supplied _ => material root visit recognition U7 calculus anchor frame seed supplied
def materialCombined : SourceNativeProjectionLaw (E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource :=
  ({(E.Shared.base frame).root.source.base with projectionLaw:=R.component seed frame}.withProjectionCoface
    (actionLaw root visit recognition U7 calculus anchor frame seed)).projectionLaw
def combined : SourceNativeProjectionLaw (E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource :=
 ({(E.Shared.base frame).root.source.base with projectionLaw:=materialCombined root visit recognition U7 calculus anchor frame seed}.withProjectionCoface
  (ActiveRaw.component root visit recognition U7 calculus anchor frame)).projectionLaw
abbrev sourceEnvironmentRead {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Action.C.Occurrence frame (current:=current)) :=
  ((actionLaw root visit recognition U7 calculus anchor frame seed).project PUnit.unit occurrence PUnit.unit).2.2.2.2.2.2
def physicalWritten := SourceOperationPaidRelations.exposure frame.paidRead.state.2
def accumulated := SourceHistoryCommon.seed
  (match frame.inventory with
   | none => physicalWritten root visit recognition frame
   | some prior => SourceHistoryCommon.seed prior (physicalWritten root visit recognition frame))
  (Action.written root visit recognition U7 calculus anchor frame)
def nextScalar := match (R.programme seed).nextInventory frame with
  | none => accumulated root visit recognition U7 calculus anchor frame
  | some original => SourceHistoryCommon.seed original (accumulated root visit recognition U7 calculus anchor frame)
def pairEvent : PresentedRelationEventAt
    (Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) (Observer.resultSlot root recognition)) →
    PresentedRelationEventAt
      (Expr (PairValue (Observer.Value root visit recognition)) (Observer.Variable root visit recognition) (Observer.resultSlot root recognition))
  | .generator expression => .generator (liftExpr expression)
  | .relation word => .relation (Finsupp.mapDomain liftExpr word)
def pairWritten := (Action.written root visit recognition U7 calculus anchor frame).map (pairEvent root visit recognition)
def nextPair := match (R.programme seed).nextPairInventory frame with
  | none => pairWritten root visit recognition U7 calculus anchor frame
  | some prior => SourceHistoryCommon.seed prior (pairWritten root visit recognition U7 calculus anchor frame)
def configuration := {R.programme seed with
  datum:=fun sourceFrame => {
    component:=some (combined root visit recognition U7 calculus anchor sourceFrame seed)
    reader:=(R.programme seed).datum sourceFrame |>.reader
    nextEnvironmentReadAt:=some (fun {_current} supplied _ => sourceEnvironmentRead root visit recognition U7 calculus anchor sourceFrame seed supplied) }
  nextInventory:=fun sourceFrame => some (nextScalar root visit recognition U7 calculus anchor sourceFrame seed)
  nextPairInventory:=fun sourceFrame => some (nextPair root visit recognition U7 calculus anchor sourceFrame seed) }
def materialEmbedding : SourceNativeProjectionLaw.InstallationAt
    (actionLaw root visit recognition U7 calculus anchor frame seed) (materialCombined root visit recognition U7 calculus anchor frame seed) :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    ({(E.Shared.base frame).root.source.base with projectionLaw:=R.component seed frame})
    (actionLaw root visit recognition U7 calculus anchor frame seed)
def actionEmbedding : SourceNativeProjectionLaw.InstallationAt
 (actionLaw root visit recognition U7 calculus anchor frame seed) (combined root visit recognition U7 calculus anchor frame seed) :=
 (materialEmbedding root visit recognition U7 calculus anchor frame seed).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  ({(E.Shared.base frame).root.source.base with projectionLaw:=materialCombined root visit recognition U7 calculus anchor frame seed})
  (ActiveRaw.component root visit recognition U7 calculus anchor frame))
def activeEmbedding : SourceNativeProjectionLaw.InstallationAt
 (ActiveRaw.component root visit recognition U7 calculus anchor frame) (combined root visit recognition U7 calculus anchor frame seed) :=
 SourceNativeProjectionLaw.InstallationAt.componentCoface
 ({(E.Shared.base frame).root.source.base with projectionLaw:=materialCombined root visit recognition U7 calculus anchor frame seed})
 (ActiveRaw.component root visit recognition U7 calculus anchor frame)
def installed := (actionEmbedding root visit recognition U7 calculus anchor (E.epoch frame) seed).trans
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (E.Shared.base frame).root.source.base
    (combined root visit recognition U7 calculus anchor (E.epoch frame) seed)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.baseRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.queryLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.queryRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.resultLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.resultRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.consumerLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.consumerRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.compilationLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed)))
def activeInstalled := (activeEmbedding root visit recognition U7 calculus anchor (E.epoch frame) seed).trans
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (E.Shared.base frame).root.source.base
    (combined root visit recognition U7 calculus anchor (E.epoch frame) seed)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.baseRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.queryLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.queryRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.resultLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.resultRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.consumerLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.Shared.consumerRoot frame (configuration root visit recognition U7 calculus anchor seed)).source.base
    (E.Shared.compilationLaw (E.epoch frame) (configuration root visit recognition U7 calculus anchor seed)))
def face : SourceNativeRootSemanticFaceAt (E.Shared.root frame (configuration root visit recognition U7 calculus anchor seed))
    (E.Shared.visit frame (configuration root visit recognition U7 calculus anchor seed)) where
  projection:=(installed root visit recognition U7 calculus anchor frame seed).embed PUnit.unit
  active:=PUnit.unit
  classifier_eq:=rfl
def activeFace : SourceNativeRootSemanticFaceAt (E.Shared.root frame (configuration root visit recognition U7 calculus anchor seed))
 (E.Shared.visit frame (configuration root visit recognition U7 calculus anchor seed)) where
 projection:=(activeInstalled root visit recognition U7 calculus anchor frame seed).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
theorem active_raw : (activeFace root visit recognition U7 calculus anchor frame seed).rootRead=
 ActiveRaw.rawAt root visit recognition U7 calculus anchor (E.epoch frame) (E.Shared.actualOccurrence frame) := rfl
abbrev initial := Observer.Installation.initial root visit recognition U7 calculus anchor
abbrev sourceSeed := Observer.Installation.seed root visit recognition U7 calculus anchor
abbrev programme := configuration root visit recognition U7 calculus anchor (sourceSeed root visit recognition U7 calculus anchor)
abbrev runtime := E.Shared.runtime (initial root visit recognition U7 calculus anchor) (programme root visit recognition U7 calculus anchor)
abbrev frameAt (stage : Nat) := E.Shared.frames (initial root visit recognition U7 calculus anchor)
  (programme root visit recognition U7 calculus anchor) stage
abbrev materialFace (stage : Nat) := face root visit recognition U7 calculus anchor (frameAt root visit recognition U7 calculus anchor stage)
  (sourceSeed root visit recognition U7 calculus anchor)
abbrev born (stage : Nat) := SourceGeneratedInquiryReceiptAction.Inventory.Born.generated
  (frameAt root visit recognition U7 calculus anchor stage) (programme root visit recognition U7 calculus anchor)
abbrev generated := (runtime root visit recognition U7 calculus anchor,
  fun stage => born root visit recognition U7 calculus anchor stage,
  fun stage => materialFace root visit recognition U7 calculus anchor stage)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
