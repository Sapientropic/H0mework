import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Outgoing.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Action.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Runtime

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live
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
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Dynamic.Frame root visit recognition)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt
 (Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition) (CurrentChild.resultSlot root recognition))))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Dynamic.C.Occurrence frame (current:=current))
abbrev originalRawAt := ((R.programme seed).datum frame).reader supplied
def dynamicRawAt : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (CurrentChild.Value root visit recognition)) (Var:=CurrentChild.Variable root visit recognition)
 (sort:=CurrentChild.resultSlot root recognition) :=
 ⟨pairEnvironment (Dynamic.environmentAt root visit recognition frame supplied)
   (Dynamic.Action.incrementAt root visit recognition frame supplied),
  liftExpr (Dynamic.rawAt root visit recognition U7 calculus anchor frame supplied).expression⟩
def rawAt := JointLow.raw (originalRawAt root visit recognition frame seed supplied).environment
 (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).environment
 (originalRawAt root visit recognition frame seed supplied).expression
 (dynamicRawAt root visit recognition U7 calculus anchor frame supplied).expression
def paidAt := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (E.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} occurrence => rawAt root visit recognition U7 calculus anchor frame seed occurrence) supplied
def traceAt := execution (rawAt root visit recognition U7 calculus anchor frame seed supplied).environment
 (rawAt root visit recognition U7 calculus anchor frame seed supplied).expression
def materialAt := (R.material seed frame supplied,
 Dynamic.Action.materialAt root visit recognition U7 calculus anchor frame supplied,
 originalRawAt root visit recognition frame seed supplied,dynamicRawAt root visit recognition U7 calculus anchor frame supplied,
 rawAt root visit recognition U7 calculus anchor frame seed supplied,
 paidAt root visit recognition U7 calculus anchor frame seed supplied,
 traceAt root visit recognition U7 calculus anchor frame seed supplied)
def component : SourceNativeProjectionLaw (E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit.{u+1}
 ActiveAt:=fun _ {_current} _ => PUnit.{u+1}
 InactiveAt:=fun _ {_current} _ => PEmpty.{u+1}
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun _ {_current} occurrence _ => type_of% (materialAt root visit recognition U7 calculus anchor frame seed occurrence)
 project:=fun _ {_current} occurrence _ => materialAt root visit recognition U7 calculus anchor frame seed occurrence
def mainRawComponent : SourceNativeProjectionLaw (E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit.{u+1}
 ActiveAt:=fun _ {_current} _ => PUnit.{u+1}
 InactiveAt:=fun _ {_current} _ => PEmpty.{u+1}
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun _ {_current} occurrence _ => type_of% (rawAt root visit recognition U7 calculus anchor frame seed occurrence)
 project:=fun _ {_current} occurrence _ => rawAt root visit recognition U7 calculus anchor frame seed occurrence
def materialCombined : SourceNativeProjectionLaw (E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource :=
 ({(E.Shared.base frame).root.source.base with projectionLaw:=R.component seed frame}.withProjectionCoface
 (component root visit recognition U7 calculus anchor frame seed)).projectionLaw
def combined : SourceNativeProjectionLaw (E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource :=
 ({(E.Shared.base frame).root.source.base with projectionLaw:=materialCombined root visit recognition U7 calculus anchor frame seed}.withProjectionCoface
 (mainRawComponent root visit recognition U7 calculus anchor frame seed)).projectionLaw
def physicalWritten := SourceOperationPaidRelations.exposure frame.paidRead.state.2
def actorWritten := SourceHistoryCommon.seed
 (SourceOperationPaidRelations.exposure
  (Dynamic.actorPaidAt root visit recognition frame (E.Shared.actualOccurrence frame)).2.1.2)
 (SourceOperationPaidRelations.exposure
  (Dynamic.actorPaidFor root visit recognition frame (Dynamic.nextRead root visit recognition frame)
   (E.Shared.actualOccurrence frame)).2.1.2)
def currentWritten := SourceHistoryCommon.seed
 (SourceOperationPaidRelations.exposure
  (Dynamic.paidAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)).2.1.2)
 (SourceOperationPaidRelations.exposure
  (Dynamic.traceAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)))
def written := SourceHistoryCommon.seed (actorWritten root visit recognition frame)
 (SourceHistoryCommon.seed (currentWritten root visit recognition U7 calculus anchor frame)
  (Dynamic.Action.written root visit recognition U7 calculus anchor frame))
def accumulated := SourceHistoryCommon.seed
 (match frame.inventory with
 | none => physicalWritten root visit recognition frame
 | some prior => SourceHistoryCommon.seed prior (physicalWritten root visit recognition frame))
 (written root visit recognition U7 calculus anchor frame)
def nextScalar := match (R.programme seed).nextInventory frame with
 | none => accumulated root visit recognition U7 calculus anchor frame
 | some prior => SourceHistoryCommon.seed prior (accumulated root visit recognition U7 calculus anchor frame)
def pairEvent : PresentedRelationEventAt
 (Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition) (CurrentChild.resultSlot root recognition)) →
 PresentedRelationEventAt
 (Expr (PairValue (CurrentChild.Value root visit recognition)) (CurrentChild.Variable root visit recognition) (CurrentChild.resultSlot root recognition))
 | .generator term => .generator (liftExpr term)
 | .relation word => .relation (Finsupp.mapDomain liftExpr word)
def pairWritten := (written root visit recognition U7 calculus anchor frame).map
 (pairEvent root visit recognition)
def nextPair := match (R.programme seed).nextPairInventory frame with
 | none => pairWritten root visit recognition U7 calculus anchor frame
 | some prior => SourceHistoryCommon.seed prior (pairWritten root visit recognition U7 calculus anchor frame)
def configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=CurrentChild.Value root visit recognition) (PhysicalVar:=CurrentChild.Variable root visit recognition)
 (sort:=CurrentChild.resultSlot root recognition) where
 LowVar:=JointLow.Variable (X:=CurrentChild.Variable root visit recognition)
 datum:=fun sourceFrame => {
  component:=some (combined root visit recognition U7 calculus anchor sourceFrame seed)
  reader:=fun {_current} occurrence => rawAt root visit recognition U7 calculus anchor sourceFrame seed occurrence
  nextEnvironmentReadAt:=some (fun {_current} occurrence _ =>
   Dynamic.generatedEnvironmentAt root visit recognition sourceFrame occurrence) }
 nextInventory:=fun sourceFrame => some (nextScalar root visit recognition U7 calculus anchor sourceFrame seed)
 nextPairInventory:=fun sourceFrame => some (nextPair root visit recognition U7 calculus anchor sourceFrame seed)
def materialEmbedding : SourceNativeProjectionLaw.InstallationAt
 (component root visit recognition U7 calculus anchor frame seed) (materialCombined root visit recognition U7 calculus anchor frame seed) :=
 SourceNativeProjectionLaw.InstallationAt.componentCoface
 ({(E.Shared.base frame).root.source.base with projectionLaw:=R.component seed frame})
 (component root visit recognition U7 calculus anchor frame seed)
def embedding : SourceNativeProjectionLaw.InstallationAt
 (component root visit recognition U7 calculus anchor frame seed) (combined root visit recognition U7 calculus anchor frame seed) :=
 (materialEmbedding root visit recognition U7 calculus anchor frame seed).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  ({(E.Shared.base frame).root.source.base with projectionLaw:=materialCombined root visit recognition U7 calculus anchor frame seed})
  (mainRawComponent root visit recognition U7 calculus anchor frame seed))
def mainRawEmbedding : SourceNativeProjectionLaw.InstallationAt
 (mainRawComponent root visit recognition U7 calculus anchor frame seed) (combined root visit recognition U7 calculus anchor frame seed) :=
 SourceNativeProjectionLaw.InstallationAt.componentCoface
 ({(E.Shared.base frame).root.source.base with projectionLaw:=materialCombined root visit recognition U7 calculus anchor frame seed})
 (mainRawComponent root visit recognition U7 calculus anchor frame seed)
def installed := (embedding root visit recognition U7 calculus anchor (E.epoch frame) seed).trans
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
def mainRawInstalled := (mainRawEmbedding root visit recognition U7 calculus anchor (E.epoch frame) seed).trans
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
 projection := (installed root visit recognition U7 calculus anchor frame seed).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def mainRawFace : SourceNativeRootSemanticFaceAt (E.Shared.root frame (configuration root visit recognition U7 calculus anchor seed))
 (E.Shared.visit frame (configuration root visit recognition U7 calculus anchor seed)) where
 projection := (mainRawInstalled root visit recognition U7 calculus anchor frame seed).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
theorem main_raw : (mainRawFace root visit recognition U7 calculus anchor frame seed).rootRead=
 rawAt root visit recognition U7 calculus anchor (E.epoch frame) seed (E.Shared.actualOccurrence frame) := rfl
variable (sourceStage : Nat)
abbrev initial := Dynamic.initial root visit recognition U7 calculus anchor sourceStage
abbrev sourceSeed := Dynamic.sourceSeed root visit recognition U7 calculus anchor sourceStage
abbrev programme := configuration root visit recognition U7 calculus anchor (sourceSeed root visit recognition U7 calculus anchor sourceStage)
abbrev runtime := E.Shared.runtime (initial root visit recognition U7 calculus anchor sourceStage)
 (programme root visit recognition U7 calculus anchor sourceStage)
abbrev frameAt (stage : Nat) := E.Shared.frames (initial root visit recognition U7 calculus anchor sourceStage)
 (programme root visit recognition U7 calculus anchor sourceStage) stage
abbrev materialFace (stage : Nat) := face root visit recognition U7 calculus anchor
 (frameAt root visit recognition U7 calculus anchor sourceStage stage)
 (sourceSeed root visit recognition U7 calculus anchor sourceStage)
def birthCount : Nat → Nat
 | 0 => CurrentActor.birthCount root visit recognition U7 calculus anchor sourceStage
 | count+1 => match (frameAt root visit recognition U7 calculus anchor sourceStage count).action with
  | .inr _ => birthCount count
  | .inl _ => birthCount count+1
def nodeAt (stage : Nat) :=
 (Branch.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor sourceStage stage]
 (Branch.node root visit recognition)
def actorAt (stage : Nat) := Branch.Fresh.Outcome.complete root recognition visit
 (Branch.constructor root visit recognition (nodeAt root visit recognition U7 calculus anchor sourceStage stage) [])
def nextActorAt (stage : Nat) := Branch.Fresh.Outcome.complete root recognition visit
 (Branch.constructor root visit recognition (Branch.nextNode root visit recognition
  (nodeAt root visit recognition U7 calculus anchor sourceStage stage)) [])
abbrev receipt (stage : Nat) := SourceGeneratedInquiryReceiptAction.generated
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)

abbrev lowBareInitial (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.lowBareInitial
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev lowStock (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.lowStock
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev outgoingMaterial (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.outgoingMaterial
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev outgoingScalar (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.outgoingScalar
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev outgoingPair (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.outgoingPair
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev lowWritten (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.lowWritten
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev lowPairWritten (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.lowPairWritten
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev lowInitial (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.lowInitial
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev lowSeed (stage : Nat) := SourceGeneratedInquiryReceiptAction.Configured.lowSeed
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)
abbrev lowProgramme (stage : Nat) := R.programme (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
abbrev lowRuntime (stage : Nat) := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.runtime
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage) (lowInitial root visit recognition U7 calculus anchor sourceStage stage)
abbrev lowFrameAt (stage offset : Nat) := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.frameAt
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage) (lowInitial root visit recognition U7 calculus anchor sourceStage stage) offset
abbrev lowFace (stage offset : Nat) := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.face
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage) (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset)
abbrev generated := (runtime root visit recognition U7 calculus anchor sourceStage,
 fun stage => receipt root visit recognition U7 calculus anchor sourceStage stage,
 fun stage => lowRuntime root visit recognition U7 calculus anchor sourceStage stage)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
