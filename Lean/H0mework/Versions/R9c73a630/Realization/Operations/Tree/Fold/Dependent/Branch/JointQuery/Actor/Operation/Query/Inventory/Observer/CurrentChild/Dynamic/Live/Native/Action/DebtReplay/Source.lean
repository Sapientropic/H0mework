import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace P
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live (sourceSeed)
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow (Variable right)
end L
end P
namespace Original
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake (sourceFrame sourceProgramme)
namespace ActionCfg
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action (configuration)
end ActionCfg
end Original
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence query datum next runtime frames)
end Shared
end A
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage : Nat)
abbrev Value := CurrentChild.Value root visit recognition
abbrev Variable := CurrentChild.Variable root visit recognition
abbrev slot := CurrentChild.resultSlot root recognition
local instance : ∀ s,AddCommGroup (Value root visit recognition s) := inferInstance
abbrev Frame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Value root visit recognition) (Var:=Variable root visit recognition) (sort:=slot root recognition)
abbrev originalConfiguration := Original.sourceProgramme root visit recognition U7 calculus anchor sourceStage
namespace Lower
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
abbrev originalRaw := ((originalConfiguration root visit recognition U7 calculus anchor sourceStage).datum frame).reader supplied
def debtTerm := P.L.right (liftExpr frame.rawRead.expression)
def raw : type_of% (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied) :=
 ⟨(originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).environment,
  .add (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).expression (debtTerm root visit recognition frame)⟩
def paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (A.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} occurrence => raw root visit recognition U7 calculus anchor sourceStage frame occurrence) supplied
abbrev trace := (paid root visit recognition U7 calculus anchor sourceStage frame supplied).2.1.2
-- The old Raw and its source environment remain literal assets alongside the replay.
def material := (frame.rawRead,frame.paidRead,
 originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied,
 debtTerm root visit recognition frame,raw root visit recognition U7 calculus anchor sourceStage frame supplied,
 trace root visit recognition U7 calculus anchor sourceStage frame supplied,
 paid root visit recognition U7 calculus anchor sourceStage frame supplied,
 (originalConfiguration root visit recognition U7 calculus anchor sourceStage).nextInventory frame,
 (originalConfiguration root visit recognition U7 calculus anchor sourceStage).nextPairInventory frame)
def component : SourceNativeProjectionLaw (A.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit.{u+1}
 ActiveAt:=fun _ {_current} _ => PUnit.{u+1}
 InactiveAt:=fun _ {_current} _ => PEmpty.{u+1}
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun _ {_current} occurrence _ => type_of% (material root visit recognition U7 calculus anchor sourceStage frame occurrence)
 project:=fun _ {_current} occurrence _ => material root visit recognition U7 calculus anchor sourceStage frame occurrence
def combined := match ((originalConfiguration root visit recognition U7 calculus anchor sourceStage).datum frame).component with
 | none => component root visit recognition U7 calculus anchor sourceStage frame
 | some old => ({(A.Shared.base frame).root.source.base with projectionLaw:=old}.withProjectionCoface
  (component root visit recognition U7 calculus anchor sourceStage frame)).projectionLaw
end Lower
-- The actual reader changes before query and result emission; the original decoder is retained.
def configuration := {originalConfiguration root visit recognition U7 calculus anchor sourceStage with
 datum:=fun frame => {((originalConfiguration root visit recognition U7 calculus anchor sourceStage).datum frame) with
  component:=some (Lower.combined root visit recognition U7 calculus anchor sourceStage frame)
  reader:=fun {_current} supplied => Lower.raw root visit recognition U7 calculus anchor sourceStage frame supplied} }
variable (stage : Nat)
abbrev sourceFrame := Original.sourceFrame root visit recognition U7 calculus anchor sourceStage stage
abbrev supplied := A.Shared.actualOccurrence (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
abbrev sourceRaw := Lower.raw root visit recognition U7 calculus anchor sourceStage
 (A.epoch (sourceFrame root visit recognition U7 calculus anchor sourceStage stage))
 (supplied root visit recognition U7 calculus anchor sourceStage stage)
abbrev sourceMaterial := SourceGeneratedInquiryReceiptAction.actualMaterial
 (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
 (configuration root visit recognition U7 calculus anchor sourceStage)
namespace Embedding
variable {S : Type u} {A X B Y : S → Type u} [∀ s,AddCommGroup (A s)] [∀ s,AddCommGroup (B s)] {s : S}
def event (map : Expr A X s → Expr B Y s) : PresentedRelationEventAt (Expr A X s) → PresentedRelationEventAt (Expr B Y s)
 | .generator term => .generator (map term)
 | .relation word => .relation (Finsupp.mapDomain map word)
end Embedding
def scalarEmbedding (term : Expr (Value root visit recognition) (Variable root visit recognition) (slot root recognition)) :=
 P.L.right (liftExpr term)
def pairEmbedding (term : Expr (PairValue (Value root visit recognition)) (Variable root visit recognition) (slot root recognition)) :=
 P.L.right (liftExpr term)
def originalScalar := SourceHistoryCommon.seed
 ((P.sourceSeed root visit recognition U7 calculus anchor sourceStage).map (Embedding.event (scalarEmbedding root visit recognition)))
 (match (originalConfiguration root visit recognition U7 calculus anchor sourceStage).nextInventory
   (sourceFrame root visit recognition U7 calculus anchor sourceStage stage) with
 | none => RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (scalarEmbedding root visit recognition
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).registered.input.expression))
 | some stock => stock.map (Embedding.event (scalarEmbedding root visit recognition)))
def originalPair : RootedAccountedUnfolding (PresentedRelationEventAt
 (Expr (PairValue (PairValue (Value root visit recognition)))
  (P.L.Variable (X:=Variable root visit recognition)) (slot root recognition))) := match (originalConfiguration root visit recognition U7 calculus anchor sourceStage).nextPairInventory
 (sourceFrame root visit recognition U7 calculus anchor sourceStage stage) with
 | none => RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (pairEmbedding root visit recognition
  (liftExpr (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).registered.input.expression)))
 | some stock => stock.map (Embedding.event (pairEmbedding root visit recognition))
abbrev bareReceiver := SourceGeneratedInquiryReceiptAction.Configured.lowInitial
 (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
 (configuration root visit recognition U7 calculus anchor sourceStage)
def scalarStock := SourceHistoryCommon.seed
 (SourceGeneratedInquiryReceiptAction.Configured.lowWritten
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
  (configuration root visit recognition U7 calculus anchor sourceStage))
 (originalScalar root visit recognition U7 calculus anchor sourceStage stage)
def pairStock := SourceHistoryCommon.seed
 (SourceGeneratedInquiryReceiptAction.Configured.lowPairWritten
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
  (configuration root visit recognition U7 calculus anchor sourceStage))
 (originalPair root visit recognition U7 calculus anchor sourceStage stage)
def receiver := {bareReceiver root visit recognition U7 calculus anchor sourceStage stage with
 inventory:=some (scalarStock root visit recognition U7 calculus anchor sourceStage stage)
 pairInventory:=some (pairStock root visit recognition U7 calculus anchor sourceStage stage)}
def seed := SourceHistoryCommon.seed (scalarStock root visit recognition U7 calculus anchor sourceStage stage)
 (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (receiver root visit recognition U7 calculus anchor sourceStage stage).registered.input.expression))
abbrev receiverConfiguration := Original.ActionCfg.configuration root visit recognition
 (seed root visit recognition U7 calculus anchor sourceStage stage)
abbrev runtime := A.Shared.runtime (receiver root visit recognition U7 calculus anchor sourceStage stage)
 (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage)
abbrev frameAt := A.Shared.frames (receiver root visit recognition U7 calculus anchor sourceStage stage)
 (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
