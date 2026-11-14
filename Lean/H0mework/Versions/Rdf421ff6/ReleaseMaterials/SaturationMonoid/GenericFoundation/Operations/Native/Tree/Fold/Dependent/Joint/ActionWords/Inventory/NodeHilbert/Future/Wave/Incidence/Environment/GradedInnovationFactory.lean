import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.JointMeasuredConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Factory.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source
import H0mework.Realization.Operations.InventoryLift.Substitution

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
namespace J
export PaidSourceContentEnvironment.JointMeasured
  (Slot Value OldSlot Orbit oldInjection measuredInjection decode expression)
end J
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (Factory Seed Packet cfg defaultFactory)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
  (Value groups)
end L
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
  (codeAt collapseValue code_base_value)
end CF
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
  (preserve liftEvent)
end T
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base baseRoot actualOccurrence datum resultFace root visit)
end S
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum epoch)
end A
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end I
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader actionResultAt)
end R
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (resultAt)
end O
namespace FG
export SourceGeneratedFiniteGram.Projection (gram rhs coefficients predictable innovationCLM compatible full_fibre)
end FG

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
abbrev Original (K : Type u) := J.Value K
abbrev W (K : Type u) := PairValue (PairValue (Original K))

/-- Admission writes its complete target value here. All old variables are
retained, but old source terms read their semantic restrictions from joint. -/
abbrev X : J.Slot → Type u
  | .old sort => PaidSourceMacroHistory.Var sort
  | .measured => PUnit.{u+1}
  | .joint => PUnit.{u+1}
local instance baseGroups (target : J.Slot) : AddCommGroup (W K target) := inferInstance
local instance familyGroups (n : Nat) (target : J.Slot) : AddCommGroup (L.Value (W K) n target) := L.groups (W K) n target
abbrev Frame (n : Nat) := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=L.Value (W K) n) (Var:=X) (sort:=.joint)

def orbitProjection : (J.Orbit × K) →+ J.Orbit := AddMonoidHom.fst _ _
def measuredProjection : (J.Orbit × K) →+ K := AddMonoidHom.snd _ _
def sourceBinding : (sort : J.Slot) → JointMeasured.Var sort → Expr (Original K) X sort
  | .old .model,_ => .linear (s:=.joint) orbitProjection (.var PUnit.unit)
  | .old .orbit,_ => .linear (s:=.joint) orbitProjection (.var PUnit.unit)
  | .measured,_ => .linear (s:=.joint) measuredProjection (.var PUnit.unit)
  | .joint,absent => PEmpty.elim absent
def pairBinding (sort : J.Slot) (name : JointMeasured.Var sort) := liftExpr (sourceBinding (K:=K) sort name)
def eventMap : PresentedRelationEventAt (Expr (Original K) JointMeasured.Var .joint) →
    PresentedRelationEventAt (Expr (Original K) X .joint)
  | .generator term => .generator (term.subst sourceBinding)
  | .relation word => .relation (substitution (R:=ℤ) sourceBinding word)
def pairEventMap : PresentedRelationEventAt (Expr (PairValue (Original K)) JointMeasured.Var .joint) →
    PresentedRelationEventAt (Expr (PairValue (Original K)) X .joint)
  | .generator term => .generator (term.subst pairBinding)
  | .relation word => .relation (substitution (R:=ℤ) pairBinding word)

def baseDatum (n : Nat) (seed : SF.Seed (W K) X .joint n) (frame : Frame (K:=K) n) :=
  (SF.defaultFactory (W K) X .joint).datum n seed frame
def sourceReader (n : Nat) (seed : SF.Seed (W K) X .joint n) (frame : Frame (K:=K) n)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : I.Occurrence frame (current:=current)) :=
  (baseDatum n seed frame).reader supplied
def stock (n : Nat) (frame : Frame (K:=K) n) :=
  T.preserve frame.inventory (RootedAccountedUnfolding.zero
    (PresentedRelationEventAt.generator frame.rawRead.expression))
def requests (n : Nat) (frame : Frame (K:=K) n) :=
  SourceInventoryExecutionFeed.requests (stock n frame)
abbrev Index (n : Nat) (frame : Frame (K:=K) n) :=
  Fin (requests n frame).length

variable (read : J.Orbit →ₗ[ℤ] K) (n : Nat)
variable (seed : SF.Seed (W K) X .joint n) (frame : Frame (K:=K) n)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current:=current))

/-- Collapse is used only after evaluation, as a feature measurement. The
source word, its whole pair carrier and both inventories remain unchanged. -/
def columns (index : Index n frame) : K :=
  let request := (requests n frame).get index
  let material := I.materialAt frame supplied
  let environment := pairEnvironment material.raw.environment
    (material.nextRaw.environment-material.raw.environment)
  let evaluated := (liftExpr request.expression).eval environment
  let fullBase := CF.collapseValue (W:=W K) n evaluated
  let measured := CF.collapseValue (W:=Original K) 2 fullBase
  let total := measured.1+measured.2
  request.coefficient • (read total.1+total.2)
def baseCode : Expr (PairValue (W K)) X .joint :=
  CF.codeAt (W:=Original K)
    (liftExpr ((J.expression read (columns read n frame supplied)).subst sourceBinding)) 2
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=PairValue (L.Value (W K) n)) (Var:=X) (sort:=.joint) :=
  ⟨(sourceReader n seed frame supplied).environment,
    CF.codeAt (baseCode read n frame supplied) n⟩
def calculation :=
  let source := columns read n frame supplied
  let baseEnvironment := fun target name => CF.collapseValue (W:=Original K) 2
    (CF.collapseValue (W:=W K) n ((sourceReader n seed frame supplied).environment target name))
  let measured := (liftExpr ((JointMeasured.inputTerm read).subst sourceBinding)).eval baseEnvironment
  let increment := measured.1+measured.2
  let matrix := FG.gram source
  let bill := FG.rhs source increment
  (I.materialAt frame supplied,seed,frame.inventory,frame.pairInventory,
    requests n frame,source,matrix,bill,
    SourceGeneratedFiniteGram.solutionClass matrix (Matrix.isHermitian_gram ℂ source) bill (FG.compatible source increment),
    FG.coefficients source increment,SourceGeneratedFiniteGram.Kernel matrix,
    (⟨fun a => FG.full_fibre source increment a⟩ : PLift (∀ a : SourceGeneratedFiniteGram.Coordinates (Index n frame),
      SourceGeneratedFiniteGram.action matrix a = bill ↔ a-FG.coefficients source increment ∈ SourceGeneratedFiniteGram.Kernel matrix)),
    FG.predictable source increment,FG.innovationCLM source increment,
    baseCode read n frame supplied,raw read n seed frame supplied)
def calculationLaw : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => type_of% (calculation read n seed frame occurrence)
  project := fun _ {_current} occurrence _ => calculation read n seed frame occurrence
def combinedLaw : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource :=
  match (baseDatum n seed frame).component with
  | none => calculationLaw read n seed frame
  | some old => ({(S.base frame).root.source.base with projectionLaw:=old}.withProjectionCoface
      (calculationLaw read n seed frame)).projectionLaw
def actualDatum : A.SourceDatum (PhysicalValue:=L.Value (W K) n) (PhysicalVar:=X)
    (sort:=.joint) X frame :=
  {baseDatum n seed frame with
    component := some (combinedLaw read n seed frame)
    calculationReader := some (fun {_sourceCurrent} occurrence => raw read n seed frame occurrence)}
def localCfg : A.Programme (PhysicalValue:=L.Value (W K) n) (PhysicalVar:=X) (sort:=.joint) where
  LowVar := X
  datum := actualDatum read n seed
  nextInventory := (SF.defaultFactory (W K) X .joint).nextInventory n seed
  nextPairInventory := (SF.defaultFactory (W K) X .joint).nextPairInventory n seed
def paid := O.resultAt (S.base frame).root.toAuthoritativeRoot
  (fun {_sourceCurrent} occurrence => raw read n seed frame occurrence) (S.actualOccurrence frame)
def pairedTrace :=
  let material := R.actualMaterial frame (localCfg read n seed)
  execution (pairEnvironment material.environment material.increment) (liftExpr material.raw)
def factory : SF.Factory (W K) X .joint where
  datum := actualDatum read
  nextInventory := (SF.defaultFactory (W K) X .joint).nextInventory
  nextPairInventory := (SF.defaultFactory (W K) X .joint).nextPairInventory
  extraScalar := fun grade source currentFrame => some (SourceOperationPaidRelations.exposure (paid read grade source currentFrame).2.1.2)
  extraPair := fun grade source currentFrame => some (SourceOperationPaidRelations.exposure (pairedTrace read grade source currentFrame))

namespace Origin
variable (read : J.Orbit →ₗ[ℤ] K) (sourceFrame : JointMeasured.Frame (K:=K))

abbrev paidFrame := JointMeasured.Phase.actualBorn read sourceFrame
abbrev paidCfg := SourceGeneratedInquiryReceiptAction.Inventory.Born.consumer
  (JointMeasured.Phase.stop sourceFrame) (JointMeasured.configuration read)
abbrev canonicalFrame := SourceGeneratedInquiryReceiptAction.bornFrame
  (paidFrame read sourceFrame) (paidCfg read sourceFrame)
def joint : W K .joint :=
  (SourceGeneratedInquiryReceiptAction.actionResultAt
    (paidFrame read sourceFrame) (paidCfg read sourceFrame)
    (S.actualOccurrence (paidFrame read sourceFrame))).2.2.1

def binding (target : J.Slot) (name : JointMeasured.Var target) : Expr (W K) X target :=
  liftExpr (liftExpr (sourceBinding (K:=K) target name))
def pairBinding (target : J.Slot) (name : JointMeasured.Var target) :=
  liftExpr (binding (K:=K) target name)
def eventMap : PresentedRelationEventAt (Expr (W K) JointMeasured.Var .joint) →
    PresentedRelationEventAt (Expr (W K) X .joint)
  | .generator term => .generator (term.subst binding)
  | .relation word => .relation (substitution (R:=ℤ) binding word)
def pairEventMap : PresentedRelationEventAt (Expr (PairValue (W K)) JointMeasured.Var .joint) →
    PresentedRelationEventAt (Expr (PairValue (W K)) X .joint)
  | .generator term => .generator (term.subst pairBinding)
  | .relation word => .relation (substitution (R:=ℤ) pairBinding word)

def environment : Env (W K) X
  | .old target,name => (canonicalFrame read sourceFrame).rawRead.environment (.old target) name
  | .measured,_ => (canonicalFrame read sourceFrame).rawRead.environment .measured PUnit.unit
  | .joint,_ => joint read sourceFrame

def input
    (occurrence : (canonicalFrame read sourceFrame).currentState.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      (canonicalFrame read sourceFrame).currentState.visit.current) :
    RootGeneratedDebtActivationJointSource.RawInputAt (Value:=W K) (Var:=X) (sort:=.joint)
      (canonicalFrame read sourceFrame).currentState.root.toAuthoritativeRoot.toLedgerRoot
      (canonicalFrame read sourceFrame).currentState.visit.current occurrence := by
  rcases occurrence with ⟨support,event⟩
  cases event
  exact { environment := environment read sourceFrame
          expression := (canonicalFrame read sourceFrame).rawRead.expression.subst binding
          owner := (canonicalFrame read sourceFrame).currentState.entryAt PUnit.unit }

def registered := RootGeneratedDebtActivationJointSource.register (input read sourceFrame)
def initial : Frame (K:=K) 0 where
  N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World
    (canonicalFrame read sourceFrame).registered
  V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
    (canonicalFrame read sourceFrame).registered (canonicalFrame read sourceFrame).packetAt
  old := (canonicalFrame read sourceFrame).currentState
  registered := registered read sourceFrame
  packetAt := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.programme
    (canonicalFrame read sourceFrame).old (canonicalFrame read sourceFrame).registered
    (canonicalFrame read sourceFrame).packetAt (canonicalFrame read sourceFrame).depth
  environment := fun {_current} _occurrence => environment read sourceFrame
  depth := 0
  inventory := (canonicalFrame read sourceFrame).inventory.map (fun prior => prior.map eventMap)
  pairInventory := (canonicalFrame read sourceFrame).pairInventory.map (fun prior => prior.map pairEventMap)
def sourceSeed := stock 0 (initial read sourceFrame)
def firstCfg := SF.cfg (factory read) 0 (sourceSeed read sourceFrame)
def material := (JointMeasured.Phase.generated read sourceFrame,
  canonicalFrame read sourceFrame,joint read sourceFrame,
  (canonicalFrame read sourceFrame).rawRead,
  (canonicalFrame read sourceFrame).inventory,(canonicalFrame read sourceFrame).pairInventory,
  initial read sourceFrame)
end Origin

end PaidSourceContentEnvironment.GradedInnovation
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
