import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Catalogue
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Source
import H0mework.Realization.Operations.Execution.InventoryVector.Source

set_option autoImplicit false
noncomputable section
universe u w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open RootLawDependentJointStateController RootLawDependentJointTransition
namespace SomePacket
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
abbrev currentVisit := SourceOperationNative.Tree.Fold.Dependent.Branch.Side.visit root code
abbrev step := recognition.generateStepAt (currentVisit root code)
variable (successor : StepLedgerSuccessorAt (step root recognition code))
abbrev SourceHistory := SourceHistoryCommon.Root.sourceHistory root (currentVisit root code) recognition
abbrev TargetHistory := SourceHistoryCommon.Root.targetHistory root (currentVisit root code) recognition successor
abbrev Data := SourceOperationNative.Tree.Fold.Dependent.Branch.Side.DataAt root recognition code (some successor)
variable (data : Data root recognition code successor)
abbrev sourceSeed := data.1.source.seed
abbrev targetSeed := data.1.target.seed
abbrev SourceRow := Fin (sourceSeed root recognition code successor data).trace.length
abbrev TargetRow := Fin (targetSeed root recognition code successor data).trace.length
abbrev SourceNode := Fin data.2.2.2.1.trace.length
abbrev TargetNode := Fin data.2.2.2.2.trace.length
abbrev Index := (SourceRow root recognition code successor data × TargetRow root recognition code successor data) ⊕
  ((SourceNode root recognition code successor data × SourceRow root recognition code successor data) ⊕
    (TargetNode root recognition code successor data × TargetRow root recognition code successor data))
abbrev Carrier := (SourceHistory root recognition code).CompletionCarrier ×
  (TargetHistory root recognition code successor).CompletionCarrier
variable (source_eq : sourceSeed root recognition code successor data = (SourceHistory root recognition code).seed)
variable (target_eq : targetSeed root recognition code successor data = (TargetHistory root recognition code successor).seed)
def sourcePoint (index : SourceRow root recognition code successor data) :
    (SourceHistory root recognition code).CompletionCarrier :=
  Catalogue.value (SourceHistory root recognition code)
    ⟨(sourceSeed root recognition code successor data).trace.get index,by
      rw [← source_eq]
      exact List.get_mem _ _⟩
def targetPoint (index : TargetRow root recognition code successor data) :
    (TargetHistory root recognition code successor).CompletionCarrier :=
  Catalogue.value (TargetHistory root recognition code successor)
    ⟨(targetSeed root recognition code successor data).trace.get index,by
      rw [← target_eq]
      exact List.get_mem _ _⟩
def point : Index root recognition code successor data → Carrier root recognition code successor
  | .inl pair => (sourcePoint root recognition code successor data source_eq pair.1,
      targetPoint root recognition code successor data target_eq pair.2)
  | .inr (.inl pair) => (sourcePoint root recognition code successor data source_eq pair.2,0)
  | .inr (.inr pair) => (0,targetPoint root recognition code successor data target_eq pair.2)
def action : Index root recognition code successor data →
    Carrier root recognition code successor →ₗ[ℤ] Carrier root recognition code successor
  | .inl _ => data.2.2.1.source.sourceAction.carrierAction.prodMap
      data.2.2.1.target.sourceAction.carrierAction
  | .inr (.inl pair) => ((data.2.2.2.1.trace.get pair.1).2.sourceAction.carrierAction).prodMap LinearMap.id
  | .inr (.inr pair) => LinearMap.id.prodMap ((data.2.2.2.2.trace.get pair.1).2.sourceAction.carrierAction)
abbrev OldValue := fun (_ : PUnit.{u+1}) => Carrier root recognition code successor
abbrev Variable := fun (_ : PUnit.{u+1}) => ULift.{u} (Index root recognition code successor data)
def environment : Env (OldValue root recognition code successor) (Variable root recognition code successor data) :=
  fun _ index => point root recognition code successor data source_eq target_eq index.down
def binding : ∀ slot, Variable root recognition code successor data slot →
    Expr (OldValue root recognition code successor) (Variable root recognition code successor data) slot :=
  fun _ index => .linear (action root recognition code successor data index.down).toAddMonoidHom (.var index)
-- Zero fills only the unused side of a coproduct; every operand comes from its own seed.
def indices : List (Index root recognition code successor data) :=
  (List.ofFn (fun first : SourceRow root recognition code successor data =>
    List.ofFn (fun second : TargetRow root recognition code successor data =>
      Sum.inl (first,second)))).flatten ++
  (List.ofFn (fun first : SourceNode root recognition code successor data =>
    List.ofFn (fun second : SourceRow root recognition code successor data =>
      Sum.inr (Sum.inl (first,second))))).flatten ++
  (List.ofFn (fun first : TargetNode root recognition code successor data =>
    List.ofFn (fun second : TargetRow root recognition code successor data =>
      Sum.inr (Sum.inr (first,second))))).flatten
def items : List (Index root recognition code successor data ×
    Expr (OldValue root recognition code successor) (Variable root recognition code successor data) PUnit.unit) :=
  (indices root recognition code successor data).map
    (fun index => (index,binding root recognition code successor data PUnit.unit ⟨index⟩))
def expression := InventoryVector.query (Index root recognition code successor data) (items root recognition code successor data)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=InventoryVector.VectorValue (Index root recognition code successor data) (Value:=OldValue root recognition code successor))
    (Var:=Variable root recognition code successor data) (sort:=PUnit.unit) :=
  ⟨InventoryVector.environment _ (environment root recognition code successor data source_eq target_eq),
    expression root recognition code successor data⟩
def trace := execution (raw root recognition code successor data source_eq target_eq).environment
  (raw root recognition code successor data source_eq target_eq).expression
def reader {_current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt _current) :=
  raw root recognition code successor data source_eq target_eq
def paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt root.toAuthoritativeRoot
  (reader root recognition code successor data source_eq target_eq) (root.emitted (currentVisit root code).current)
theorem source_seed_eq : sourceSeed root recognition code successor
    (SourceOperationNative.Tree.Fold.Dependent.Branch.Side.generateAt root recognition code (some successor)) =
      (SourceHistory root recognition code).seed := rfl
theorem target_seed_eq : targetSeed root recognition code successor
    (SourceOperationNative.Tree.Fold.Dependent.Branch.Side.generateAt root recognition code (some successor)) =
      (TargetHistory root recognition code successor).seed := rfl
end SomePacket

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
structure SomeResult (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
    (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
    (successor : StepLedgerSuccessorAt (SomePacket.step root recognition code)) where
  data : SomePacket.Data root recognition code successor
  source_eq : SomePacket.sourceSeed root recognition code successor data = (SomePacket.SourceHistory root recognition code).seed
  target_eq : SomePacket.targetSeed root recognition code successor data = (SomePacket.TargetHistory root recognition code successor).seed
  canonical : data = SourceOperationNative.Tree.Fold.Dependent.Branch.Side.generateAt root recognition code (some successor)
  result : type_of% (SomePacket.paid root recognition code successor data source_eq target_eq)
def ResultAt (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
    (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) :
    Option (StepLedgerSuccessorAt (SomePacket.step root recognition code)) → Type u
  | none => SourceTemporalMaterial.Action.Receipt root
  | some successor => SomeResult root recognition code successor
private def fromDataAt (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
    (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
    (selected : Option (StepLedgerSuccessorAt (SomePacket.step root recognition code)))
    (data : SourceOperationNative.Tree.Fold.Dependent.Branch.Side.DataAt root recognition code selected)
    (canonical : data = SourceOperationNative.Tree.Fold.Dependent.Branch.Side.generateAt root recognition code selected) :
    ResultAt root recognition code selected := by
  cases selected with
  | none => exact data
  | some successor =>
      let hs := (congrArg (SomePacket.sourceSeed root recognition code successor) canonical).trans
        (SomePacket.source_seed_eq root recognition code successor)
      let ht := (congrArg (SomePacket.targetSeed root recognition code successor) canonical).trans
        (SomePacket.target_seed_eq root recognition code successor)
      exact ⟨data,hs,ht,canonical,SomePacket.paid root recognition code successor data hs ht⟩

namespace SomeResult
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (SomePacket.step root recognition code))
variable (result : SomeResult root recognition code successor)
def raw := SomePacket.raw root recognition code successor result.data result.source_eq result.target_eq
def trace := SomePacket.trace root recognition code successor result.data result.source_eq result.target_eq
def paidState := result.result.2.1
def paidTrace := result.result.2.1.2
def value := result.result.2.2.1
def sourceMaterial := result.result.2.2.2
def material := (result.data,result.result,trace root recognition code successor result)
end SomeResult

def sourceOperationAtCode (root : SourceNativeLivingRootClosure N V)
    (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root) :=
  fromDataAt root recognition code (stepSuccessor? (SomePacket.step root recognition code))
    (SourceOperationNative.Tree.Fold.Dependent.Branch.Side.generate root recognition code) rfl

def sourceOperation (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root) :
    Σ actor : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Carrier root recognition,
      ResultAt root recognition actor.1.1 (stepSuccessor? (SomePacket.step root recognition actor.1.1)) :=
  let actor := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.nextActor root visit recognition
  ⟨actor,fromDataAt root recognition actor.1.1
    (stepSuccessor? (SomePacket.step root recognition actor.1.1)) actor.1.2 rfl⟩

def material (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root) :=
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.originalPaid root visit recognition,
    SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.paid root visit recognition,
    sourceOperation root visit recognition)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
