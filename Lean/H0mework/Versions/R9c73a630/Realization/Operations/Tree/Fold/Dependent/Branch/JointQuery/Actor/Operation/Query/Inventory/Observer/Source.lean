import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.Source
import H0mework.Versions.R9c73a630.Realization.Perfectification.Occurrence.Temporal.History.Common.Action.Source
import H0mework.Realization.Operations.ObservationModel

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition
open SourceOperationEffects SourceOperationExecution
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence)
end Shared
end E
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
abbrev Row := Σ index : Inventory.ChildIndex root recognition,
  Inventory.P.Index root recognition index.1 index.2 (Inventory.childData root recognition index)
def rowsAtCode (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) : List (Row root recognition) :=
  match stepSuccessor? (Inventory.P.step root recognition code) with
  | none => []
  | some successor => (Operation.SomePacket.indices root recognition code successor
      (Inventory.childData root recognition ⟨code,successor⟩)).map (fun row => ⟨⟨code,successor⟩,row⟩)
def rows := rowsAtCode root recognition (Inventory.oldCode root visit recognition) ++
  rowsAtCode root recognition (Inventory.nextCode root visit recognition)
abbrev Index := Fin (rows root visit recognition).length
def rowAt (index : Index root visit recognition) := (rows root visit recognition).get index
abbrev Measured := WithLp 2 (H × H)
abbrev Carrier (row : Row root recognition) := Inventory.P.Carrier root recognition row.1.1 row.1.2
abbrev sourceRawType (row : Row root recognition) := type_of% (Side.sourceExposureTree root recognition row.1.1).root
abbrev targetRawType (row : Row root recognition) := type_of% (Side.targetExposureTree root recognition row.1.1 row.1.2).root
def sourceExposure (row : Row root recognition) : sourceRawType root recognition row :=
  match row.2 with
  | .inr (.inl pair) => (Inventory.childData root recognition row.1).2.2.2.1.trace.get pair.1
  | _ => ⟨stepSourcePairing (Inventory.P.step root recognition row.1.1),
      (Inventory.childData root recognition row.1).2.2.1.source⟩
def targetExposure (row : Row root recognition) : targetRawType root recognition row :=
  match row.2 with
  | .inr (.inr pair) => (Inventory.childData root recognition row.1).2.2.2.2.trace.get pair.1
  | _ => ⟨stepTargetPairing (Inventory.P.step root recognition row.1.1) row.1.2,
      (Inventory.childData root recognition row.1).2.2.1.target⟩
def measurement (row : Row root recognition) : Carrier root recognition row →ₗ[ℤ] Measured (H:=H) :=
  (WithLp.linearEquiv 2 ℤ (H × H)).symm.toLinearMap.comp
    ((sourceExposure root recognition row).2.measurement.prodMap (targetExposure root recognition row).2.measurement)
def action (row : Row root recognition) : Carrier root recognition row →ₗ[ℤ] Carrier root recognition row :=
  Operation.SomePacket.action root recognition row.1.1 row.1.2 (Inventory.childData root recognition row.1) row.2
def sourceEvolution (row : Row root recognition) : H →ₗᵢ[ℂ] H :=
  (sourceExposure root recognition row).2.hilbertEvolution
def targetEvolution (row : Row root recognition) : H →ₗᵢ[ℂ] H :=
  (targetExposure root recognition row).2.hilbertEvolution
def evolution (row : Row root recognition) : Measured (H:=H) →ₗᵢ[ℂ] Measured (H:=H) :=
  (sourceEvolution root recognition row).withLpProdMap 2 (targetEvolution root recognition row)
abbrev Model (row : Row root recognition) := SourceGeneratedActionObservationHistory.Model
  (action root recognition row) (measurement root recognition row)
def modelProjection (row : Row root recognition) := SourceGeneratedActionObservationHistory.projection
  (action root recognition row) (measurement root recognition row)
def modelAction (row : Row root recognition) := SourceGeneratedActionObservationHistory.modelAction
  (action root recognition row) (measurement root recognition row)

variable (frame : Inventory.Action.Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Inventory.Action.C.Occurrence frame (current:=current))
def pointAt (row : Row root recognition) : Carrier root recognition row :=
  Inventory.Action.environmentAt root visit recognition frame supplied (.inr (.inl row.1)) ⟨row.2⟩ row.2
def nextPointAt (row : Row root recognition) : Carrier root recognition row :=
  Inventory.Action.generatedEnvironmentAt root visit recognition frame supplied (.inr (.inl row.1)) ⟨row.2⟩ row.2

theorem next_point_at (row : Row root recognition) : nextPointAt root visit recognition frame supplied row =
    action root recognition row (pointAt root visit recognition frame supplied row) :=
  rfl

theorem actual_model_at (row : Row root recognition) :
    modelAction root recognition row (modelProjection root recognition row (pointAt root visit recognition frame supplied row)) =
      modelProjection root recognition row (nextPointAt root visit recognition frame supplied row) :=
  (SourceGeneratedActionObservationHistory.modelAction_source (action root recognition row) (measurement root recognition row)
    (pointAt root visit recognition frame supplied row)).trans
      (congrArg (modelProjection root recognition row) (next_point_at root visit recognition frame supplied row).symm)

inductive ExtraSlot : Type u | measurement | gram | output deriving DecidableEq
abbrev Slot := Inventory.Slot root recognition ⊕ (Inventory.ChildIndex root recognition ⊕ ExtraSlot.{u})
abbrev Observations := Index root visit recognition → Fin 4 → Measured (H:=H)
abbrev Sample := Index root visit recognition × Fin 4
abbrev Gram := Sample root visit recognition → Sample root visit recognition → ULift.{u} ℂ
abbrev Output := Inventory.Output root visit recognition × Observations root visit recognition × Gram root visit recognition
abbrev Value : Slot root recognition → Type u
  | .inl slot => Inventory.Value root visit recognition slot
  | .inr (.inl index) => Inventory.P.Carrier root recognition index.1 index.2
  | .inr (.inr .measurement) => Measured (H:=H)
  | .inr (.inr .gram) => ULift.{u} ℂ
  | .inr (.inr .output) => Output root visit recognition
abbrev Variable : Slot root recognition → Type u
  | .inl slot => Inventory.Variable root visit recognition slot
  | .inr _ => PEmpty.{u+1}
instance : ∀ slot, AddCommGroup (Value root visit recognition slot)
  | .inl _ => inferInstance
  | .inr (.inl _) => inferInstance
  | .inr (.inr .measurement) => inferInstance
  | .inr (.inr .gram) => inferInstance
  | .inr (.inr .output) => inferInstance
abbrev resultSlot : Slot root recognition := .inr (.inr .output)
abbrev measuredSlot : Slot root recognition := .inr (.inr .measurement)
abbrev gramSlot : Slot root recognition := .inr (.inr .gram)
def environmentAt : Env (Value root visit recognition) (Variable root visit recognition)
  | .inl slot, name => Inventory.Action.environmentAt root visit recognition frame supplied slot name
  | .inr _, absent => PEmpty.elim absent

def embed {slot : Inventory.Slot root recognition} : Expr (Inventory.Value root visit recognition)
    (Inventory.Variable root visit recognition) slot → Expr (Value root visit recognition) (Variable root visit recognition) (.inl slot)
  | .var name => .var name
  | .const value => .const value
  | .add first second => .add (embed first) (embed second)
  | .linear operation argument => .linear operation (embed argument)
  | .bilinear operation first second => .bilinear operation (embed first) (embed second)
def coordinate (row : Row root recognition) : Inventory.ChildValue root recognition row.1 →+ Carrier root recognition row where
  toFun value := value row.2
  map_zero' := rfl
  map_add' _ _ := rfl

def pointTerm (row : Row root recognition) : Expr (Value root visit recognition) (Variable root visit recognition) (.inr (.inl row.1)) :=
  .linear (s:=.inl (.inr (.inl row.1))) (coordinate root recognition row) ((.var (⟨row.2⟩ : Inventory.ChildVar root recognition row.1)) :
      Expr (Value root visit recognition) (Variable root visit recognition) (.inl (.inr (.inl row.1))))
def nextPointTerm (row : Row root recognition) : Expr (Value root visit recognition) (Variable root visit recognition) (.inr (.inl row.1)) :=
  .linear (s:=.inl (.inr (.inl row.1))) (coordinate root recognition row)
    (embed root visit recognition (Inventory.Action.binding root visit recognition (.inr (.inl row.1)) ⟨row.2⟩))
def measuredTerm (row : Row root recognition) : Expr (Value root visit recognition) (Variable root visit recognition) (measuredSlot root recognition) :=
  .linear (s:=.inr (.inl row.1)) (measurement root recognition row).toAddMonoidHom (pointTerm root visit recognition row)
def nextMeasuredTerm (row : Row root recognition) : Expr (Value root visit recognition) (Variable root visit recognition) (measuredSlot root recognition) :=
  .linear (s:=.inr (.inl row.1)) (measurement root recognition row).toAddMonoidHom (nextPointTerm root visit recognition row)
def coherentTerm (row : Row root recognition) : Expr (Value root visit recognition) (Variable root visit recognition) (measuredSlot root recognition) :=
  .linear (s:=measuredSlot root recognition) (evolution root recognition row).toLinearMap.toAddMonoidHom (measuredTerm root visit recognition row)
def residualTerm (row : Row root recognition) : Expr (Value root visit recognition) (Variable root visit recognition) (measuredSlot root recognition) :=
  .add (coherentTerm root visit recognition row) (.linear (s:=measuredSlot root recognition)
    (-AddMonoidHom.id _) (nextMeasuredTerm root visit recognition row))
def observationTerm (index : Index root visit recognition) (kind : Fin 4) :=
  match kind.val with
  | 0 => measuredTerm root visit recognition (rowAt root visit recognition index)
  | 1 => nextMeasuredTerm root visit recognition (rowAt root visit recognition index)
  | 2 => coherentTerm root visit recognition (rowAt root visit recognition index)
  | _ => residualTerm root visit recognition (rowAt root visit recognition index)

def innerOperation : Measured (H:=H) →+ Measured (H:=H) →+ ULift.{u} ℂ where
  toFun first := {
    toFun := fun second => ⟨inner ℂ first second⟩
    map_zero' := by apply ULift.ext; exact inner_zero_right _
    map_add' := by intro second third; apply ULift.ext; exact inner_add_right _ _ _ }
  map_zero' := by ext second; exact inner_zero_left _
  map_add' := by intro first second; ext third; exact inner_add_left _ _ _
def gramTerm (first second : Sample root visit recognition) :
    Expr (Value root visit recognition) (Variable root visit recognition) (gramSlot root recognition) :=
  .bilinear (s:=measuredSlot root recognition) (t:=measuredSlot root recognition) innerOperation
    (observationTerm root visit recognition first.1 first.2)
    (observationTerm root visit recognition second.1 second.2)

def oldInjection : Inventory.Output root visit recognition →+ Output root visit recognition := (AddMonoidHom.id _).prod 0
def oldOutputEmbed (term : Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition)
    (Inventory.resultSlot root recognition)) : Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  .linear (s:=.inl (Inventory.resultSlot root recognition)) (oldInjection root visit recognition) (embed root visit recognition term)
def pairEmbed {slot : Inventory.Slot root recognition} :
    Expr (SourceOperationScalarInventoryLift.PairValue (Inventory.Value root visit recognition))
      (Inventory.Variable root visit recognition) slot →
    Expr (SourceOperationScalarInventoryLift.PairValue (Value root visit recognition))
      (Variable root visit recognition) (.inl slot)
  | .var name => .var name
  | .const value => .const value
  | .add first second => .add (pairEmbed first) (pairEmbed second)
  | @Expr.linear _ _ _ _ source target operation argument =>
      Expr.linear (Value:=SourceOperationScalarInventoryLift.PairValue (Value root visit recognition))
        (Var:=Variable root visit recognition) (s:=Sum.inl source) (t:=Sum.inl target) operation (pairEmbed argument)
  | @Expr.bilinear _ _ _ _ firstSort secondSort target operation first second =>
      Expr.bilinear (Value:=SourceOperationScalarInventoryLift.PairValue (Value root visit recognition))
        (Var:=Variable root visit recognition) (s:=Sum.inl firstSort) (t:=Sum.inl secondSort) (r:=Sum.inl target)
        operation (pairEmbed first) (pairEmbed second)
def pairOutputEmbed (term : Expr (SourceOperationScalarInventoryLift.PairValue (Inventory.Value root visit recognition))
    (Inventory.Variable root visit recognition) (Inventory.resultSlot root recognition)) :
    Expr (SourceOperationScalarInventoryLift.PairValue (Value root visit recognition))
      (Variable root visit recognition) (resultSlot root recognition) :=
  Expr.linear (Value:=SourceOperationScalarInventoryLift.PairValue (Value root visit recognition))
    (Var:=Variable root visit recognition) (s:=.inl (Inventory.resultSlot root recognition)) (t:=resultSlot root recognition)
    ((oldInjection root visit recognition).prodMap (oldInjection root visit recognition)) (pairEmbed root visit recognition term)
def eventMap : CofinalHistorySettlement.PresentedRelationEventAt
    (Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition) (Inventory.resultSlot root recognition)) →
    CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))
  | .generator term => .generator (oldOutputEmbed root visit recognition term)
  | .relation word => .relation (Finsupp.mapDomain (oldOutputEmbed root visit recognition) word)
def pairEventMap : CofinalHistorySettlement.PresentedRelationEventAt
    (Expr (SourceOperationScalarInventoryLift.PairValue (Inventory.Value root visit recognition))
      (Inventory.Variable root visit recognition) (Inventory.resultSlot root recognition)) →
    CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root visit recognition))
        (Variable root visit recognition) (resultSlot root recognition))
  | .generator term => .generator (pairOutputEmbed root visit recognition term)
  | .relation word => .relation (Finsupp.mapDomain (pairOutputEmbed root visit recognition) word)
def observationInjection (index : Index root visit recognition) (kind : Fin 4) :
    Measured (H:=H) →+ Output root visit recognition := by
  classical
  exact (0 : Measured (H:=H) →+ Inventory.Output root visit recognition).prod
    (((AddMonoidHom.single (fun _ : Index root visit recognition => Fin 4 → Measured (H:=H)) index).comp
      (AddMonoidHom.single (fun _ : Fin 4 => Measured (H:=H)) kind)).prod 0)
def gramInjection (first second : Sample root visit recognition) : ULift.{u} ℂ →+ Output root visit recognition := by
  classical
  exact (0 : ULift.{u} ℂ →+ Inventory.Output root visit recognition).prod
    ((0 : ULift.{u} ℂ →+ Observations root visit recognition).prod
      ((AddMonoidHom.single (fun _ : Sample root visit recognition => Sample root visit recognition → ULift.{u} ℂ) first).comp
        (AddMonoidHom.single (fun _ : Sample root visit recognition => ULift.{u} ℂ) second)))
def oldTerm : Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  .linear (s:=.inl (Inventory.resultSlot root recognition)) (oldInjection root visit recognition)
    (embed root visit recognition (Inventory.Action.C.materialAt frame supplied).raw.expression)
def observationOutput (index : Index root visit recognition) (kind : Fin 4) :
    Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  .linear (s:=measuredSlot root recognition) (observationInjection root visit recognition index kind)
    (observationTerm root visit recognition index kind)
def gramOutput (first second : Sample root visit recognition) :
    Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  .linear (s:=gramSlot root recognition) (gramInjection root visit recognition first second)
    (gramTerm root visit recognition first second)
def observerTerms := (List.ofFn (fun index : Index root visit recognition =>
  List.ofFn (fun kind : Fin 4 => observationOutput root visit recognition index kind))).flatten
def samples := (List.ofFn (fun index : Index root visit recognition =>
  List.ofFn (fun kind : Fin 4 => (index,kind)))).flatten
def gramTerms := (samples root visit recognition).flatMap (fun first =>
  (samples root visit recognition).map (fun second => gramOutput root visit recognition first second))
def programme : List (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition)) →
    Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition)
  | [] => .const 0
  | first::rest => .add first (programme rest)
def expressionAt := programme root visit recognition (oldTerm root visit recognition frame supplied ::
  (observerTerms root visit recognition ++ gramTerms root visit recognition))
def rawAt : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=Variable root visit recognition) (sort:=resultSlot root recognition) :=
  ⟨environmentAt root visit recognition frame supplied,expressionAt root visit recognition frame supplied⟩
def traceAt := execution (environmentAt root visit recognition frame supplied) (expressionAt root visit recognition frame supplied)
def paidAt := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt (E.Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} occurrence => rawAt root visit recognition frame occurrence) supplied

def vectorsAt (index : Index root visit recognition) :=
  let row := rowAt root visit recognition index
  let current := pointAt root visit recognition frame supplied row
  let next := nextPointAt root visit recognition frame supplied row
  (measurement root recognition row current, measurement root recognition row next,
    evolution root recognition row (measurement root recognition row current),
    evolution root recognition row (measurement root recognition row current)-measurement root recognition row next)
def materialAt := ((Inventory.Action.C.materialAt frame supplied),
  Operation.sourceOperationAtCode root (Inventory.oldCode root visit recognition) recognition,
  Operation.sourceOperationAtCode root (Inventory.nextCode root visit recognition) recognition,
  fun index : Index root visit recognition =>
    (sourceExposure root recognition (rowAt root visit recognition index),
      targetExposure root recognition (rowAt root visit recognition index), vectorsAt root visit recognition frame supplied index,
      modelProjection root recognition (rowAt root visit recognition index)
        (pointAt root visit recognition frame supplied (rowAt root visit recognition index))),
  rawAt root visit recognition frame supplied,paidAt root visit recognition frame supplied,traceAt root visit recognition frame supplied)

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
def sourceFrame (stage : Nat) := Inventory.Live.frameAt root visit recognition U7 calculus stage
abbrev sourceOccurrence (stage : Nat) := E.Shared.actualOccurrence (sourceFrame root visit recognition U7 calculus stage)
abbrev raw (stage : Nat) := rawAt root visit recognition (sourceFrame root visit recognition U7 calculus stage)
  (sourceOccurrence root visit recognition U7 calculus stage)
abbrev environment (stage : Nat) := environmentAt root visit recognition (sourceFrame root visit recognition U7 calculus stage)
  (sourceOccurrence root visit recognition U7 calculus stage)
abbrev trace (stage : Nat) := traceAt root visit recognition (sourceFrame root visit recognition U7 calculus stage)
  (sourceOccurrence root visit recognition U7 calculus stage)
abbrev paid (stage : Nat) := paidAt root visit recognition (sourceFrame root visit recognition U7 calculus stage)
  (sourceOccurrence root visit recognition U7 calculus stage)
abbrev material (stage : Nat) := materialAt root visit recognition (sourceFrame root visit recognition U7 calculus stage)
  (sourceOccurrence root visit recognition U7 calculus stage)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
