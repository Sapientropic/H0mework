import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Consumer
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Runtime
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest

/-! Each mother occurrence supplies the complete charged trace that generates
its native-shift residual. The low source family retains both whole ledgers,
new first-write material and canonical next without identifying their worlds. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Family
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
namespace E
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
  (receiptAt originRoot reader state stage calculationRoot)
end E
namespace C
export SourceOperationInquiry.Context.Native.Orbit.Installation
  (cursorAt materialAt MaterialAt Relations.pairRaw Cursor)
end C
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base root query state resultFace actualOccurrence actualVisit)
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
end A
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree
  (Raw Current authoritativeRoot mathEntry action nextState whole sourceSuccessor)
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (SourceMaterialAt sourceMaterialAt)
end I
namespace K
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (completed completed_value)
end K
end O
namespace R
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (MaterialAt expression input budget relations updated_value residual_value)
end R
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current))

abbrev sourceRaw := (E.receiptAt frame occurrence).raw
abbrev sourceCursor := C.cursorAt frame occurrence
abbrev sourceEndpoint := E.state frame occurrence (remaining (sourceRaw frame occurrence).expression + 1)
abbrev childRoot := O.authoritativeRoot (E.originRoot frame) current (E.reader frame occurrence)
abbrev childOccurrence := (childRoot frame occurrence).emitted (sourceEndpoint frame occurrence)

def residualMaterial : R.MaterialAt
    (Value := PairValue PhysicalValue) (Var := SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar)
    (sort := sort) (lower := (childRoot frame occurrence).toLedgerRoot)
    (current := sourceEndpoint frame occurrence) (childOccurrence frame occurrence) where
  environment := (sourceRaw frame occurrence).environment
  increment := SourceSubstitution.sourceEnvironment SourceOperationInquiry.Context.Native.Orbit.binding
    (sourceRaw frame occurrence).environment - (sourceRaw frame occurrence).environment
  raw := (sourceRaw frame occurrence).expression
  state := sourceEndpoint frame occurrence
  owner := O.mathEntry (E.originRoot frame) current (E.reader frame occurrence) (sourceEndpoint frame occurrence)

abbrev residualRaw : O.Raw (Value := PairValue PhysicalValue)
    (Var := SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar) (sort := sort) :=
  ⟨(R.input (residualMaterial frame occurrence)).environment, (R.input (residualMaterial frame occurrence)).expression⟩

theorem environment_actual_shift : (residualRaw frame occurrence).environment =
    (C.Relations.pairRaw (sourceCursor frame occurrence).next).environment := by
  change (sourceRaw frame occurrence).environment +
    (SourceSubstitution.sourceEnvironment SourceOperationInquiry.Context.Native.Orbit.binding
      (sourceRaw frame occurrence).environment - (sourceRaw frame occurrence).environment) = _
  rw [add_sub_cancel]
  let cursor := sourceCursor frame occurrence
  funext target name
  have first := congrArg (fun environment : Env PhysicalValue
    (SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar) => environment target name) cursor.shift_environment
  have second := congrArg (fun environment : Env PhysicalValue
    (SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar) => environment target name) cursor.next.shift_environment
  change (cursor.orbitEnvironment target (name.1 + 1, name.2),
    cursor.next.orbitEnvironment target (name.1 + 1, name.2) - cursor.orbitEnvironment target (name.1 + 1, name.2)) = _
  change cursor.orbitEnvironment target (name.1 + 1, name.2) = _ at first
  change cursor.next.orbitEnvironment target (name.1 + 1, name.2) = _ at second
  rw [first, second]
  rfl

theorem residual_effect : (residualRaw frame occurrence).expression.eval
    (residualRaw frame occurrence).environment =
    effectEvaluator (R := ℤ) (sourceRaw frame occurrence).environment
      (SourceSubstitution.sourceEnvironment SourceOperationInquiry.Context.Native.Orbit.binding
        (sourceRaw frame occurrence).environment - (sourceRaw frame occurrence).environment)
      (relationMap (R := ℤ) (sourceRaw frame occurrence).environment
        (R.relations (R := ℤ) (residualMaterial frame occurrence))) :=
  R.updated_value (R := ℤ) (residualMaterial frame occurrence)

def registered := RootGeneratedDebtActivationJointSource.register
  (fun supplied : (childRoot frame occurrence).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      (sourceEndpoint frame occurrence) => by
    rcases supplied with ⟨support, event⟩
    cases event
    exact R.input (residualMaterial frame occurrence))

private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement
    (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law
    (registered frame occurrence).input.environment (registered frame occurrence).input.expression).settlement_budget_zero settled
  have bound := R.budget (residualMaterial frame occurrence)
  change remaining (R.expression (residualMaterial frame occurrence)) = 0 at zero
  omega

def firstStep := match _selected : RootGeneratedDebtActivationJointSource.mathAction
    (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence)) with
  | .inl settled => False.elim (not_settled frame occurrence settled)
  | .inr paid => paid

theorem firstStep_generated : RootGeneratedDebtActivationJointSource.mathAction
    (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence)) =
      .inr (firstStep frame occurrence) := by
  unfold firstStep
  cases selected : RootGeneratedDebtActivationJointSource.mathAction
      (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence)) with
  | inl settled => exact False.elim (not_settled frame occurrence settled)
  | inr paid => rfl

private theorem successorFound {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source.source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? generated).isSome = true := by
  cases generated with
  | nativeWrite => rfl
  | relationWrite => rfl
  | continuedTransport => rfl
  | borromeanRedirect => rfl
  | faithfulTerminal => exact nomatch successor

private theorem sourcePacketExists {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (lower : SourceNativeLedgerRootClosure N V) (current : V.Current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current) (lower.generatedLedgerAt current)) :
    (RootGeneratedDebtActivationJointSource.Successor.read? lower current).isSome = true := by
  have found := successorFound (lower.generatedLedgerAt current) successor
  unfold RootGeneratedDebtActivationJointSource.Successor.read?
  cases selected : SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (lower.generatedLedgerAt current) with
  | none => simp only [selected, Option.isSome_none] at found; exact Bool.noConfusion found
  | some successor => rfl

def packetProgramme (childCurrent : (RootGeneratedDebtActivationJointSource.OwnerFree.vocabulary
    (E.originRoot frame) current (E.reader frame occurrence)).Current) :=
  (RootGeneratedDebtActivationJointSource.Successor.read? (childRoot frame occurrence).toLedgerRoot childCurrent).get
    (sourcePacketExists (childRoot frame occurrence).toLedgerRoot childCurrent
      (O.sourceSuccessor (E.originRoot frame) current (E.reader frame occurrence) childCurrent))

def firstJoin := RootGeneratedDebtActivationJointSource.Successor.join
  (packetProgramme frame occurrence (sourceEndpoint frame occurrence))
  (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence))

def firstRuntime := RootGeneratedDebtActivationJointSource.Successor.Restructuring.initialRuntime
  (childRoot frame occurrence) (registered frame occurrence) (packetProgramme frame occurrence)

abbrev firstRoot := (firstRuntime frame occurrence).current.root.toAuthoritativeRoot
abbrev firstOccurrence := (firstRoot frame occurrence).emitted (firstRuntime frame occurrence).current.visit.current

def ChildMaterial : Type u := O.I.SourceMaterialAt (childRoot frame occurrence) (childOccurrence frame occurrence)
def OriginalMaterial : Type u := C.MaterialAt frame occurrence
def ExecutionReceipts : Type u :=
  SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.ReceiptAt frame occurrence

def FirstMaterial : Type u := O.I.SourceMaterialAt (firstRoot frame occurrence) (firstOccurrence frame occurrence)
abbrev nextRoot := (firstRuntime frame occurrence).tick.next.current.root.toAuthoritativeRoot
abbrev nextOccurrence := (nextRoot frame occurrence).emitted (firstRuntime frame occurrence).tick.next.current.visit.current
def NextMaterial : Type u := O.I.SourceMaterialAt (nextRoot frame occurrence) (nextOccurrence frame occurrence)

abbrev PacketAt : Type u := OriginalMaterial frame occurrence × ExecutionReceipts frame occurrence ×
  ChildMaterial frame occurrence × (Σ residual : O.Raw (Value := PairValue PhysicalValue)
    (Var := SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar) (sort := sort),
      SourceOperationExecutionDebt.State residual.environment residual.expression) ×
  FirstMaterial frame occurrence × NextMaterial frame occurrence

def packetAt : PacketAt frame occurrence :=
  ⟨C.materialAt frame occurrence, E.receiptAt frame occurrence,
    O.I.sourceMaterialAt (childRoot frame occurrence) (childOccurrence frame occurrence),
    ⟨residualRaw frame occurrence, (firstStep frame occurrence).1⟩,
    O.I.sourceMaterialAt (firstRoot frame occurrence) (firstOccurrence frame occurrence),
    O.I.sourceMaterialAt (nextRoot frame occurrence) (nextOccurrence frame occurrence)⟩

theorem first_material_generated :
    HEq (firstRuntime frame occurrence).tick.generated.wholeLedgerWriteBack
      (O.I.sourceMaterialAt (firstRoot frame occurrence) (firstOccurrence frame occurrence)).1.1 := HEq.rfl

theorem next_material_generated :
    HEq (firstRuntime frame occurrence).tick.next.tick.generated.wholeLedgerWriteBack
      (O.I.sourceMaterialAt (nextRoot frame occurrence) (nextOccurrence frame occurrence)).1.1 := HEq.rfl

theorem next_math :
    (RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
      (childRoot frame occurrence) (registered frame occurrence) (packetProgramme frame occurrence)
      (firstRuntime frame occurrence).tick.next).2.state = (firstStep frame occurrence).1 := by
  apply (RootGeneratedDebtActivationJointSource.Successor.Restructuring.tick_math
    (childRoot frame occurrence) (registered frame occurrence) (packetProgramme frame occurrence)
    (firstRuntime frame occurrence)).trans
  change RootGeneratedDebtActivationJointSource.mathTarget
    (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence)) = _
  unfold RootGeneratedDebtActivationJointSource.mathTarget
  rw [firstStep_generated frame occurrence]

theorem full_first_write : type_of% (RootGeneratedDebtActivationJointSource.Successor.join_whole_paid
    (packetProgramme frame occurrence (sourceEndpoint frame occurrence))
    (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence))
    (firstStep frame occurrence) (firstStep_generated frame occurrence)) :=
  RootGeneratedDebtActivationJointSource.Successor.join_whole_paid
    (packetProgramme frame occurrence (sourceEndpoint frame occurrence))
    (RootGeneratedDebtActivationJointSource.initialEvent (registered frame occurrence))
    (firstStep frame occurrence) (firstStep_generated frame occurrence)

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Family
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
