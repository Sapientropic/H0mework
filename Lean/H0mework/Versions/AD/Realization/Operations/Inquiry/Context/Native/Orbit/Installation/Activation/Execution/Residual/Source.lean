import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Consumer
import H0mework.Foundation.Responsibility.JointSource.Successor.Step
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Runtime
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest
/-! The complete charged trace and source-owned native shift generate the
next residual registration. Its existing source successor installs the new
mathematical write while retaining the completed row and every old face. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
namespace E
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
  (chargedProgramme commonReader actualResult settled settled_value result_state_receipt)
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot actualVisit)
end S
end E
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (authoritativeRoot mathEntry Current law)
end O
namespace R
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (MaterialAt input expression relations budget action_is_paid updated_value residual_value)
end R
namespace J
export RootGeneratedDebtActivationJointSource (register mathAction initialEvent)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev old := (E.S.baseRoot frame E.chargedProgramme).toAuthoritativeRoot
abbrev origin := (E.S.actualVisit frame).current
abbrev reader := E.commonReader frame
abbrev root := O.authoritativeRoot (old frame) (origin frame) (reader frame)
abbrev endpoint : O.Current (old frame) (origin frame) (reader frame) := (E.actualResult frame).2.1
abbrev raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue PhysicalValue)
    (Var:=SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar) (sort:=sort) := (E.actualResult frame).1
abbrev updatedEnvironment := SourceSubstitution.sourceEnvironment SourceOperationInquiry.Context.Native.Orbit.binding (raw frame).environment

private theorem shift_pair {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ target, AddCommGroup (Value target)] {sort : Sorts}
    (cursor : SourceOperationInquiry.Context.Native.Orbit.Installation.Cursor
      (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort)) :
    SourceSubstitution.sourceEnvironment SourceOperationInquiry.Context.Native.Orbit.binding
      (SourceOperationScalarInventoryLift.pairEnvironment cursor.orbitEnvironment
        (cursor.next.orbitEnvironment - cursor.orbitEnvironment)) =
    SourceOperationScalarInventoryLift.pairEnvironment cursor.next.orbitEnvironment
      (cursor.next.next.orbitEnvironment - cursor.next.orbitEnvironment) := by
  funext target name
  have first := congrArg (fun environment : Env Value (SourceOperationInquiry.Context.Native.Orbit.Var Var) =>
    environment target name) cursor.shift_environment
  have second := congrArg (fun environment : Env Value (SourceOperationInquiry.Context.Native.Orbit.Var Var) =>
    environment target name) cursor.next.shift_environment
  change (cursor.orbitEnvironment target (name.1 + 1, name.2),
    cursor.next.orbitEnvironment target (name.1 + 1, name.2) -
      cursor.orbitEnvironment target (name.1 + 1, name.2)) = _
  change cursor.orbitEnvironment target (name.1 + 1, name.2) = _ at first
  change cursor.next.orbitEnvironment target (name.1 + 1, name.2) = _ at second
  rw [first, second]
  rfl

def cursor := SourceOperationInquiry.Context.Native.Orbit.Installation.cursorAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)

theorem environment_actual_shift : updatedEnvironment frame =
    (SourceOperationInquiry.Context.Native.Orbit.Installation.Relations.pairRaw (cursor frame).next).environment :=
  shift_pair (cursor frame)

abbrev Occurrence := (root frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (endpoint frame)

def material (occurrence : Occurrence frame) : R.MaterialAt
    (Value:=SourceOperationScalarInventoryLift.PairValue PhysicalValue)
    (Var:=SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar) (sort:=sort) occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact {
    environment := (raw frame).environment
    increment := updatedEnvironment frame - (raw frame).environment
    raw := (raw frame).expression
    state := endpoint frame
    owner := O.mathEntry (old frame) (origin frame) (reader frame) (endpoint frame) }

def registered := J.register (fun occurrence : Occurrence frame => R.input (material frame occurrence))
def actualMaterial := material frame ((root frame).emitted (endpoint frame))

theorem environment_source : (registered frame).input.environment = updatedEnvironment frame := by
  change (raw frame).environment + (updatedEnvironment frame - (raw frame).environment) = _
  abel

theorem residual_effect : (registered frame).input.expression.eval (registered frame).input.environment =
    effectEvaluator (R:=ℤ) (raw frame).environment (updatedEnvironment frame - (raw frame).environment)
      (relationMap (R:=ℤ) (raw frame).environment (R.relations (R:=ℤ) (actualMaterial frame))) :=
  R.updated_value (R:=ℤ) (actualMaterial frame)

theorem inverse_value : (residualEquivRange (evaluation (R:=ℤ) (registered frame).input.environment)
    (canonicalResidual (evaluation (R:=ℤ) (registered frame).input.environment)
      (relationMap (R:=ℤ) (raw frame).environment (R.relations (R:=ℤ) (actualMaterial frame))))).val =
    (registered frame).input.expression.eval (registered frame).input.environment :=
  R.residual_value (R:=ℤ) (actualMaterial frame)

private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement
    (J.initialEvent (registered frame)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law (registered frame).input.environment
    (registered frame).input.expression).settlement_budget_zero settled
  change remaining (R.expression (actualMaterial frame)) = 0 at zero
  have bound := R.budget (actualMaterial frame)
  have impossible := bound.symm.trans zero
  omega

def firstStep := match _selected : J.mathAction (J.initialEvent (registered frame)) with
  | .inl settled => False.elim (not_settled frame settled)
  | .inr paid => paid

theorem firstStep_generated : J.mathAction (J.initialEvent (registered frame)) = .inr (firstStep frame) := by
  unfold firstStep
  cases selected : J.mathAction (J.initialEvent (registered frame)) with
  | inl settled => exact False.elim (not_settled frame settled)
  | inr paid => rfl

private theorem successor_option_exists {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source.source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? generated).isSome = true := by
  cases generated with
  | faithfulTerminal _ _ _ => exact nomatch successor
  | nativeWrite => rfl
  | relationWrite => rfl
  | continuedTransport => rfl
  | borromeanRedirect => rfl

private theorem packet_exists {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (lower : SourceNativeLedgerRootClosure N V) (current : V.Current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current) (lower.generatedLedgerAt current)) :
    (J.read? lower current).isSome = true := by
  have found := successor_option_exists (lower.generatedLedgerAt current) successor
  unfold RootGeneratedDebtActivationJointSource.Successor.read?
  cases selected : SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (lower.generatedLedgerAt current) with
  | none => simp only [selected, Option.isSome_none] at found; exact Bool.noConfusion found
  | some successor => rfl

def packet : J.Packet (root frame).toLedgerRoot (endpoint frame) :=
  (J.read? (root frame).toLedgerRoot (endpoint frame)).get
    (packet_exists (root frame).toLedgerRoot (endpoint frame)
      (RootGeneratedDebtActivationJointSource.OwnerFree.sourceSuccessor (old frame) (origin frame) (reader frame) (endpoint frame)))

def whole := J.join (packet frame) (J.initialEvent (registered frame))

theorem actual_whole : type_of% (J.join_whole_paid (packet frame) (J.initialEvent (registered frame))
    (firstStep frame) (firstStep_generated frame)) :=
  J.join_whole_paid (packet frame) (J.initialEvent (registered frame)) (firstStep frame) (firstStep_generated frame)

def programme (current : (RootGeneratedDebtActivationJointSource.OwnerFree.vocabulary
    (old frame) (origin frame) (reader frame)).Current) : J.Packet (root frame).toLedgerRoot current :=
  (J.read? (root frame).toLedgerRoot current).get
    (packet_exists (root frame).toLedgerRoot current
      (RootGeneratedDebtActivationJointSource.OwnerFree.sourceSuccessor (old frame) (origin frame) (reader frame) current))

def writebackRoot := RootGeneratedDebtActivationJointSource.Successor.Restructuring.livingRoot
  (root frame) (registered frame) (programme frame)
def runtime := RootGeneratedDebtActivationJointSource.Successor.Restructuring.initialRuntime
  (root frame) (registered frame) (programme frame)

def wholeCertificate := (runtime frame).current.root.toAuthoritativeRoot.source.restructuringSource.compiler.certifyRestructuring
  (runtime frame).tick.generated.occurrence


end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
