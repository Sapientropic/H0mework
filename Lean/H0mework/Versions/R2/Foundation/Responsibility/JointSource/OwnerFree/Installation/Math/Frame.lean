import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime

/-! A completed mathematical source registers its actual equation residual.
The existing first-write target and Shared engine consume that fresh request. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt old.visit.current →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))

private theorem successor_found {W : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
    {source : SourceNativeLedgerSource W L} {current : L.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source.source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? generated).isSome = true := by
  cases generated <;> first | rfl | exact nomatch successor

private theorem packet_found {W : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
    (lower : SourceNativeLedgerRootClosure W L) (current : L.Current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current) (lower.generatedLedgerAt current)) :
    (Successor.read? lower current).isSome = true := by
  have found := successor_found (lower.generatedLedgerAt current) successor
  unfold Successor.read?
  cases selected : SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (lower.generatedLedgerAt current) with
  | none => simp only [selected, Option.isSome_none] at found; exact Bool.noConfusion found
  | some successor => rfl

def packet (current : vocabulary (original old) old.visit.current reader |>.Current) :
    Successor.Packet (endpointState old reader).root.toAuthoritativeRoot.toLedgerRoot current :=
  (Successor.read? (endpointState old reader).root.toAuthoritativeRoot.toLedgerRoot current).get
    (packet_found (endpointState old reader).root.toAuthoritativeRoot.toLedgerRoot current
      (sourceSuccessor (original old) old.visit.current reader current))

-- This calculation has fixed original support and environment. Its new
-- request is the actual equation residual, with its complete paid past.
def residualMaterial (occurrence : (endpointState old reader).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (endpointState old reader).visit.current) :
    Native.ResidualRequest.MaterialAt (Value:=Value) (Var:=Var) (sort:=sort) occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact { environment := (raw (original old) old.visit.current reader).environment
          increment := 0
          raw := (raw (original old) old.visit.current reader).expression
          state := (visit old reader (endpointCount old reader)).current
          owner := entry old reader (endpointCount old reader) }

def residualRegistered := register (fun occurrence => Native.ResidualRequest.input (residualMaterial old reader occurrence))
def residualEnvironment {current : vocabulary (original old) old.visit.current reader |>.Current}
    (_occurrence : (endpointState old reader).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  (raw (original old) old.visit.current reader).environment

private theorem residual_not_settled (settled : SourceOperationExecutionDebt.Settlement
    (initialEvent (residualRegistered old reader)).state) : False := by
  have zero := (Idle.law (residualRegistered old reader).input.environment (residualRegistered old reader).input.expression).settlement_budget_zero settled
  have positive := Native.ResidualRequest.budget (residualMaterial old reader
    ((endpointState old reader).root.emitted (endpointState old reader).visit.current))
  change remaining (residualRegistered old reader).input.expression = 0 at zero
  change remaining (residualRegistered old reader).input.expression = _ at positive
  omega

def residualFirstStep := match mathAction (initialEvent (residualRegistered old reader)) with
  | .inl settled => False.elim (residual_not_settled old reader settled)
  | .inr paid => paid

theorem residual_first_action : mathAction (initialEvent (residualRegistered old reader)) = .inr (residualFirstStep old reader) := by
  cases selected : mathAction (initialEvent (residualRegistered old reader)) with
  | inl settled => exact False.elim (residual_not_settled old reader settled)
  | inr paid => simp only [residualFirstStep, selected]

def residualTarget := Successor.Inquiry.targetAt (endpointState old reader) (endpointInput old reader).query
  (residualRegistered old reader) (packet old reader)
  ((endpointState old reader).authorityAt (endpointInput old reader).query)
  (residualFirstStep old reader) (residual_first_action old reader)
  ((endpointState old reader).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (endpointState old reader).visit)

def frame : Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=sort) where
  N := World old reader
  V := vocabulary (original old) old.visit.current reader
  old := endpointState old reader
  registered := residualRegistered old reader
  packetAt := packet old reader
  environment := residualEnvironment old reader
  depth := 0

theorem residual_first_receipt : type_of% (residualTarget old reader).firstDestination_heq :=
  (residualTarget old reader).firstDestination_heq

theorem residual_frame_next : (residualTarget old reader).targetAnswerAndNext.nextCurrent =
    (frame old reader).currentPresentation.erase.current := (residualTarget old reader).targetAnswerAndNext_next_eq

abbrev runtime := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.runtime (frame old reader)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme

theorem activated_next (offset : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next (frame old reader)
      SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next (frame old reader)
    SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset

theorem activated_query (offset : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query (frame old reader)
      SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query (frame old reader)
    SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset

theorem activated_answer (offset : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer (frame old reader)
      SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer (frame old reader)
    SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset
end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
