import H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime

/-! A completed mathematical source registers its actual equation residual.
The existing first-write target and Shared engine consume that fresh request. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
open RootGeneratedDebtActivationJointSource.OwnerFree
open RootGeneratedDebtActivationJointSource.OwnerFree.Installation
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (sourceRoot : SourceNativeLivingRootClosure N V)
variable (sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot)
variable (sourceU7 : U7ProducerCalculus N)
variable (sourceCalculus : U7ObstructionEvolutionCalculus N sourceU7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceVisit.current →
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

def packet (current : vocabulary (original sourceRoot) sourceVisit.current reader |>.Current) :
    Successor.Packet (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot current :=
  (Successor.read? (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot current).get
    (packet_found (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot current
      (sourceSuccessor (original sourceRoot) sourceVisit.current reader current))

-- This calculation has fixed original support and environment. Its new
-- request is the actual equation residual, with its complete paid past.
def residualMaterial (occurrence : (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).visit.current) :
    Native.ResidualRequest.MaterialAt (Value:=Value) (Var:=Var) (sort:=sort) occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact { environment := (raw (original sourceRoot) sourceVisit.current reader).environment
          increment := 0
          raw := (raw (original sourceRoot) sourceVisit.current reader).expression
          state := (visit sourceRoot sourceVisit reader (endpointCount sourceRoot sourceVisit reader)).current
          owner := entry sourceRoot sourceVisit reader (endpointCount sourceRoot sourceVisit reader) }

def residualRegistered := register (fun occurrence => Native.ResidualRequest.input (residualMaterial sourceRoot sourceVisit sourceU7 sourceCalculus reader occurrence))
def residualEnvironment {current : vocabulary (original sourceRoot) sourceVisit.current reader |>.Current}
    (_occurrence : (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  (raw (original sourceRoot) sourceVisit.current reader).environment

private theorem residual_not_settled (settled : SourceOperationExecutionDebt.Settlement
    (initialEvent (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader)).state) : False := by
  have zero := (Idle.law (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader).input.environment (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader).input.expression).settlement_budget_zero settled
  have positive := Native.ResidualRequest.budget (residualMaterial sourceRoot sourceVisit sourceU7 sourceCalculus reader
    ((endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.emitted (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).visit.current))
  change remaining (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader).input.expression = 0 at zero
  change remaining (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader).input.expression = _ at positive
  omega

def residualFirstStep := match mathAction (initialEvent (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader)) with
  | .inl settled => False.elim (residual_not_settled sourceRoot sourceVisit sourceU7 sourceCalculus reader settled)
  | .inr paid => paid

theorem residual_first_action : mathAction (initialEvent (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader)) = .inr (residualFirstStep sourceRoot sourceVisit sourceU7 sourceCalculus reader) := by
  cases selected : mathAction (initialEvent (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader)) with
  | inl settled => exact False.elim (residual_not_settled sourceRoot sourceVisit sourceU7 sourceCalculus reader settled)
  | inr paid => simp only [residualFirstStep, selected]

def residualTarget := Successor.Inquiry.targetAt (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader) (endpointInput sourceRoot sourceVisit sourceU7 sourceCalculus reader).query
  (residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader) (packet sourceRoot sourceVisit sourceU7 sourceCalculus reader)
  ((endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).authorityAt (endpointInput sourceRoot sourceVisit sourceU7 sourceCalculus reader).query)
  (residualFirstStep sourceRoot sourceVisit sourceU7 sourceCalculus reader) (residual_first_action sourceRoot sourceVisit sourceU7 sourceCalculus reader)
  ((endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).visit)

def frame : Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=sort) where
  N := World sourceRoot sourceVisit reader
  V := vocabulary (original sourceRoot) sourceVisit.current reader
  old := endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader
  registered := residualRegistered sourceRoot sourceVisit sourceU7 sourceCalculus reader
  packetAt := packet sourceRoot sourceVisit sourceU7 sourceCalculus reader
  environment := residualEnvironment sourceRoot sourceVisit sourceU7 sourceCalculus reader
  depth := 0

theorem residual_first_receipt : type_of% (residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus reader).firstDestination_heq :=
  (residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus reader).firstDestination_heq

theorem residual_frame_next : (residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus reader).targetAnswerAndNext.nextCurrent =
    (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader).currentPresentation.erase.current := (residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus reader).targetAnswerAndNext_next_eq

abbrev runtime := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.runtime (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme

theorem activated_next (offset : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader)
      SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader)
    SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset

theorem activated_query (offset : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader)
      SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader)
    SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset

theorem activated_answer (offset : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader)
      SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader)
    SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme offset
end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
