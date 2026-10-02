import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Programme
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Math
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest

/-! The installed root's complete raw and paid faces, with one fixed original
occurrence environment reader, generate the next executable residual request. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion CompilerFromPacketSourceLaw

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current)
variable (environment : {current : V.Current} →
  old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → Env Value Var)
variable (depth : Nat)

abbrev currentState := mathState old registered packetAt depth
abbrev Occurrence := (currentState old registered packetAt depth).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  (currentState old registered packetAt depth).visit.current

def rawRead : Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort) :=
  (rawFace old registered packetAt depth).rootRead

def paidRead := (mathAnswerFace old registered packetAt depth).rootRead

def environmentAt (source : Occurrence old registered packetAt depth) : Env Value Var :=
  environment (originalOccurrence registered packetAt source)

def actualOccurrence : Occurrence old registered packetAt depth :=
  (currentState old registered packetAt depth).root.emitted (currentState old registered packetAt depth).visit.current

def material (source : Occurrence old registered packetAt depth) :
    Native.ResidualRequest.MaterialAt (Value := Value) (Var := Var) (sort := sort) source := by
  rcases source with ⟨support, event⟩
  cases event
  exact { environment := (rawRead old registered packetAt depth).environment
          increment := environmentAt old registered packetAt environment depth
            (actualOccurrence old registered packetAt depth) - (rawRead old registered packetAt depth).environment
          raw := (rawRead old registered packetAt depth).expression
          state := (paidRead old registered packetAt depth).state
          owner := mathEntry old registered packetAt depth }

def reader (source : Occurrence old registered packetAt depth) :=
  Native.ResidualRequest.input (material old registered packetAt environment depth source)

def request := register (reader old registered packetAt environment depth)

def actualMaterial := material old registered packetAt environment depth (actualOccurrence old registered packetAt depth)

theorem request_environment :
    (request old registered packetAt environment depth).input.environment =
      environmentAt old registered packetAt environment depth (actualOccurrence old registered packetAt depth) := by
  change (rawRead old registered packetAt depth).environment +
    (environmentAt old registered packetAt environment depth (actualOccurrence old registered packetAt depth) -
      (rawRead old registered packetAt depth).environment) = _
  abel

theorem environment_source :
    environmentAt old registered packetAt environment depth (actualOccurrence old registered packetAt depth) =
      environment (old.root.emitted (mathCurrent old registered packetAt depth).1) := rfl

theorem request_owner : (request old registered packetAt environment depth).input.owner =
    (currentState old registered packetAt depth).entryAt PUnit.unit := rfl

theorem request_budget : remaining (request old registered packetAt environment depth).input.expression =
    remaining (rawRead old registered packetAt depth).expression +
      remaining (paidRead old registered packetAt depth).state.1 + 2 :=
  Native.ResidualRequest.budget (actualMaterial old registered packetAt environment depth)

def programme (current : (JointV registered packetAt).Current) :
    Packet (currentState old registered packetAt depth).root.toAuthoritativeRoot.toLedgerRoot current :=
  nextProgramme old.root.toAuthoritativeRoot registered packetAt current

private theorem request_not_settled (settled : SourceOperationExecutionDebt.Settlement
    (initialEvent (request old registered packetAt environment depth)).state) : False := by
  have zero := (Idle.law (request old registered packetAt environment depth).input.environment
    (request old registered packetAt environment depth).input.expression).settlement_budget_zero settled
  change remaining (request old registered packetAt environment depth).input.expression = 0 at zero
  have growth := request_budget old registered packetAt environment depth
  omega

def firstStep : DebtActivationWorld.GeneratedStepAt
    (Idle.law (request old registered packetAt environment depth).input.environment
      (request old registered packetAt environment depth).input.expression)
    (initialEvent (request old registered packetAt environment depth)).state :=
  match mathAction (initialEvent (request old registered packetAt environment depth)) with
  | .inl settled => False.elim (request_not_settled old registered packetAt environment depth settled)
  | .inr paid => paid

theorem firstStep_generated :
    mathAction (initialEvent (request old registered packetAt environment depth)) =
      .inr (firstStep old registered packetAt environment depth) := by
  cases selected : mathAction (initialEvent (request old registered packetAt environment depth)) with
  | inl settled => exact False.elim (request_not_settled old registered packetAt environment depth settled)
  | inr paid => simp only [firstStep, selected]

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
