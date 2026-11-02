import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (depth : Nat)

def ordinal := Future.Runtime.ordinal inventory (ChallengeLine.word inventory)
def baseRoot := Future.Runtime.root inventory (ChallengeLine.word inventory) depth

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))
      (ordinal inventory)).current → ChallengeLine.Disposition inventory depth
  project := fun _ {_} _ _ _own => ChallengeLine.produce inventory depth

def root := (baseRoot inventory depth).withProjectionCoface (projectionLaw inventory depth)

theorem root_is_the_original_joint_response_root :
    (root inventory depth).toAuthoritativeRoot.toRoot = (baseRoot inventory depth).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))) :=
  ⟨ProgrammeSource.V (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory))),root inventory depth,
    ProgrammeHistory.temporalVisit (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory))) index⟩

def process : SourceNativeLivingRootProcess
    (ProgrammeSource.N (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))) where
  State := Nat
  stateAt := stateAt inventory depth
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory))) first).current =
        (ProgrammeHistory.visitAt (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory))) second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory))) currents
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

abbrev Face := Sum Future.Runtime.Face Unit

def facade : SourceNativeLivingRuntimeFacade
    (ProgrammeSource.N (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))) where
  process := process inventory depth
  FaceAt := fun _ => Face
  componentAt := fun _state face => match face with
    | .inl previous => (Future.Runtime.facade inventory (ChallengeLine.word inventory) depth).componentAt
        (Future.Runtime.activated inventory (ChallengeLine.word inventory) depth 0) previous
    | .inr _ => projectionLaw inventory depth
  installationAt := by
    intro state face
    have inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (baseRoot inventory depth).toAuthoritativeRoot.source (projectionLaw inventory depth)
    cases face with
    | inl previous => exact ((Future.Runtime.facade inventory (ChallengeLine.word inventory) depth).installationAt
        (Future.Runtime.activated inventory (ChallengeLine.word inventory) depth 0) previous).trans inherited
    | inr own =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (baseRoot inventory depth).toAuthoritativeRoot.source (projectionLaw inventory depth)
  projectionAt := fun _state face => match face with
    | .inl previous => (Future.Runtime.facade inventory (ChallengeLine.word inventory) depth).projectionAt
        (Future.Runtime.activated inventory (ChallengeLine.word inventory) depth 0) previous
    | .inr _ => ()

def activated (index : Nat) : LivingRuntimeState (process inventory depth) := (facade inventory depth).seed.advance index

def fromRoot : ChallengeLine.Disposition inventory depth :=
  (projectionLaw inventory depth).project ()
    (ProgrammeSource.emitted (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))
      (ProgrammeHistory.visitAt (Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory)))
        (ordinal inventory)).current) () rfl

theorem consumes_the_actual_source_generated_challenge_or_own_residual :
    fromRoot inventory depth = ChallengeLine.produce inventory depth := rfl

theorem the_actual_newborn_full_run_financial_account_and_own_next_share_the_original_root :
    fromRoot inventory depth = ChallengeLine.produce inventory depth ∧
    (fromRoot inventory depth).answer = Future.Runtime.fromRoot inventory (ChallengeLine.word inventory) depth ∧
    (∀ active : Mandate.Response.Active (current epoch inventory.inputs),
      ((fromRoot inventory depth).completeNewbornRun active).events =
        ((fromRoot inventory depth).newborn active).1.state.generated.events) ∧
    Financial.Family.ledgerClaims sources (fromRoot inventory depth).packet.2.finance.current =
      (current (fromRoot inventory depth).packet.1 (fromRoot inventory depth).packet.2.inputs).claims ∧
    HEq ((facade inventory depth).readoutAt (activated inventory depth (ordinal inventory)) (.inr ()))
      ((activated inventory depth (ordinal inventory)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated inventory depth (ordinal inventory)).tick.generated.wholeLedgerWriteBack
      ((activated inventory depth (ordinal inventory)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated inventory depth (ordinal inventory)).current.visit.current) ∧
    (activated inventory depth (ordinal inventory)).tick.nextCurrent =
      (facade inventory depth).process.stateAt ((facade inventory depth).process.successor
        (activated inventory depth (ordinal inventory)).state) := by
  have factor := (facade inventory depth).readoutAt_factorizes (activated inventory depth (ordinal inventory)) (.inr ())
  exact ⟨rfl,(fromRoot inventory depth).answer_exact,
    fun active => ((fromRoot inventory depth).newborn active).2.complete_is_the_whole_saved_event_sequence,
    (fromRoot inventory depth).packet.2.matrix,factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩

theorem actual_paid_birth_forbids_native_seals_at_every_later_actual_controller
    (paid : (fromRoot inventory depth).answer.result.event.original.original.decision.kind = .paid) :
    NativePastNonClosure (fromRoot inventory depth).answer.result.packet ∧
    HEq ((facade inventory depth).readoutAt (activated inventory depth (ordinal inventory)) (.inr ()))
      ((activated inventory depth (ordinal inventory)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated inventory depth (ordinal inventory)).tick.generated.wholeLedgerWriteBack
      ((activated inventory depth (ordinal inventory)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated inventory depth (ordinal inventory)).current.visit.current) ∧
    (activated inventory depth (ordinal inventory)).tick.nextCurrent =
      (facade inventory depth).process.stateAt ((facade inventory depth).process.successor
        (activated inventory depth (ordinal inventory)).state) := by
  have factor := (facade inventory depth).readoutAt_factorizes (activated inventory depth (ordinal inventory)) (.inr ())
  exact ⟨paid_response_generates_its_own_native_past_nonclosure (fromRoot inventory depth).answer.result paid,
    factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine.Runtime
