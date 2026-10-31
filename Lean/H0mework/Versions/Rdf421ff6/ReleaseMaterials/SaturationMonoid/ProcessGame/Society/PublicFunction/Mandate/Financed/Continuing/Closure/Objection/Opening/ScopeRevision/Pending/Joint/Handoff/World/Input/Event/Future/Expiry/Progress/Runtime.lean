import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev selected := (Progress.produce inventory).1
abbrev finalCut := (selected inventory).ending.1
def ordinal := Future.Runtime.ordinal (finalCut inventory) (ownWord (finalCut inventory))
def baseRoot := Future.Runtime.root (finalCut inventory) (ownWord (finalCut inventory)) 0

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Progress.I inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (Progress.I inventory) (ordinal inventory)).current →
      {trace : Trace inventory // trace.steps ≤ remaining inventory + 1}
  project := fun _ {_} _ _ _own => Progress.produce inventory

def root := (baseRoot inventory).withProjectionCoface (projectionLaw inventory)

theorem root_is_the_original_last_response_root :
    (root inventory).toAuthoritativeRoot.toRoot = (baseRoot inventory).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Progress.I inventory)) :=
  ⟨ProgrammeSource.V (Progress.I inventory),root inventory,ProgrammeHistory.temporalVisit (Progress.I inventory) index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Progress.I inventory)) where
  State := Nat
  stateAt := stateAt inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Progress.I inventory)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Progress.I inventory) first).current =
        (ProgrammeHistory.visitAt (Progress.I inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Progress.I inventory) currents
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

abbrev Face := Sum Future.Runtime.Face Unit

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Progress.I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _state face => match face with
    | .inl previous => (Future.Runtime.facade (finalCut inventory) (ownWord (finalCut inventory)) 0).componentAt
        (Future.Runtime.activated (finalCut inventory) (ownWord (finalCut inventory)) 0 0) previous
    | .inr _ => projectionLaw inventory
  installationAt := by
    intro state face
    have inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
    cases face with
    | inl previous => exact ((Future.Runtime.facade (finalCut inventory) (ownWord (finalCut inventory)) 0).installationAt
        (Future.Runtime.activated (finalCut inventory) (ownWord (finalCut inventory)) 0 0) previous).trans inherited
    | inr own =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _state face => match face with
    | .inl previous => (Future.Runtime.facade (finalCut inventory) (ownWord (finalCut inventory)) 0).projectionAt
        (Future.Runtime.activated (finalCut inventory) (ownWord (finalCut inventory)) 0 0) previous
    | .inr _ => ()

def activated (index : Nat) : LivingRuntimeState (process inventory) := (facade inventory).seed.advance index

def fromRoot : {trace : Trace inventory // trace.steps ≤ remaining inventory + 1} :=
  (projectionLaw inventory).project ()
    (ProgrammeSource.emitted (Progress.I inventory)
      (ProgrammeHistory.visitAt (Progress.I inventory) (ordinal inventory)).current) () rfl

abbrev trace := (fromRoot inventory).1

theorem the_actual_boundary_is_finite_fresh_or_expired :
    (trace inventory).steps ≤ remaining inventory + 1 ∧
    (epoch.scope.task.deadline < (trace inventory).packet.1.scope.task.deadline ∨
      ((trace inventory).packet.1 = epoch ∧
       epoch.scope.task.deadline < (current (trace inventory).packet.1 (trace inventory).packet.2.inputs).clock ∧
       (trace inventory).ending.2.1.event.original.original.decision.kind = .reviewBlocked)) ∧
    (current epoch inventory.inputs).clock < (current (trace inventory).packet.1 (trace inventory).packet.2.inputs).clock :=
  ⟨(fromRoot inventory).2,(trace inventory).fresh_scope_or_actual_expired_blocker,
    (trace inventory).the_actual_boundary_is_not_a_clock_self_loop⟩

theorem full_source_original_account_writeback_and_next_are_consumed_together :
    fromRoot inventory = Progress.produce inventory ∧
    Progress.I inventory = OutstandingSource.History.input epoch.source (trace inventory).finalInputs ∧
    (∀ visit ∈ (trace inventory).visits,
      ((trace inventory).actualIncoming visit).submitted = ownWord visit.1 ∧
      ((trace inventory).actualIncoming visit).before = current epoch visit.1.inputs) ∧
    Financial.Family.ledgerClaims sources (trace inventory).packet.2.finance.current =
      (current (trace inventory).packet.1 (trace inventory).packet.2.inputs).claims ∧
    HEq ((facade inventory).readoutAt (activated inventory (ordinal inventory)) (.inr ()))
      ((activated inventory (ordinal inventory)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated inventory (ordinal inventory)).tick.generated.wholeLedgerWriteBack
      ((activated inventory (ordinal inventory)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated inventory (ordinal inventory)).current.visit.current) ∧
    (activated inventory (ordinal inventory)).tick.nextCurrent =
      (facade inventory).process.stateAt ((facade inventory).process.successor (activated inventory (ordinal inventory)).state) := by
  have factor := (facade inventory).readoutAt_factorizes (activated inventory (ordinal inventory)) (.inr ())
  exact ⟨rfl,the_selected_root_input_is_the_whole_executed_history inventory,
    (trace inventory).every_incoming_is_actually_interpreted_by_the_final_source,
    (trace inventory).packet.2.matrix,factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Runtime
