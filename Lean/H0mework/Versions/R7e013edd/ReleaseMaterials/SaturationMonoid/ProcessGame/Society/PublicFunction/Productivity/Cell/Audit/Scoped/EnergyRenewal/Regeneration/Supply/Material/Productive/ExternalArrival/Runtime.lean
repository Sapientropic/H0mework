import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Effect

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Runtime
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Protocol.SymbolicAuthentication Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
noncomputable section

def sourceInput := (Export.trace 3).cursor.source.input
private theorem physical_input (actual : RenewableArchiveSource.State
    (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port)
    (Technology := Bool) (Instrument := Unit)) (model : FreshSigningReplay.Model)
    (point : Cursor model.source.code) (same : FreshSigningReplay.physical actual=⟨model,point⟩) :
    actual.point.source.input=point.source.input := by
  cases actual
  cases same
  rfl

theorem source_input_is_the_complete_actual_source :
    sourceInput=(Packet.full true).actual.point.source.input :=
  (physical_input Root.after.actual (Export.model 3) (Export.trace 3).cursor
    Root.after_is_the_complete_actual_export_occurrence).symm

def ordinal : Nat := EventStep.boundary (Export.trace 3).cursor-1
variable {plan : Plan} (state : Finance.State plan)

def result (index : Nat) : Finance.State plan := if index=ordinal then Effect.receive state else state
def projectionLaw : SourceNativeProjectionLaw (ProgrammeLiving.authoritySource sourceInput).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (index : Nat) → current=(ProgrammeHistory.visitAt sourceInput index).current → Finance.State plan
  project := fun _ {_} _ _ index _ => result state index

def root := (ProgrammeLiving.livingRoot sourceInput).withProjectionCoface (projectionLaw state)
def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N sourceInput) :=
  ⟨ProgrammeSource.V sourceInput,root state,ProgrammeHistory.temporalVisit sourceInput index⟩
def process : SourceNativeLivingRootProcess (ProgrammeSource.N sourceInput) where
  State := Nat
  stateAt := stateAt state
  stateAt_injective := by
    intro first second same
    have labels:=congrArg (fun current : SourceNativeLivingRootCurrentAt (ProgrammeSource.N sourceInput) =>
      (⟨current.V.Current,current.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective sourceInput (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun n => ⟨n+1,rfl,HEq.rfl⟩

inductive Face where | execution | arrival
def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N sourceInput) where
  process := process state
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw sourceInput
    | .arrival => projectionLaw state
  installationAt := by
    intro tick face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface (ProgrammeLiving.authoritySource sourceInput) (projectionLaw state)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface (ProgrammeLiving.authoritySource sourceInput) (projectionLaw state)
  projectionAt := fun _ face => match face with | .execution => .execution | .arrival => ()

def activated (index : Nat) := (facade state).seed.advance index
theorem activated_state (index : Nat) : (activated state index).state=index := by
  induction index with | zero => rfl | succ n ih => exact congrArg Nat.succ ih
def consume (index : Nat) : Finance.State plan :=
  match (facade state).readoutAt (activated state index) .arrival with
  | .inl ⟨_,payload⟩ => payload index (by
      change (ProgrammeHistory.visitAt sourceInput (activated state index).state).current=_
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem same_occurrence_whole_ledger_and_own_next (index : Nat) :
    (activated state index).tick.generated.occurrence=
      (activated state index).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated state index).current.visit.current ∧
    HEq (activated state index).tick.generated.wholeLedgerWriteBack
      ((activated state index).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated state index).current.visit.current) ∧
    HEq ((facade state).readoutAt (activated state index) .arrival)
      ((activated state index).tick.generated.projectionOutcome
        (((facade state).installationAt (activated state index) .arrival).embed
          ((facade state).projectionAt (activated state index) .arrival))) ∧
    (activated state index).tick.nextCurrent=
      (process state).stateAt ((process state).successor (activated state index).state) :=
  ((facade state).readoutAt_factorizes (activated state index) .arrival).2

theorem consume_is_the_installed_result (index : Nat) : consume state index=result state index := rfl
end
def nativeReceive {plan : Plan} : Finance.State plan → Finance.State plan := Effect.receive
theorem native_is_the_original_source_face {plan : Plan} (state : Finance.State plan) :
    nativeReceive state=consume state ordinal := by
  rw [consume_is_the_installed_result]
  simp [result,nativeReceive]
theorem native_receive_effect {plan : Plan} (state : Finance.State plan) :
    nativeReceive state=Effect.receive state := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Runtime
