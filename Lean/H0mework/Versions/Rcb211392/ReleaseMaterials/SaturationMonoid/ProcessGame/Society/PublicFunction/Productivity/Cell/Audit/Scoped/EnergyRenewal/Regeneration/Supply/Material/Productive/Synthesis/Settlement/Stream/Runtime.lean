import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Runtime
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable (basis : State) (requests : Requests.Source)

structure Result (ordinal : Nat) where
  legacy : State
  legacyExact : legacy=basis
  frame : Frame basis
  frameExact : frame=run basis requests (ordinal+1)
  account : Finance.Account
  accountExact : account=Financial.Family.continueVisits Finance.sources (input basis requests) 0 (ordinal+1) basis.delivery

def result (ordinal : Nat) : Result basis requests ordinal :=
  ⟨basis,rfl,run basis requests (ordinal+1),rfl,
   Financial.Family.continueVisits Finance.sources (input basis requests) 0 (ordinal+1) basis.delivery,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input basis requests)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (ordinal : Nat) →
    current=(ProgrammeHistory.visitAt (input basis requests) ordinal).current → Result basis requests ordinal
  project := fun _ {_} _ _ ordinal _ => result basis requests ordinal

def root := (ProgrammeLiving.livingRoot (input basis requests)).withProjectionCoface (projectionLaw basis requests)
def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input basis requests)) :=
  ⟨ProgrammeSource.V (input basis requests),root basis requests,
   ProgrammeHistory.temporalVisit (input basis requests) ordinal⟩
def process : SourceNativeLivingRootProcess (ProgrammeSource.N (input basis requests)) where
  State := Nat
  stateAt := stateAt basis requests
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input basis requests)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where | execution | service

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input basis requests)) where
  process := process basis requests
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (input basis requests)
    | .service => projectionLaw basis requests
  installationAt := by
    intro tick face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw basis requests)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw basis requests)
  projectionAt := fun _ face => match face with | .execution => .execution | .service => ()

def activated (ordinal : Nat) := (facade basis requests).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated basis requests ordinal).state=ordinal := by
  induction ordinal with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

def consume (ordinal : Nat) : Result basis requests ordinal :=
  match (facade basis requests).readoutAt (activated basis requests ordinal) .service with
  | .inl ⟨_,payload⟩ => payload ordinal (by
      change (ProgrammeHistory.visitAt (input basis requests) (activated basis requests ordinal).state).current=_
      rw [activated_state])
  | .inr impossible => nomatch impossible

def execution (ordinal : Nat) :=
  match (facade basis requests).readoutAt (activated basis requests ordinal) .execution with
  | .inl ⟨_,payload⟩ => payload
  | .inr impossible => nomatch impossible

theorem same_occurrence_whole_ledger_and_own_next (ordinal : Nat) :
    HEq ((facade basis requests).readoutAt (activated basis requests ordinal) .service)
      ((activated basis requests ordinal).tick.generated.projectionOutcome
        (((facade basis requests).installationAt (activated basis requests ordinal) .service).embed
          ((facade basis requests).projectionAt (activated basis requests ordinal) .service))) ∧
    HEq (activated basis requests ordinal).tick.generated.wholeLedgerWriteBack
      ((activated basis requests ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated basis requests ordinal).current.visit.current) ∧
    (activated basis requests ordinal).tick.nextCurrent=
      (process basis requests).stateAt ((process basis requests).successor (activated basis requests ordinal).state) := by
  have same := ((facade basis requests).readoutAt_factorizes (activated basis requests ordinal) .service).2
  exact ⟨same.2.2.1,same.2.1,same.2.2.2⟩

theorem full_legacy_carrier_is_preserved (ordinal : Nat) : (consume basis requests ordinal).legacy=basis :=
  (consume basis requests ordinal).legacyExact

theorem actual_after_is_the_published_frame (ordinal : Nat) :
    (execution basis requests ordinal).after=(consume basis requests ordinal).frame.raw := by
  rw [(consume basis requests ordinal).frameExact]
  change (ProgrammeLiving.executionFace (input basis requests)
    (ProgrammeSource.emitted (input basis requests)
      (ProgrammeHistory.visitAt (input basis requests) (activated basis requests ordinal).state).current)).after=_
  rw [activated_state]
  exact (ProgrammeLiving.projected_execution_uses_actual_root_next _ _).trans
    (own_current basis requests (ordinal+1))

theorem old_delivery_archives_are_preserved (ordinal index : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : basis.delivery.current.slots[index]?=some (.terminal archive)) :
    (consume basis requests ordinal).account.current.slots[index]?=some (.terminal archive) := by
  rw [(consume basis requests ordinal).accountExact]
  let migrated := Financial.Family.Migration.follow Finance.sources
    (Financial.Family.continueVisits_run Finance.sources (input basis requests) 0 (ordinal+1) basis.delivery)
    index (.terminal archive) present
  exact migrated.present.trans (congrArg some (migrated.path.terminal_is_unchanged Finance.sources))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Runtime
