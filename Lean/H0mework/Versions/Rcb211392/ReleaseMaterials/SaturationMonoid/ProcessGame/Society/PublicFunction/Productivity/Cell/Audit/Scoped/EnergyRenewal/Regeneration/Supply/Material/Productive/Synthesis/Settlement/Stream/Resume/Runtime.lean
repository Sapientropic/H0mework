import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Runtime
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable (seed : Seed) (requests : Requests.Source) (mode : Material.Mode)

structure Result (ordinal : Nat) where
  legacy : Stream.Runtime.Result seed.basis (Requests.finite 3) 9
  legacyExact : legacy=seed.original
  frame : Frame seed.basis
  frameExact : frame=run seed requests mode (ordinal+1)
  account : Finance.Account
  accountExact : account=Financial.Family.continueVisits Finance.sources (input seed requests mode) 0 (ordinal+1) (seed.original).account

def result (ordinal : Nat) : Result seed requests mode ordinal :=
  ⟨seed.original,rfl,run seed requests mode (ordinal+1),rfl,
   Financial.Family.continueVisits Finance.sources (input seed requests mode) 0 (ordinal+1) (seed.original).account,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input seed requests mode)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (ordinal : Nat) →
    current=(ProgrammeHistory.visitAt (input seed requests mode) ordinal).current → Result seed requests mode ordinal
  project := fun _ {_} _ _ ordinal _ => result seed requests mode ordinal

def root := (ProgrammeLiving.livingRoot (input seed requests mode)).withProjectionCoface (projectionLaw seed requests mode)
def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input seed requests mode)) :=
  ⟨ProgrammeSource.V (input seed requests mode),root seed requests mode,
   ProgrammeHistory.temporalVisit (input seed requests mode) ordinal⟩
def process : SourceNativeLivingRootProcess (ProgrammeSource.N (input seed requests mode)) where
  State := Nat
  stateAt := stateAt seed requests mode
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input seed requests mode)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where | execution | service

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input seed requests mode)) where
  process := process seed requests mode
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (input seed requests mode)
    | .service => projectionLaw seed requests mode
  installationAt := by
    intro tick face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw seed requests mode)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw seed requests mode)
  projectionAt := fun _ face => match face with | .execution => .execution | .service => ()

def activated (ordinal : Nat) := (facade seed requests mode).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated seed requests mode ordinal).state=ordinal := by
  induction ordinal with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

def consume (ordinal : Nat) : Result seed requests mode ordinal :=
  match (facade seed requests mode).readoutAt (activated seed requests mode ordinal) .service with
  | .inl ⟨_,payload⟩ => payload ordinal (by
      change (ProgrammeHistory.visitAt (input seed requests mode) (activated seed requests mode ordinal).state).current=_
      rw [activated_state])
  | .inr impossible => nomatch impossible

def execution (ordinal : Nat) :=
  match (facade seed requests mode).readoutAt (activated seed requests mode ordinal) .execution with
  | .inl ⟨_,payload⟩ => payload
  | .inr impossible => nomatch impossible

theorem same_occurrence_whole_ledger_and_own_next (ordinal : Nat) :
    HEq ((facade seed requests mode).readoutAt (activated seed requests mode ordinal) .service)
      ((activated seed requests mode ordinal).tick.generated.projectionOutcome
        (((facade seed requests mode).installationAt (activated seed requests mode ordinal) .service).embed
          ((facade seed requests mode).projectionAt (activated seed requests mode ordinal) .service))) ∧
    HEq (activated seed requests mode ordinal).tick.generated.wholeLedgerWriteBack
      ((activated seed requests mode ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated seed requests mode ordinal).current.visit.current) ∧
    (activated seed requests mode ordinal).tick.nextCurrent=
      (process seed requests mode).stateAt ((process seed requests mode).successor (activated seed requests mode ordinal).state) := by
  have same := ((facade seed requests mode).readoutAt_factorizes (activated seed requests mode ordinal) .service).2
  exact ⟨same.2.2.1,same.2.1,same.2.2.2⟩

theorem full_legacy_carrier_is_preserved (ordinal : Nat) : (consume seed requests mode ordinal).legacy=seed.original :=
  (consume seed requests mode ordinal).legacyExact

theorem actual_after_is_the_published_frame (ordinal : Nat) :
    (execution seed requests mode ordinal).after=(consume seed requests mode ordinal).frame.raw := by
  rw [(consume seed requests mode ordinal).frameExact]
  change (ProgrammeLiving.executionFace (input seed requests mode)
    (ProgrammeSource.emitted (input seed requests mode)
      (ProgrammeHistory.visitAt (input seed requests mode) (activated seed requests mode ordinal).state).current)).after=_
  rw [activated_state]
  exact (ProgrammeLiving.projected_execution_uses_actual_root_next _ _).trans
    (own_current seed requests mode (ordinal+1))

theorem old_delivery_archives_are_preserved (ordinal index : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : (seed.original).account.current.slots[index]?=some (.terminal archive)) :
    (consume seed requests mode ordinal).account.current.slots[index]?=some (.terminal archive) := by
  rw [(consume seed requests mode ordinal).accountExact]
  let migrated := Financial.Family.Migration.follow Finance.sources
    (Financial.Family.continueVisits_run Finance.sources (input seed requests mode) 0 (ordinal+1) (seed.original).account)
    index (.terminal archive) present
  exact migrated.present.trans (congrArg some (migrated.path.terminal_is_unchanged Finance.sources))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Runtime
