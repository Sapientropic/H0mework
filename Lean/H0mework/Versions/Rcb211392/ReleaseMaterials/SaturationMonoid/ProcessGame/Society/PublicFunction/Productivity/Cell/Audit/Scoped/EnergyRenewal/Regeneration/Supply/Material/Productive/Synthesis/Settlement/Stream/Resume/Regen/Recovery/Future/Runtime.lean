import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Preservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {seed : Seed} {oldRequests : Requests.Source} {oldPermission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests oldPermission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  {cut : Cut source requests authority index} {count : Nat}
  (original : Snapshot cut count)
  (futureRequests : Requests.Source) (futureAuthority : Authority) (futurePermission : Material.Mode)

local notation "start" => startAt (baseCut := baseCut) (index := index) (count := count)
local notation "prog" => input original futureRequests futureAuthority futurePermission

def account (n : Nat) : Finance.Account :=
  Financial.Family.continueVisits Finance.sources prog start n original.account

def familyRun (n : Nat) :=
  Financial.Family.continueVisits_run Finance.sources prog start n original.account

structure Result (n : Nat) where
  private mk ::
  frame : Frame seed.basis
  frameExact : frame = run original futureRequests futureAuthority futurePermission (n + 1)
  account : Finance.Account
  accountExact : account = Runtime.account original futureRequests futureAuthority futurePermission (n + 1)

def result (n : Nat) : Result original futureRequests futureAuthority futurePermission n :=
  ⟨run original futureRequests futureAuthority futurePermission (n + 1), rfl,
    account original futureRequests futureAuthority futurePermission (n + 1), rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource prog).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt prog (start + n)).current →
      Result original futureRequests futureAuthority futurePermission n
  project := fun _ {_} _ _ n _ => result original futureRequests futureAuthority futurePermission n

def root := (ProgrammeLiving.livingRoot prog).withProjectionCoface
  (projectionLaw original futureRequests futureAuthority futurePermission)

def stateAt (n : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N prog) :=
  ⟨ProgrammeSource.V prog, root original futureRequests futureAuthority futurePermission,
    ProgrammeHistory.temporalVisit prog (start + n)⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N prog) where
  State := Nat
  stateAt := stateAt original futureRequests futureAuthority futurePermission
  stateAt_injective := by
    intro first second same
    have current := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N prog) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact Nat.add_left_cancel (ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj current).2))
  initial := 0
  successorAt := fun n => ⟨n + 1, rfl, HEq.rfl⟩

inductive Face where | execution | settlement

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N prog) where
  process := process original futureRequests futureAuthority futurePermission
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw prog
    | .settlement => projectionLaw original futureRequests futureAuthority futurePermission
  installationAt := by
    intro tick face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw original futureRequests futureAuthority futurePermission)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource _) (projectionLaw original futureRequests futureAuthority futurePermission)
  projectionAt := fun _ face => match face with | .execution => .execution | .settlement => ()

def activated (n : Nat) := (facade original futureRequests futureAuthority futurePermission).seed.advance n

theorem activated_state (n : Nat) :
    (activated original futureRequests futureAuthority futurePermission n).state = n := by
  induction n with
  | zero => rfl
  | succ n previous => exact congrArg Nat.succ previous

def consume (n : Nat) : Result original futureRequests futureAuthority futurePermission n :=
  match (facade original futureRequests futureAuthority futurePermission).readoutAt
      (activated original futureRequests futureAuthority futurePermission n) .settlement with
  | .inl ⟨_, payload⟩ => payload n (by
      change (ProgrammeHistory.visitAt prog
        (start + (show Nat from (activated original futureRequests futureAuthority futurePermission n).state))).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

def execution (n : Nat) :=
  match (facade original futureRequests futureAuthority futurePermission).readoutAt
      (activated original futureRequests futureAuthority futurePermission n) .execution with
  | .inl ⟨_, payload⟩ => payload
  | .inr impossible => nomatch impossible

theorem actual_before_and_after (n : Nat) :
    (execution original futureRequests futureAuthority futurePermission n).before =
      (run original futureRequests futureAuthority futurePermission n).raw ∧
    (execution original futureRequests futureAuthority futurePermission n).after =
      (consume original futureRequests futureAuthority futurePermission n).frame.raw := by
  constructor
  · change ProgrammeSource.rawCurrent prog (ProgrammeHistory.visitAt prog
      (start + (show Nat from (activated original futureRequests futureAuthority futurePermission n).state))).current = _
    rw [activated_state]
    exact own_current original futureRequests futureAuthority futurePermission n
  · rw [(consume original futureRequests futureAuthority futurePermission n).frameExact]
    change (ProgrammeLiving.executionFace prog (ProgrammeSource.emitted prog
      (ProgrammeHistory.visitAt prog
        (start + (show Nat from (activated original futureRequests futureAuthority futurePermission n).state))).current)).after = _
    rw [activated_state]
    exact (ProgrammeLiving.projected_execution_uses_actual_root_next _ _).trans
      (own_current original futureRequests futureAuthority futurePermission (n + 1))

theorem same_occurrence_whole_ledger_and_own_next (n : Nat) :
    HEq (activated original futureRequests futureAuthority futurePermission n).tick.generated.wholeLedgerWriteBack
      ((activated original futureRequests futureAuthority futurePermission n).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated original futureRequests futureAuthority futurePermission n).current.visit.current) ∧
    (activated original futureRequests futureAuthority futurePermission n).tick.nextCurrent =
      (activated original futureRequests futureAuthority futurePermission (n + 1)).current := by
  have factorization := ((facade original futureRequests futureAuthority futurePermission).readoutAt_factorizes
    (activated original futureRequests futureAuthority futurePermission n) .settlement).2
  refine ⟨factorization.2.1, ?_⟩
  rw [factorization.2.2.2]
  change (process original futureRequests futureAuthority futurePermission).stateAt
      ((show Nat from (activated original futureRequests futureAuthority futurePermission n).state) + 1) =
    (process original futureRequests futureAuthority futurePermission).stateAt
      (show Nat from (activated original futureRequests futureAuthority futurePermission (n + 1)).state)
  rw [activated_state, activated_state]
  rfl

theorem every_original_claim_keeps_its_native_position (n : Nat) :
    original.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (account original futureRequests futureAuthority futurePermission n).current.slots.map
        (Financial.Family.slotClaim Finance.sources) :=
  Financial.Family.continueVisits_preserves_original_claims Finance.sources prog start n original.account

theorem every_original_archive_is_preserved (n position : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : original.account.current.slots[position]? = some (.terminal archive)) :
    (account original futureRequests futureAuthority futurePermission n).current.slots[position]? = some (.terminal archive) := by
  let carried := Financial.Family.Migration.follow Finance.sources
    (familyRun original futureRequests futureAuthority futurePermission n) position (.terminal archive) present
  exact carried.present.trans (congrArg some (carried.path.terminal_is_unchanged Finance.sources))

theorem original_native_history_is_preserved (n : Nat) :
    original.account.current.history <+:
      (account original futureRequests futureAuthority futurePermission n).current.history := by
  unfold account
  rw [(familyRun original futureRequests futureAuthority futurePermission n).history_eq]
  exact List.prefix_append _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime
