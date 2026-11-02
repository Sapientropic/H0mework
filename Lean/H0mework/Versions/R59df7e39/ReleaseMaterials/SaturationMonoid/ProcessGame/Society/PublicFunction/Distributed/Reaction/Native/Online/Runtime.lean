import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Recovery
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
  (cursor : Cursor seed driver)

structure Snapshot where
  private mk ::
  learning : Cursor seed driver
  learning_exact : learning = cursor
  native : Authority.FullDisposition cursor.model (cursor.depth-1)
  native_exact : native = Authority.fullGenerate cursor.model (cursor.depth-1)

def generate : Snapshot cursor := ⟨cursor,rfl,Authority.fullGenerate cursor.model (cursor.depth-1),rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource cursor.source.val.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt cursor.source.val.input cursor.depth).current → Snapshot cursor
  project := fun _ {_} _ _ _own => generate cursor

def root := (AuthorityRuntime.root cursor.model).withProjectionCoface (projectionLaw cursor)

theorem original_programme_root_is_preserved : (root cursor).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot cursor.source.val.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N cursor.source.val.input) :=
  ⟨ProgrammeSource.V _,root cursor,ProgrammeHistory.temporalVisit _ ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N cursor.source.val.input) where
  State := Nat
  stateAt := stateAt cursor
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N cursor.source.val.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt cursor.source.val.input first).current =
        (ProgrammeHistory.visitAt cursor.source.val.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : AuthorityRuntime.Face)
  | online

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N cursor.source.val.input) where
  process := process cursor
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (AuthorityRuntime.facade cursor.model).componentAt (AuthorityRuntime.facade cursor.model).seed previous
    | .online => projectionLaw cursor
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((AuthorityRuntime.facade cursor.model).installationAt (AuthorityRuntime.facade cursor.model).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (AuthorityRuntime.root cursor.model).toAuthoritativeRoot.source (projectionLaw cursor))
    | online =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (AuthorityRuntime.root cursor.model).toAuthoritativeRoot.source (projectionLaw cursor)
  projectionAt := fun _ face => match face with
    | .previous previous => (AuthorityRuntime.facade cursor.model).projectionAt (AuthorityRuntime.facade cursor.model).seed previous
    | .online => ()

abbrev activated := (facade cursor).seed.advance cursor.depth

theorem activated_state : (activated cursor).state = cursor.depth := by
  have all (n : Nat) : ((facade cursor).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Snapshot cursor :=
  match (facade cursor).readoutAt (activated cursor) .online with
  | .inl actual => actual.2 (by
      change (ProgrammeHistory.visitAt cursor.source.val.input (activated cursor).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_online_learning_complete_native_rows_the_entire_ledger_and_its_own_next :
    let active := activated cursor
    (read cursor).learning = cursor ∧
    (read cursor).native = Authority.fullGenerate cursor.model (cursor.depth-1) ∧
    cursor.state.current = cursor.source.val.currentAt (cursor.depth+1) ∧
    HEq ((facade cursor).readoutAt active .online) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process cursor).stateAt ((process cursor).successor active.state) := by
  have rooted := (facade cursor).readoutAt_factorizes (activated cursor) .online
  exact ⟨rfl,rfl,cursor.aligned,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
variable {oldDepth : Nat} {word : List (Future.Recovery.Action seed)}

theorem the_paid_recovery_frame_is_consumed_by_the_same_online_root
    (made : Recovery.Receipt cursor oldDepth word) :
    let next := made.next
    let active := activated next
    (read next).learning = next ∧
    next.model = made.output.bound ∧
    (read next).native = Authority.fullGenerate next.model (next.depth-1) ∧
    next.state.frame.word = cursor.state.frame.word ++
      ((List.range (made.output.walk.finish.depth-cursor.depth)).map
        (fun index => (made.output.bound.source.actualExecution (cursor.depth+index)).submitted)).flatten ∧
    HEq next.state.past cursor.state.past ∧
    HEq next.state.frame.inbox cursor.state.frame.inbox ∧
    HEq next.state.frame.sent cursor.state.frame.sent ∧
    HEq ((facade next).readoutAt active .online) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process next).stateAt ((process next).successor active.state) := by
  have rooted := (facade made.next).readoutAt_factorizes (activated made.next) .online
  have memory := cursor.recovery_preserves_communication_without_fabricating_events made.output
  exact ⟨rfl,made.actual_paid_source_is_the_online_source,rfl,
    cursor.recovery_frame_contains_every_actual_invoice_and_retry made.output,
    memory.1,memory.2.1,memory.2.2,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Runtime
