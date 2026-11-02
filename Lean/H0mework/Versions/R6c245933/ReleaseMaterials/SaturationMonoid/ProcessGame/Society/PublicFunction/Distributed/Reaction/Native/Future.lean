import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Continuation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Challenge

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (oldDepth : Nat) (target : Authority.Sources old.base old.scope) (count : Nat)
  (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)

abbrev targetDepth := Machine.Continuation.depth target.val count
abbrev atTarget := (target.val.actualExecution (targetDepth old target count)).before
abbrev plan := Mandate.Replay.compile old.base old.scope (atTarget old target count) word
abbrev installed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨old.base,old.scope,Machine.Continuation.extend target.val count (plan old target count word).output,
    target.property.1,target.property.2⟩

/-- The original permission is checked at its original actual source cut. The
    new execution and every native row are generated at the different target cut. -/
structure Receipt where
  private mk ::
  origin : Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word
  native : Authority.FullDisposition (installed old target count word) (targetDepth old target count)
  native_exact : native = Authority.fullGenerate (installed old target count word) (targetDepth old target count)

def produce : PLift (¬ Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word) ⊕
    Receipt old oldDepth target count word :=
  if legal : Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word then
    .inr ⟨legal,Authority.fullGenerate _ _,rfl⟩
  else .inl ⟨legal⟩

namespace Receipt
variable {old oldDepth target count word} (made : Receipt old oldDepth target count word)

include made in
theorem old_word_was_legal_at_its_original_actual_cut :
    Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word := made.origin

theorem original_residual_is_retained :
    (plan old target count word).consumed ++ (plan old target count word).residual = word :=
  (plan old target count word).original_split

theorem actual_word_and_before :
    ((installed old target count word).source.actualExecution (targetDepth old target count)).submitted =
      (plan old target count word).output ∧
    ((installed old target count word).source.actualExecution (targetDepth old target count)).before =
      atTarget old target count :=
  ⟨Machine.Continuation.submitted target.val count _,Machine.Continuation.before target.val count _⟩

theorem exact_failure_is_really_executed (failure : (plan old target count word).succeeded = false) :
    ∃ item ∈ (installed old target count word).source.code.law.rawItems
      ((installed old target count word).source.actualExecution (targetDepth old target count)).before
      ((installed old target count word).source.actualExecution (targetDepth old target count)).submitted,
      item.index = (plan old target count word).consumed.length ∧
        ¬ (installed old target count word).source.code.law.Valid item.before item.request := by
  rw [actual_word_and_before.1,actual_word_and_before.2]
  change ∃ item ∈ target.val.code.law.rawItems (atTarget old target count) (plan old target count word).output,
    item.index = (plan old target count word).consumed.length ∧ ¬ target.val.code.law.Valid item.before item.request
  rw [target.property.1]
  exact (plan old target count word).failure_is_an_actual_raw_item failure

theorem all_actual_native_accounts_keep_their_original_prefix (ordinal : Nat)
    (earlier : ordinal ≤ targetDepth old target count+1) :
    Coupling.Match target.val.code target.val.input (installed old target count word).source.input
      (Financial.accountAt target.val.input ordinal)
      (Financial.accountAt (installed old target count word).source.input ordinal) :=
  Machine.Continuation.complete_financial_prefix target.val count _ ordinal earlier

include made in
theorem complete_native_rows_use_the_replaying_input :
    made.native = Authority.fullGenerate (installed old target count word) (targetDepth old target count) := made.native_exact

/-- All inherited services, grants, challenges and finance are read from this
    emitting input; the transport proof is installed on its own occurrence. -/
def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (installed old target count word).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (installed old target count word).source.input (targetDepth old target count+1)).current →
      Receipt old oldDepth target count word
  project := fun _ {_} _ _ _own => made

def root := (AuthorityRuntime.root (installed old target count word)).withProjectionCoface made.projectionLaw

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (installed old target count word).source.input) :=
  ⟨ProgrammeSource.V _,made.root,ProgrammeHistory.temporalVisit _ ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (installed old target count word).source.input) where
  State := Nat
  stateAt := made.stateAt
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (installed old target count word).source.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (installed old target count word).source.input first).current =
        (ProgrammeHistory.visitAt (installed old target count word).source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : AuthorityRuntime.Face)
  | future

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (installed old target count word).source.input) where
  process := made.process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (AuthorityRuntime.facade (installed old target count word)).componentAt
        (AuthorityRuntime.facade (installed old target count word)).seed previous
    | .future => made.projectionLaw
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((AuthorityRuntime.facade (installed old target count word)).installationAt
        (AuthorityRuntime.facade (installed old target count word)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (AuthorityRuntime.root (installed old target count word)).toAuthoritativeRoot.source made.projectionLaw)
    | future =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (AuthorityRuntime.root (installed old target count word)).toAuthoritativeRoot.source made.projectionLaw
  projectionAt := fun _ face => match face with
    | .previous previous => (AuthorityRuntime.facade (installed old target count word)).projectionAt
        (AuthorityRuntime.facade (installed old target count word)).seed previous
    | .future => ()

abbrev activated := made.facade.seed.advance (targetDepth old target count+1)

theorem activated_state : made.activated.state = targetDepth old target count+1 := by
  have all (n : Nat) : (made.facade.seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Receipt old oldDepth target count word :=
  match made.facade.readoutAt made.activated .future with
  | .inl actual => actual.2 (by
      change (ProgrammeHistory.visitAt (installed old target count word).source.input made.activated.state).current = _
      rw [made.activated_state]
      rfl)
  | .inr impossible => nomatch impossible

theorem read_exact : made.read = made := rfl

theorem the_actual_root_consumes_the_replay_full_native_rows_and_its_own_next :
    let active := made.activated
    made.native = Authority.fullGenerate (installed old target count word) (targetDepth old target count) ∧
    (plan old target count word).consumed ++ (plan old target count word).residual = word ∧
    HEq (made.facade.readoutAt active .future) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor active.state) := by
  have rooted := made.facade.readoutAt_factorizes made.activated .future
  exact ⟨made.native_exact,original_residual_is_retained,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end Receipt

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future
