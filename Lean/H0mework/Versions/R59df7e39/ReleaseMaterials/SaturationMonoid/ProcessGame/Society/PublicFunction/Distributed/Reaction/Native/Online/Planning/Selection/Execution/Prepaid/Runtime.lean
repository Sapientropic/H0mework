import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Runtime
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
  {cursor : Cursor seed driver} {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {reference : Term cursor} {actor : Party} {position : Nat}
  (record : Protocol cursor pricing n reference actor position)
abbrev point := record.endpoint
structure Snapshot where
  private mk ::
  execution : Protocol cursor pricing n reference actor position
  execution_exact : execution = record
  planning : Cursor seed driver
  planning_exact : planning = record.planning
  work : List (Sigma fun stage : Cursor seed driver => Operation stage)
  work_exact : work = record.work
  pending : List (Sigma fun stage : Cursor seed driver => Pending stage)
  pending_exact : pending = record.pending
  learning : Cursor seed driver
  learning_exact : learning = point record
  whole : Evaluation (point record).source.val.code
  whole_exact : whole = Window.evaluate (point record).model cursor.depth ((point record).depth-cursor.depth)
  native : Authority.FullDisposition (point record).model ((point record).depth-1)
  native_exact : native = Authority.fullGenerate _ _

def generate : Snapshot record :=
  ⟨record,rfl,record.planning,rfl,record.work,rfl,record.pending,rfl,point record,rfl,Window.evaluate (point record).model cursor.depth ((point record).depth-cursor.depth),rfl,
    Authority.fullGenerate _ _,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (point record).source.val.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (point record).source.val.input (point record).depth).current → Snapshot record
  project := fun _ {_} _ _ _own => generate record

def root := (Online.Runtime.root (point record)).withProjectionCoface (projectionLaw record)

theorem original_programme_root_is_preserved : (root record).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (point record).source.val.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (point record).source.val.input) :=
  ⟨ProgrammeSource.V _,root record,ProgrammeHistory.temporalVisit _ ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (point record).source.val.input) where
  State := Nat
  stateAt := stateAt record
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (point record).source.val.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (point record).source.val.input first).current =
        (ProgrammeHistory.visitAt (point record).source.val.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Online.Runtime.Face)
  | computation

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (point record).source.val.input) where
  process := process record
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Online.Runtime.facade (point record)).componentAt (Online.Runtime.facade (point record)).seed previous
    | .computation => projectionLaw record
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Online.Runtime.facade (point record)).installationAt (Online.Runtime.facade (point record)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Online.Runtime.root (point record)).toAuthoritativeRoot.source (projectionLaw record))
    | computation =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Online.Runtime.root (point record)).toAuthoritativeRoot.source (projectionLaw record)
  projectionAt := fun _ face => match face with
    | .previous previous => (Online.Runtime.facade (point record)).projectionAt (Online.Runtime.facade (point record)).seed previous
    | .computation => ()

abbrev activated := (facade record).seed.advance (point record).depth

theorem activated_state : (activated record).state = (point record).depth := by
  have all (n : Nat) : ((facade record).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Snapshot record :=
  match (facade record).readoutAt (activated record) .computation with
  | .inl actual => actual.2 (by
      change (ProgrammeHistory.visitAt (point record).source.val.input (activated record).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_the_prepaid_fresh_choice_all_quote_obligations_full_payment_interval_and_next :
    let active := activated record
    (read record).execution = record ∧
    (read record).planning = record.planning ∧
    (read record).work = record.work ∧
    (read record).pending = record.pending ∧ (read record).learning = record.endpoint ∧
    (read record).whole = Window.evaluate (point record).model cursor.depth ((point record).depth-cursor.depth) ∧
    (read record).native = Authority.fullGenerate (point record).model ((point record).depth-1) ∧
    HEq ((facade record).readoutAt active .computation) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (process record).stateAt ((process record).successor active.state) := by
  have rooted := (facade record).readoutAt_factorizes (activated record) .computation
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Runtime
