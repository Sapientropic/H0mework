import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Failure
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm (withCutoff)
open PublicFunction PublicFunction.Mandate
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Native" => OutstandingSource Party Good Port (State Party Technology) Instrument

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port))
  (first second : Party) (unit : Good)
  (initial : RawCurrent Party Good (State Party Technology) Instrument)
  (original : RawEvent Party Good Port (State Party Technology) Instrument)
  (service : List (RawEvent Party Good Port (State Party Technology) Instrument))

local notation "Words" => [] :: original :: service

def OriginDenied (expiry : ℚ) : Prop :=
  let active := law base (withCutoff scope expiry)
  ∃ item ∈ active.rawItems (active.next initial []) original,
    ¬ active.Valid item.before item.request

/-- The original task due date belongs to its registered service. The
new authorization horizon is supplied by the actual calendar solve. -/
structure Opening where
  term : SafeTerm base scope first second unit
  considered : term ∈ frontier base scope first second unit initial Words
  origin : OriginDenied base scope initial original term.band.lower

local notation "Open" => Opening base scope first second unit initial original service

namespace Opening

variable {base scope first second unit initial original service}
  (opening : Opening base scope first second unit initial original service)

def installedScope := withCutoff scope opening.term.band.lower

def source (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :
    BoundSource base opening.installedScope :=
  ⟨{ seed := {
        law := law base opening.installedScope
        initial := initial
        task := scope.task
        actionsAt := actions
        budget := budget
        original := original
        refused := opening.origin },
      positive := positive },
    rfl⟩

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem fold_at_prefix (source : Native) (past : source.ExecutionPrefix) (words : List Word) :
    ((words.foldl OutstandingSource.ExecutionPrefix.append past).frame.raw) =
      words.foldl source.seed.law.next past.frame.raw := by
  induction words generalizing past with
  | nil => rfl
  | cons word rest ih => exact ih (past.append word)

private theorem replay_target_is_the_original_fold (expiry : ℚ) (current : Raw) (words : List Word) :
    (replay base scope expiry current words).2 = words.foldl (law base (withCutoff scope expiry)).next current := by
  induction words generalizing current with
  | nil => rfl
  | cons word rest ih => exact ih ((law base (withCutoff scope expiry)).next current word)

/-- The deadline solver and the public programme agree at the very
review visit where the original signatures are actually consumed. -/
theorem actual_appointment (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :
    OutstandingSource.History.currentAt (opening.source actions budget positive).source service
      (service.length + 2) = opening.term.cell.target := by
  let native := (opening.source actions budget positive).source
  let date := opening.term.band.lower
  have fits := (term_band_exact scope.task opening.term.cell opening.term.assigned date).mp
    opening.term.at_least_owns_its_review.2
  have inCalendar : opening.term.cell ∈ cells base scope ⟨initial.clock, none⟩ initial Words := by
    obtain ⟨cell, listed, trial⟩ := List.mem_flatMap.mp opening.considered
    obtain ⟨assigned, _, selected⟩ := List.mem_filterMap.mp trial
    split at selected
    · exact (congrArg SafeTerm.cell (Option.some.inj selected)) ▸ listed
    · cases selected
  obtain ⟨_, exactCalendar⟩ := (cell_replays_at_every_deadline base scope ⟨initial.clock, none⟩
    initial Words opening.term.cell inCalendar).2 date fits.1
  have exactClock : (replay base scope date initial Words).2 = opening.term.cell.target :=
    congrArg Prod.snd exactCalendar
  calc
    _ = (OutstandingSource.History.replay native service).frame.raw :=
      (OutstandingSource.History.all_finite_inputs_reach_their_own_actual_current native service).1
    _ = service.foldl native.seed.law.next (native.canonicalPrefix 2).frame.raw :=
      fold_at_prefix native _ service
    _ = (replay base scope date initial Words).2 := by
      have bootstrapped : (native.canonicalPrefix 2).frame.raw =
          (law base (withCutoff scope date)).next ((law base (withCutoff scope date)).next initial []) original := rfl
      rw [bootstrapped]
      exact (replay_target_is_the_original_fold (base := base) (scope := scope) date initial Words).symm
    _ = _ := exactClock

def reviewWord : Word :=
  reviewPair base opening.installedScope opening.term.cell.target first second

def inputs : List Word := service ++ [opening.reviewWord]

def input (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :=
  OutstandingSource.History.input (opening.source actions budget positive).source opening.inputs

abbrev actual (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :=
  OutstandingSource.History.actualExecution (opening.source actions budget positive).source opening.inputs
    (service.length + 1)

theorem actual_reviews_are_the_registered_paid_word (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :
    (opening.actual actions budget positive).before = opening.term.cell.target ∧
      (opening.actual actions budget positive).submitted = opening.reviewWord := by
  let native := (opening.source actions budget positive).source
  have same := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix native service
    [opening.reviewWord] (service.length + 2) (Nat.le_refl _)
  have word := OutstandingSource.History.scheduled_input_is_actual native opening.inputs service.length
    (by simp [inputs])
  refine ⟨?_, ?_⟩
  · change OutstandingSource.History.currentAt native opening.inputs (service.length + 2) = _
    exact ((OutstandingSource.History.actual_frame native opening.inputs _).1.trans
      (congrArg (fun past => past.frame.raw) same)).trans
      (((OutstandingSource.History.actual_frame native service _).1).symm.trans
        (opening.actual_appointment actions budget positive))
  · change (OutstandingSource.History.actualExecution native opening.inputs (service.length + 1)).submitted = _
    rw [word]
    simp [inputs]

abbrev root (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :=
  ProgrammeLiving.livingRoot (opening.input actions budget positive)

abbrev visit (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :=
  ProgrammeHistory.temporalVisit (opening.input actions budget positive) (service.length + 2)

abbrev wholeLedger (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :=
  ((opening.root actions budget positive).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (opening.visit actions budget positive)).wholeLedgerWriteBack

abbrev next (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :=
  (opening.root actions budget positive).generatedNextCurrentAt (opening.visit actions budget positive)

theorem generated_review_consumes_both_costs_on_the_original_root (actions : Raw → List Req) (budget : Nat)
    (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2) :
    let actual := opening.actual actions budget positive
    actual.after.technology.holder = none ∧ actual.after.technology.offered = none ∧
      actual.after.claims = actual.before.claims ∧
      actual.after = ProgrammeSource.rawCurrent (opening.input actions budget positive)
        (ProgrammeHistory.visitAt (opening.input actions budget positive) (service.length + 3)).current := by
  dsimp only
  have words := opening.actual_reviews_are_the_registered_paid_word actions budget positive
  have raw := raw_release_consumes_generated_cutoff base scope opening.term.cell.target first second unit
    opening.term.band.lower
    (((term_band_exact scope.task opening.term.cell opening.term.assigned _).mp
      opening.term.at_least_owns_its_review.2).2.1) opening.term.ready
  have release := raw.released
  rw [List.append_nil] at release
  refine ⟨?_, ?_, ?_, (opening.actual actions budget positive).root_next_exact⟩
  all_goals rw [(opening.actual actions budget positive).after_exact, words.1, words.2]
  · change ((law base opening.installedScope).next opening.term.cell.target opening.reviewWord).technology.holder = none
    exact release.1
  · change ((law base opening.installedScope).next opening.term.cell.target opening.reviewWord).technology.offered = none
    exact release.2.1
  · change ((law base opening.installedScope).next opening.term.cell.target opening.reviewWord).claims = opening.term.cell.target.claims
    exact release.2.2

end Opening

inductive Result where
  | blocked (none : ∀ expiry, ¬ Feasible base scope first second unit initial Words expiry)
      (explain : ∀ expiry, CandidateFailure base scope first second unit expiry initial Words)
  | alreadyAdmitted (expiry : ℚ) (noOriginalRefusal : ¬ OriginDenied base scope initial original expiry)
  | installed (opening : Opening base scope first second unit initial original service)
      (least : IsLeast {expiry | Feasible base scope first second unit initial Words expiry} opening.term.band.lower)

/-- Compute the first authorization cutoff before constructing the original
source. Failed service or review leaves the original task uninstalled. -/
def compile : Result base scope first second unit initial original service :=
  match found : shortest? base scope first second unit initial Words with
  | none =>
    let absent := (shortest_eq_none_iff base scope first second unit initial Words).mp found
    .blocked absent fun expiry =>
      explainCandidate base scope first second unit expiry initial Words (absent expiry)
  | some term =>
    let exact := shortest_exact base scope first second unit initial Words found
    let active := law base (withCutoff scope term.band.lower)
    match inspectList (fun item => active.Valid item.before item.request)
        (active.rawItems (active.next initial []) original) with
    | .failure item listed rejected => .installed ⟨term, exact.1, item, listed, rejected⟩ exact.2
    | .clear paid => .alreadyAdmitted term.band.lower (fun ⟨item, listed, denied⟩ =>
      denied (paid item listed))

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
