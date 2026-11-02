import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {target : Authority.Sources old.base old.scope} {count : Nat}
  {word : List (Action old)}

structure Cursor (old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (oldDepth : Nat) (word : List (Action old)) where
  private mk ::
  origin : Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word
  source : Authority.Sources old.base old.scope
  count : Nat
  begun : 0 < count
  consumed : List (Action old)
  residual : List (Action old)
  split : consumed ++ residual = word

def begin (made : Receipt old oldDepth target count word) : Cursor old oldDepth word :=
  ⟨made.origin,Authority.sourceIndex (installed old target count word),count+1,by omega,
    (plan old target count word).consumed,(plan old target count word).residual,
    (plan old target count word).original_split⟩

namespace Cursor
variable (cursor : Cursor old oldDepth word)

abbrev model : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨old.base,old.scope,cursor.source.val,cursor.source.property.1,cursor.source.property.2⟩
abbrev depth := Machine.Continuation.depth cursor.source.val cursor.count
abbrev before : Current cursor.model := (cursor.source.val.actualExecution cursor.depth).before
abbrev proposal (actor : Party) := Search.selected cursor.model cursor.before actor cursor.residual
abbrev retry (actor : Party) := (cursor.proposal actor).retry cursor.model cursor.before cursor.residual
abbrev work (actor : Party) := (cursor.proposal actor).word cursor.model cursor.before cursor.residual
abbrev quality (actor : Party) := (cursor.proposal actor).quality cursor.model cursor.before cursor.residual

/-- Extra actual work keeps the original word's positions outstanding. -/
def appendActual (emitted : List (Action old)) : Cursor old oldDepth word :=
  ⟨cursor.origin,
    ⟨Machine.Continuation.extend cursor.source.val cursor.count emitted,cursor.source.property.1,cursor.source.property.2⟩,
    cursor.count+1,by omega,cursor.consumed,cursor.residual,cursor.split⟩

def replayPreparation (preparation : List (Action old)) : Cursor old oldDepth word :=
  let selected : Search.Proposal cursor.model := ⟨preparation⟩
  let retry := selected.retry cursor.model cursor.before cursor.residual
  ⟨cursor.origin,
    ⟨Machine.Continuation.extend cursor.source.val cursor.count
      (selected.word cursor.model cursor.before cursor.residual),cursor.source.property.1,cursor.source.property.2⟩,
    cursor.count+1,by omega,cursor.consumed ++ retry.consumed,retry.residual,by
      rw [List.append_assoc,retry.original_split,cursor.split]⟩

def emit (emitted consumed residual : List (Action old))
    (split : consumed ++ residual = cursor.residual) : Cursor old oldDepth word :=
  ⟨cursor.origin,
    ⟨Machine.Continuation.extend cursor.source.val cursor.count emitted,cursor.source.property.1,cursor.source.property.2⟩,
    cursor.count+1,by omega,cursor.consumed ++ consumed,residual,by
      rw [List.append_assoc,split,cursor.split]⟩

def after (actor : Party) : Cursor old oldDepth word :=
  cursor.emit (cursor.work actor) (cursor.retry actor).consumed (cursor.retry actor).residual
    (cursor.retry actor).original_split

def feePath (fee : List (Action old)) := Mandate.Replay.compile old.base old.scope cursor.before fee

def charged (fee : List (Action old)) : Cursor old oldDepth word :=
  cursor.emit (cursor.feePath fee).output [] cursor.residual rfl

def attemptPath := Mandate.Replay.compile old.base old.scope cursor.before cursor.residual

def attempt : Cursor old oldDepth word :=
  cursor.emit cursor.attemptPath.output cursor.attemptPath.consumed cursor.attemptPath.residual cursor.attemptPath.original_split

theorem emit_depth (emitted consumed residual : List (Action old)) (split : consumed ++ residual = cursor.residual) :
    (cursor.emit emitted consumed residual split).depth = cursor.depth+1 := rfl

theorem emit_prior_events (emitted consumed residual : List (Action old)) (split : consumed ++ residual = cursor.residual)
    (ordinal : Nat) (earlier : ordinal < cursor.depth+1) :
    ProgrammeSource.rawEvent (cursor.emit emitted consumed residual split).source.val.input
      (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current =
      ProgrammeSource.rawEvent cursor.source.val.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
  Machine.Continuation.prior_events cursor.source.val cursor.count emitted ordinal earlier

theorem emit_prior_currents (emitted consumed residual : List (Action old)) (split : consumed ++ residual = cursor.residual)
    (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    (ProgrammeHistory.visitAt (cursor.emit emitted consumed residual split).source.val.input ordinal).current =
      (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
  Machine.Continuation.prior_currents cursor.source.val cursor.count emitted ordinal earlier

theorem charged_depth (fee : List (Action old)) : (cursor.charged fee).depth = cursor.depth+1 := rfl

theorem attempt_depth : cursor.attempt.depth = cursor.depth+1 := rfl

theorem the_fee_is_the_actual_source_event (fee : List (Action old)) :
    ((cursor.charged fee).source.val.actualExecution cursor.depth).submitted = (cursor.feePath fee).output :=
  Machine.Continuation.submitted cursor.source.val cursor.count _

theorem a_paid_fee_has_only_legal_actual_requests (fee : List (Action old))
    (paid : (cursor.feePath fee).succeeded = true) :
    Mandate.Replay.Legal (base := old.base) old.scope cursor.before (cursor.feePath fee).output :=
  (cursor.feePath fee).successful_output_is_all_legal paid

theorem charging_preserves_every_unconsumed_original_position (fee : List (Action old)) :
    (cursor.charged fee).consumed = cursor.consumed ∧ (cursor.charged fee).residual = cursor.residual := by
  constructor
  · exact List.append_nil _
  · rfl

/-- No new signer is chosen: the first still-unconsumed original request owns recovery. -/
def step : Cursor old oldDepth word := match cursor.residual with
  | [] => cursor
  | head :: _ => cursor.after head.signer

theorem the_original_word_is_never_rewritten_or_dropped :
    cursor.consumed ++ cursor.residual = word := cursor.split

theorem begin_is_the_previous_root_actual_next (made : Receipt old oldDepth target count word) :
    (begin made).before =
      (installed old target count word).source.currentAt (targetDepth old target count+2) := rfl

theorem preparation_is_fully_authorized_and_paid (actor : Party) :
    Mandate.Replay.Legal (base := old.base) old.scope cursor.before
      ((cursor.proposal actor).prepared cursor.model cursor.before).output :=
  ((cursor.proposal actor).prepared (Search.Context.ofBound cursor.model) cursor.before).successful_output_is_all_legal
    (Search.selected_preparation_is_legal (Search.Context.ofBound cursor.model) cursor.before actor cursor.residual)

theorem the_actual_recovery_word_is_emitted (actor : Party) :
    ((cursor.after actor).source.val.actualExecution cursor.depth).submitted = cursor.work actor :=
  Machine.Continuation.submitted cursor.source.val cursor.count _

theorem recovery_starts_from_this_actual_current (actor : Party) :
    ((cursor.after actor).source.val.actualExecution cursor.depth).before = cursor.before :=
  Machine.Continuation.before cursor.source.val cursor.count _

theorem recovery_generates_its_own_actual_next (actor : Party) :
    (cursor.after actor).before = cursor.source.val.code.law.next cursor.before (cursor.work actor) := by
  have actual := Machine.Continuation.actual_next cursor.source.val cursor.count (cursor.work actor)
  change (Machine.Continuation.extend cursor.source.val cursor.count (cursor.work actor)).currentAt
    (cursor.source.val.history.length+1+(cursor.count+1)+1) = _
  have address : cursor.source.val.history.length+1+(cursor.count+1)+1 = cursor.depth+2 := by
    dsimp only [depth,Machine.Continuation.depth];omega
  rw [address]
  exact actual

theorem every_previous_financial_origin_and_archive_is_retained (actor : Party) (ordinal : Nat)
    (earlier : ordinal ≤ cursor.depth+1) :
    Coupling.Match cursor.source.val.code cursor.source.val.input (cursor.after actor).source.val.input
      (Financial.accountAt cursor.source.val.input ordinal) (Financial.accountAt (cursor.after actor).source.val.input ordinal) :=
  Machine.Continuation.complete_financial_prefix cursor.source.val cursor.count _ ordinal earlier

theorem after_depth (actor : Party) : (cursor.after actor).depth = cursor.depth+1 := rfl

theorem prior_events (actor : Party) (ordinal : Nat) (earlier : ordinal < cursor.depth+1) :
    ProgrammeSource.rawEvent (cursor.after actor).source.val.input
      (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current =
      ProgrammeSource.rawEvent cursor.source.val.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
  Machine.Continuation.prior_events cursor.source.val cursor.count (cursor.work actor) ordinal earlier

theorem prior_currents (actor : Party) (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    (ProgrammeHistory.visitAt (cursor.after actor).source.val.input ordinal).current =
      (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
  Machine.Continuation.prior_currents cursor.source.val cursor.count (cursor.work actor) ordinal earlier

theorem positive_recovery_strictly_consumes_the_original_tail (actor : Party)
    (positive : 0 < cursor.quality actor) : (cursor.after actor).residual.length < cursor.residual.length := by
  have paid := Search.selected_preparation_is_legal cursor.model cursor.before actor cursor.residual
  have size := congrArg List.length (cursor.retry actor).original_split
  simp only [List.length_append] at size
  change 0 < (cursor.proposal actor).quality cursor.model cursor.before cursor.residual at positive
  simp only [Search.Proposal.quality,paid,if_true] at positive
  change 0 < (cursor.retry actor).consumed.length at positive
  change (cursor.retry actor).consumed.length + (cursor.retry actor).residual.length = cursor.residual.length at size
  change (cursor.retry actor).residual.length < cursor.residual.length
  omega

end Cursor

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
