import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering

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

inductive Walk : Cursor old oldDepth word → Type where
  | finished (cursor : Cursor old oldDepth word) (closed : cursor.residual = []) : Walk cursor
  | blocked (cursor : Cursor old oldDepth word) (head : Action old) (tail : List (Action old))
      (pending : cursor.residual = head :: tail) (noProgress : cursor.quality head.signer = 0) : Walk cursor
  | billed (cursor : Cursor old oldDepth word) (fee : List (Action old))
      (supported : fee ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
      (paid : (cursor.feePath fee).succeeded = true) (later : Walk (cursor.charged fee)) : Walk cursor
  | unsupported (cursor : Cursor old oldDepth word) (fee : List (Action old))
      (outside : fee ∉ words cursor.source.val.code.actions cursor.source.val.code.actionLimit) : Walk cursor
  | unpaid (cursor : Cursor old oldDepth word) (fee : List (Action old))
      (supported : fee ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
      (refused : (cursor.feePath fee).succeeded = false) : Walk cursor
  | advanced (cursor : Cursor old oldDepth word) (head : Action old) (tail : List (Action old))
      (pending : cursor.residual = head :: tail) (progress : 0 < cursor.quality head.signer)
      (later : Walk (cursor.after head.signer)) : Walk cursor

  | workloadStopped (cursor : Cursor old oldDepth word) (position : Nat)
      (made : Metering.Stage cursor position)
      (stopped : ¬ made.endpoint.residual.length < cursor.residual.length) : Walk cursor
  | workloadAdvanced (cursor : Cursor old oldDepth word) (position : Nat)
      (made : Metering.Stage cursor position)
      (progress : made.endpoint.residual.length < cursor.residual.length)
      (later : Walk made.endpoint) : Walk cursor

/-- The original unconsumed positions themselves bound continued successful repair. -/
def execute (cursor : Cursor old oldDepth word) : Walk cursor :=
  match pending : cursor.residual with
  | [] => .finished cursor pending
  | head :: tail =>
    if progress : 0 < cursor.quality head.signer then
      .advanced cursor head tail pending progress (execute (cursor.after head.signer))
    else .blocked cursor head tail pending (Nat.eq_zero_of_not_pos progress)
termination_by cursor.residual.length
decreasing_by exact cursor.positive_recovery_strictly_consumes_the_original_tail _ progress

/-- A registered batch quote is paid at the actual cut before its finite search. -/
def executePaid (fee : List (Action old)) (cursor : Cursor old oldDepth word) : Walk cursor :=
  match pending : cursor.residual with
  | [] => .finished cursor pending
  | head :: tail =>
      if supported : fee ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit then
        if paid : (cursor.feePath fee).succeeded = true then
          let charged := cursor.charged fee
          if progress : 0 < charged.quality head.signer then
            .billed cursor fee supported paid
              (.advanced charged head tail pending progress (executePaid fee (charged.after head.signer)))
          else .billed cursor fee supported paid (.blocked charged head tail pending (Nat.eq_zero_of_not_pos progress))
        else .unpaid cursor fee supported (Bool.eq_false_iff.mpr paid)
      else .unsupported cursor fee supported
termination_by cursor.residual.length
decreasing_by exact (cursor.charged fee).positive_recovery_strictly_consumes_the_original_tail _ progress

/-- Each recursive node consumes the same source-generated invoice, score cache and actual retry. -/
def executeWorkload (position : Nat) (cursor : Cursor old oldDepth word) : Walk cursor :=
  if empty : cursor.residual = [] then .finished cursor empty
  else
    let made := Metering.stage cursor position
    if progress : made.endpoint.residual.length < cursor.residual.length then
      .workloadAdvanced cursor position made progress (executeWorkload position made.endpoint)
    else .workloadStopped cursor position made progress
termination_by cursor.residual.length

namespace Walk

/-- A search node is admitted only under its preceding source-paid batch. -/
inductive Metered (fee : List (Action old)) : {cursor : Cursor old oldDepth word} → Walk cursor → Prop where
  | finished (cursor : Cursor old oldDepth word) (empty : cursor.residual = []) :
      Metered fee (.finished cursor empty)
  | unsupported (cursor : Cursor old oldDepth word)
      (outside : fee ∉ words cursor.source.val.code.actions cursor.source.val.code.actionLimit) :
      Metered fee (.unsupported cursor fee outside)
  | unpaid (cursor : Cursor old oldDepth word)
      (supported : fee ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
      (refused : (cursor.feePath fee).succeeded = false) : Metered fee (.unpaid cursor fee supported refused)
  | blocked (cursor : Cursor old oldDepth word) (head : Action old) (tail : List (Action old))
      (pending : cursor.residual = head :: tail)
      (supported : fee ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
      (paid : (cursor.feePath fee).succeeded = true) (noProgress : (cursor.charged fee).quality head.signer = 0) :
      Metered fee (.billed cursor fee supported paid (.blocked (cursor.charged fee) head tail pending noProgress))
  | advanced (cursor : Cursor old oldDepth word) (head : Action old) (tail : List (Action old))
      (pending : cursor.residual = head :: tail)
      (supported : fee ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
      (paid : (cursor.feePath fee).succeeded = true) (progress : 0 < (cursor.charged fee).quality head.signer)
      (later : Walk ((cursor.charged fee).after head.signer)) (metered : Metered fee later) :
      Metered fee (.billed cursor fee supported paid (.advanced (cursor.charged fee) head tail pending progress later))

inductive WorkloadMetered (position : Nat) : {cursor : Cursor old oldDepth word} → Walk cursor → Prop where
  | finished (cursor : Cursor old oldDepth word) (empty : cursor.residual = []) :
      WorkloadMetered position (.finished cursor empty)
  | stopped (cursor : Cursor old oldDepth word) (made : Metering.Stage cursor position)
      (stopped : ¬ made.endpoint.residual.length < cursor.residual.length) :
      WorkloadMetered position (.workloadStopped cursor position made stopped)
  | advanced (cursor : Cursor old oldDepth word) (made : Metering.Stage cursor position)
      (progress : made.endpoint.residual.length < cursor.residual.length)
      (later : Walk made.endpoint) (metered : WorkloadMetered position later) :
      WorkloadMetered position (.workloadAdvanced cursor position made progress later)

def searchBatches : {cursor : Cursor old oldDepth word} → Walk cursor → Nat
  | _,.finished _ _ | _,.unsupported _ _ _ | _,.unpaid _ _ _ _ => 0
  | _,.blocked _ _ _ _ _ => 1
  | _,.advanced _ _ _ _ _ later => 1+later.searchBatches
  | _,.billed _ _ _ _ later => later.searchBatches
  | _,.workloadStopped _ _ made _ => made.result.searches
  | _,.workloadAdvanced _ _ made _ later => made.result.searches+later.searchBatches

def paidBatches : {cursor : Cursor old oldDepth word} → Walk cursor → Nat
  | _,.finished _ _ | _,.unsupported _ _ _ | _,.unpaid _ _ _ _ | _,.blocked _ _ _ _ _ => 0
  | _,.advanced _ _ _ _ _ later => later.paidBatches
  | _,.billed _ _ _ _ later => 1+later.paidBatches
  | _,.workloadStopped _ _ made _ => made.result.searches
  | _,.workloadAdvanced _ _ made _ later => made.result.searches+later.paidBatches

/-- Workload rows are generated after payment, from that actual material state. -/
def searchRows : {cursor : Cursor old oldDepth word} → Walk cursor → Nat
  | _,.finished _ _ | _,.unsupported _ _ _ | _,.unpaid _ _ _ _ => 0
  | _,.blocked cursor head _ _ _ => (Search.proposals (Search.Context.ofBound cursor.model) cursor.before head.signer cursor.residual).length
  | _,.advanced cursor head _ _ _ later =>
      (Search.proposals (Search.Context.ofBound cursor.model) cursor.before head.signer cursor.residual).length+later.searchRows
  | _,.billed _ _ _ _ later => later.searchRows
  | _,.workloadStopped _ _ made _ => made.result.rows
  | _,.workloadAdvanced _ _ made _ later => made.result.rows+later.searchRows

theorem Metered.every_search_has_its_own_preceding_paid_batch
    {fee : List (Action old)} {cursor : Cursor old oldDepth word} {made : Walk cursor} (metered : Metered fee made) :
    made.searchBatches = made.paidBatches := by
  induction metered with
  | finished | unsupported | unpaid | blocked => rfl
  | advanced _ _ _ _ _ _ _ _ _ ih => exact congrArg (Nat.add 1) ih

theorem WorkloadMetered.every_search_has_its_own_preceding_paid_invoices
    {position : Nat} {cursor : Cursor old oldDepth word} {made : Walk cursor}
    (metered : WorkloadMetered position made) : made.searchBatches = made.paidBatches := by
  induction metered with
  | finished | stopped => rfl
  | advanced _ _ _ _ _ ih => exact congrArg (Nat.add _) ih

variable {cursor : Cursor old oldDepth word}

def finish : {cursor : Cursor old oldDepth word} → Walk cursor → Cursor old oldDepth word
  | _,.finished cursor _ => cursor
  | _,.blocked cursor head _ _ _ => cursor.after head.signer
  | _,.billed _ _ _ _ later => finish later
  | _,.unsupported cursor _ _ => cursor.attempt
  | _,.unpaid cursor fee _ _ => (cursor.charged fee).attempt
  | _,.advanced _ _ _ _ _ later => finish later
  | _,.workloadStopped _ _ made _ => made.endpoint.attempt
  | _,.workloadAdvanced _ _ _ _ later => finish later

/-- Closure is either no original residual or an exact registered-family obstruction. -/
def Closed : {cursor : Cursor old oldDepth word} → Walk cursor → Prop
  | _,.finished cursor _ => cursor.residual = []
  | _,.blocked cursor head _ _ _ =>
    ∀ proposal ∈ Search.proposals (Search.Context.ofBound cursor.model) cursor.before head.signer cursor.residual,
      (proposal.prepared (Search.Context.ofBound cursor.model) cursor.before).succeeded = true →
        (proposal.retry (Search.Context.ofBound cursor.model) cursor.before cursor.residual).succeeded = false
  | _,.billed cursor fee _ _ later => (cursor.feePath fee).succeeded = true ∧ Closed later
  | _,.unsupported cursor fee _ => fee ∉ words cursor.source.val.code.actions cursor.source.val.code.actionLimit
  | _,.unpaid cursor fee _ _ => (cursor.feePath fee).succeeded = false
  | _,.advanced _ _ _ _ _ later => Closed later
  | _,.workloadStopped _ _ made _ => made.result.Quiescent
  | _,.workloadAdvanced _ _ made _ later => made.result.Released ∧ Closed later

theorem closed (made : Walk cursor) : made.Closed := by
  induction made with
  | finished cursor empty => exact empty
  | billed _ _ _ paid _ ih => exact ⟨paid,ih⟩
  | unsupported _ _ outside => exact outside
  | unpaid _ _ _ refused => exact refused
  | blocked cursor head tail pending noProgress =>
    intro proposal registered prepared
    cases complete : (proposal.retry (Search.Context.ofBound cursor.model) cursor.before cursor.residual).succeeded with
    | false => rfl
    | true =>
      have full := Search.any_registered_complete_recovery_is_found (Search.Context.ofBound cursor.model) cursor.before head.signer
        cursor.residual proposal registered prepared complete
      have zero : (cursor.retry head.signer).consumed.length = 0 := by
        have paid := Search.selected_preparation_is_legal (Search.Context.ofBound cursor.model) cursor.before head.signer cursor.residual
        change (cursor.proposal head.signer).quality (Search.Context.ofBound cursor.model) cursor.before cursor.residual = 0 at noProgress
        simpa only [Search.Proposal.quality,paid,if_true] using noProgress
      have consumed : (cursor.retry head.signer).consumed = [] := List.eq_nil_of_length_eq_zero zero
      have residual := Search.no_residual_after_success (Search.Context.ofBound cursor.model) (cursor.retry head.signer) full
      have split := (cursor.retry head.signer).original_split
      rw [consumed,residual,List.nil_append, pending] at split
      cases split
  | advanced _ _ _ _ _ _ ih => exact ih
  | workloadStopped _ _ made stopped => exact made.quiescent stopped
  | workloadAdvanced _ _ made progress _ ih => exact ⟨made.released progress,ih⟩

theorem source_code_is_retained (made : Walk cursor) : made.finish.source.val.code = cursor.source.val.code := by
  induction made with
  | finished | blocked | unsupported | unpaid => rfl
  | billed _ _ _ _ _ ih => exact ih
  | advanced _ _ _ _ _ _ ih => exact ih
  | workloadStopped _ _ made _ => exact made.preserves.code
  | workloadAdvanced _ _ made _ _ ih => exact ih.trans made.preserves.code

theorem prior_events (made : Walk cursor) (ordinal : Nat) (earlier : ordinal < cursor.depth+1) :
    ProgrammeSource.rawEvent made.finish.source.val.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current =
      ProgrammeSource.rawEvent cursor.source.val.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current := by
  induction made with
  | finished => rfl
  | blocked cursor head _ _ _ => exact cursor.prior_events head.signer ordinal earlier
  | unsupported cursor fee _ =>
      exact cursor.emit_prior_events cursor.attemptPath.output cursor.attemptPath.consumed cursor.attemptPath.residual cursor.attemptPath.original_split ordinal earlier
  | unpaid cursor fee _ _ =>
      have nextBound : ordinal < (cursor.charged fee).depth+1 := by
        change ordinal < cursor.depth+1+1
        omega
      have next := (cursor.charged fee).emit_prior_events (cursor.charged fee).attemptPath.output (cursor.charged fee).attemptPath.consumed (cursor.charged fee).attemptPath.residual (cursor.charged fee).attemptPath.original_split ordinal nextBound
      have current : (ProgrammeHistory.visitAt (cursor.charged fee).source.val.input ordinal).current =
          (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
        cursor.emit_prior_currents (cursor.feePath fee).output [] cursor.residual rfl ordinal (by omega)
      rw [current] at next
      exact next.trans (cursor.emit_prior_events (cursor.feePath fee).output [] cursor.residual rfl ordinal earlier)
  | billed cursor fee _ _ _ ih =>
      have nextBound : ordinal < (cursor.charged fee).depth+1 := by
        change ordinal < cursor.depth+1+1
        omega
      have next := ih nextBound
      have current : (ProgrammeHistory.visitAt (cursor.charged fee).source.val.input ordinal).current =
          (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
        cursor.emit_prior_currents (cursor.feePath fee).output [] cursor.residual rfl ordinal (by omega)
      rw [current] at next
      exact next.trans (cursor.emit_prior_events (cursor.feePath fee).output [] cursor.residual rfl ordinal earlier)
  | advanced cursor head _ _ _ later ih =>
      have nextBound : ordinal < (cursor.after head.signer).depth+1 := by rw [cursor.after_depth];omega
      have next := ih nextBound
      rw [cursor.prior_currents head.signer ordinal (by omega)] at next
      exact next.trans (cursor.prior_events head.signer ordinal earlier)

  | workloadStopped cursor _ made _ =>
      have ordered := made.preserves.depth
      have next := made.endpoint.emit_prior_events made.endpoint.attemptPath.output made.endpoint.attemptPath.consumed made.endpoint.attemptPath.residual made.endpoint.attemptPath.original_split ordinal (by omega)
      rw [made.preserves.currents ordinal (by omega)] at next
      exact next.trans (made.preserves.events ordinal earlier)
  | workloadAdvanced cursor _ made _ _ ih =>
      have ordered := made.preserves.depth
      have next := ih (by omega)
      rw [made.preserves.currents ordinal (by omega)] at next
      exact next.trans (made.preserves.events ordinal earlier)

/-- A stopped metering service still emits the original raw retry on its actual post-invoice cut. -/
theorem workload_stopping_never_withholds_the_old_attempt (position : Nat)
    (made : Metering.Stage cursor position)
    (stopped : ¬ made.endpoint.residual.length < cursor.residual.length) :
    (((Walk.workloadStopped cursor position made stopped).finish).source.val.actualExecution made.endpoint.depth).submitted =
      made.endpoint.attemptPath.output :=
  Machine.Continuation.submitted made.endpoint.source.val made.endpoint.count _

theorem complete_financial_prefix (made : Walk cursor) (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    Coupling.Match cursor.source.val.code cursor.source.val.input made.finish.source.val.input
      (Financial.accountAt cursor.source.val.input ordinal) (Financial.accountAt made.finish.source.val.input ordinal) :=
  Coupling.History.complete_accounts cursor.source.val.code cursor.source.val.input made.finish.source.val.input
    (congrArg Code.law made.source_code_is_retained) (congrArg Code.initial made.source_code_is_retained)
    (cursor.depth+1) made.prior_events cursor.source.val.body made.finish.source.val.body rfl rfl ordinal earlier

theorem the_complete_original_word_survives_every_recovery (made : Walk cursor) :
    made.finish.consumed ++ made.finish.residual = word := made.finish.split
end Walk

theorem every_source_priced_search_is_actually_prepaid (fee : List (Action old)) (cursor : Cursor old oldDepth word) :
    Walk.Metered fee (executePaid fee cursor) := by
  unfold executePaid
  split
  · exact .finished _ _
  · split
    · split
      · dsimp only
        split
        · exact .advanced _ _ _ _ _ _ _ _ (every_source_priced_search_is_actually_prepaid fee _)
        · exact .blocked _ _ _ _ _ _ _
      · exact .unpaid _ _ _
    · exact .unsupported _ _
termination_by cursor.residual.length
decreasing_by exact (cursor.charged fee).positive_recovery_strictly_consumes_the_original_tail _ (by assumption)

theorem every_workload_search_is_generated_after_its_actual_invoices (position : Nat) (cursor : Cursor old oldDepth word) :
    Walk.WorkloadMetered position (executeWorkload position cursor) := by
  unfold executeWorkload
  split
  · exact .finished _ _
  · dsimp only
    split
    · exact .advanced _ _ _ _ (every_workload_search_is_generated_after_its_actual_invoices position _)
    · exact .stopped _ _ _
termination_by cursor.residual.length



end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
