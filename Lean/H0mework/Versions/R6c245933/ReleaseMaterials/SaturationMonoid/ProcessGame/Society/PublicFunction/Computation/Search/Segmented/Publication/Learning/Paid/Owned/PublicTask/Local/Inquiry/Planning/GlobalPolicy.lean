import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Preservation.Restoration
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.RecallBirth
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.World

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

inductive Service (cache : Inquiry.Frame task) where
  | unavailable (step : Stage task cache) (generated : step = stage task cache) (missing : step.ready = none)
  | completed (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (outcome : Prefix.Global.Outcome (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme)
      (compiled : outcome = Prefix.Global.compile (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme)


  | worldShort (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input)
      (rate : Fin task.model.source.code.actions.length) (declared : task.accountingRate = some rate)
      (missing : ¬ Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits task + World.units task input))
  | worldCompleted (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input)
      (rate : Fin task.model.source.code.actions.length) (declared : task.accountingRate = some rate)
      (covered : Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits task + World.units task input))
      (selected : World.Selection task input step.path.finish)

/-- The original service consumes the paid complete directory before choosing a World policy. -/
def invoke (cache : Inquiry.Frame task) : Service task cache :=
  match World.preflight task cache with
  | .unavailable step generated missing => .unavailable step generated missing
  | .legacy step generated permit paid _ => .completed step generated permit paid
      (Prefix.Global.compile (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme) rfl
  | .short step generated permit paid input supplied rate declared missing =>
      .worldShort step generated permit paid input supplied rate declared missing
  | .covered step generated permit paid input supplied rate declared covered =>
      .worldCompleted step generated permit paid input supplied rate declared covered
        (World.select task input step.path.finish)

namespace Service
variable {task} {cache : Inquiry.Frame task}

def paidCurrent : Service task cache → Cursor task.model.source.code
  | .unavailable step _ _ => (Planning.current task step.path.finish).point
  | .completed step _ _ _ _ _ => (Planning.current task step.path.finish).point
  | .worldShort step .. | .worldCompleted step .. => (Planning.current task step.path.finish).point

def controls : Service task cache → List (Prefix.Rule task.model.source.code)
  | .unavailable step _ _ => step.path.finish.past
  | .completed step _ _ _ outcome _ => match outcome with
      | .blocked _ => step.path.finish.past
      | .selected candidate => Prefix.Runtime.completeControls (original := task.original) task.point.point candidate.protocol

  | .worldShort step .. => step.path.finish.past
  | .worldCompleted step _ _ _ _ _ _ _ _ selected => match (World.Selection.candidate? task selected) with
      | none => step.path.finish.past
      | some candidate => Prefix.Runtime.completeControls (original := task.original) task.point.point candidate.protocol

def full : Service task cache → Cursor task.model.source.code
  | .unavailable step _ _ => (Planning.current task step.path.finish).point
  | .completed step _ _ _ outcome _ => match outcome with
      | .blocked _ => (Planning.current task step.path.finish).point
      | .selected candidate => Splice.install (Planning.current task step.path.finish).point task.rival
          (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol)

  | .worldShort step .. => (Planning.current task step.path.finish).point
  | .worldCompleted step _ _ _ _ _ _ _ _ selected => match (World.Selection.candidate? task selected) with
      | none => (Planning.current task step.path.finish).point
      | some candidate => Splice.install (Planning.current task step.path.finish).point task.rival
          (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol)

abbrev bound (made : Service task cache) := Replanning.native task.model made.full
abbrev facade (made : Service task cache) := Native.AuthorityRuntime.facade made.bound
abbrev activated (made : Service task cache) := Inquiry.Runtime.readState made.bound (depth made.full)

theorem selected_is_the_entire_original_source
    (step : Stage task cache) (permit : Permit task step.path.finish)
    (candidate : Prefix.Global.Candidate (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme) :
    let actual := Splice.install (Planning.current task step.path.finish).point task.rival
      (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol)
    actual.source.input = (Window.Whole.source task.point.point task.original
      (Prefix.Runtime.normalized task.point.point candidate.protocol) task.rival).input := by
  have positive : 0 < Prefix.Runtime.actualHorizon task.point.point := by
    change 0 < (Computation.Cut.seed task.point.point).remaining
    exact Nat.zero_lt_of_lt permit.live.1
  have retained := candidate.committed_prefix step.path.finish.within
  have short : (Prefix.Runtime.normalized task.point.point candidate.protocol).controls.take step.path.finish.past.length =
      step.path.finish.past := by
    change (candidate.protocol.controls.take (Prefix.Runtime.actualHorizon task.point.point)).take _ = _
    rw [List.take_take,Nat.min_eq_left step.path.finish.actualWithin]
    exact retained
  have padded := Prefix.Padding.preserves_prefix task.original _ step.path.finish.past short
  have split := List.take_append_drop step.path.finish.past.length
    (Prefix.Runtime.completeControls (original := task.original) task.point.point candidate.protocol)
  rw [padded] at split
  have assembled : Splice.install (Planning.current task step.path.finish).point task.rival
      (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol) =
      Splice.install task.point.point task.rival
        (Prefix.Runtime.completeControls (original := task.original) task.point.point candidate.protocol) := by
    have current := Paid.State.current_is_the_actual_control_prefix step.path.finish.shell task.point task.rival
    change Splice.install (step.path.finish.shell.current task.point task.rival).point task.rival _ = _
    rw [current]
    change List.foldl _ (List.foldl _ _ _) _ = _
    rw [←List.foldl_append,split]
    rfl
  have nonempty : Prefix.Runtime.completeControls (original := task.original) task.point.point candidate.protocol ≠ [] := by
    intro empty
    have size := Prefix.Padding.length task.original (Prefix.Runtime.normalized task.point.point candidate.protocol)
    change (Prefix.Runtime.completeControls (original := task.original) task.point.point candidate.protocol).length = _ at size
    rw [empty] at size
    exact (Nat.ne_of_gt positive) size.symm
  dsimp only
  rw [assembled,Splice.input_assembly _ _ task.original _ nonempty,Prefix.Padding.same_entire_source]

theorem selected_normalization_preserves_every_complete_future
    {cache : Inquiry.Frame task} (step : Stage task cache)
    (candidate : Prefix.Global.Candidate (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme)
    (rival : Opponent task.model.source.code) :
    Window.Whole.Restoration.actualTensor (tariff := task.recoveryPricing) task.model task.point.point task.original
      (Prefix.Runtime.normalized task.point.point candidate.protocol) rival =
    Window.Whole.Restoration.actualTensor (tariff := task.recoveryPricing) task.model task.point.point task.original candidate.protocol rival :=
  Window.Whole.Restoration.clipping_preserves_the_complete_actual_tensor (tariff := task.recoveryPricing) task.model task.point.point task.original
    candidate.protocol (Prefix.Runtime.actualHorizon task.point.point) (Nat.le_refl _) rival

def programme : Service task cache → Program task.model.source.code (horizon task.domain)
  | .unavailable step _ _ => step.path.finish.programme
  | .completed step _ _ _ outcome _ => match outcome with
      | .blocked _ => step.path.finish.programme
      | .selected candidate => candidate.protocol

  | .worldShort step .. => step.path.finish.programme
  | .worldCompleted step _ _ _ _ _ _ _ _ selected => match (World.Selection.candidate? task selected) with
      | none => step.path.finish.programme
      | some candidate => candidate.protocol

theorem restores (made : Service task cache) :
    Inquiry.Preservation.Restoration.Accepts task cache.programme made.programme := by
  cases made with
  | unavailable step generated => simpa only [programme,generated] using Inquiry.Preservation.Restoration.stage task cache
  | completed step generated _ _ outcome _ =>
      have charged := Inquiry.Preservation.Restoration.stage task cache
      cases outcome with
      | blocked => simpa only [programme,generated] using charged
      | selected candidate =>
          exact Inquiry.Preservation.Restoration.trans task (by simpa only [generated] using charged) candidate.fullAccepted


  | worldShort step generated _ _ _ _ _ _ _ =>
      simpa only [programme,generated] using Inquiry.Preservation.Restoration.stage task cache
  | worldCompleted step generated _ _ _ _ _ _ _ selected =>
      have charged := Inquiry.Preservation.Restoration.stage task cache
      cases found : (World.Selection.candidate? task selected) with
      | none => simpa only [programme,found,generated] using charged
      | some candidate =>
          simpa only [programme,found] using Inquiry.Preservation.Restoration.trans task
            (by simpa only [generated] using charged) candidate.fullAccepted

/-- No unpaid service branch invokes the full-policy compiler. -/
private def PaidContract : Service task cache → Prop
  | .unavailable step _ _ => step.ready = none
  | .completed step _ _ _ outcome _ =>
      Charge.paid task.quote task.model task.reader (Planning.current task cache) task.rival
        (Charge.endAt task.quote task.model task.reader (Planning.current task cache) task.rival) ∧
      (∃ bill, step.accounting = some bill ∧ bill.Released) ∧
      match outcome with
      | .selected candidate => Selection.Restoration.verify (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.programme candidate.protocol = true ∧
          (∀ rival : Opponent task.model.source.code,
            Window.Whole.Restoration.actualTensor (tariff := task.recoveryPricing) task.model task.point.point task.original
              (Prefix.Runtime.normalized task.point.point candidate.protocol) rival =
            Window.Whole.Restoration.actualTensor (tariff := task.recoveryPricing) task.model task.point.point task.original candidate.protocol rival) ∧
          (Splice.install (Planning.current task step.path.finish).point task.rival
            (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol)).source.input =
            (Window.Whole.source task.point.point task.original
              (Prefix.Runtime.normalized task.point.point candidate.protocol) task.rival).input
      | .blocked rejected => ∀ tail,Prefix.Global.reviewFailure (tariff := task.recoveryPricing) (requested := task.futureRequests)
          (Prefix.Global.proposal task.model task.domain step.path.finish.past tail) (rejected tail) = true


  | .worldShort step _ _ _ _ _ _ _ _ =>
      Charge.paid task.quote task.model task.reader (Planning.current task cache) task.rival
        (Charge.endAt task.quote task.model task.reader (Planning.current task cache) task.rival) ∧
      (∃ bill, step.accounting = some bill ∧ bill.Released)
  | .worldCompleted step _ _ _ input _ rate _ covered selected =>
      Charge.paid task.quote task.model task.reader (Planning.current task cache) task.rival
        (Charge.endAt task.quote task.model task.reader (Planning.current task cache) task.rival) ∧
      (∃ bill, step.accounting = some bill ∧ bill.Released) ∧
      Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits task + World.units task input) ∧
      World.Selection.Reviewed task selected

def Contract (made : Service task cache) : Prop :=
  Inquiry.Preservation.Restoration.Accepts task cache.programme made.programme ∧ made.PaidContract

theorem contract (made : Service task cache) : made.Contract := by
  refine ⟨made.restores,?_⟩
  cases made with
  | unavailable step _ missing => exact missing
  | completed step _ permit paid outcome _ =>
      refine ⟨step.charged (by rw [paid];rfl),step.accounted (by rw [paid];rfl),?_⟩
      cases outcome with
      | selected candidate => exact ⟨candidate.verified,selected_normalization_preserves_every_complete_future step candidate,selected_is_the_entire_original_source step permit candidate⟩
      | blocked rejected => exact fun tail => Prefix.Global.every_failure_is_independently_replayable (tariff := task.recoveryPricing) (requested := task.futureRequests) _ (rejected tail)


  | worldShort step _ _ paid _ _ _ _ _ =>
      exact ⟨step.charged (by rw [paid];rfl),step.accounted (by rw [paid];rfl)⟩
  | worldCompleted step _ _ paid _ _ _ _ covered selected =>
      exact ⟨step.charged (by rw [paid];rfl),step.accounted (by rw [paid];rfl),covered,
        World.Selection.reviewed task selected⟩

theorem complete_paid_prefix (made : Service task cache) (visit : Nat) (earlier : visit ≤ arrival made.paidCurrent) :
    Native.Coupling.Match task.model.source.code made.paidCurrent.source.input made.full.source.input
      (Financial.accountAt made.paidCurrent.source.input visit) (Financial.accountAt made.full.source.input visit) := by
  cases made with
  | unavailable step _ _ =>
      exact Native.Coupling.History.complete_accounts task.model.source.code _ _ rfl rfl visit
        (fun _ _ => rfl) _ _ rfl rfl visit (Nat.le_refl _)
  | completed step _ _ _ outcome _ =>
      cases outcome with
      | blocked =>
          exact Native.Coupling.History.complete_accounts task.model.source.code _ _ rfl rfl visit
            (fun _ _ => rfl) _ _ rfl rfl visit (Nat.le_refl _)
      | selected candidate =>
          exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := task.model) _ task.rival _ visit earlier


  | worldShort step _ _ _ _ _ _ _ _ =>
      exact Native.Coupling.History.complete_accounts task.model.source.code _ _ rfl rfl visit
        (fun _ _ => rfl) _ _ rfl rfl visit (Nat.le_refl _)
  | worldCompleted step _ _ _ _ _ _ _ _ selected =>
      cases found : (World.Selection.candidate? task selected) with
      | none =>
          simp only [paidCurrent,full]
          rw [found]
          exact Native.Coupling.History.complete_accounts task.model.source.code
            (Planning.current task step.path.finish).point.source.input
            (Planning.current task step.path.finish).point.source.input rfl rfl visit
            (fun _ _ => rfl) _ _ rfl rfl visit (Nat.le_refl _)
      | some candidate =>
          simp only [paidCurrent,full]
          rw [found]
          exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix
            (model := task.model) (Planning.current task step.path.finish).point task.rival
            (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol)
            visit earlier

theorem the_actual_native_root_consumes_the_paid_global_policy_and_its_own_next (made : Service task cache) :
    let active := made.activated
    made.Contract ∧
    HEq (made.facade.readoutAt active .responsibilities)
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor active.state) := by
  have rooted := made.facade.readoutAt_factorizes made.activated .responsibilities
  exact ⟨made.contract,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end Service

inductive Output where
  | rejected (row : Selection.Rejection task.model task.domain task.original task.baseline task.baseline)
  | generated (cache : Inquiry.Frame task) (outcome : Service task cache)

def produce : Output task := match Owned.Source.seed task with
  | .rejected row => .rejected row
  | .accepted cache _ _ _ => .generated (Inquiry.Frame.pack cache) (invoke task (Inquiry.Frame.pack cache))

namespace Public
variable (request : PublicTask.Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : Cursor (RecallBirth.code request)) (future : Opponent (RecallBirth.code request)) (localRounds : Nat)

abbrev Prior := Local.Output (RecallBirth.born request) quotas point future localRounds

def Follow : Prior request quotas point future localRounds → Type
  | .inherited _ => Unit
  | .installed fits _ _ choice _ actual _ =>
      let task := PublicTask.Feedback.task (RecallBirth.born request) _ fits quotas point future choice
      Service task (Inquiry.Frame.pack actual.1)

def follow (prior : Prior request quotas point future localRounds) : Follow request quotas point future localRounds prior :=
  match prior with
  | .inherited _ => ()
  | .installed fits _ _ choice _ actual _ =>
      let task := PublicTask.Feedback.task (RecallBirth.born request) _ fits quotas point future choice
      invoke task (Inquiry.Frame.pack actual.1)

def produce :=
  let prior := Local.produce (RecallBirth.born request) quotas point future localRounds
  Sigma.mk prior (follow request quotas point future localRounds prior)

def Contract (prior : Prior request quotas point future localRounds)
    (next : Follow request quotas point future localRounds prior) : Prop :=
  match prior,next with
  | .inherited _,_ => True
  | .installed _ _ _ _ _ _ _,next => next.Contract

theorem every_legal_public_history_generates_a_paid_global_policy_or_its_exact_obstruction
    (origin : Distributed.Recall.Information.Origin (RecallBirth.native request))
    (stages : List (EventHistory.Stage (code := RecallBirth.code request)))
    (installed : stages.map Prod.fst = (RecallBirth.born request).installed) :
    let point := EventHistory.execute (EventHistory.ofOrigin (RecallBirth.native request) request.budget origin) stages
    let made := produce request quotas point future localRounds
    made.1.Sound ∧ Contract request quotas point future localRounds made.1 made.2 := by
  refine ⟨Local.all_public_histories_generate_actual_local_installation
    (RecallBirth.born request) quotas future localRounds origin stages installed,?_⟩
  have good (point : Cursor (RecallBirth.code request)) (prior : Prior request quotas point future localRounds) :
      Contract request quotas point future localRounds prior (follow request quotas point future localRounds prior) := by
    cases prior with
    | inherited => trivial
    | installed => exact Service.contract _
  exact good _ _
end Public

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy
