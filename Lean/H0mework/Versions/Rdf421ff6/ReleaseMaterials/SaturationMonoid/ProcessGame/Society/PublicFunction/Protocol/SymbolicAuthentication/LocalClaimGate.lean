import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CausalClaim

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalClaimGate

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev native (cursor : Cursor model.source.code) := LocalContentRuntime.native model cursor
abbrev sourceIndex (cursor : Cursor model.source.code) := Native.Authority.sourceIndex (native model cursor)
def completed (cursor : Cursor model.source.code) :=
  CausalClaim.trace (Native.Authority.programme model) (sourceIndex model cursor) (EventStep.boundary cursor)
def pending (cursor : Cursor model.source.code) (worker : Fin model.source.code.sites) :=
  CausalClaim.ownPending (base := model.base) (scope := model.scope) (completed model cursor) (model.source.code.siteParty worker)

theorem the_gate_consumes_exactly_the_completed_original_native_inventory
    (cursor : Cursor model.source.code) (worker : Fin model.source.code.sites) :
    pending model cursor worker =
      (Mandate.Challenge.recordsAt (Native.Authority.programme model) (sourceIndex model cursor)
        (EventStep.boundary cursor)).any (fun row =>
          row.1.signer (Native.Authority.programme model) (sourceIndex model cursor) == model.source.code.siteParty worker &&
          row.2.isPending (Native.Authority.programme model) (sourceIndex model cursor)) :=
  CausalClaim.own_pending_consumes_every_original_and_newborn_native_claim _ _ _ _

theorem matched_completed_sources_have_the_same_pending
    (left right : Cursor model.source.code) (same : EventStep.Matches left right)
    (worker : Fin model.source.code.sites) : pending model left worker = pending model right worker := by
  have boundary : EventStep.boundary left = EventStep.boundary right := by
    simp only [EventStep.boundary, same.history_length, same.cut]
  unfold pending completed
  rw [boundary]
  apply congrArg (fun events => CausalClaim.ownPending (base := model.base) (scope := model.scope) events _)
  apply CausalClaim.the_view_depends_only_on_the_completed_actual_items
  intro ordinal inside
  change model.source.code.law.rawItems (left.source.currentAt ordinal)
      (ProgrammeSource.rawEvent left.source.input (ProgrammeHistory.visitAt left.source.input ordinal).current) =
    model.source.code.law.rawItems (right.source.currentAt ordinal)
      (ProgrammeSource.rawEvent right.source.input (ProgrammeHistory.visitAt right.source.input ordinal).current)
  rw [same.currents ordinal (Nat.le_of_lt inside), same.words ordinal inside]

variable (start : Cursor model.source.code) (installed : List (Rule model.source.code))
  (worker : Fin model.source.code.sites) (signal : Fin model.source.code.signals)

inductive Query where
  | unseen (empty : LocalWithdrawal.fibre model start installed worker signal = [])
  | known (value : Bool) (first : Cursor model.source.code)
      (actual : first ∈ LocalWithdrawal.fibre model start installed worker signal)
      (exact : pending model first worker = value)
      (uniform : ∀ other ∈ LocalWithdrawal.fibre model start installed worker signal, pending model other worker = value)
  | ambiguous (first second : Cursor model.source.code)
      (left : first ∈ LocalWithdrawal.fibre model start installed worker signal)
      (right : second ∈ LocalWithdrawal.fibre model start installed worker signal)
      (different : pending model second worker ≠ pending model first worker)

def query : Query model start installed worker signal :=
  match selected : LocalWithdrawal.fibre model start installed worker signal with
  | [] => .unseen selected
  | first :: rest =>
    match inspect (fun other => pending model other worker = pending model first worker) rest with
    | .accepted uniform => .known (pending model first worker) first
        (by rw [selected]; exact List.mem_cons_self) rfl (by
          intro other member
          rw [selected] at member
          rcases List.mem_cons.mp member with same | later
          · exact same ▸ rfl
          · exact uniform other later)
    | .rejected other member different => .ambiguous first other
        (by rw [selected]; exact List.mem_cons_self)
        (by rw [selected]; exact List.mem_cons_of_mem _ member) different

def answer : Query model start installed worker signal → Option Bool
  | .known value .. => some value
  | _ => none

theorem the_generated_local_answer_recovers_the_actual_completed_responsibility
    (past : List (EventHistory.Stage (code := model.source.code))) (value : Bool)
    (prepared : answer model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker)
      (query model start (past.map Prod.fst) worker (LocalWithdrawal.reading model (EventHistory.execute start past) worker)) = some value) :
    pending model (EventHistory.execute start past) worker = value := by
  obtain ⟨representative, inside, same⟩ := LocalWithdrawal.every_adaptive_actual_prefix_has_a_compatible_representative model start worker past
  cases selected : query model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) with
  | unseen empty => simp only [selected, answer] at prepared; contradiction
  | ambiguous first second left right different => simp only [selected, answer] at prepared; contradiction
  | known candidate first actual precise uniform =>
    simp only [selected, answer, Option.some.injEq] at prepared
    exact (matched_completed_sources_have_the_same_pending model representative _ same worker).symm.trans ((uniform _ inside).trans prepared)

def work := if answer model start installed worker signal (query model start installed worker signal) = some true
  then WithdrawalInquiry.work model start installed worker signal else []

theorem supported : work model start installed worker signal ∈ words model.source.code.actions model.source.code.actionLimit := by
  unfold work
  split
  · exact WithdrawalInquiry.work_supported model start installed worker signal
  · exact (mem_words_iff _ _ _).mpr (by simp)

def event : LocalMove model.source.code worker :=
  match query model start installed worker signal with
  | .known true .. => WithdrawalInquiry.event model start installed worker signal
  | .ambiguous .. => (WithdrawalInquiry.reads model worker).headD (WithdrawalInquiry.waiting model worker)
  | _ => WithdrawalInquiry.waiting model worker

def policy : model.source.code.Policy := fun key _ => work model start installed key.1 key.2
theorem policy_generated : policy model start installed ∈ model.source.code.policies := by
  apply model.source.code.every_local_policy_is_enumerated
  intro key inside
  exact supported model start installed key.1 key.2

def protocol : Rule model.source.code where
  work := ⟨policy model start installed, policy_generated model start installed⟩
  events := fun key _ => event model start installed key.1 key.2

theorem a_locally_closed_site_does_not_create_another_claim
    (known : answer model start installed worker signal (query model start installed worker signal) = some false) :
    work model start installed worker signal = [] ∧
      localEvent model.source.code (protocol model start installed) worker signal = none := by
  refine ⟨by simp [work, known], ?_⟩
  change (event model start installed worker signal).val = none
  cases selected : query model start installed worker signal <;> simp_all [answer, event, WithdrawalInquiry.waiting]

theorem every_nonempty_local_work_has_its_own_actual_pending_responsibility
    (past : List (EventHistory.Stage (code := model.source.code)))
    (nonempty : work model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) ≠ []) :
    pending model (EventHistory.execute start past) worker = true := by
  unfold work at nonempty
  split at nonempty
  · rename_i required
    exact the_generated_local_answer_recovers_the_actual_completed_responsibility model start worker past true required
  · contradiction

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalClaimGate
