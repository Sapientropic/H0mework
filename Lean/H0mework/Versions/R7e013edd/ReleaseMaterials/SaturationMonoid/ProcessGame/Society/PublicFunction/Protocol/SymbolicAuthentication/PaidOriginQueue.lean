import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidInvocationSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryDeadline

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueue
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (origin : Cursor old) (past : List (EventHistory.Stage (code := old)))

abbrev saved := EventHistory.execute origin past
abbrev code := PaidInvocationSource.code old contract
abbrev lifted := CatalogueHandoffSource.cursor old (PaidInvocationSource.catalogue old contract) origin
abbrev paid (enabled accept : Bool) := PaidInvocationSource.paid old contract (saved old origin past) enabled accept

structure Ready (enabled accept : Bool) where
 private mk ::
 original : origin.side = .original
 accepted : PaidInvocationSource.admitted old contract (saved old origin past) enabled accept = true

inductive Obstruction where
 | replacedOrigin | unpaid
 deriving DecidableEq
inductive Plan (enabled accept : Bool) where
 | blocked (reason : Obstruction)
 | ready (answer : Ready old contract origin past enabled accept)

def plan (enabled accept : Bool) : Plan old contract origin past enabled accept :=
 match original : origin.side with
 | .original =>
  if accepted : PaidInvocationSource.admitted old contract (saved old origin past) enabled accept = true then
   .ready ⟨original,accepted⟩ else .blocked .unpaid
 | .replacement => .blocked .replacedOrigin

theorem fromPayment {enabled accept : Bool} (original : origin.side = .original)
 (accepted : PaidInvocationSource.admitted old contract (saved old origin past) enabled accept = true) :
 Ready old contract origin past enabled accept := ⟨original,accepted⟩

variable {old contract origin past} {enabled accept : Bool}
theorem ready_was_generated_by_the_actual_source_check
 (answer : Ready old contract origin past enabled accept) :
 plan old contract origin past enabled accept = .ready answer := by
 unfold plan
 split
 · simp only [answer.accepted,dif_pos]
 · rename_i replaced
   have impossible : Side.original = Side.replacement := answer.original.symm.trans replaced
   cases impossible

private theorem execute_side (start : Cursor old) (stages : List (EventHistory.Stage (code := old))) :
 (EventHistory.execute start stages).side = start.side := by
 induction stages generalizing start with
 | nil => rfl
 | cons stage tail ih => exact ih (start.after stage.1 stage.2)

abbrev Ready.account (answer : Ready old contract origin past enabled accept) :=
 PaidInvocationSource.opened old contract (saved old origin past) enabled accept answer.accepted
abbrev Ready.start (answer : Ready old contract origin past enabled accept) := answer.account.point
abbrev Ready.required (answer : Ready old contract origin past enabled accept) :=
 OriginQueue.horizon (lifted old contract origin) answer.start
abbrev Ready.count (answer : Ready old contract origin past enabled accept) :=
 min answer.required (EventStep.seed answer.start).remaining
abbrev Ready.complete (answer : Ready old contract origin past enabled accept) : Bool :=
 decide (answer.required ≤ (EventStep.seed answer.start).remaining)
abbrev Ready.protocols (_ : Ready old contract origin past enabled accept) (_ : Nat) : Rule (code old contract) := SilentWindow.quiet
abbrev Ready.stages (answer : Ready old contract origin past enabled accept) :=
 OriginQueue.stages (lifted old contract origin) answer.protocols answer.count
abbrev Ready.final (answer : Ready old contract origin past enabled accept) :=
 EventHistory.execute answer.start answer.stages
abbrev Ready.row (answer : Ready old contract origin past enabled accept) :=
 OriginQueue.row (lifted old contract origin) answer.start answer.protocols

theorem Ready.is_the_original_paid_opening (answer : Ready old contract origin past enabled accept) :
 PaidInvocationSource.produce old contract (saved old origin past) enabled accept = .opened answer.account :=
 PaidInvocationSource.actual_admission_generates_the_paid_window old contract _ enabled accept answer.accepted

theorem Ready.opening_keeps_the_original_memory_and_budget (answer : Ready old contract origin past enabled accept) :
 (EventStep.seed answer.start).past = (EventStep.seed (paid old contract origin past enabled accept)).past ∧
 (EventStep.seed answer.start).frame = (EventStep.seed (paid old contract origin past enabled accept)).frame ∧
 (EventStep.seed answer.start).remaining =
  (EventStep.seed (paid old contract origin past enabled accept)).remaining + contract.steps := by
 rw [PaidInvocationSource.paid_opening_preserves_the_entire_actual_endpoint old contract _ enabled accept answer.accepted]
 exact ⟨rfl,rfl,rfl⟩

theorem Ready.original_baseline (answer : Ready old contract origin past enabled accept) :
 OriginQueue.baseline (lifted old contract origin) = OriginQueue.baseline origin := by
 have seed := CatalogueHandoffSource.seed old (PaidInvocationSource.catalogue old contract) origin answer.original
 exact congrArg (fun state => state.past.length) seed

theorem Ready.fits (answer : Ready old contract origin past enabled accept) :
 OriginQueue.baseline (lifted old contract origin) ≤ (EventStep.seed answer.start).past.length := by
 rw [answer.original_baseline,answer.opening_keeps_the_original_memory_and_budget.1]
 have before := OriginQueue.an_actual_prefix_retains_the_original_baseline origin past
 have side : (saved old origin past).side = .original := (execute_side origin past).trans answer.original
 have migrated := CatalogueHandoffSource.seed old (PaidInvocationSource.catalogue old contract) (saved old origin past) side
 have preserved := OriginQueue.an_actual_prefix_retains_the_original_baseline
  (PaidInvocationSource.start old contract (saved old origin past)) (PaidInvocationSource.stages old contract enabled accept)
 have startPast : (EventStep.seed (PaidInvocationSource.start old contract (saved old origin past))).past =
   (EventStep.seed (saved old origin past)).past := congrArg (fun state => state.past) migrated
 rw [startPast] at preserved
 exact (before.trans preserved).length_le

theorem Ready.actual_history_and_fuel (answer : Ready old contract origin past enabled accept) :
 (EventStep.seed answer.start).past <+: (EventStep.seed answer.final).past ∧
 (EventStep.seed answer.final).remaining = (EventStep.seed answer.start).remaining-answer.count := by
 unfold Ready.final Ready.stages
 rw [OriginQueue.executed_stages_are_the_actual_cursor]
 exact ⟨(OriginQueue.memory_and_queue_extend (lifted old contract origin) answer.start answer.protocols 0 answer.count (Nat.zero_le _)).1,
  (OriginQueue.clocks_and_roster (lifted old contract origin) answer.start answer.protocols answer.count).2.1⟩

theorem Ready.complete_generates_every_original_pending_delivery
 (answer : Ready old contract origin past enabled accept) (complete : answer.complete = true)
 (serial : Nat) (present : serial < (EventStep.seed answer.start).frame.sent.length)
 (pending : serial ∈ QueueScheduler.untried (code old contract) (OriginQueue.baseline origin)
  (EventStep.seed answer.start).past) :
 ∃ index, index < answer.count ∧
  (StageTrace.records answer.start answer.stages)[index]? = some (answer.row index) ∧
  StageReception.delivered (answer.row index) serial = true := by
 have enough := of_decide_eq_true complete
 have count : answer.count = answer.required := Nat.min_eq_left enough
 rw [← answer.original_baseline] at pending
 obtain ⟨index,bounded,delivered⟩ := OriginQueue.the_source_window_generates_an_actual_delivery_attempt
  (lifted old contract origin) answer.start answer.protocols answer.fits serial enough present pending
 refine ⟨index,by simpa only [count] using bounded,?_,delivered⟩
 exact OriginQueue.row_at_its_actual_index _ _ _ _ _ (by simpa only [count] using bounded)

theorem Ready.already_attempted_packets_are_never_replayed
 (answer : Ready old contract origin past enabled accept) (serial index : Nat)
 (attempted : serial ∈ QueueScheduler.attempted (code old contract) (OriginQueue.baseline origin)
  (EventStep.seed answer.start).past) : StageReception.delivered (answer.row index) serial = false := by
 have previous : serial ∈ QueueScheduler.attempted (code old contract)
   (OriginQueue.baseline (lifted old contract origin))
   (OriginQueue.state (lifted old contract origin) answer.start answer.protocols index).past := by
  apply (OriginQueue.attempted_memory_is_the_actual_stage_delivery_history
   (lifted old contract origin) answer.start answer.protocols answer.fits index serial).mpr
  exact Or.inl (by rw [answer.original_baseline]; exact attempted)
 unfold StageReception.delivered StageTransport.admission Ready.row OriginQueue.row
 dsimp only [StageTrace.material]
 dsimp only [OriginQueue.state] at previous
 generalize current : OriginQueue.cursorAt (lifted old contract origin) answer.start answer.protocols index = here at *
 dsimp only [Ready.protocols]
 by_cases stopped : (EventStep.seed here).remaining = 0
 · simp only [StageTrace.capture, stopped, if_true, ControlExecution.admitted]
 · simp only [StageTrace.capture, stopped, if_false]
   cases own : Distributed.Recall.Information.Agency.ownerAt (code old contract) here.ownerStart
     (EventStep.seed here).history.length with
   | some site => simp only [ControlExecution.admitted, localEvent, SilentWindow.quiet]
   | none =>
     cases chosen : OriginQueue.environment (lifted old contract origin) (EventStep.seed here).history
       (EventStep.seed here).past (EventStep.seed here).frame with
     | none => rfl
     | some event =>
       obtain ⟨address,kind,_,fresh⟩ := QueueScheduler.generated_move_has_actual_queue_and_fresh_address
        (code old contract) (OriginQueue.baseline (lifted old contract origin)) _ _ _ event chosen
       have different : address ≠ serial := by
        intro same
        subst address
        exact (Finset.mem_sdiff.mp fresh).2 previous
       simp only [ControlExecution.admitted, Distributed.Recall.Information.Agency.externalChoice, kind]
       exact beq_eq_false_iff_ne.mpr different

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueue
