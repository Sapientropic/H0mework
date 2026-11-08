import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningReplay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage FreshSigningReplay

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}

structure Request where
 enabled : Bool
 accept : Bool
 scope : Scope
 value : Bool
 beats : Nat
 depth : Nat
 work : List (Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument)

variable (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (before : JointReceptionSource.State root)
 (request : Request (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

abbrev policy := RecursiveSigningSource.normalPolicy before.actual.model (EventStep.seed before.actual.point).frame.sent.length base (laws before.actual.model) request.work
abbrev generated := RecursiveSigningSource.dynamic before.actual.model before.actual.point (policy base laws before request) request.beats
abbrev inputs := (generated base laws before request).inputs
abbrev origin := FreshSigningReplay.origin before (inputs base laws before request)
abbrev result := FreshSigningReplay.report contract before (inputs base laws before request) base (laws before.actual.model)
 request.scope request.value request.depth

def next : JointReceptionSource.State root :=
 FreshSigningReplay.next contract before (inputs base laws before request) base (laws before.actual.model)
  request.scope request.value request.depth

theorem the_source_policy_uses_only_the_actual_registered_interface
 (actual : LocalCommandRun.State before.actual.model before.actual.point) :
 policy base laws before request before.actual.point actual∈CommandWindowSource.menu before.actual.model :=
 RecursiveSigningSource.normal_policy_uses_the_original_registered_interface before.actual.model (EventStep.seed before.actual.point).frame.sent.length
  base (laws before.actual.model) request.work before.actual.point actual

theorem generated_inputs_are_exactly_the_actual_dynamic_execution :
 LocalCommandRun.run before.actual.model before.actual.point (inputs base laws before request)=generated base laws before request ∧
 (inputs base laws before request).length=request.beats :=
 ⟨RecursiveSigningSource.dynamic_inputs_replay_the_same_actual_execution before.actual.model before.actual.point
   (policy base laws before request) request.beats,
  RecursiveSigningSource.dynamic_control_retains_exactly_its_requested_attempts before.actual.model before.actual.point
   (policy base laws before request) request.beats⟩

theorem every_new_context_is_the_real_requested_predecessor :
 (origin base laws before request).origin=before.actual.point ∧
 (origin base laws before request).stages=(generated base laws before request).stages := by
 refine ⟨rfl,?_⟩
 change (LocalCommandRun.run before.actual.model before.actual.point (inputs base laws before request)).stages=_
 rw [(generated_inputs_are_exactly_the_actual_dynamic_execution base laws before request).1]

theorem the_next_global_state_and_the_fresh_report_are_the_same_complete_physical_occurrence :
 physical (next contract base laws before request).actual=physical (result contract base laws before request).final.actual :=
 the_generated_repair_is_replayed_on_the_original_global_successor contract before (inputs base laws before request)
  base (laws before.actual.model) request.scope request.value request.depth

theorem every_round_retains_all_original_archives_windows_and_rows :
 before.actual.archive <+: (next contract base laws before request).actual.archive ∧
 before.actual.windows <+: (next contract base laws before request).actual.windows ∧
 before.rows <+: (next contract base laws before request).rows := by
 have first := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract before
  [.execute (inputs base laws before request)]
 have later := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract
  (FreshSigningReplay.globalStart contract before (inputs base laws before request))
  (result contract base laws before request).commands
 exact ⟨first.1.trans later.1,first.2.1.trans later.2.1,first.2.2.trans later.2.2⟩

theorem every_round_is_completed_or_has_its_real_bounded_block :
 (result contract base laws before request).status=.complete ∨
 (result contract base laws before request).status=.blocked :=
 SourceRepairRun.the_producer_always_completes_or_returns_its_exact_bounded_obstruction contract
  ((origin base laws before request).vocabulary before.actual.model base)
  ((origin base laws before request).law before.actual.model (laws before.actual.model))
  (origin base laws before request).origin (origin base laws before request).stages
  (currentScope before request.scope) request.value request.depth
  (FreshSigningReplay.localStart before (inputs base laws before request))

inductive Status where
 | received | missingSource | blocked
 deriving DecidableEq

def status : Status :=
 if (JointReceptionSource.targets ((origin base laws before request).vocabulary before.actual.model base)
  (origin base laws before request).origin (origin base laws before request).stages
  (FreshSigningReplay.currentScope before request.scope) request.value).card=0 then .missingSource
 else match (result contract base laws before request).status with
 | .complete => .received
 | .blocked | .exhausted => .blocked

-- Each cycle first makes the original paid invocation attempt on the actual state.
def prepared : JointReceptionSource.State root :=
 JointReceptionSource.advance contract before (.renew request.enabled request.accept)

def cycle : JointReceptionSource.State root :=
 next contract base laws (prepared contract before request) request

def cycleStatus : Status := status contract base laws (prepared contract before request) request

theorem the_real_paid_attempt_is_the_exact_preparation :
 (prepared contract before request).actual=RenewableArchiveSource.renew contract before.actual request.enabled request.accept := rfl

theorem every_paid_cycle_retains_all_original_archives_windows_and_rows :
 before.actual.archive <+: (cycle contract base laws before request).actual.archive ∧
 before.actual.windows <+: (cycle contract base laws before request).actual.windows ∧
 before.rows <+: (cycle contract base laws before request).rows := by
 have prior := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract before
  [.renew request.enabled request.accept]
 have following := every_round_retains_all_original_archives_windows_and_rows contract base laws (prepared contract before request) request
 exact ⟨prior.1.trans following.1,prior.2.1.trans following.2.1,prior.2.2.trans following.2.2⟩

abbrev Controller := (state : JointReceptionSource.State root) →
 Request (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

def run (start : JointReceptionSource.State root) (control : Controller (root := root)) : Nat → JointReceptionSource.State root :=
 Nat.rec start fun _ current => cycle contract base laws current (control current)

theorem all_later_dynamic_rounds_keep_the_original_archive_windows_and_actual_rows
 (start : JointReceptionSource.State root) (control : Controller (root := root)) (count : Nat) :
 start.actual.archive <+: (run contract base laws start control count).actual.archive ∧
 start.actual.windows <+: (run contract base laws start control count).actual.windows ∧
 start.rows <+: (run contract base laws start control count).rows := by
 induction count with
 | zero => exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _⟩
 | succ count ih =>
   have next := every_paid_cycle_retains_all_original_archives_windows_and_rows contract base laws
    (run contract base laws start control count) (control (run contract base laws start control count))
   exact ⟨ih.1.trans next.1,ih.2.1.trans next.2.1,ih.2.2.trans next.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningSource
