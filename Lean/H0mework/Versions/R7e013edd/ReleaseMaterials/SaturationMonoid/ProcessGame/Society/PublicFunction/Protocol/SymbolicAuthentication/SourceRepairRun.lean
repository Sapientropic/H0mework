import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairSearch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairRun
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage SourceRepairSearch

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

inductive Status where
 | complete | blocked | exhausted
 deriving DecidableEq

structure Report (root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) where
 private mk ::
 commands : List RenewableArchiveSource.Command
 final : JointReceptionSource.State root
 status : Status

private theorem path_append (start : JointReceptionSource.State root)
 (first more : List RenewableArchiveSource.Command)
 (one : Path contract start first) (two : Path contract (execute contract start first) more) :
 Path contract start (first++more) := by
 induction first generalizing start with
 | nil => exact two
 | cons command tail ih => exact ⟨one.1,ih _ one.2 two⟩

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law root) (origin : Cursor root) (past : List (EventHistory.Stage (code := root)))
 (scope : Scope) (value : Bool) (depth : Nat)

def step (recur : JointReceptionSource.State root → Report root) (state : JointReceptionSource.State root) : Report root :=
 match SourceRepairSearch.produce contract vocabulary law origin past scope value state depth with
 | .complete _ => ⟨[],state,.complete⟩
 | .blocked _ _ => ⟨[],state,.blocked⟩
 | .repaired branch _ _ =>
   let later := recur branch.final
   ⟨branch.commands++later.commands,later.final,later.status⟩

def run : Nat → JointReceptionSource.State root → Report root :=
 Nat.rec (fun state => ⟨[],state,.exhausted⟩)
  (fun _ recur state => step contract vocabulary law origin past scope value depth recur state)

theorem run_succ (fuel : Nat) (start : JointReceptionSource.State root) :
 run contract vocabulary law origin past scope value depth (fuel+1) start=
 step contract vocabulary law origin past scope value depth
  (run contract vocabulary law origin past scope value depth fuel) start := rfl

theorem every_report_replays_only_its_selected_actual_source_commands
 (fuel : Nat) (start : JointReceptionSource.State root) :
 execute contract start (run contract vocabulary law origin past scope value depth fuel start).commands=
  (run contract vocabulary law origin past scope value depth fuel start).final ∧
 Path contract start (run contract vocabulary law origin past scope value depth fuel start).commands ∧
 (run contract vocabulary law origin past scope value depth fuel start).commands.length≤fuel*depth := by
 induction fuel generalizing start with
 | zero => exact ⟨rfl,trivial,Nat.zero_le _⟩
 | succ fuel ih =>
   rw [run_succ]
   unfold step
   cases chosen : SourceRepairSearch.produce contract vocabulary law origin past scope value start depth with
   | complete cleared => exact ⟨rfl,trivial,Nat.zero_le _⟩
   | blocked unresolved exhausted => exact ⟨rfl,trivial,Nat.zero_le _⟩
   | repaired branch generated progress =>
     obtain ⟨actual,path,bounded⟩ := every_generated_branch_replays_the_exact_original_commands contract depth start branch generated
     obtain ⟨later,more,count⟩ := ih branch.final
     dsimp only
     refine ⟨?_,?_,?_⟩
     · change (branch.commands++_).foldl _ start=_
       rw [List.foldl_append]
       change execute contract (execute contract start branch.commands) _=_
       rw [actual]
       exact later
     · exact path_append contract start _ _ path (actual.symm ▸ more)
     · simp only [List.length_append,Nat.add_mul,Nat.one_mul]
       omega

theorem every_completed_report_has_no_unreceived_original_target
 (fuel : Nat) (start : JointReceptionSource.State root)
 (complete : (run contract vocabulary law origin past scope value depth fuel start).status=.complete) :
 debt vocabulary law origin past scope value (run contract vocabulary law origin past scope value depth fuel start).final=0 := by
 induction fuel generalizing start with
 | zero => cases complete
 | succ fuel ih =>
   rw [run_succ] at complete ⊢
   unfold step at complete ⊢
   cases chosen : SourceRepairSearch.produce contract vocabulary law origin past scope value start depth with
   | complete cleared => exact cleared
   | blocked unresolved exhausted => simp only [chosen] at complete;contradiction
   | repaired branch generated progress =>
     simp only [chosen] at complete ⊢
     exact ih branch.final complete

theorem every_blocked_report_has_the_actual_unresolved_bounded_obstruction
 (fuel : Nat) (start : JointReceptionSource.State root)
 (blocked : (run contract vocabulary law origin past scope value depth fuel start).status=.blocked) :
 0<debt vocabulary law origin past scope value (run contract vocabulary law origin past scope value depth fuel start).final ∧
 ∀ commands, Path contract (run contract vocabulary law origin past scope value depth fuel start).final commands → commands.length≤depth →
 debt vocabulary law origin past scope value (run contract vocabulary law origin past scope value depth fuel start).final ≤
 debt vocabulary law origin past scope value
  (execute contract (run contract vocabulary law origin past scope value depth fuel start).final commands) := by
 induction fuel generalizing start with
 | zero => cases blocked
 | succ fuel ih =>
   rw [run_succ] at blocked ⊢
   unfold step at blocked ⊢
   cases chosen : SourceRepairSearch.produce contract vocabulary law origin past scope value start depth with
   | complete cleared => simp only [chosen] at blocked;contradiction
   | blocked unresolved exhausted =>
     exact ⟨unresolved,fun commands path bounded =>
      a_computed_block_excludes_every_bounded_original_repair contract vocabulary law origin past scope value start depth exhausted commands path bounded⟩
   | repaired branch generated progress =>
     simp only [chosen] at blocked ⊢
     exact ih branch.final blocked

theorem original_delivery_debt_bounds_all_recursive_search_rounds
 (fuel : Nat) (start : JointReceptionSource.State root)
 (enough : debt vocabulary law origin past scope value start<fuel) :
 (run contract vocabulary law origin past scope value depth fuel start).status≠.exhausted := by
 induction fuel generalizing start with
 | zero => omega
 | succ fuel ih =>
   rw [run_succ]
   unfold step
   cases chosen : SourceRepairSearch.produce contract vocabulary law origin past scope value start depth with
   | complete cleared => intro bad;cases bad
   | blocked unresolved exhausted => intro bad;cases bad
   | repaired branch generated progress =>
     have strict := of_decide_eq_true progress
     exact ih branch.final (by omega)

def produce (start : JointReceptionSource.State root) : Report root :=
 run contract vocabulary law origin past scope value depth (debt vocabulary law origin past scope value start+1) start

theorem the_producer_always_completes_or_returns_its_exact_bounded_obstruction
 (start : JointReceptionSource.State root) :
 (produce contract vocabulary law origin past scope value depth start).status=.complete ∨
 (produce contract vocabulary law origin past scope value depth start).status=.blocked := by
 have finite := original_delivery_debt_bounds_all_recursive_search_rounds contract vocabulary law origin past scope value depth
  (debt vocabulary law origin past scope value start+1) start (by omega)
 cases status : (produce contract vocabulary law origin past scope value depth start).status with
 | complete => exact Or.inl rfl
 | blocked => exact Or.inr rfl
 | exhausted => exact False.elim (finite status)

theorem replay_keeps_the_original_archives_windows_and_actual_rows
 (start : JointReceptionSource.State root) (commands : List RenewableArchiveSource.Command) :
 start.actual.archive <+: (execute contract start commands).actual.archive ∧
 start.actual.windows <+: (execute contract start commands).actual.windows ∧
 start.rows <+: (execute contract start commands).rows := by
 induction commands generalizing start with
 | nil => exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _⟩
 | cons command tail ih =>
   have kept := RenewableArchiveSource.every_actual_command_keeps_all_original_issuing_contexts contract start.actual command
   rw [← JointReceptionSource.advance_is_the_original_actual_command contract start command] at kept
   obtain ⟨archives,windows,rows⟩ := ih (JointReceptionSource.advance contract start command)
   have actualRows : start.rows <+: (JointReceptionSource.advance contract start command).rows := by
    rw [JointReceptionSource.advance_appends_only_actual_rows]
    exact List.prefix_append _ _
   exact ⟨kept.1.trans archives,kept.2.trans windows,actualRows.trans rows⟩

theorem every_final_report_retains_its_original_source_history
 (start : JointReceptionSource.State root) :
 start.actual.archive <+: (produce contract vocabulary law origin past scope value depth start).final.actual.archive ∧
 start.actual.windows <+: (produce contract vocabulary law origin past scope value depth start).final.actual.windows ∧
 start.rows <+: (produce contract vocabulary law origin past scope value depth start).final.rows := by
 have replay := (every_report_replays_only_its_selected_actual_source_commands contract vocabulary law origin past scope value depth
  (debt vocabulary law origin past scope value start+1) start).1
 have retained := replay_keeps_the_original_archives_windows_and_actual_rows contract start
  (produce contract vocabulary law origin past scope value depth start).commands
 rw [show execute contract start (produce contract vocabulary law origin past scope value depth start).commands=
  (produce contract vocabulary law origin past scope value depth start).final from replay] at retained
 exact retained

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairRun
