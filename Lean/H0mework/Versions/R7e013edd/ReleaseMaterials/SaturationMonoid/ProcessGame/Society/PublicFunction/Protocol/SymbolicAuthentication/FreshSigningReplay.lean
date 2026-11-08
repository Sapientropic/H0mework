import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairArchive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningReplay
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
abbrev Model := Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)
abbrev Physical := (model : Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) × Cursor model.source.code

variable (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

def physical (state : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) :
 Physical (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 ⟨state.model,state.point⟩

theorem the_actual_command_depends_only_on_the_complete_model_and_cursor
 (left right : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (same : physical left=physical right) (command : RenewableArchiveSource.Command) :
 physical (RenewableArchiveSource.next contract left command)=physical (RenewableArchiveSource.next contract right command) := by
 cases left
 cases right
 cases same
 cases command <;> rfl

theorem the_same_actual_command_keeps_both_complete_metadata_prefixes
 (left right : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (archives : List (RenewableArchiveSource.Context (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)))
 (windows : List (RenewableArchiveSource.Window (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)))
 (same : physical left=physical right)
 (archive : left.archive=archives++right.archive) (paid : left.windows=windows++right.windows)
 (command : RenewableArchiveSource.Command) :
 (RenewableArchiveSource.next contract left command).archive=
  archives++(RenewableArchiveSource.next contract right command).archive ∧
 (RenewableArchiveSource.next contract left command).windows=
  windows++(RenewableArchiveSource.next contract right command).windows := by
 cases left
 cases right
 cases same
 cases command with
 | execute inputs =>
   exact ⟨by change _++[_]=archives++(_++[_]);rw [archive,List.append_assoc];rfl,paid⟩
 | renew enabled accept =>
   exact ⟨by change _++[_]=archives++(_++[_]);rw [archive,List.append_assoc];rfl,
    by change _++[_]=windows++(_++[_]);rw [paid,List.append_assoc];rfl⟩

variable {old new : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}

theorem replay_keeps_the_same_complete_physical_occurrence
 (left : JointReceptionSource.State old) (right : JointReceptionSource.State new)
 (same : physical left.actual=physical right.actual) (commands : List RenewableArchiveSource.Command) :
 physical (SourceRepairSearch.execute contract left commands).actual=
 physical (SourceRepairSearch.execute contract right commands).actual := by
 induction commands generalizing left right with
 | nil => exact same
 | cons command tail ih =>
   apply ih (JointReceptionSource.advance contract left command) (JointReceptionSource.advance contract right command)
   rw [JointReceptionSource.advance_is_the_original_actual_command,
    JointReceptionSource.advance_is_the_original_actual_command]
   exact the_actual_command_depends_only_on_the_complete_model_and_cursor contract _ _ same command

theorem the_same_actual_occurrence_has_the_same_registered_repair_paths
 (left : JointReceptionSource.State old) (right : JointReceptionSource.State new)
 (same : physical left.actual=physical right.actual) (commands : List RenewableArchiveSource.Command)
 (path : SourceRepairSearch.Path contract right commands) : SourceRepairSearch.Path contract left commands := by
 induction commands generalizing left right with
 | nil => trivial
 | cons command tail ih =>
   have model : left.actual.model=right.actual.model := congrArg Sigma.fst same
   have menu : SourceRepairSearch.menu left=SourceRepairSearch.menu right := by
    simp only [SourceRepairSearch.menu,model]
   refine ⟨menu.symm ▸ path.1,?_⟩
   apply ih (JointReceptionSource.advance contract left command) (JointReceptionSource.advance contract right command) _ path.2
   rw [JointReceptionSource.advance_is_the_original_actual_command,
    JointReceptionSource.advance_is_the_original_actual_command]
   exact the_actual_command_depends_only_on_the_complete_model_and_cursor contract _ _ same command

theorem replay_retains_the_complete_original_metadata_prefixes
 (left : JointReceptionSource.State old) (right : JointReceptionSource.State new)
 (same : physical left.actual=physical right.actual)
 (archives : List (RenewableArchiveSource.Context (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)))
 (windows : List (RenewableArchiveSource.Window (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)))
 (archive : left.actual.archive=archives++right.actual.archive)
 (paid : left.actual.windows=windows++right.actual.windows) (commands : List RenewableArchiveSource.Command) :
 (SourceRepairSearch.execute contract left commands).actual.archive=
  archives++(SourceRepairSearch.execute contract right commands).actual.archive ∧
 (SourceRepairSearch.execute contract left commands).actual.windows=
  windows++(SourceRepairSearch.execute contract right commands).actual.windows := by
 induction commands generalizing left right with
 | nil => exact ⟨archive,paid⟩
 | cons command tail ih =>
   have physical := the_actual_command_depends_only_on_the_complete_model_and_cursor contract left.actual right.actual same command
   have prefixes := the_same_actual_command_keeps_both_complete_metadata_prefixes contract left.actual right.actual archives windows
    same archive paid command
   rw [← JointReceptionSource.advance_is_the_original_actual_command contract left command,
    ← JointReceptionSource.advance_is_the_original_actual_command contract right command] at physical prefixes
   exact ih _ _ physical prefixes.1 prefixes.2

variable (before : JointReceptionSource.State old) (inputs : List LocalCommandSource.Input)

abbrev parent := RecursiveSigningSource.next before.actual.model before.actual.point
 (RecursiveSigningSource.initial before.actual.model before.actual.point) inputs
abbrev origin := RenewableArchiveSource.fresh before.actual inputs
abbrev localStart := JointReceptionSource.initial before.actual.model before.actual.point (parent before inputs)
abbrev globalStart := JointReceptionSource.advance contract before (.execute inputs)

theorem the_new_origin_is_the_actual_predecessor :
 (origin before inputs).origin=before.actual.point := rfl

theorem the_fresh_context_is_generated_in_the_local_archive :
 (parent before inputs).archive=[origin before inputs] := rfl

theorem both_starts_are_the_same_actual_model_and_cursor :
 physical (globalStart contract before inputs).actual=physical (localStart before inputs).actual := rfl

theorem the_global_archive_keeps_the_new_context_and_every_old_context :
 (globalStart contract before inputs).actual.archive=before.actual.archive++
 [RenewableArchiveSource.Context.ofSegment before.actual.model (origin before inputs)] ∧
 (globalStart contract before inputs).actual.windows=before.actual.windows := ⟨rfl,rfl⟩

variable (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law before.actual.model.source.code) (scope : Scope) (value : Bool) (depth : Nat)

def currentScope : Scope := {scope with phase := before.actual.point.cut}

def report : SourceRepairRun.Report before.actual.model.source.code :=
 SourceRepairRun.produce contract ((origin before inputs).vocabulary before.actual.model base)
  ((origin before inputs).law before.actual.model law) (origin before inputs).origin (origin before inputs).stages
  (currentScope before scope) value depth (localStart before inputs)

def next : JointReceptionSource.State old :=
 SourceRepairSearch.execute contract (globalStart contract before inputs)
  (report contract before inputs base law scope value depth).commands

theorem the_generated_repair_is_replayed_on_the_original_global_successor :
 physical (next contract before inputs base law scope value depth).actual=
 physical (report contract before inputs base law scope value depth).final.actual := by
 have replay := (SourceRepairRun.every_report_replays_only_its_selected_actual_source_commands contract
  ((origin before inputs).vocabulary before.actual.model base) ((origin before inputs).law before.actual.model law)
  (origin before inputs).origin (origin before inputs).stages (currentScope before scope) value depth
  (SourceRepairSearch.debt ((origin before inputs).vocabulary before.actual.model base)
    ((origin before inputs).law before.actual.model law) (origin before inputs).origin (origin before inputs).stages
    (currentScope before scope) value (localStart before inputs)+1) (localStart before inputs)).1
 have joined := replay_keeps_the_same_complete_physical_occurrence contract
  (globalStart contract before inputs) (localStart before inputs)
  (both_starts_are_the_same_actual_model_and_cursor contract before inputs)
  (report contract before inputs base law scope value depth).commands
 exact joined.trans (congrArg (fun state => physical state.actual) replay)

theorem new_signatures_cannot_reuse_a_previous_phase
 (ballot : StageBudget.Ballot (code := before.actual.model.source.code))
 (issued : ballot∈StageBudget.ledger ((origin before inputs).vocabulary before.actual.model base)
  (origin before inputs).origin (origin before inputs).stages) :
 before.actual.point.cut≤ballot.cut ∧ ballot.scope.phase=before.actual.point.cut :=
 RecursiveSigningSource.each_new_ballot_is_born_in_its_own_actual_phase before.actual.model base (origin before inputs) ballot issued

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningReplay
