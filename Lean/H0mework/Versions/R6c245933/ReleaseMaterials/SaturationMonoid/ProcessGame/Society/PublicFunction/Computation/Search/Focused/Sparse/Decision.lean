import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Work

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Decision
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference protocol : Program model.source.code fuel)

def field (world : Replanning.Point model domain) (current prior : Evaluation model.source.code)
    (test : Replanning.Test model domain world) : Prop :=
  match test with
  | .legal => current.legal = true
  | .complete => current.complete = true
  | .profile => current.profile = prior.profile
  | .native => Authority.Trace.Lawful.NoWorse current.native prior.native
  | .economic axis => current.value axis.val ≤ prior.value axis.val

instance (world : Replanning.Point model domain) (current prior : Evaluation model.source.code)
    (test : Replanning.Test model domain world) : Decidable (field model domain world current prior test) := by
  unfold field
  cases test <;> infer_instance

theorem all_fields_iff (world : Replanning.Point model domain) (current prior : Evaluation model.source.code) :
    (∀ test ∈ Replanning.tests model domain world,field model domain world current prior test) ↔
      Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut) current prior := by
  constructor
  · intro all
    refine ⟨all .legal (Replanning.every_test_is_generated _ _ _ _),
      all .complete (Replanning.every_test_is_generated _ _ _ _),
      all .profile (Replanning.every_test_is_generated _ _ _ _),
      all .native (Replanning.every_test_is_generated _ _ _ _),?_⟩
    intro axis inside
    exact all (.economic ⟨axis,inside⟩) (Replanning.every_test_is_generated _ _ _ _)
  · intro all test _
    cases test with
    | legal => exact all.1
    | complete => exact all.2.1
    | profile => exact all.2.2.1
    | native => exact all.2.2.2.1
    | economic axis => exact all.2.2.2.2 axis.val axis.property

def silentRow (world : Replanning.Point model domain) (test : Replanning.Test model domain world) :
    Replanning.Row model domain :=
  ⟨world,⟨externalTable world.val PublicDomain.silent,Residual.restriction_is_generated _ _ _ _⟩,test⟩

theorem silent_field_is_an_original_test (world : Replanning.Point model domain)
    (test : Replanning.Test model domain world) :
    field model domain world (actualEvaluation model world.val original protocol PublicDomain.silent)
      (actualEvaluation model world.val original reference PublicDomain.silent) test ↔
      Selection.holds model domain original reference protocol (silentRow model domain world test) := by
  simp only [Selection.holds,Selection.readTable,silentRow]
  rw [one_common_table_preserves_the_entire_actual_evaluation,
    one_common_table_preserves_the_entire_actual_evaluation]
  cases test <;> rfl

def quietHolds (world : Replanning.Point model domain) : Prop :=
  Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
    (actualEvaluation model world.val original protocol PublicDomain.silent)
    (actualEvaluation model world.val original reference PublicDomain.silent)

inductive QuietResult (worlds : List (Replanning.Point model domain)) where
  | accepted (all : ∀ world ∈ worlds,quietHolds model domain original reference protocol world)
  | rejected (row : Replanning.Row model domain) (generated : row ∈ Replanning.rows model domain)
      (broken : ¬ Selection.holds model domain original reference protocol row)

/-- Each world generates its two evaluations once. Failure retains an original row,
    while the erased membership proof never enumerates the external-table catalogue. -/
def quietScan : (worlds : List (Replanning.Point model domain)) → QuietResult model domain original reference protocol worlds
  | [] => .accepted (by simp)
  | world :: rest =>
    let current := actualEvaluation model world.val original protocol PublicDomain.silent
    let prior := actualEvaluation model world.val original reference PublicDomain.silent
    match Distributed.inspect (field model domain world current prior) (Replanning.tests model domain world) with
    | .rejected test _ broken => .rejected (silentRow model domain world test)
        (Replanning.every_row_is_source_generated _ _ _) (by
          intro valid
          exact broken ((silent_field_is_an_original_test model domain original reference protocol world test).mpr valid))
    | .accepted checked =>
      match quietScan rest with
      | .rejected row generated broken => .rejected row generated broken
      | .accepted all => .accepted (by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other
            exact (all_fields_iff model domain world current prior).mp checked
          · exact all other later)

def inspect : Inspection (Selection.holds model domain original reference protocol) (Replanning.rows model domain) :=
  if quiet : PublicDomain.quiet (code := model.source.code) = true then
    match quietScan model domain original reference protocol (Replanning.points model domain) with
    | .rejected row generated broken => .rejected row generated broken
    | .accepted checked => .accepted ((Selection.compactPacked_iff model domain original reference protocol).mp (by
        simpa only [Selection.compactPacked,quiet,ite_true,quietHolds] using checked))
  else Distributed.inspect (Selection.holds model domain original reference protocol) (Replanning.rows model domain)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Decision
