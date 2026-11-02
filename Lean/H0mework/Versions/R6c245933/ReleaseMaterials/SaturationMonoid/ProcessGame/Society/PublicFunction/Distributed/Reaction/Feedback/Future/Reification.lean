import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Continuation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)
  (opponent : Opponent source.code) (term : List (Option source.code.Policy))
  (active : source.feedback? = some input) (empty : source.continuation = [])
  (generated : term ∈ Residual.scheduleTerms source input cut)

include active empty generated

theorem joint_actual_submitted (ordinal : Nat)
    (bounded : ordinal < source.history.length+1+cut+(Residual.seed source input cut).remaining) :
    ((target source input cut (jointOpponent source input cut opponent) term).actualExecution ordinal).submitted =
      ((target source input cut opponent term).actualExecution ordinal).submitted := by
  have same := joint_occurrences source input cut opponent term active empty generated (ordinal+1) (by omega)
  change ProgrammeSource.rawEvent (target source input cut (jointOpponent source input cut opponent) term).input
    (ProgrammeHistory.visitAt (target source input cut (jointOpponent source input cut opponent) term).input (ordinal+1)).current =
      ProgrammeSource.rawEvent (target source input cut opponent term).input
        (ProgrammeHistory.visitAt (target source input cut opponent term).input (ordinal+1)).current
  exact same.2

theorem joint_actual_continuation_past (count : Nat) (bounded : count ≤ cut+(Residual.seed source input cut).remaining) :
    Machine.Continuation.past (target source input cut (jointOpponent source input cut opponent) term) count =
      Machine.Continuation.past (target source input cut opponent term) count := by
  unfold Machine.Continuation.past
  congr 1
  funext index
  exact joint_actual_submitted source input cut opponent term active empty generated _ (by
    change source.history.length+1+index.val < source.history.length+1+cut+(Residual.seed source input cut).remaining
    omega)

omit active empty generated in
private theorem entries_after_feedback_update (feedback : Option (Input source.code))
    (start : Nat) (controls : List (Option source.code.Policy)) :
    Execution.entries {source with feedback? := feedback} start controls = Execution.entries source start controls := by
  induction controls generalizing start with
  | nil => rfl
  | cons head tail ih => simp only [Execution.entries,ih]

/-- The feedback function is erased only after its actual finite word prefix has
    been generated. The two old machines themselves are not identified. -/
theorem reified_joint_successor_is_the_same_actual_source
    (count : Nat) (bounded : count ≤ cut+(Residual.seed source input cut).remaining)
    (word : RawEvent Party Good Port Technology Instrument) :
    Machine.Continuation.extend (target source input cut (jointOpponent source input cut opponent) term) count word =
      Machine.Continuation.extend (target source input cut opponent term) count word := by
  unfold Machine.Continuation.extend
  rw [joint_actual_continuation_past source input cut opponent term active empty generated count bounded]
  generalize shared : Machine.Continuation.past (target source input cut opponent term) count ++ [word] = words
  unfold Machine.withContinuation target Execution.target
  simp only [entries_after_feedback_update]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future
