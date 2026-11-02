import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Feedback Distributed.Recall.Information.Agency.Protocol

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {target : Authority.Sources old.base old.scope} {count : Nat}
  {word : List (Action old)} {receipt : Receipt old oldDepth target count word}

namespace Walk
theorem finish_depth_is_not_earlier {cursor : Cursor old oldDepth word} (made : Walk cursor) :
    cursor.depth ≤ made.finish.depth := by
  induction made with
  | finished => exact Nat.le_refl _
  | blocked cursor head _ _ _ =>
      change cursor.depth ≤ (cursor.after head.signer).depth
      rw [cursor.after_depth];omega
  | unsupported cursor _ _ =>
      change cursor.depth ≤ cursor.depth+1
      omega
  | unpaid cursor fee _ _ =>
      change cursor.depth ≤ cursor.depth+1+1
      omega
  | billed cursor _ _ _ _ ih =>
      change cursor.depth+1 ≤ _ at ih
      exact (Nat.le_succ _).trans ih
  | advanced cursor head _ _ _ _ ih =>
      rw [cursor.after_depth] at ih
      exact (Nat.le_succ cursor.depth).trans ih
  | workloadStopped cursor _ made _ =>
      have ordered := made.preserves.depth
      change cursor.depth ≤ made.endpoint.depth+1
      omega
  | workloadAdvanced _ _ made _ _ ih => exact made.preserves.depth.trans ih
  | quotedStopped cursor _ made _ =>
      have ordered := made.preserves.depth
      change cursor.depth ≤ made.endpoint.depth+1
      omega
  | quotedAdvanced _ _ made _ _ ih => exact made.preserves.depth.trans ih
end Walk

namespace Output
variable (made : Output receipt)

theorem source_code_is_the_target_code : made.bound.source.code = target.val.code :=
  made.walk.source_code_is_retained

/-- The entire old-word attempt and every generated repair belong to one actual interval. -/
abbrev scoreStart (_made : Output receipt) := targetDepth old target count
abbrev scoreSpan := made.walk.finish.depth-made.scoreStart

theorem evaluation_arrives_at_its_exact_actual_next :
    Window.finish made.scoreStart made.scoreSpan = made.walk.finish.depth+1 := by
  have earlier := made.walk.finish_depth_is_not_earlier
  change targetDepth old target count+1 ≤ made.walk.finish.depth at earlier
  dsimp only [Window.finish,scoreSpan,scoreStart]
  omega

def evaluation : Evaluation target.val.code :=
  made.source_code_is_the_target_code ▸ Window.evaluate made.bound made.scoreStart made.scoreSpan

def evaluationAxes : List (EconomicAxis target.val.code) :=
  made.source_code_is_the_target_code ▸ Window.axes made.bound made.scoreStart

/-- Earlier paid task, inquiry and publication events remain in the same source.
    Their actual starting cut can therefore be included without another feedback run. -/
def evaluationFrom (start : Nat) : Evaluation target.val.code :=
  made.source_code_is_the_target_code ▸ Window.evaluate made.bound start (made.walk.finish.depth-start)

theorem an_earlier_evaluation_reaches_the_same_actual_next (start : Nat) (earlier : start ≤ made.scoreStart) :
    Window.finish start (made.walk.finish.depth-start) = made.walk.finish.depth+1 := by
  have stop := made.evaluation_arrives_at_its_exact_actual_next
  dsimp only [Window.finish] at stop ⊢
  omega

theorem the_score_contains_the_original_failed_attempt_and_every_recovery_emission :
    made.scoreStart+made.scoreSpan = made.walk.finish.depth ∧
      Window.terminal made.bound made.scoreStart made.scoreSpan = made.walk.finish.before := by
  have stop := made.evaluation_arrives_at_its_exact_actual_next
  constructor
  · dsimp only [Window.finish] at stop;omega
  · change made.bound.source.currentAt (Window.finish made.scoreStart made.scoreSpan) = _
    rw [stop]
    rfl

theorem the_installed_output_reads_its_own_complete_evaluation :
    made.read.evaluation = made.evaluation := by rw [made.read_exact]

theorem actual_window_independent_review :
    Window.verify made.bound made.scoreStart made.scoreSpan
      (Window.evaluate made.bound made.scoreStart made.scoreSpan) = true :=
  Window.verifies_generated _ _ _

end Output

/-- The vocabulary is fixed by the old source. A candidate supplies an actual machine,
    not its future recovery result or any comparison certificate. -/
abbrev SameCodeTarget (old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  {source : Machine Party Good Port (Mandate.State Party Technology) Instrument // source.code = old.source.code}

def SameCodeTarget.indexed (source : SameCodeTarget old) : Authority.Sources old.base old.scope :=
  ⟨source.val,(congrArg Code.law source.property).trans old.law_exact,(congrArg Code.task source.property).trans old.task_exact⟩

/-- Registration is a seed vocabulary, not a veto over this actual emitted word. -/
def capabilities (old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (oldDepth : Nat) :=
  (old.source.code.historyAlphabet.insert (old.source.actualExecution oldDepth).submitted).filter fun word =>
    decide (Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word)

theorem capability_is_available_and_legal (word : List (Action old))
    (inside : word ∈ capabilities old oldDepth) :
    (word = (old.source.actualExecution oldDepth).submitted ∨ word ∈ old.source.code.historyAlphabet) ∧
      Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word := by
  have original := List.mem_filter.mp inside
  exact ⟨by simpa only [List.mem_insert_iff] using original.1,of_decide_eq_true original.2⟩

theorem every_registered_legal_word_remains_available (word : List (Action old))
    (registered : word ∈ old.source.code.historyAlphabet)
    (legal : Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth) word) :
    word ∈ capabilities old oldDepth := by
  apply List.mem_filter.mpr
  exact ⟨by simp only [List.mem_insert_iff];exact Or.inr registered,decide_eq_true legal⟩

theorem every_actual_legal_emission_is_available
    (legal : Mandate.Replay.Legal (base := old.base) old.scope (Authority.currentAt old oldDepth)
      (old.source.actualExecution oldDepth).submitted) :
    (old.source.actualExecution oldDepth).submitted ∈ capabilities old oldDepth := by
  apply List.mem_filter.mpr
  exact ⟨by simp,decide_eq_true legal⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
