import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression

open Institutions.Capitalism.Universal.Source.Program

def need : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .use true [((), 1)] .necessity⟩
abbrev waste := Distributed.Regression.waste

abbrev code : Code Bool Unit Unit Unit Unit :=
  { Distributed.Regression.code with
    initial := PublicFunction.Regression.initial 3
    task := ⟨[⟨true, [((), 1)], .necessity⟩], 0, 10, by decide +kernel⟩
    actions := [waste, need]
    actionLimit := 2 }

def reference : code.Policy := fun _ _ => [waste, need]
def efficient : code.Policy := fun _ _ => [need]

theorem reference_is_generated : reference ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [reference])

theorem efficient_is_generated : efficient ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [efficient])

def opponent : Opponent code := fun _ past _ =>
  if past.isEmpty then some ⟨.activate 0, by simp [code, Distributed.Regression.code]⟩ else none

def source : Machine Bool Unit Unit Unit Unit where
  code := code
  reference := reference
  reference_generated := reference_is_generated
  history := []
  original := by simp [Code.histories, code, sequences, Code.historyLegal]
  opponent := opponent
  side := .replacement

def isSelected : Outcome code reference → Bool
  | .selected _ => true | .blocked _ => false

theorem paired_selection_and_independent_verifier_accept :
    isSelected source.answer = true ∧ verify code reference efficient = true ∧
      verify code reference reference = false := by decide +kernel

theorem both_source_occurrences_are_paid_and_preserve_original_claims :
    ((source.withSide .original).actualExecution 0).submitted = [waste, need] ∧
      ((source.withSide .replacement).actualExecution 0).submitted = [need] ∧
      ((source.withSide .original).actualExecution 0).after.stock true () = 1 ∧
      ((source.withSide .replacement).actualExecution 0).after.stock true () = 2 ∧
      ((source.withSide .original).actualExecution 0).after.claims () true false = 7 ∧
      ((source.withSide .replacement).actualExecution 0).after.claims () true false = 7 := by decide +kernel

abbrev reactiveCode := { code with eventLimit := 3, eligible := fun _ => true }
def reactiveReference : reactiveCode.Policy := fun _ _ => [waste, need]
def reactiveEfficient : reactiveCode.Policy := fun _ _ => [need]

def punishingOpponent : Opponent reactiveCode := fun _ past frame =>
  if past.isEmpty || frame.word.length == past.length then
    some ⟨.activate 0, by simp [reactiveCode, code, Distributed.Regression.code]⟩ else none

def originalProgram (efficient : Bool) : reactiveCode.Policy :=
  if efficient then reactiveEfficient else reactiveReference

theorem original_program_is_generated (efficient : Bool) : originalProgram efficient ∈ reactiveCode.policies := by
  apply reactiveCode.every_local_policy_is_enumerated
  intro key _
  cases efficient <;>
    apply (mem_words_iff _ _ _).mpr <;>
    simp [originalProgram, reactiveReference, reactiveEfficient]

def reactiveSource (efficient : Bool) : Machine Bool Unit Unit Unit Unit where
  code := reactiveCode
  reference := originalProgram efficient
  reference_generated := original_program_is_generated efficient
  history := []
  original := by simp [Code.histories, reactiveCode, code, sequences, Code.historyLegal]
  opponent := punishingOpponent
  side := .original

theorem the_same_opponent_generates_different_actual_paths :
    (trace reactiveCode reactiveReference [] punishingOpponent).length = 1 ∧
      (trace reactiveCode reactiveEfficient [] punishingOpponent).length = 3 ∧
      ((reactiveSource false).actualExecution 0).after.stock true () = 1 ∧
      ((reactiveSource true).actualExecution 0).after.stock true () = 0 := by decide +kernel

theorem same_script_order_does_not_imply_same_opponent_order :
    reactiveCode.NoWorseThan reactiveEfficient reactiveReference ∧
      ¬ AgainstEveryOpponent reactiveCode reactiveEfficient reactiveReference := by
  constructor
  · decide +kernel
  · intro bounded
    have original : [] ∈ reactiveCode.histories := by
      simp [Code.histories, reactiveCode, code, sequences, Code.historyLegal]
    have impossible : ¬ payoff reactiveCode reactiveEfficient [] punishingOpponent (.raw (.debit true ())) ≤
        payoff reactiveCode reactiveReference [] punishingOpponent (.raw (.debit true ())) := by decide +kernel
    exact impossible (bounded punishingOpponent [] original (.raw (.debit true ())))

theorem the_generated_joint_table_comparison_rejects_false_dominance :
    ¬ NonRegression reactiveCode reactiveEfficient reactiveReference := by
  intro bounded
  exact same_script_order_does_not_imply_same_opponent_order.2
    ((finite_comparison_iff_every_same_opponent reactiveCode _ _
      (original_program_is_generated true) (original_program_is_generated false)).mp bounded)

abbrev historyCode := { code with eventAlphabet := [.deliver 0, .activate 0], eventLimit := 2 }
def rememberingOpponent : Opponent historyCode := fun _ past _ =>
  if past.isEmpty then some ⟨.deliver 0, by simp [historyCode]⟩
  else some ⟨.activate 0, by simp [historyCode]⟩

theorem opponent_memory_is_not_collapsed_to_the_current_frame :
    historyCode.step reference (historyCode.historyCurrent []) historyCode.start (.deliver 0) = historyCode.start ∧
      trace historyCode reference [] rememberingOpponent = [.deliver 0, .activate 0] := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression
