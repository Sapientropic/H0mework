import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev need := Reaction.Regression.need
def waste : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .use true [((), 2)] .contribution⟩
def issue : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false 2⟩
def repay : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .settle () true false 2⟩

def law : RawLaw Bool Unit Unit Unit Unit := { Reaction.Regression.code.law with
  policy := .opaque fun current request => match request.operation with
    | .use _ _ .necessity => decide (current.stock true () = 1)
    | _ => true }

abbrev code : Code Bool Unit Unit Unit Unit := { Reaction.Regression.code with
  law := law
  initial := {Reaction.Regression.code.initial with claims := fun _ _ _ => 0}
  bootstrap := [issue]
  actions := [waste, repay, need]
  historyAlphabet := []
  historyLimit := 0 }

def referencePolicy : code.Policy := fun _ _ => [waste, need]
def efficientPolicy : code.Policy := fun _ _ => [repay, need]

theorem reference_generated : referencePolicy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key inside
  exact (mem_words_iff _ _ _).mpr (by simp [referencePolicy])

theorem efficient_generated : efficientPolicy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key inside
  exact (mem_words_iff _ _ _).mpr (by simp [efficientPolicy])

abbrev efficient : Program code := ⟨efficientPolicy, efficient_generated⟩

def opponent : Opponent code := fun _ past _ => if past.isEmpty then
  some ⟨.activate 0, by simp [code, Reaction.Regression.code, Distributed.Regression.code]⟩ else none

def seed : Machine Bool Unit Unit Unit Unit :=
  ⟨code, referencePolicy, reference_generated, [[issue]], by decide +kernel, opponent, .original, [], none, []⟩

theorem original_is_feasible : seed.code.feasible seed.reference := by decide +kernel
theorem efficient_is_feasible : code.feasible efficientPolicy := by decide +kernel

theorem efficient_preserves_every_realized_right :
    ∀ history ∈ code.histories.attach, ∀ table ∈ tables code,
      profile code efficient history table = profile code (Settlement.reference seed) history table := by
  decide +kernel

theorem payment_is_a_verified_strict_improvement : Better code (Settlement.reference seed) efficient := by
  apply (strictness_comes_from_actual_values code _ _).mpr
  exact ⟨by unfold Improves NoWorse; decide +kernel, fun history table generated =>
    efficient_preserves_every_realized_right history (List.mem_attach _ _) table generated⟩

private theorem constant_policy (policy : code.Policy) : policy = fun _ _ => policy (0, 0) (code.key_mem _) := by
  funext key inside
  have unique : key = (0, 0) := Subsingleton.elim _ _
  subst key
  rfl

theorem feasible_program_is_one_of_two_paid_words (program : Program code) (feasible : code.feasible program.val) :
    program.val = referencePolicy ∨ program.val = efficientPolicy := by
  have finite : ∀ word ∈ words code.actions code.actionLimit,
      ((code.replay (fun _ _ => word) (code.historyCurrent [[issue]]) [.activate 0]).localLegal = true ∧
        ServiceAdequate law (code.historyCurrent [[issue]]) code.task word) →
          word = [waste, need] ∨ word = [repay, need] := by decide +kernel
  have support := (List.mem_pi _ _).mp program.property (0, 0) (code.key_mem _)
  have constant := constant_policy program.val
  have accepted : code.feasible (fun _ _ => program.val (0, 0) (code.key_mem _)) := constant ▸ feasible
  have concrete := accepted ([[issue]], [.activate 0]) (by decide +kernel)
  change _ ∧ ServiceAdequate law (code.historyCurrent [[issue]]) code.task
    (code.replay (fun _ _ => program.val (0, 0) (code.key_mem _))
      (code.historyCurrent [[issue]]) [.activate 0]).word at concrete
  have actualWord : (code.replay (fun _ _ => program.val (0, 0) (code.key_mem _))
      (code.historyCurrent [[issue]]) [.activate 0]).word = program.val (0, 0) (code.key_mem _) := rfl
  rw [actualWord] at concrete
  rcases finite _ support concrete with old | new
  · exact .inl (constant.trans (by rw [old]; rfl))
  · exact .inr (constant.trans (by rw [new]; rfl))

abbrev chosen := selection seed original_is_feasible
abbrev source := replacement seed original_is_feasible
abbrev oldSource := original seed

theorem chosen_policy_is_the_actual_payment : chosen.policy.policy = efficient := by
  rcases feasible_program_is_one_of_two_paid_words chosen.policy.policy chosen.policy.feasible with old | new
  · have same : chosen.policy.policy = Settlement.reference seed := Subtype.ext old
    have improves : Better code chosen.policy.policy efficient := by rw [same]; exact payment_is_a_verified_strict_improvement
    exact False.elim (selected_has_no_feasible_dominator code (Settlement.reference seed) chosen
      efficient efficient_is_feasible improves)
  · exact Subtype.ext new

theorem actual_source_is_the_generated_payment : source = machine code efficient (Settlement.history seed) (Settlement.table seed) := by
  unfold source replacement
  rw [chosen_policy_is_the_actual_payment]
  rfl

theorem actual_payment_replaces_material_destruction_and_keeps_the_original_issue :
    (source.actualExecution 0).submitted = [issue] ∧
      (source.actualExecution 1).submitted = [repay, need] ∧
      (oldSource.actualExecution 1).submitted = [waste, need] ∧
      (source.actualExecution 1).after.stock true () = 0 ∧
      (oldSource.actualExecution 1).after.stock true () = 0 ∧
      (source.actualExecution 1).after.stock false () = 2 ∧
      (oldSource.actualExecution 1).after.stock false () = 0 ∧
      Financial.outstanding source.input (Native.generate source 1).finance.current = 0 ∧
      Financial.outstanding oldSource.input (Native.generate oldSource 1).finance.current = 2 ∧
      (Native.generate source 1).finance.current.slots.length = 1 ∧
      verify code (Settlement.reference seed) chosen.policy.policy = true := by
  refine ⟨public_bootstrap_is_actually_emitted source (by decide +kernel), ?_, by decide +kernel, ?_, by decide +kernel, ?_, by decide +kernel, ?_, by decide +kernel, ?_,
    independent_replay_accepts_selection _ _ chosen⟩
  all_goals rw [actual_source_is_the_generated_payment]; decide +kernel

theorem old_exact_archive_comparison_rejects_this_actual_payment :
    ¬ Identity.NonRegression code efficient (Settlement.reference seed) := by
  intro bounded
  have changed : Identity.profile code efficient (Settlement.history seed) (Settlement.table seed) ≠
      Identity.profile code (Settlement.reference seed) (Settlement.history seed) (Settlement.table seed) := by
    decide +kernel
  exact changed (((Identity.comparison_iff code _ _).mp bounded).2 _ _
    (restriction_is_generated code opponent))

def forgedIssue : Request Bool Unit Unit Unit Unit := ⟨false, [], (), [], .issue () true false 2⟩
abbrev deniedCode : Code Bool Unit Unit Unit Unit := {code with bootstrap := [forgedIssue]}
def deniedSource : Machine Bool Unit Unit Unit Unit where
  code := deniedCode
  reference := fun _ _ => []
  reference_generated := by
    apply deniedCode.every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := [[forgedIssue]]
  original := by decide +kernel
  opponent := fun _ _ _ => none
  side := .original

theorem refused_public_bootstrap_is_actual_and_cannot_mint_an_issue :
    deniedCode.histories ≠ [] ∧
      (deniedSource.actualExecution 0).submitted = [forgedIssue] ∧
      (Native.generate deniedSource 0).finance.current.slots.length = 0 ∧
      (deniedSource.actualExecution 0).after.claims () true false = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

abbrev unbackedCode : Code Bool Unit Unit Unit Unit := { code with
  law := Reaction.Regression.code.law
  bootstrap := []
  initial := {code.initial with claims := fun _ debtor creditor => if debtor && !creditor then 2 else 0} }

def unbackedOld : Program unbackedCode := ⟨fun _ _ => [waste, need], by
  apply unbackedCode.every_local_policy_is_enumerated
  intro key inside
  exact (mem_words_iff _ _ _).mpr (by simp)⟩
def unbackedNew : Program unbackedCode := ⟨fun _ _ => [repay, need], by
  apply unbackedCode.every_local_policy_is_enumerated
  intro key inside
  exact (mem_words_iff _ _ _).mpr (by simp)⟩

theorem numerical_claims_cannot_impersonate_an_original_native_issue :
    ¬ NonRegression unbackedCode unbackedNew unbackedOld := by
  intro bounded
  let history : OriginalHistory unbackedCode := ⟨[], by decide +kernel⟩
  let table : Table unbackedCode := restrict unbackedCode (fun _ _ _ =>
    some ⟨.activate 0, by simp [unbackedCode, code, Reaction.Regression.code, Distributed.Regression.code]⟩)
  have refused : (profile unbackedCode unbackedNew history table).uncoveredClaims ≠
      (profile unbackedCode unbackedOld history table).uncoveredClaims := by decide +kernel
  exact refused (congrArg Profile.uncoveredClaims
    (((comparison_iff unbackedCode _ _).mp bounded).2 history table
      (restriction_is_generated unbackedCode _)))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Regression
