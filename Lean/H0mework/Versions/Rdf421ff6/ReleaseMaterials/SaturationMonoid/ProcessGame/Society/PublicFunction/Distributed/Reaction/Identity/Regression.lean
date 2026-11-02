import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Principal

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev need := Reaction.Regression.need
abbrev waste := Reaction.Regression.waste

def issue : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false 2⟩
def repay : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .settle () true false 2⟩

abbrev code : Code Bool Unit Unit Unit Unit :=
  { Reaction.Regression.code with
    initial := { Reaction.Regression.code.initial with claims := fun _ _ _ => 0 }
    actions := [need]
    historyAlphabet := [[issue]]
    historyLimit := 1 }

def referencePolicy : code.Policy := fun _ _ => [need, need]
def efficientPolicy : code.Policy := fun _ _ => [need]

theorem reference_generated : referencePolicy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [referencePolicy])

theorem efficient_generated : efficientPolicy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [efficientPolicy])

def opponent : Opponent code := fun _ past _ =>
  if past.isEmpty then some ⟨.activate 0, by simp [code, Reaction.Regression.code, Distributed.Regression.code]⟩ else none

def seed : Machine Bool Unit Unit Unit Unit :=
  ⟨code, referencePolicy, reference_generated, [[issue]], by decide +kernel, opponent, .original, [], none, []⟩

theorem original_is_feasible : seed.code.feasible seed.reference := by decide +kernel

abbrev source := replacement seed original_is_feasible
abbrev oldSource := original seed
abbrev chosen := selection seed original_is_feasible

abbrev efficientProgram : Program code := ⟨efficientPolicy, efficient_generated⟩

theorem efficient_is_feasible : code.feasible efficientPolicy := by decide +kernel

theorem efficient_preserves_every_native_profile :
    ∀ history ∈ code.histories.attach, ∀ table ∈ tables code,
      profile code efficientProgram history table = profile code (Identity.reference seed) history table := by
  decide +kernel

theorem efficient_strictly_improves_the_original : Better code (Identity.reference seed) efficientProgram := by
  apply (strictness_comes_from_the_original_vector code _ _).mpr
  exact ⟨by decide +kernel, fun history table generated =>
    efficient_preserves_every_native_profile history (List.mem_attach _ _) table generated⟩

private theorem policy_eq_constant (policy : code.Policy) (word : RawEvent Bool Unit Unit Unit Unit)
    (same : policy (0, 0) (code.key_mem _) = word) : policy = fun _ _ => word := by
  funext key inside
  have unique : key = (0, 0) := Subsingleton.elim _ _
  subst key
  exact same

/-- The generic maximality certificate identifies the generated result;
receipt checking does not rerun the selector at every field. -/
theorem chosen_policy_is_efficient : chosen.policy.policy = efficientProgram := by
  apply Subtype.ext
  let program : Program code := chosen.policy.policy
  change program.val = efficientPolicy
  have supported := (List.mem_pi _ _).mp program.property (0, 0) (code.key_mem _)
  have alternatives : program.val (0, 0) (code.key_mem _) = [] ∨
      program.val (0, 0) (code.key_mem _) = [need] ∨
      program.val (0, 0) (code.key_mem _) = [need, need] := by
    simpa [words, code] using supported
  rcases alternatives with empty | efficient | repeated
  · have same := policy_eq_constant chosen.policy.policy.val [] empty
    have impossible : ¬ code.feasible (fun _ _ => []) := by decide +kernel
    exact False.elim (impossible (same ▸ chosen.policy.feasible))
  · exact policy_eq_constant chosen.policy.policy.val [need] efficient
  · have same : chosen.policy.policy.val = referencePolicy := policy_eq_constant _ _ repeated
    have improves : Better code chosen.policy.policy efficientProgram := by
      have programs : chosen.policy.policy = Identity.reference seed := Subtype.ext same
      rw [programs]
      exact efficient_strictly_improves_the_original
    exact False.elim (selected_has_no_feasible_dominator code (Identity.reference seed) chosen
      efficientProgram efficient_is_feasible improves)

theorem actual_source_is_the_generated_efficient_program :
    source = machine code efficientProgram (Identity.history seed) (Identity.table seed) := by
  unfold source replacement
  rw [chosen_policy_is_efficient]
  rfl

theorem actual_improvement_keeps_the_original_native_debt :
    (source.actualExecution 1).submitted = [need] ∧
      (source.actualExecution 1).after.stock true () = 2 ∧
      (oldSource.actualExecution 1).after.stock true () = 1 ∧
      (Native.generate source 1).finance.current.slots.length = 1 ∧
      Financial.outstanding source.input (Native.generate source 1).finance.current = 2 ∧
      verify seed.code (Identity.reference seed) chosen.policy.policy = true := by
  have replay := independent_replay_accepts_selection _ _ chosen
  refine ⟨?_, ?_, by decide +kernel, ?_, ?_, replay⟩
  all_goals rw [actual_source_is_the_generated_efficient_program]; decide +kernel

abbrev swapCode : Code Bool Unit Unit Unit Unit :=
  { code with
    initial := {code.initial with stock := fun party _ => if party then 6 else 0}
    actions := [waste, need, repay, issue]
    actionLimit := 3 }

def oldPolicy : swapCode.Policy := fun _ _ => [waste, waste, need]
def swappedPolicy : swapCode.Policy := fun _ _ => [repay, issue, need]

theorem old_generated : oldPolicy ∈ swapCode.policies := by
  apply swapCode.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [oldPolicy])

theorem swapped_generated : swappedPolicy ∈ swapCode.policies := by
  apply swapCode.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [swappedPolicy])

abbrev oldProgram : Program swapCode := ⟨oldPolicy, old_generated⟩
abbrev swappedProgram : Program swapCode := ⟨swappedPolicy, swapped_generated⟩
abbrev oldHistory : OriginalHistory swapCode := ⟨[[issue]], by decide +kernel⟩
def swapOpponent : Opponent swapCode := fun _ past _ =>
  if past.isEmpty then some ⟨.activate 0, by simp [swapCode, code, Reaction.Regression.code, Distributed.Regression.code]⟩ else none
abbrev swapTable := restrict swapCode swapOpponent

theorem aggregate_equality_cannot_replace_an_original_issue :
    (∀ metric ∈ Reaction.metrics swapCode,
      payoff swapCode swappedPolicy oldHistory.val swapOpponent metric ≤
        payoff swapCode oldPolicy oldHistory.val swapOpponent metric) ∧
      ¬ NonRegression swapCode swappedProgram oldProgram := by
  refine ⟨by decide +kernel, ?_⟩
  intro accepted
  have same := ((comparison_iff swapCode swappedProgram oldProgram).mp accepted).2 oldHistory swapTable
    (restriction_is_generated swapCode swapOpponent)
  have different : profile swapCode swappedProgram oldHistory swapTable ≠ profile swapCode oldProgram oldHistory swapTable := by
    decide +kernel
  exact different same

abbrev publicNativeIdentityFacade := Runtime.facade seed original_is_feasible
abbrev originalNativeIdentityFacade := Native.Runtime.facade oldSource

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Regression
