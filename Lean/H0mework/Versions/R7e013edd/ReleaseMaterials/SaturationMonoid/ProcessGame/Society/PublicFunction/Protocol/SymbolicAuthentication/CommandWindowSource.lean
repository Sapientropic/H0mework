import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommandWindowSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open LocalCommandSource LocalCommandRun

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

-- Include one literal interface miss of each kind; unbounded raw indexes remain
-- available in LocalCommandRun, outside this finite source-control domain.
def menu : List LocalCommandSource.Input := .idle ::
  ((List.range (model.source.code.actions.length+1)).map LocalCommandSource.Input.command ++
   (List.range (model.source.code.eventAlphabet.length+1)).map LocalCommandSource.Input.event)

def advance (state : LocalCommandRun.State model start) :=
  (menu model).map (LocalCommandRun.step model start state)
def cases (state : LocalCommandRun.State model start) : Nat → List (LocalCommandRun.State model start) :=
  Nat.rec [state] (fun _ previous => previous.flatMap (advance model start))
abbrev branches (state : LocalCommandRun.State model start) (count : Nat) :=
  (cases model start state count).map LocalCommandRun.State.stages
abbrev Command := {input : LocalCommandSource.Input // input ∈ menu model}

def actual (choose : Nat → LocalCommandRun.State model start → Command model)
    (state : LocalCommandRun.State model start) (count : Nat) : LocalCommandRun.State model start :=
  Nat.rec state (fun index previous => LocalCommandRun.step model start previous (choose index previous).val) count

theorem the_source_menu_contains_every_original_command (index : Nat)
    (bounded : index < model.source.code.actions.length) : .command index ∈ menu model := by
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨index,List.mem_range.mpr (by omega),rfl⟩

theorem every_actual_adaptive_input_has_its_source_branch
    (choose : Nat → LocalCommandRun.State model start → Command model)
    (state : LocalCommandRun.State model start) (count : Nat) :
    actual model start choose state count ∈ cases model start state count := by
  induction count with
  | zero => exact List.mem_singleton_self _
  | succ count ih =>
    exact List.mem_flatMap.mpr ⟨_,ih,List.mem_map.mpr ⟨(choose count _).val,(choose count _).property,rfl⟩⟩

theorem every_domain_has_an_actual_generated_branch (state : LocalCommandRun.State model start) (count : Nat) :
    ∃ branch, branch ∈ cases model start state count := by
  let choose : Nat → LocalCommandRun.State model start → Command model := fun _ _ => ⟨.idle,List.mem_cons_self⟩
  exact ⟨_,every_actual_adaptive_input_has_its_source_branch model start choose state count⟩

theorem every_branch_keeps_its_literal_attempts_and_original_stages
    (state branch : LocalCommandRun.State model start) (count : Nat)
    (inside : branch ∈ cases model start state count) :
    state.entries <+: branch.entries ∧ state.stages <+: branch.stages ∧
      branch.inputs.length = state.inputs.length + count ∧ branch.stages.length = state.stages.length + count := by
  induction count generalizing branch with
  | zero =>
    cases List.mem_singleton.mp inside
    exact ⟨List.prefix_refl _,List.prefix_refl _,by omega,by omega⟩
  | succ count ih =>
    obtain ⟨previous,member,next⟩ := List.mem_flatMap.mp inside
    obtain ⟨input,_,same⟩ := List.mem_map.mp next
    rw [← same]
    have before := ih previous member
    have after := LocalCommandRun.actual_extension_preserves_all_attempts_and_stages model start [input] previous
    refine ⟨before.1.trans after.1,before.2.1.trans after.2,?_,?_⟩
    · rw [(LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage model start previous input).1,
        List.length_append,List.length_singleton,before.2.2.1]
      omega
    · change (previous.stages ++ [_]).length = _
      rw [List.length_append,List.length_singleton,before.2.2.2]
      omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommandWindowSource
