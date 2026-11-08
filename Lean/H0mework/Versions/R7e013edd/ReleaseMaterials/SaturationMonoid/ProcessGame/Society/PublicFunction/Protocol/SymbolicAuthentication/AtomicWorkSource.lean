import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (batch : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)

-- The raw word is source code, not a certificate or a supplied endpoint.
-- One activation preserves its original batch/visit semantics.
def catalogue : CatalogueHandoffSource.Catalogue old :=
  ⟨batch,batch.length,[],0,(List.finRange old.sites).map Event.activate⟩
abbrev code := CatalogueHandoffSource.code old (catalogue old batch)
abbrev cursor (saved : Cursor old) := CatalogueHandoffSource.cursor old (catalogue old batch) saved

def protocol (submit : Bool) : Rule (code old batch) where
  work := ⟨fun _ _ => if submit then batch else [], by
    apply (code old batch).every_local_policy_is_enumerated
    intro key member
    apply (mem_words_iff _ _ _).mpr
    cases submit with
    | false => simp
    | true => exact ⟨Nat.le_max_right _ _,fun request inside => List.mem_append_right _ inside⟩⟩
  events := fun key _ => ⟨some ⟨.activate key.1,by
    exact List.mem_append_right _ (List.mem_map.mpr ⟨key.1,List.mem_finRange _,rfl⟩)⟩,by
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨⟨.activate key.1,?_⟩,?_,rfl⟩
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨key.1,List.mem_finRange _,rfl⟩)
      · exact List.mem_filter.mpr ⟨List.mem_attach _ _,by simp⟩⟩

abbrev row (saved : Cursor old) (submit : Bool) (rival : Opponent (code old batch)) :=
  StageTrace.material (cursor old batch saved) (protocol old batch submit) rival
abbrev next (saved : Cursor old) (submit : Bool) (rival : Opponent (code old batch)) :=
  (cursor old batch saved).after (protocol old batch submit) rival

inductive Verdict where
  | withheld | stopped | external | notReady | refused | executed
  deriving DecidableEq

def assess (saved : Cursor old) (submit : Bool) (rival : Opponent (code old batch)) : Verdict :=
  if submit = false then .withheld
  else match StageTrace.activation (row old batch saved submit rival) with
    | none => if (row old batch saved submit rival).before.remaining = 0 then .stopped else .external
    | some site => if (code old batch).memoryReady ((row old batch saved submit rival).before.frame.inbox site) then
        if ∀ item ∈ StageTrace.items (row old batch saved submit rival),
            (code old batch).law.Valid item.before item.request then .executed else .refused
      else .notReady

theorem selected_batch_is_one_actual_step (saved : Cursor old) (submit : Bool)
    (rival : Opponent (code old batch)) (site : Fin old.sites)
    (owned : StageTrace.activation (row old batch saved submit rival) = some site)
    (ready : (code old batch).memoryReady ((row old batch saved submit rival).before.frame.inbox site) = true) :
    (row old batch saved submit rival).submitted = (if submit then batch else []) ∧
      (EventStep.seed (next old batch saved submit rival)).current =
        old.law.next (row old batch saved submit rival).before.current (if submit then batch else []) := by
  have selected := (StageTrace.an_owned_activation_submits_its_selected_work
    (cursor old batch saved) (protocol old batch submit) rival site owned).2
  have word : (row old batch saved submit rival).submitted = (if submit then batch else []) := by
    rw [selected]
    change (if (code old batch).memoryReady ((row old batch saved submit rival).before.frame.inbox site)
      then (if submit then batch else []) else []) = _
    rw [ready]; rfl
  refine ⟨word,?_⟩
  rw [← (StageTrace.material_is_the_actual_step (cursor old batch saved) (protocol old batch submit) rival).1]
  change old.law.next (row old batch saved submit rival).before.current
    (row old batch saved submit rival).submitted = _
  rw [word]

theorem executed_uses_the_original_whole_word (saved : Cursor old) (submit : Bool)
    (rival : Opponent (code old batch))
    (success : assess old batch saved submit rival = .executed) :
    submit = true ∧ (row old batch saved submit rival).submitted = batch ∧
      (EventStep.seed (next old batch saved submit rival)).current =
        old.law.next (row old batch saved submit rival).before.current batch ∧
      (∀ item ∈ StageTrace.items (row old batch saved submit rival), old.law.Valid item.before item.request) := by
  by_cases withheld : submit = false
  · simp only [assess,if_pos withheld] at success
    contradiction
  · have submitted : submit = true := by cases submit <;> simp_all
    simp only [assess,if_neg withheld] at success
    cases owned : StageTrace.activation (row old batch saved submit rival) with
    | none =>
      simp only [owned] at success
      split at success <;> contradiction
    | some site =>
      simp only [owned] at success
      split at success
      · rename_i ready
        split at success
        · rename_i paid
          have actual := selected_batch_is_one_actual_step old batch saved submit rival site owned ready
          simp only [if_pos submitted] at actual
          exact ⟨submitted,actual.1,actual.2,paid⟩
        · contradiction
      · contradiction
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkSource
