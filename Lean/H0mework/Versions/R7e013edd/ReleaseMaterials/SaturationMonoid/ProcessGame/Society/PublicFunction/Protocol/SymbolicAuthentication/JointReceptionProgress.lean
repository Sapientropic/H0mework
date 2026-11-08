import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionProgress
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage JointReceptionSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}
 (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law root) (origin : Cursor root) (past : List (EventHistory.Stage (code := root)))
 (scope : Scope) (value : Bool)
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem support_mono (before after : HeaderReception.Receiver (code := root))
 (historyPrefix : before.receipts <+: after.receipts) :
 ActorQuorum.support before scope value ⊆ ActorQuorum.support after scope value := by
 intro actor inside
 obtain ⟨key,member,owner⟩ := (ActorQuorum.mem_support_iff _ _ _ _).mp inside
 obtain ⟨receipt,present,sameScope,choice,signed⟩ := (StageQuorum.mem_support_iff _ _ _ _).mp member
 exact (ActorQuorum.mem_support_iff _ _ _ _).mpr ⟨key,
  (StageQuorum.mem_support_iff _ _ _ _).mpr ⟨receipt,historyPrefix.subset present,sameScope,choice,signed⟩,owner⟩

theorem every_actual_command_preserves_received_actor_support
 (state : JointReceptionSource.State root) (command : RenewableArchiveSource.Command) (recipient : Fin root.sites) :
 ActorQuorum.support (observed vocabulary law origin past state recipient) scope value ⊆
 ActorQuorum.support (observed vocabulary law origin past (advance contract state command) recipient) scope value := by
 apply support_mono scope value
 unfold observed
 rw [advance_appends_only_actual_rows,RenewableHistoryReception.scan_append]
 exact RenewableHistoryReception.scan_keeps_all_prior_receipts _ _ _ _ _ _ _ _

theorem every_actual_command_can_only_reduce_the_original_delivery_debt
 (state : JointReceptionSource.State root) (command : RenewableArchiveSource.Command) :
 pending vocabulary law origin past scope value (advance contract state command) ⊆
 pending vocabulary law origin past scope value state := by
 intro task inside
 obtain ⟨target,missing⟩ := Finset.mem_filter.mp inside
 exact Finset.mem_filter.mpr ⟨target,fun received => missing
  (every_actual_command_preserves_received_actor_support vocabulary law origin past scope value contract
   state command task.1 received)⟩

theorem selected_service_delivers_a_previously_missing_original_identity
 (state : JointReceptionSource.State root) (task : Fin root.sites × LocalCommandSource.Input)
 (chosen : selected vocabulary law origin past scope value state=some task) :
 ∃ wire,
 (task.1,root.siteParty wire.ballot.key)∈pending vocabulary law origin past scope value state ∧
 wire.ballot.scope=scope ∧ wire.ballot.choice=value ∧
 RenewableHistoryReception.check vocabulary law origin past task.1 (row state task.2)
  ((observed vocabulary law origin past state task.1).receipts.map fun receipt =>
   (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire=.accepted wire ∧
 (observed vocabulary law origin past (advance contract state (.execute [task.2])) task.1).receipts=
 (observed vocabulary law origin past state task.1).receipts++
 [⟨wire,state.rows.length,(row state task.2).material.cursor.cut⟩] := by
 have accepted := (selected_service_is_registered_and_computed vocabulary law origin past scope value state task chosen).2
 cases found : RenewableHistoryReception.incoming vocabulary origin past (row state task.2) with
 | none => simp only [offer,found] at accepted; contradiction
 | some wire =>
   simp only [offer,found] at accepted
   split at accepted <;> try contradiction
   rename_i result checked
   have same := (RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ checked).1
   subst result
   obtain ⟨missing,sameScope,choice⟩ := of_decide_eq_true accepted
   refine ⟨wire,missing,sameScope,choice,checked,?_⟩
   unfold observed
   rw [executing_one_input_is_the_exact_checked_row,RenewableHistoryReception.scan_append]
   change (RenewableHistoryReception.receive _ _ _ _ _ _ (0+state.rows.length)
    (observed vocabulary law origin past state task.1)).receipts=_
   simp only [Nat.zero_add,RenewableHistoryReception.receive,found,checked]
   rfl

theorem selected_service_strictly_reduces_joint_delivery_debt
 (state : JointReceptionSource.State root) (external : RenewableArchiveSource.Command)
 (task : Fin root.sites × LocalCommandSource.Input)
 (chosen : selected vocabulary law origin past scope value state=some task) :
 (pending vocabulary law origin past scope value
  (step vocabulary law origin past scope value contract state external)).card <
 (pending vocabulary law origin past scope value state).card := by
 have same : step vocabulary law origin past scope value contract state external=
  advance contract state (.execute [task.2]) := by simp only [step,command,chosen]
 rw [same]
 obtain ⟨wire,missing,sameScope,choice,_,receipts⟩ :=
  selected_service_delivers_a_previously_missing_original_identity vocabulary law origin past scope value contract state task chosen
 have now : root.siteParty wire.ballot.key∈ActorQuorum.support
  (observed vocabulary law origin past (advance contract state (.execute [task.2])) task.1) scope value := by
  apply (ActorQuorum.mem_support_iff _ _ _ _).mpr
  refine ⟨wire.ballot.key,(StageQuorum.mem_support_iff _ _ _ _).mpr ?_,rfl⟩
  refine ⟨⟨wire,state.rows.length,(row state task.2).material.cursor.cut⟩,?_,sameScope,choice,rfl⟩
  rw [receipts]
  exact List.mem_append_right _ (List.mem_singleton_self _)
 have subset := every_actual_command_can_only_reduce_the_original_delivery_debt vocabulary law origin past scope value contract
  state (.execute [task.2])
 have different : pending vocabulary law origin past scope value (advance contract state (.execute [task.2]))≠
  pending vocabulary law origin past scope value state := by
  intro equal
  have absent := (Finset.mem_filter.mp (equal ▸ missing)).2
  exact absent now
 exact Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨subset,different⟩)

theorem a_step_without_a_selected_service_is_the_original_external_command
 (state : JointReceptionSource.State root) (external : RenewableArchiveSource.Command)
 (absent : selected vocabulary law origin past scope value state=none) :
 step vocabulary law origin past scope value contract state external=advance contract state external := by
 simp only [step,command,absent]

theorem actual_source_opportunities_complete_joint_delivery_in_the_original_debt_bound
 (start : JointReceptionSource.State root) (external : Nat → JointReceptionSource.State root → RenewableArchiveSource.Command)
 (opportunities : ∀ index < (pending vocabulary law origin past scope value start).card,
  (pending vocabulary law origin past scope value
   (JointReceptionSource.run vocabulary law origin past scope value contract start external index)).Nonempty →
  ∃ task∈menu (JointReceptionSource.run vocabulary law origin past scope value contract start external index),
   offer vocabulary law origin past scope value
    (JointReceptionSource.run vocabulary law origin past scope value contract start external index) task=true) :
 pending vocabulary law origin past scope value
  (JointReceptionSource.run vocabulary law origin past scope value contract start external
   (pending vocabulary law origin past scope value start).card)=∅ := by
 let debt := (pending vocabulary law origin past scope value start).card
 have bounded : ∀ index≤debt,
  (pending vocabulary law origin past scope value (JointReceptionSource.run vocabulary law origin past scope value contract start external index)).card=0 ∨
  (pending vocabulary law origin past scope value (JointReceptionSource.run vocabulary law origin past scope value contract start external index)).card+index≤debt := by
  intro index
  induction index with
  | zero => intro _;exact Or.inr (Nat.le_refl _)
  | succ index ih =>
    intro limit
    have previous := ih (by omega)
    let current := JointReceptionSource.run vocabulary law origin past scope value contract start external index
    change (pending vocabulary law origin past scope value current).card=0 ∨
     (pending vocabulary law origin past scope value current).card+index≤debt at previous
    have subset := every_actual_command_can_only_reduce_the_original_delivery_debt vocabulary law origin past scope value contract
     current (command vocabulary law origin past scope value current (external index current))
    have monotone := Finset.card_le_card subset
    change (pending vocabulary law origin past scope value
     (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+1))).card≤_ at monotone
    by_cases zero : (pending vocabulary law origin past scope value current).card=0
    · exact Or.inl (by omega)
    · have nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero zero)
      obtain ⟨task,registered,offered⟩ := opportunities index (by omega) nonempty
      obtain ⟨chosen,found⟩ := an_actual_menu_opportunity_forces_a_selected_service vocabulary law origin past scope value current task registered offered
      have decrease := selected_service_strictly_reduces_joint_delivery_debt vocabulary law origin past scope value contract
       current (external index current) chosen found
      change (pending vocabulary law origin past scope value
       (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+1))).card<_ at decrease
      exact Or.inr (by rcases previous with previous | previous <;> omega)
 apply Finset.card_eq_zero.mp
 have finish := bounded debt (Nat.le_refl _)
 dsimp only [debt] at finish
 rcases finish with done | done
 · exact done
 · omega

theorem arbitrary_later_dynamic_controls_cannot_restore_delivery_debt
 (start : JointReceptionSource.State root)
 (external : Nat → JointReceptionSource.State root → RenewableArchiveSource.Command) (index delay : Nat) :
 pending vocabulary law origin past scope value
  (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) ⊆
 pending vocabulary law origin past scope value
  (JointReceptionSource.run vocabulary law origin past scope value contract start external index) := by
 induction delay with
 | zero => exact Finset.Subset.refl _
 | succ delay ih =>
   exact Finset.Subset.trans
    (every_actual_command_can_only_reduce_the_original_delivery_debt vocabulary law origin past scope value contract
     (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay))
     (command vocabulary law origin past scope value
      (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay))
      (external (index+delay) (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay))))) ih

theorem recurrent_actual_menu_opportunities_generate_finite_joint_completion
 (start : JointReceptionSource.State root)
 (external : Nat → JointReceptionSource.State root → RenewableArchiveSource.Command)
 (opportunities : ∀ index,
  (pending vocabulary law origin past scope value
   (JointReceptionSource.run vocabulary law origin past scope value contract start external index)).Nonempty →
  ∃ delay task, task∈menu (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) ∧
   offer vocabulary law origin past scope value
    (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) task=true) :
 ∃ index, pending vocabulary law origin past scope value
  (JointReceptionSource.run vocabulary law origin past scope value contract start external index)=∅ := by
 classical
 let debt (index : Nat) := (pending vocabulary law origin past scope value
  (JointReceptionSource.run vocabulary law origin past scope value contract start external index)).card
 have attained : ∃ amount, ∃ index, debt index=amount := ⟨debt 0,0,rfl⟩
 obtain ⟨index,smallest⟩ := Nat.find_spec attained
 by_cases zero : debt index=0
 · exact ⟨index,Finset.card_eq_zero.mp zero⟩
 · have nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero zero)
   obtain ⟨delay,task,registered,offered⟩ := opportunities index nonempty
   obtain ⟨chosen,found⟩ := an_actual_menu_opportunity_forces_a_selected_service vocabulary law origin past scope value
    (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) task registered offered
   have strict := selected_service_strictly_reduces_joint_delivery_debt vocabulary law origin past scope value contract
    (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay))
    (external (index+delay) (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay))) chosen found
   have monotone := Finset.card_le_card
    (arbitrary_later_dynamic_controls_cannot_restore_delivery_debt vocabulary law origin past scope value contract start external index delay)
   have lower : debt (index+delay+1)<Nat.find attained := by
    change debt (index+delay+1)<debt (index+delay) at strict
    change debt (index+delay)≤debt index at monotone
    omega
   exact False.elim ((Nat.find_min attained lower) ⟨index+delay+1,rfl⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionProgress
