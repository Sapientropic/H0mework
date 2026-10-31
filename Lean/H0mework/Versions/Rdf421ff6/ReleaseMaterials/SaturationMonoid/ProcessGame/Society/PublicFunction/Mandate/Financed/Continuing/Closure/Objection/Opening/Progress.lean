import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ} {originInputs inputs : List (List Action)} {original : Claim fuel originInputs}

theorem source_signature_reconfirms_every_old_target (cut : Cut fuel inputs) (tail : List Action)
    (active : Mandate.Response.Active cut.past.frame.raw) (target : Cross.Target original inputs)
    (inside : target.claim.position.ordinal < cut.depth + 2) :
    (Cross.readReconfirmation (Cross.transportTarget cut (signedWord tail) target inside)
      (signaturePosition cut tail)).isSome = true := by
  have oldOrdinal := (Response.replacement_preserves_original_item_and_snapshot cut (signedWord tail) target.claim inside).2.2.1
  have actualPosition := Response.read_position _ _ (signature_is_actually_read cut tail active)
  have later : Later fuel (branchInputs cut (signedWord tail))
      (Cross.transportTarget cut (signedWord tail) target inside).claim.position (signature cut tail active).position := by
    apply Or.inl
    change (Response.replacement cut (signedWord tail) target.claim inside).position.ordinal < _
    rw [oldOrdinal, actualPosition]
    exact inside
  simp only [Cross.readReconfirmation, signature_is_actually_read cut tail active, dif_pos later]
  rfl

theorem reconfirmation_adds_actual_progress {laterInputs : List (List Action)}
    (target : Cross.Target original laterInputs) (state : (Cross.process original).GeneratedState)
    (slots : state.current.slots = [.live (Cross.tracked target)])
    (position : Position fuel laterInputs) (receipt : Cross.Reconfirmation target)
    (renewed : Cross.readReconfirmation target position = some receipt) :
    ((Cross.History.pending target state slots).receive position).state.current.history.map LifecycleEvent.kind =
      state.current.history.map LifecycleEvent.kind ++ [.progressed] := by
  simp only [Cross.History.receive, renewed, Cross.History.state,
    NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
    List.map_append, List.map_cons, List.map_nil]
  rfl

theorem transported_pending_history_gains_source_progress (cut : Cut fuel inputs) (tail : List Action)
    (active : Mandate.Response.Active cut.past.frame.raw) (target : Cross.Target original inputs)
    (state : (Cross.process original).GeneratedState)
    (slots : state.current.slots = [.live (Cross.tracked target)])
    (inside : target.claim.position.ordinal < cut.depth + 2) :
    ((Cross.transportHistory cut (signedWord tail) (.pending target state slots) inside).receive
      (signaturePosition cut tail)).state.current.history.map LifecycleEvent.kind =
      state.current.history.map LifecycleEvent.kind ++ [.progressed] := by
  let next := Cross.transportTarget cut (signedWord tail) target inside
  have same : Cross.tracked next = Cross.tracked target :=
    congrArg (fun residual : State Bool Unit => { obligation fuel originInputs original with residual := residual })
      (Cross.transported_target_keeps_snapshot cut (signedWord tail) target inside)
  have nextSlots := slots.trans (congrArg (fun obligation => [ObligationSlot.live obligation]) same).symm
  have found := source_signature_reconfirms_every_old_target cut tail active target inside
  let receipt := (Cross.readReconfirmation next (signaturePosition cut tail)).get found
  have renewed : Cross.readReconfirmation next (signaturePosition cut tail) = some receipt := (Option.some_get found).symm
  exact reconfirmation_adds_actual_progress next state nextSlots (signaturePosition cut tail) receipt renewed

private theorem pending_history_gains_source_progress (cut : Cut fuel inputs) (tail : List Action)
    (active : Mandate.Response.Active cut.past.frame.raw) (history : Cross.History original inputs)
    (within : history.Within (cut.depth + 2)) (pending : history.isPending = true) :
    ((Cross.transportHistory cut (signedWord tail) history within).receive (signaturePosition cut tail)).state.current.history.map LifecycleEvent.kind =
      history.state.current.history.map LifecycleEvent.kind ++ [.progressed] := by
  cases history with
  | closed state archive slots => cases pending
  | pending target state slots =>
    exact transported_pending_history_gains_source_progress cut tail active target state slots within

theorem every_pending_thread_gains_progress_in_the_actual_word (cut : Cut fuel inputs)
    (tail : List Action) (active : Mandate.Response.Active cut.past.frame.raw)
    (thread : Joint.Thread ⟨originInputs, original⟩ cut) (pending : thread.history.isPending = true) :
    (thread.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      ((thread.transport (signedWord tail)).fold (Joint.actualEvents cut (signedWord tail))).history.state.current.history.map LifecycleEvent.kind := by
  let inventory := Joint.initial cut
  let index : Fin (Joint.actualEvents cut (signedWord tail)).length := ⟨0, (firstIndex inventory tail).isLt⟩
  let first := (Joint.actualEvents cut (signedWord tail)).get index
  have position : first.val = signaturePosition cut tail := first_event_is_the_signature_position inventory tail
  have progress : ((thread.transport (signedWord tail)).receive first).history.state.current.history.map LifecycleEvent.kind =
      thread.history.state.current.history.map LifecycleEvent.kind ++ [.progressed] := by
    change ((Cross.transportHistory cut (signedWord tail) thread.history thread.within).receive first.val).state.current.history.map LifecycleEvent.kind = _
    rw [position]
    exact pending_history_gains_source_progress cut tail active thread.history thread.within pending
  have split : Joint.actualEvents cut (signedWord tail) =
      first :: (Joint.actualEvents cut (signedWord tail)).drop 1 := by
    have decomposition : Joint.actualEvents cut (signedWord tail) =
        (Joint.actualEvents cut (signedWord tail)).take index.val ++
          (Joint.actualEvents cut (signedWord tail)).get index ::
            (Joint.actualEvents cut (signedWord tail)).drop (index.val + 1) := by
      rw [List.cons_get_drop_succ, List.take_append_drop]
    simpa only [index, List.take_zero, List.nil_append, Nat.zero_add] using decomposition
  rw [split]
  change _ <+: (((thread.transport (signedWord tail)).receive first).fold _).history.state.current.history.map LifecycleEvent.kind
  rw [((thread.transport (signedWord tail)).receive first).foldRun _ |>.history_eq, List.map_append, progress]
  exact List.prefix_append _ _

theorem every_carried_pending_row_keeps_its_source_progress (inventory : Joint.Inventory fuel)
    (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) (pending : row.isPending = true) :
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (Joint.carry inventory (emit inventory) row inside).thread.history.state.current.history.map LifecycleEvent.kind := by
  rw [(Joint.carry inventory (emit inventory) row inside).exact_thread, active_emission inventory active]
  exact every_pending_thread_gains_progress_in_the_actual_word inventory.cut
    (suffix inventory.cut.past.frame.raw) active row.2 pending

theorem active_pending_native_state_cannot_be_a_self_loop (inventory : Joint.Inventory fuel)
    (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) (pending : row.isPending = true) :
    row.2.history.state.current ≠ (Joint.carry inventory (emit inventory) row inside).thread.history.state.current := by
  have larger := (every_carried_pending_row_keeps_its_source_progress inventory row inside active pending).length_le
  simp only [List.length_append, List.length_map, List.length_singleton] at larger
  intro same
  have lengths := congrArg (fun state : ResponsibilityState (V fuel row.1.1) => state.history.length) same
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
