import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.ArrivalDeliveryLedger
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.ArrivalSlotHistory

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalWirePrivacy
open Lean Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open EnergyRenewal.Privacy (ResultRel)

structure Related {lp rp : Plan} (left : Consume.State lp) (right : Consume.State rp) : Prop where
  slots : ArrivalSlotHistory.Related left right
  leftLedger : ArrivalDeliveryLedger.Tracked left.service
  rightLedger : ArrivalDeliveryLedger.Tracked right.service

theorem advance_related {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (command : Json) : Related (Wire.advance left command) (Wire.advance right command) :=
  ⟨ArrivalSlotHistory.advance_related same.slots command,
    ArrivalDeliveryLedger.wire_advance_is_tracked left same.leftLedger command,
    ArrivalDeliveryLedger.wire_advance_is_tracked right same.rightLedger command⟩

theorem every_json_word_is_related {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (commands : List Json) :
    Related (commands.foldl Wire.advance left) (commands.foldl Wire.advance right) := by
  induction commands generalizing left right with
  | nil => exact same
  | cons command rest ih => exact ih (advance_related same command)

theorem original_source_generates_the_wire_relation (source : Json) :
    ResultRel (fun (left : History.Execution false) (right : History.Execution true) => Related left.state right.state)
      (History.restore false source []) (History.restore true source []) := by
  have original := ArrivalSlotHistory.original_source_generates_the_arrival_slot_relation source
  cases left : History.restore false source [] with
  | error message =>
    cases right : History.restore true source [] with
    | error other => rw [left, right] at original; cases original; exact .error message
    | ok _ => rw [left, right] at original; cases original
  | ok first =>
    cases right : History.restore true source [] with
    | error _ => rw [left, right] at original; cases original
    | ok second =>
      rw [left, right] at original
      cases original with
      | ok same => exact .ok ⟨same,
          ArrivalDeliveryLedger.restored_source_is_tracked false source [] first left,
          ArrivalDeliveryLedger.restored_source_is_tracked true source [] second right⟩

theorem actual_wire_accounts_are_equal {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) : Wire.account left = Wire.account right := by
  have debts : Financial.Family.ledgerClaims Finance.sources left.service.account.current .delivery =
      Financial.Family.ledgerClaims Finance.sources right.service.account.current .delivery :=
    same.leftLedger.delivery.trans ((congrFun same.slots.material.session.current.claims .delivery).trans
      same.rightLedger.delivery.symm)
  simp only [Wire.account, same.slots.slots, debts]

theorem actual_state_json_is_equal {left right : Current} (same : Supply.Privacy.Twin left right) :
    Supply.Privacy.Wire.stateJson left = Supply.Privacy.Wire.stateJson right := by
  have stocks : (actors.flatMap fun actor =>
      (goods.filter fun good => (actor, good) != (receiver, Good.feed)).map fun good =>
        Json.arr #[Supply.Privacy.Wire.actorJson actor, toJson (Supply.Privacy.Wire.goodName good), toJson (toString (left.stock actor good))]) =
      (actors.flatMap fun actor =>
      (goods.filter fun good => (actor, good) != (receiver, Good.feed)).map fun good =>
        Json.arr #[Supply.Privacy.Wire.actorJson actor, toJson (Supply.Privacy.Wire.goodName good), toJson (toString (right.stock actor good))]) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro actor _
    apply List.map_congr_left
    intro good member
    have outside : (actor, good) ≠ (receiver, Good.feed) := by
      intro hidden
      have rejected := (List.mem_filter.mp member).2
      have equalPair : ((actor, good) != (receiver, Good.feed)) = false := by rw [hidden]; rfl
      rw [equalPair] at rejected
      cases rejected
    rw [same.stock actor good outside]
  simp only [Supply.Privacy.Wire.stateJson, same.clock, same.round, same.technology, same.claims, stocks]

theorem actual_wire_replies_are_equal {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (command : Json) : Wire.render left command = Wire.render right command := by
  have next := advance_related same command
  have before := actual_state_json_is_equal same.slots.material.session.current
  have after := actual_state_json_is_equal next.slots.material.session.current
  have source : Consume.sourceCurrent left = Consume.sourceCurrent right := congrArg Packet.current same.slots.material.spent
  have sourceNext : Consume.sourceCurrent (Wire.advance left command) = Consume.sourceCurrent (Wire.advance right command) :=
    congrArg Packet.current next.slots.material.spent
  have account := actual_wire_accounts_are_equal next
  cases parsed : Wire.eventOfJson command with
  | error message =>
    simp only [Wire.render, parsed, before, after, same.slots.material.session.scope,
      next.slots.material.session.scope, source, sourceNext, next.slots.material.spent, account]
  | ok event =>
    cases event with
    | arrival quantity =>
      simp only [Wire.render, parsed, before, after, same.slots.material.session.scope,
        next.slots.material.session.scope, source, sourceNext, same.slots.material.spent, next.slots.material.spent, account]
    | service request =>
      have answer := Productive.answer_public left.service right.service same.slots.material.session request
      simp only [Wire.render, parsed, answer, before, after, same.slots.material.session.scope,
        next.slots.material.session.scope, source, sourceNext, next.slots.material.spent, account]

def accumulate {plan : Plan} (prior : Consume.State plan × List Json) (command : Json) : Consume.State plan × List Json :=
  (Wire.advance prior.1 command, prior.2 ++ [Wire.render prior.1 command])

theorem accumulated_json_words_are_equal {lp rp : Plan}
    (left : Consume.State lp × List Json) (right : Consume.State rp × List Json)
    (same : Related left.1 right.1) (past : left.2 = right.2) (commands : List Json) :
    Related (commands.foldl accumulate left).1 (commands.foldl accumulate right).1 ∧
      (commands.foldl accumulate left).2 = (commands.foldl accumulate right).2 := by
  induction commands generalizing left right with
  | nil => exact ⟨same, past⟩
  | cons command rest ih =>
    exact ih (accumulate left command) (accumulate right command) (advance_related same command)
      (by change left.2 ++ [Wire.render left.1 command] = right.2 ++ [Wire.render right.1 command]
          rw [past, actual_wire_replies_are_equal same command])

theorem original_execute_is_its_exact_fold (larger : Bool) (request source : Json) (commands : Array Json)
    (first : History.Execution larger) (sourceRead : request.getObjVal? "source" = .ok source)
    (eventsRead : request.getObjValAs? (Array Json) "events" = .ok commands)
    (restored : History.restore larger source [] = .ok first) :
    Wire.execute larger request = .ok ⟨first.input,
      (commands.foldl accumulate (first.state, [])).1, (commands.foldl accumulate (first.state, [])).2⟩ := by
  simp only [Wire.execute, sourceRead, eventsRead, restored, bind, Except.bind]
  change (forIn (m := Except String) commands (first.state, []) (fun command prior => pure (.yield (accumulate prior command)))).bind
    (fun result => pure (Wire.Execution.mk first.input result.1 result.2)) = _
  rw [Array.forIn_pure_yield_eq_foldl]
  rfl

theorem complete_original_wire_outputs_are_equal (request : Json) :
    (Wire.execute false request).map Wire.Execution.output =
      (Wire.execute true request).map Wire.Execution.output := by
  cases sourceRead : request.getObjVal? "source" with
  | error _ => simp only [Wire.execute, sourceRead, bind, Except.bind, Except.map]
  | ok source =>
    cases eventsRead : request.getObjValAs? (Array Json) "events" with
    | error _ => simp only [Wire.execute, sourceRead, eventsRead, bind, Except.bind, Except.map]
    | ok commands =>
      have original := original_source_generates_the_wire_relation source
      cases left : History.restore false source [] with
      | error message =>
        cases right : History.restore true source [] with
        | error other =>
          rw [left, right] at original
          cases original
          simp only [Wire.execute, sourceRead, eventsRead, left, right, bind, Except.bind, Except.map]
        | ok _ => rw [left, right] at original; cases original
      | ok first =>
        cases right : History.restore true source [] with
        | error _ => rw [left, right] at original; cases original
        | ok second =>
          rw [left, right] at original
          cases original with
          | ok same =>
            rw [original_execute_is_its_exact_fold false request source commands first sourceRead eventsRead left,
              original_execute_is_its_exact_fold true request source commands second sourceRead eventsRead right]
            have words := accumulated_json_words_are_equal (first.state, []) (second.state, []) same rfl commands.toList
            simpa only [Array.foldl_toList, Except.map] using congrArg Except.ok words.2

theorem original_public_readout_is_its_actual_branch (larger : Bool) (request : Json) :
    Wire.publicReadout request = Wire.actual larger request := by
  cases larger with
  | false => rfl
  | true =>
    unfold Wire.publicReadout
    have output (branch : Bool) : Wire.actual branch request =
        ((Wire.execute branch request).map Wire.Execution.output).bind (fun replies =>
          match replies.getLast? with | none => .error "ARRIVAL_EVENT_REQUIRED" | some reply => .ok reply) := by
      unfold Wire.actual
      cases Wire.execute branch request <;> rfl
    rw [output false, output true, complete_original_wire_outputs_are_equal]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalWirePrivacy
