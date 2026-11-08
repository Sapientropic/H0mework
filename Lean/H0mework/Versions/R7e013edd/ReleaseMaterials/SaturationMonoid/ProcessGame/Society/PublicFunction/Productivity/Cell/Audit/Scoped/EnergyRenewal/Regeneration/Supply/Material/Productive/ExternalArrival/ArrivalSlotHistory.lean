import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.FinancialProjection

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalSlotHistory
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open EnergyRenewal.Privacy (ResultRel)

theorem supply_play_generates_equal_slot_counts {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session)
    (slots : left.account.current.slots.length = right.account.current.slots.length)
    (render : Supply.Privacy.Render) (strategy : Supply.Privacy.Strategy) (count : Nat) :
    (Supply.Privacy.play left render strategy count).1.account.current.slots.length =
      (Supply.Privacy.play right render strategy count).1.account.current.slots.length := by
  induction count with
  | zero => exact slots
  | succ n ih =>
    have prior := Supply.Privacy.cumulative_related_own_states_and_complete_output left right same render strategy n
    simp only [Supply.Privacy.play, ← prior.2]
    cases requested : (strategy (Supply.Privacy.play left render strategy n).2 n).request with
    | error _ => simpa only [Supply.Privacy.advance, requested] using ih
    | ok request =>
      simp only [Supply.Privacy.advance, requested]
      rw [FinancialProjection.actual_service_generates_its_public_slot_count,
        FinancialProjection.actual_service_generates_its_public_slot_count, ih, prior.1.reply request.1 request.2]

theorem productive_play_generates_equal_slot_counts {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session)
    (slots : left.account.current.slots.length = right.account.current.slots.length)
    (render : Render) (strategy : Strategy) (count : Nat) :
    (Productive.play left render strategy count).1.account.current.slots.length =
      (Productive.play right render strategy count).1.account.current.slots.length := by
  induction count with
  | zero => exact slots
  | succ n ih =>
    have prior := Productive.cumulative_related_own_states_and_complete_output left right same render strategy n
    simp only [Productive.play, ← prior.2]
    exact FinancialProjection.advance_generates_equal_slot_counts _ _ prior.1 ih _

theorem original_source_generates_the_productive_slot_relation (source : Lean.Json) :
    ResultRel (fun (left : Productive.Wire.Execution false) (right : Productive.Wire.Execution true) =>
      Supply.Privacy.Source.SessionTwin left.state.session right.state.session ∧
        left.state.account.current.slots.length = right.state.account.current.slots.length)
      (Productive.Wire.execute false source) (Productive.Wire.execute true source) := by
  unfold Productive.Wire.execute
  cases parsed : Productive.Wire.decode source with
  | error message => exact .error message
  | ok decoded =>
    simp only [bind, Except.bind]
    have initial := Supply.Privacy.Source.original_source_generates_new_supply_initial_relation decoded.input
    cases left : Supply.Privacy.Source.initial false decoded.input with
    | error message =>
      cases right : Supply.Privacy.Source.initial true decoded.input with
      | error other => rw [left, right] at initial; cases initial; exact .error message
      | ok value => rw [left, right] at initial; cases initial
    | ok first =>
      cases right : Supply.Privacy.Source.initial true decoded.input with
      | error message => rw [left, right] at initial; cases initial
      | ok second =>
        rw [left, right] at initial
        cases initial with
        | ok same =>
          have prior := Supply.Privacy.cumulative_related_own_states_and_complete_output first second same.1
            Supply.Privacy.Wire.render decoded.priorStrategy decoded.prior.size
          have priorSlots := supply_play_generates_equal_slot_counts first second same.1
            (congrArg (fun account : Finance.Account => account.current.slots.length) same.2)
            Supply.Privacy.Wire.render decoded.priorStrategy decoded.prior.size
          have produced := Productive.Wire.complete_adaptive_default_output_and_own_next _ _ prior.1
            decoded.strategy decoded.commands.size
          have producedSlots := productive_play_generates_equal_slot_counts _ _ prior.1 priorSlots
            Productive.Wire.render decoded.strategy decoded.commands.size
          exact .ok ⟨produced.1, producedSlots⟩

structure Related {lp rp : Plan} (left : Consume.State lp) (right : Consume.State rp) : Prop where
  material : ArrivalBisimulation.Related left right
  slots : left.service.account.current.slots.length = right.service.account.current.slots.length

theorem step_related {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (event : Consume.Event) : Related (Consume.step left event) (Consume.step right event) := by
  refine ⟨ArrivalBisimulation.step_related same.material event, ?_⟩
  cases event with
  | arrival quantity =>
    change (Consume.arrival left quantity).service.account.current.slots.length =
      (Consume.arrival right quantity).service.account.current.slots.length
    rw [Consume.original_account_is_preserved, Consume.original_account_is_preserved]
    exact same.slots
  | service command =>
    exact FinancialProjection.advance_generates_equal_slot_counts
      left.service right.service same.material.session same.slots command

theorem advance_related {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (command : Lean.Json) : Related (Wire.advance left command) (Wire.advance right command) := by
  unfold Wire.advance
  cases Wire.eventOfJson command with
  | error _ => exact same
  | ok event => exact step_related same event

theorem every_json_word_generates_the_slot_relation {lp rp : Plan}
    {left : Consume.State lp} {right : Consume.State rp} (same : Related left right) (commands : List Lean.Json) :
    Related (commands.foldl Wire.advance left) (commands.foldl Wire.advance right) := by
  induction commands generalizing left right with
  | nil => exact same
  | cons command rest ih => exact ih (advance_related same command)

theorem the_actual_wire_slot_field_is_equal {lp rp : Plan}
    {left : Consume.State lp} {right : Consume.State rp} (same : Related left right) :
    (Wire.account left).getObjVal? "slots" = (Wire.account right).getObjVal? "slots" := by
  change Except.ok (Lean.toJson left.service.account.current.slots.length) =
    Except.ok (Lean.toJson right.service.account.current.slots.length)
  rw [same.slots]

theorem original_source_generates_the_arrival_slot_relation (source : Lean.Json) :
    ResultRel (fun (left : History.Execution false) (right : History.Execution true) => Related left.state right.state)
      (History.restore false source []) (History.restore true source []) := by
  have original := original_source_generates_the_productive_slot_relation source
  unfold History.restore
  cases left : Productive.Wire.execute false source with
  | error message =>
    cases right : Productive.Wire.execute true source with
    | error other => rw [left, right] at original; cases original; exact .error message
    | ok value => rw [left, right] at original; cases original
  | ok first =>
    cases right : Productive.Wire.execute true source with
    | error message => rw [left, right] at original; cases original
    | ok second =>
      rw [left, right] at original
      cases original with
      | ok same => exact .ok ⟨⟨same.1, rfl⟩, same.2⟩

def slotOutput (larger : Bool) (source : Lean.Json) (commands : List Lean.Json) : Except String Nat :=
  (History.restore larger source []).map fun first =>
    (commands.foldl Wire.advance first.state).service.account.current.slots.length

theorem the_original_source_generates_equal_wire_slot_outputs (source : Lean.Json) (commands : List Lean.Json) :
    slotOutput false source commands = slotOutput true source commands := by
  have original := original_source_generates_the_arrival_slot_relation source
  unfold slotOutput
  cases left : History.restore false source [] with
  | error message =>
    cases right : History.restore true source [] with
    | error other => rw [left, right] at original; cases original; rfl
    | ok value => rw [left, right] at original; cases original
  | ok first =>
    cases right : History.restore true source [] with
    | error message => rw [left, right] at original; cases original
    | ok second =>
      rw [left, right] at original
      cases original with
      | ok same => exact congrArg Except.ok (every_json_word_generates_the_slot_relation same commands).slots

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalSlotHistory
