import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Consume
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.History
open private Consume.State.mk in Consume.arrival

structure Execution (larger : Bool) where
  private mk ::
  input : EnergyRenewal.Privacy.SourceInput
  state : Consume.State (input.plan larger)

/-- The only initializer replays the original source; caller balances are never accepted. -/
def restore (larger : Bool) (source : Lean.Json) (events : List Consume.Event) : Except String (Execution larger) := do
  let original ← Productive.Wire.execute larger source
  let first : Consume.State (original.input.plan larger) := Consume.State.mk original.state false
  return ⟨original.input,events.foldl Consume.step first⟩

theorem every_restored_suffix_keeps_the_source_consumed {plan : Plan} (state : Consume.State plan)
    (spent : state.spent=true) (events : List Consume.Event) :
    (events.foldl Consume.step state).spent=true :=
  Consume.every_future_suffix_keeps_consumed_source state spent events
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.History
