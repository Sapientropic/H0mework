import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Continuation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

def deliveryRun (lane : Lane) (state : State) :=
  Financial.Family.continueVisits_run Finance.sources (input lane state.origin.scope state.raw) 0 2 state.delivery

theorem every_original_delivery_archive_survives_settlement (lane : Lane) (state : State) (index : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : state.delivery.current.slots[index]?=some (.terminal archive)) :
    (next lane state).delivery.current.slots[index]?=some (.terminal archive) := by
  let migrated := Financial.Family.Migration.follow Finance.sources (deliveryRun lane state) index (.terminal archive) present
  have unchanged := migrated.path.terminal_is_unchanged Finance.sources
  exact migrated.present.trans (congrArg some unchanged)

namespace Root

def replenishDeliveryRun (state : State) :
    (Financial.Family.process Finance.sources).Run state.delivery.current (replenish state).delivery.current := by
  unfold replenish
  split
  · exact .nil
  · exact Financial.Family.continueVisits_run _ _ _ _ _

def advanceDeliveryRun (state : State) :
    (Financial.Family.process Finance.sources).Run state.delivery.current (advance state).delivery.current :=
  (replenishDeliveryRun state).concatRuns _
    (Synthesis.transition Production.code (serviceState (replenish state)))

def futureDeliveryRun (state : State) : (count : Nat) →
    (Financial.Family.process Finance.sources).Run state.delivery.current (run state count).delivery.current
  | 0 => .nil
  | count+1 => (futureDeliveryRun state count).concatRuns _ (advanceDeliveryRun (run state count))

theorem all_future_prefixes_keep_every_original_delivery_archive (state : State) (count index : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : state.delivery.current.slots[index]?=some (.terminal archive)) :
    (run state count).delivery.current.slots[index]?=some (.terminal archive) := by
  let migrated := Financial.Family.Migration.follow Finance.sources (futureDeliveryRun state count) index (.terminal archive) present
  have unchanged := migrated.path.terminal_is_unchanged Finance.sources
  exact migrated.present.trans (congrArg some unchanged)

end Root
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement
