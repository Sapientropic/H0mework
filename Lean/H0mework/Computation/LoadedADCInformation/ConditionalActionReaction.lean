import H0mework.Computation.LoadedADCInformation.ConditionalActionHistory
import H0mework.Computation.LoadedADCInformation.AccountConsumer

/-! The actual generated account update transports both conditional mean and the complete time residual. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.ConditionalAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

def futureTime (bound : Nat) (point : Fin (bound + 1)) : ℂ :=
  AccountAction.modelTime downstreamTechnology downstreamGraph
    (AccountAction.advanceModel downstreamTechnology downstreamGraph
      (AccountAction.modelAt downstreamTechnology downstreamGraph seed point.val))

def timeCharge (bound : Nat) (point : Fin (bound + 1)) : ℂ :=
  charge downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed point.val)

theorem futureTime_actual (bound : Nat) (point : Fin (bound + 1)) :
    futureTime downstreamTechnology downstreamGraph seed bound point =
      (timeRead downstreamTechnology downstreamGraph
        (loadedExposure downstreamTechnology downstreamGraph seed (point.val + 1)) : ℂ) := by
  unfold futureTime
  rw [AccountAction.next_time_from_model, timeRead_exposure]

theorem time_source_update (bound : Nat) :
    futureTime downstreamTechnology downstreamGraph seed bound =
      timeTask downstreamTechnology downstreamGraph seed bound +
        timeCharge downstreamTechnology downstreamGraph seed bound := by
  funext point
  rw [futureTime_actual]
  change (timeRead downstreamTechnology downstreamGraph
    (loadedExposure downstreamTechnology downstreamGraph seed (point.val + 1)) : ℂ) =
      (timeRead downstreamTechnology downstreamGraph
        (loadedExposure downstreamTechnology downstreamGraph seed point.val) : ℂ) +
      (charge downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed point.val) : ℂ)
  rw [timeRead_exposure, timeRead_exposure, loadedElapsed_succ, Complex.ofReal_add]
  rfl

theorem conditional_time_update (bound : Nat) :
    transfer (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (futureTime downstreamTechnology downstreamGraph seed bound)) =
    transfer (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound)) +
    transfer (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (timeCharge downstreamTechnology downstreamGraph seed bound)) := by
  rw [time_source_update]
  exact (transfer (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)).map_add
    (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))
    (taskValue (historyPMF bound) (timeCharge downstreamTechnology downstreamGraph seed bound))

theorem residual_time_update (bound : Nat) :
    residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (futureTime downstreamTechnology downstreamGraph seed bound)) =
    residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound)) +
    residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (timeCharge downstreamTechnology downstreamGraph seed bound)) := by
  rw [time_source_update]
  exact (residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)).map_add
    (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))
    (taskValue (historyPMF bound) (timeCharge downstreamTechnology downstreamGraph seed bound))

end
end FiniteADCWholeJointCurrent.Information.ConditionalAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
