import H0mework.Physics.ADCRuntime.LoadedConditionalActionRegression
import H0mework.Computation.LoadedADCInformation.ConditionalActionFeedback

/-! Complete conditional source dynamics and their retained loss reach the old whole-account next consumer. -/

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

open SourceOwnedObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

theorem conditional_information_consumed (bound : Nat) (enough : 2 ≤ bound)
    (decoder : FiniteBinaryDrive → ℂ) :
    let first : Fin (bound + 1) := ⟨0, Nat.succ_pos bound⟩
    let supported := query_supported downstreamTechnology downstreamGraph seed bound first
    type_of% (conditional_next downstreamTechnology downstreamGraph seed bound
      (sourcePoint (driveAt downstreamTechnology downstreamGraph seed 0)) supported) ∧
    type_of% (sourceLaw_next downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (next_support_owned downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (conditional_recombines_next downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (conditional_next_not_pure downstreamTechnology downstreamGraph seed bound enough supported) ∧
    type_of% (futureTime_actual downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (time_source_update downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (conditional_time_update downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (residual_time_update downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (next_time_lower_bound downstreamTechnology downstreamGraph seed bound enough decoder) ∧
    type_of% (next_time_error_positive downstreamTechnology downstreamGraph seed bound enough decoder) ∧
    type_of% (IsometricRetainedTransfer.pullback_transfer_add_residual
      (pullback (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound))
      (taskValue (historyPMF bound) (futureTime downstreamTechnology downstreamGraph seed bound))) ∧
    type_of% (AccountAction.incremental_information_consumed downstreamTechnology downstreamGraph seed bound enough
      (futureTime downstreamTechnology downstreamGraph seed bound) decoder) := by
  let first : Fin (bound + 1) := ⟨0, Nat.succ_pos bound⟩
  let supported := query_supported downstreamTechnology downstreamGraph seed bound first
  exact ⟨conditional_next downstreamTechnology downstreamGraph seed bound _ supported,
    sourceLaw_next downstreamTechnology downstreamGraph seed bound,
    next_support_owned downstreamTechnology downstreamGraph seed bound,
    conditional_recombines_next downstreamTechnology downstreamGraph seed bound,
    conditional_next_not_pure downstreamTechnology downstreamGraph seed bound enough supported,
    futureTime_actual downstreamTechnology downstreamGraph seed bound,
    time_source_update downstreamTechnology downstreamGraph seed bound,
    conditional_time_update downstreamTechnology downstreamGraph seed bound,
    residual_time_update downstreamTechnology downstreamGraph seed bound,
    next_time_lower_bound downstreamTechnology downstreamGraph seed bound enough decoder,
    next_time_error_positive downstreamTechnology downstreamGraph seed bound enough decoder,
    IsometricRetainedTransfer.pullback_transfer_add_residual _ _,
    AccountAction.incremental_information_consumed downstreamTechnology downstreamGraph seed bound enough
      (futureTime downstreamTechnology downstreamGraph seed bound) decoder⟩

end
end FiniteADCWholeJointCurrent.Information.ConditionalAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
