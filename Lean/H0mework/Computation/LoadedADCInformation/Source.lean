import H0mework.Physics.ADCRuntime.LoadedReceiverTiming
import H0mework.Realization.OccurrenceCharge.Fold

/-! Every actual loaded phase charges the original complete occurrence tree. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def charge : ℝ :=
  (loadedStepDuration downstreamTechnology downstreamGraph seed).value

theorem charge_pos : 0 < charge downstreamTechnology downstreamGraph seed :=
  lt_of_lt_of_le
    (finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode)
    (loadedStepDuration_ge_tick downstreamTechnology downstreamGraph seed)

def timeRead (material : RootedAccountedUnfolding
    (FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) : ℝ :=
  RootedAccountedUnfolding.SourceCharge.tally (charge downstreamTechnology downstreamGraph) material

theorem timeRead_exposure (frames : Nat) :
    timeRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) =
      loadedElapsed downstreamTechnology downstreamGraph seed frames := by
  induction frames with
  | zero => simp [timeRead, loadedExposure, RootedAccountedUnfolding.observe_zero,
      RootedAccountedUnfolding.SourceCharge.tally, RootedAccountedUnfolding.zero,
      RootedAccountedUnfolding.fold, RootedAccountedUnfolding.foldBranches,
      RootedAccountedUnfolding.SourceCharge.atSource]
  | succ frames induction =>
      change RootedAccountedUnfolding.SourceCharge.tally _
        ((loadedExposure downstreamTechnology downstreamGraph seed frames).advance _) = _
      rw [RootedAccountedUnfolding.SourceCharge.advance, loadedExposure_frontier]
      change timeRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) +
        (charge downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed frames) + 0) = _
      rw [induction, add_zero, loadedElapsed_succ]
      rfl

theorem exposure_injective : Function.Injective (loadedExposure downstreamTechnology downstreamGraph seed) := by
  intro left right same
  apply (loadedElapsed_strictMono downstreamTechnology downstreamGraph seed).injective
  rw [← timeRead_exposure downstreamTechnology downstreamGraph seed left,
    ← timeRead_exposure downstreamTechnology downstreamGraph seed right, same]

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
