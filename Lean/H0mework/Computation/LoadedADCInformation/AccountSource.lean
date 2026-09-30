import H0mework.Realization.OccurrenceCharge.Model
import H0mework.Realization.OccurrenceCharge.Faces
import H0mework.Computation.LoadedADCInformation.Consumer

/-! The actual loaded current and all three account faces execute the generated incremental source action. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.AccountAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceOwnedObservationHistory
open RootedAccountedUnfolding.SourceCharge

def phaseCharge : ℝ × ℝ × ℝ :=
  ((loadedStepDuration downstreamTechnology downstreamGraph seed).value,
    (loadedStepWork downstreamTechnology downstreamGraph seed).value,
    (loadedStepHeat downstreamTechnology downstreamGraph seed).value)

def stateRead (bound : Nat) :=
  (sourcePoint (loadedAfter downstreamTechnology downstreamGraph seed bound),
    timeRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed bound),
    workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed bound),
    heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed bound))

theorem stateRead_is_retained (bound : Nat) :
    SourceAccountedAction.retained (phaseCharge downstreamTechnology downstreamGraph)
      (loadedExposure downstreamTechnology downstreamGraph seed bound) =
        stateRead downstreamTechnology downstreamGraph seed bound := by
  apply Prod.ext
  · simp [SourceAccountedAction.retained, SourceAccountedAction.frontierWord, loadedExposure_frontier, stateRead]
  · apply Prod.ext
    · exact face_tally (AddMonoidHom.fst ℝ (ℝ × ℝ))
        (phaseCharge downstreamTechnology downstreamGraph) _
    · apply Prod.ext
      · exact face_tally ((AddMonoidHom.fst ℝ ℝ).comp (AddMonoidHom.snd ℝ (ℝ × ℝ)))
          (phaseCharge downstreamTechnology downstreamGraph) _
      · exact face_tally ((AddMonoidHom.snd ℝ ℝ).comp (AddMonoidHom.snd ℝ (ℝ × ℝ)))
          (phaseCharge downstreamTechnology downstreamGraph) _

theorem incremental_next (bound : Nat) :
    SourceAccountedAction.update (loadedStep downstreamTechnology downstreamGraph)
      (phaseCharge downstreamTechnology downstreamGraph) (stateRead downstreamTechnology downstreamGraph seed bound) =
        stateRead downstreamTechnology downstreamGraph seed (bound + 1) := by
  rw [← stateRead_is_retained, ← stateRead_is_retained, SourceAccountedAction.retained_advance]
  rfl

theorem incremental_reads_actual (bound : Nat) :
    stateRead downstreamTechnology downstreamGraph seed bound =
      (sourcePoint (loadedAfter downstreamTechnology downstreamGraph seed bound),
        loadedElapsed downstreamTechnology downstreamGraph seed bound,
        (loadedFiniteWork downstreamTechnology downstreamGraph seed bound).value,
        (loadedFiniteHeat downstreamTechnology downstreamGraph seed bound).value) := by
  simp only [stateRead, timeRead_exposure, workRead_exposure, heatRead_exposure]

end
end FiniteADCWholeJointCurrent.Information.AccountAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
