import H0mework.Computation.LoadedADCInformation.Projection
import H0mework.Probability.Runtime.History
import H0mework.Probability.Recovery.Fibre
import H0mework.Probability.Recovery.Error

/-! The old empirical source weights and complete conditional transfer consume the original ADC history. -/

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

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

def query (bound : Nat) (point : Fin (bound + 1)) : FiniteBinaryDrive :=
  driveAt downstreamTechnology downstreamGraph seed point.val

def materialQuery (bound : Nat) (point : Fin (bound + 1)) :=
  loadedExposure downstreamTechnology downstreamGraph seed point.val

def timeQuery (bound : Nat) (point : Fin (bound + 1)) : ℝ :=
  timeRead downstreamTechnology downstreamGraph (materialQuery downstreamTechnology downstreamGraph seed bound point)

def timeTask (bound : Nat) (point : Fin (bound + 1)) : ℂ :=
  timeQuery downstreamTechnology downstreamGraph seed bound point

theorem timeQuery_generated (bound : Nat) (point : Fin (bound + 1)) :
    timeQuery downstreamTechnology downstreamGraph seed bound point =
      loadedElapsed downstreamTechnology downstreamGraph seed point.val :=
  timeRead_exposure downstreamTechnology downstreamGraph seed point.val

theorem timeQuery_injective (bound : Nat) :
    Function.Injective (timeQuery downstreamTechnology downstreamGraph seed bound) := by
  intro left right same
  apply Fin.ext
  apply (loadedElapsed_strictMono downstreamTechnology downstreamGraph seed).injective
  simpa only [timeQuery_generated] using same

theorem history_weight_positive (bound : Nat) (point : Fin (bound + 1)) :
    historyPMF bound point ≠ 0 := by
  simp [historyPMF_apply]

theorem history_weight (bound : Nat) (point : Fin (bound + 1)) :
    (historyPMF bound point).toReal = 1 / (bound + 1 : ℝ) := by
  rw [historyPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp [one_div]

theorem time_conditional (bound : Nat) (point : Fin (bound + 1)) :
    SourceConditionalHistory.conditional (historyPMF bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound point)
      (observed_supported _ _ point (history_weight_positive bound point)) = PMF.pure point :=
  ObservationRefinement.conditional_injective _ _
    (timeQuery_injective downstreamTechnology downstreamGraph seed bound) point (history_weight_positive bound point)

theorem time_recovers (bound : Nat) (task : Fin (bound + 1) → ℂ) (point : Fin (bound + 1)) :
    optimalDecoder (historyPMF bound) (timeQuery downstreamTechnology downstreamGraph seed bound) task
      (timeQuery downstreamTechnology downstreamGraph seed bound point) = task point :=
  ObservationRefinement.optimum_injective _ _
    (timeQuery_injective downstreamTechnology downstreamGraph seed bound) task point (history_weight_positive bound point)

theorem time_error_zero (bound : Nat) (task : Fin (bound + 1) → ℂ) :
    error (historyPMF bound) (timeQuery downstreamTechnology downstreamGraph seed bound) task
      (optimalDecoder (historyPMF bound) (timeQuery downstreamTechnology downstreamGraph seed bound) task) = 0 := by
  simp [error, time_recovers]

theorem drive_error_equation (bound : Nat) (task : Fin (bound + 1) → ℂ) (decoder : FiniteBinaryDrive → ℂ) :
    error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound) task decoder =
      ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) task)‖ ^ 2 +
      error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (fun point => conditionalMean (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound) task
          (query downstreamTechnology downstreamGraph seed bound point)
          (observed_supported _ _ point (history_weight_positive bound point))) decoder := by
  rw [residual_decomposition]
  congr 2
  funext point
  exact optimal_is_conditional _ _ _ _ _

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
