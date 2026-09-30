import H0mework.Computation.LoadedADCInformation.DistortionInformation
import H0mework.Computation.LoadedADCInformation.DistortionFuture

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped Classical InnerProductSpace
noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem compression_eventually_fails (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) :
    ∃ first : Nat, ∀ bound : Nat, first ≤ bound → ∀ decoder : FiniteBinaryDrive → ℂ,
      epsilon ^ 2 < error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder := by
  obtain ⟨first, large⟩ := gridBase_eventually_exceeds (hardware := hardware) epsilon nonnegative
  exact ⟨first, fun bound later decoder => (large bound later).trans_le
    (decoder_grid_lower downstreamTechnology downstreamGraph seed bound decoder)⟩

theorem information_future_decoder_bound (bound : Nat) (decoder : (Nat → FiniteBinaryDrive) → ℂ) :
    tick (hardware := hardware) ^ 2 / 3 *
      (Real.exp (2 * historyInformation downstreamTechnology downstreamGraph seed bound) - 1) ≤
      error (historyPMF bound) (futureQuery downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder := by
  rw [future_error_is_current]
  exact information_decoder_bound downstreamTechnology downstreamGraph seed bound _

theorem residual_next_energy (bound : Nat) :
    ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (ConditionalAction.futureTime downstreamTechnology downstreamGraph seed bound))‖ ^ 2 =
      gridBase (hardware := hardware) bound + actualExcess downstreamTechnology downstreamGraph seed bound +
        2 * Complex.re (inner ℂ
          (residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
            (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound)))
          (residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
            (taskValue (historyPMF bound) (ConditionalAction.timeCharge downstreamTechnology downstreamGraph seed bound)))) +
        ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
          (taskValue (historyPMF bound) (ConditionalAction.timeCharge downstreamTechnology downstreamGraph seed bound))‖ ^ 2 := by
  rw [ConditionalAction.residual_time_update, norm_add_sq (𝕜 := ℂ), residual_physical]
  rfl

theorem sourceGeneratedLoadedHistoryInformationDistortion (bound : Nat) (enough : 2 ≤ bound)
    (decoder : FiniteBinaryDrive → ℂ) :
    type_of% (historyInformation_formula downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (residual_physical downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (actualExcess_nonnegative downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (information_decoder_bound downstreamTechnology downstreamGraph seed bound decoder) ∧
      (∀ futureDecoder, type_of% (information_future_decoder_bound downstreamTechnology downstreamGraph seed bound futureDecoder)) ∧
      (∀ epsilon, ∀ nonnegative : 0 ≤ epsilon,
        type_of% (compression_eventually_fails downstreamTechnology downstreamGraph seed epsilon nonnegative) ∧
          type_of% (future_decoder_eventually_fails downstreamTechnology downstreamGraph seed epsilon nonnegative)) ∧
      type_of% (model_information_zero downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (AccountAction.model_recovery_zero downstreamTechnology downstreamGraph seed bound
        (timeTask downstreamTechnology downstreamGraph seed bound)) ∧
      type_of% (residual_next_energy downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (ConditionalAction.conditional_information_consumed downstreamTechnology downstreamGraph seed bound enough decoder) :=
  ⟨historyInformation_formula downstreamTechnology downstreamGraph seed bound,
    residual_physical downstreamTechnology downstreamGraph seed bound,
    actualExcess_nonnegative downstreamTechnology downstreamGraph seed bound,
    information_decoder_bound downstreamTechnology downstreamGraph seed bound decoder,
    (fun futureDecoder => information_future_decoder_bound downstreamTechnology downstreamGraph seed bound futureDecoder),
    (fun epsilon nonnegative => ⟨compression_eventually_fails downstreamTechnology downstreamGraph seed epsilon nonnegative,
      future_decoder_eventually_fails downstreamTechnology downstreamGraph seed epsilon nonnegative⟩),
    model_information_zero downstreamTechnology downstreamGraph seed bound,
    AccountAction.model_recovery_zero downstreamTechnology downstreamGraph seed bound
      (timeTask downstreamTechnology downstreamGraph seed bound),
    residual_next_energy downstreamTechnology downstreamGraph seed bound,
    ConditionalAction.conditional_information_consumed downstreamTechnology downstreamGraph seed bound enough decoder⟩

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
