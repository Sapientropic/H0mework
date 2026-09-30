import H0mework.Probability.Information.Capacity
import H0mework.Computation.LoadedADCPacket.IntervalConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Capacity

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def packetBits : Nat :=
  loadedReceiverInstalledClockBits hardware technology actualBoot + 60 * adcWordBits hardware.adcCode

theorem code_card :
    Fintype.card (Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) =
      2 ^ packetBits (hardware := hardware) (actualBoot := actualBoot) (technology := technology) :=
  finiteADCWirePacketFor_card hardware.adcCode (loadedReceiverInstalledClockBits hardware technology actualBoot)

variable {β : Type} [DecidableEq β] [Hashable β]
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def historyInformation (bound : Nat) : ℝ :=
  SourceUniformFibreInformation.conditionalEntropy bound (nowPacket downstreamTechnology downstreamGraph seed bound)

theorem time_separated (bound : Nat) (left right : Fin (bound + 1)) :
    Distortion.tick (hardware := hardware) ^ 2 * ((right.val : ℝ) - (left.val : ℝ)) ^ 2 ≤
      (timeQuery downstreamTechnology downstreamGraph seed bound right -
        timeQuery downstreamTechnology downstreamGraph seed bound left) ^ 2 := by
  rw [timeQuery_generated, timeQuery_generated]
  exact Distortion.time_pair_lower_bound downstreamTechnology downstreamGraph seed left.val right.val

theorem history_information_lower (bound : Nat) :
    Real.log (bound + 1 : ℝ) -
        (packetBits (hardware := hardware) (actualBoot := actualBoot) (technology := technology) : ℝ) * Real.log 2 ≤
      historyInformation downstreamTechnology downstreamGraph seed bound := by
  have generated := SourceUniformFibreInformation.Capacity.information_lower bound
    (nowPacket downstreamTechnology downstreamGraph seed bound)
  rw [code_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at generated
  exact generated

theorem residual_information_lower (bound : Nat) :
    Distortion.tick (hardware := hardware) ^ 2 / 12 *
        (Real.exp (2 * historyInformation downstreamTechnology downstreamGraph seed bound) - 1) ≤
      ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 :=
  SourceUniformFibreVariance.Separation.information_spread bound
    (nowPacket downstreamTechnology downstreamGraph seed bound)
    (timeQuery downstreamTechnology downstreamGraph seed bound) (Distortion.tick (hardware := hardware))
    (time_separated downstreamTechnology downstreamGraph seed bound)

theorem residual_capacity_lower (bound : Nat) :
    Distortion.tick (hardware := hardware) ^ 2 / 12 *
        (((bound + 1 : ℝ) / (2 : ℝ) ^ packetBits (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) ^ 2 - 1) ≤
      ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 := by
  have generated := SourceUniformFibreInformation.Capacity.residual_capacity_lower bound
    (nowPacket downstreamTechnology downstreamGraph seed bound)
    (timeQuery downstreamTechnology downstreamGraph seed bound) (Distortion.tick (hardware := hardware))
    (time_separated downstreamTechnology downstreamGraph seed bound)
  rw [code_card, Nat.cast_pow, Nat.cast_ofNat] at generated
  exact generated

theorem decoder_capacity_lower (bound : Nat)
    (decoder : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) → ℂ) :
    Distortion.tick (hardware := hardware) ^ 2 / 12 *
        (((bound + 1 : ℝ) / (2 : ℝ) ^ packetBits (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) ^ 2 - 1) ≤
      error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder :=
  (residual_capacity_lower downstreamTechnology downstreamGraph seed bound).trans
    (SourceUniformFibreVariance.decoder_lower bound (nowPacket downstreamTechnology downstreamGraph seed bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound) decoder)

theorem time_error_decomposition (bound : Nat)
    (decoder : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) → ℂ) :
    error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
      (timeTask downstreamTechnology downstreamGraph seed bound) decoder =
      ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 +
      error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (fun actor => optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
          (timeTask downstreamTechnology downstreamGraph seed bound)
          (nowPacket downstreamTechnology downstreamGraph seed bound actor)) decoder :=
  SourceWeightedRecovery.residual_decomposition _ _ _ _

end
end FiniteADCWholeJointCurrent.Information.Packet.Capacity
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
