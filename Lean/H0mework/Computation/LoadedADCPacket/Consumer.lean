import H0mework.Computation.LoadedADCPacket.Model
import H0mework.Computation.LoadedADCPacket.Recovery
import H0mework.Computation.LoadedADCPacket.Entropy
import H0mework.Computation.LoadedADCInformation.DistortionConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem sourceGeneratedLoadedPacketNextObservation (bound : Nat) (enough : 2 ≤ bound) :
    (∀ actor : Fin (bound + 1),
      type_of% (source_next downstreamTechnology downstreamGraph seed bound actor) ∧
      type_of% (sampleTask_eq_decode_next downstreamTechnology downstreamGraph seed bound actor) ∧
      type_of% (original_transfer_mean downstreamTechnology downstreamGraph seed bound actor) ∧
      type_of% (read_model_next downstreamTechnology downstreamGraph seed bound actor) ∧
      type_of% (sampleVariance_nonnegative downstreamTechnology downstreamGraph seed bound actor)) ∧
    (∀ value, ∀ supported : value ∈ ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).support,
      (∀ next, type_of% (conditionalNext_support downstreamTechnology downstreamGraph seed bound value supported next)) ∧
        type_of% (conditional_model_next downstreamTechnology downstreamGraph seed bound value supported)) ∧
    type_of% (conditionalNext_recombines downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (conditionalEntropy_formula downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (conditionalEntropy_zero_iff downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (original_residual_variance downstreamTechnology downstreamGraph seed bound) ∧
    (∀ decoder, type_of% (original_error_decomposition downstreamTechnology downstreamGraph seed bound decoder)) ∧
    type_of% (next_error_zero downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (joint_transfer_exact downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (current_to_joint_gain downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (next_model downstreamTechnology downstreamGraph seed bound) ∧
    (∀ left right, type_of% (model_history_fibre downstreamTechnology downstreamGraph seed left right)) ∧
    type_of% (four_phase_duration_from_packet downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed bound)) ∧
    (∀ driveDecoder, type_of% (Distortion.sourceGeneratedLoadedHistoryInformationDistortion
      downstreamTechnology downstreamGraph seed bound enough driveDecoder)) :=
  ⟨(fun actor => ⟨source_next downstreamTechnology downstreamGraph seed bound actor,
      sampleTask_eq_decode_next downstreamTechnology downstreamGraph seed bound actor,
      original_transfer_mean downstreamTechnology downstreamGraph seed bound actor,
      read_model_next downstreamTechnology downstreamGraph seed bound actor,
      sampleVariance_nonnegative downstreamTechnology downstreamGraph seed bound actor⟩),
    (fun value supported => ⟨(fun next => conditionalNext_support downstreamTechnology downstreamGraph seed bound value supported next),
      conditional_model_next downstreamTechnology downstreamGraph seed bound value supported⟩),
    conditionalNext_recombines downstreamTechnology downstreamGraph seed bound,
    conditionalEntropy_formula downstreamTechnology downstreamGraph seed bound,
    conditionalEntropy_zero_iff downstreamTechnology downstreamGraph seed bound,
    original_residual_variance downstreamTechnology downstreamGraph seed bound,
    (fun decoder => original_error_decomposition downstreamTechnology downstreamGraph seed bound decoder),
    next_error_zero downstreamTechnology downstreamGraph seed bound,
    joint_transfer_exact downstreamTechnology downstreamGraph seed bound,
    current_to_joint_gain downstreamTechnology downstreamGraph seed bound,
    next_model downstreamTechnology downstreamGraph seed bound,
    (fun left right => model_history_fibre downstreamTechnology downstreamGraph seed left right),
    four_phase_duration_from_packet downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed bound),
    (fun driveDecoder => Distortion.sourceGeneratedLoadedHistoryInformationDistortion
      downstreamTechnology downstreamGraph seed bound enough driveDecoder)⟩

end
end FiniteADCWholeJointCurrent.Information.Packet
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
