import H0mework.Computation.LoadedADCPacket.RecipientRecoveryConditional

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recipient

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open Netlist.Dissipative.Dimensioned.Producer
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped InnerProductSpace

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

variable {β : Type} [DecidableEq β] [Hashable β]
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (seed : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

private theorem mean_square_bound (bound : Nat) (value : Fin (bound + 1) → ℂ)
    (limit : ℝ) (bounded : ∀ actor, ‖value actor‖ ≤ limit) :
    (∑ actor, ((historyPMF bound) actor).toReal * ‖value actor‖ ^ 2) ≤ limit ^ 2 := by
  calc
    _ ≤ ∑ actor, ((historyPMF bound) actor).toReal * limit ^ 2 := by
      apply Finset.sum_le_sum
      intro actor _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have h := bounded actor
      nlinarith [norm_nonneg (value actor)]
    _ = limit ^ 2 := by
      rw [← Finset.sum_mul,
        SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.pmf_sum_toReal,
        one_mul]

theorem voltage_next_recovery_bound (bound : Nat) (channel : FiniteEmbodimentChannel) :
    error (historyPMF bound) (nextPacket downstreamTechnology downstreamGraph seed bound)
      (voltageTask downstreamTechnology downstreamGraph seed bound channel) (voltageDecoder channel) ≤
      ((hardware.meteredSource.fixture.coreSource.2.voltageScale.value +
        (resonantInductorOutputScaleAt
          (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).value) *
        ((1 : ℝ) / 249750)) ^ 2 := by
  rw [voltage_next_decoder_error]
  apply mean_square_bound
  intro actor
  have bounded := (voltageError_bound (loadedStep downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed actor.val)) channel).le
  simpa only [voltageSourceError, Complex.norm_real, Real.norm_eq_abs] using bounded

theorem current_next_recovery_bound (bound : Nat) (channel : FiniteEmbodimentChannel) :
    error (historyPMF bound) (nextPacket downstreamTechnology downstreamGraph seed bound)
      (currentTask downstreamTechnology downstreamGraph seed bound channel) (currentDecoder channel) ≤
      ((hardware.meteredSource.fixture.coreSource.2.voltageScale.value /
        ((compileFiniteDimensionedSeriesRLCNetlistRun
          (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)).seriesResistanceAt channel).value) *
        ((1 : ℝ) / 249750)) ^ 2 := by
  rw [current_next_decoder_error]
  apply mean_square_bound
  intro actor
  have bounded := (currentError_bound (loadedStep downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed actor.val)) channel).le
  simpa only [currentSourceError, Complex.norm_real, Real.norm_eq_abs] using bounded

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
