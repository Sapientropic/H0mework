import H0mework.Computation.LoadedADCPacket.IntervalEnergy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Interval

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

private theorem conditional_mono {Source Observed : Type} [Fintype Source]
    (source : PMF Source) (read : Source → Observed) (left right : Source → ℂ)
    (ordered : ∀ point, (left point).re ≤ (right point).re)
    (value : Observed) (supported : value ∈ (source.map read).support) :
    (conditionalMean source read left value supported).re ≤
      (conditionalMean source read right value supported).re := by
  change Complex.reCLM (∑ point, (SourceConditionalHistory.conditional source read value supported point).toReal • left point) ≤
    Complex.reCLM (∑ point, (SourceConditionalHistory.conditional source read value supported point).toReal • right point)
  simp only [map_sum, map_smul, Complex.reCLM_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro point _
  exact mul_le_mul_of_nonneg_left (ordered point) ENNReal.toReal_nonneg

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def lowerDecoder (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : ℂ :=
  (energyLower packet).value

def upperDecoder (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : ℂ :=
  (energyUpper packet).value

variable {β : Type} [DecidableEq β] [Hashable β]
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def energyTask (bound : Nat) (actor : Fin (bound + 1)) : ℂ :=
  let current := loadedStep downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed actor.val)
  (finiteADCRecipientStoredEnergyAt current.plant current.plant.val.executedDuration).value

theorem conditional_energy_interval (bound : Nat)
    (value : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (supported : value ∈ ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).support) :
    (SourceConditionalNext.mean (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
      (nextPacket downstreamTechnology downstreamGraph seed bound) lowerDecoder value supported).re ≤
        (optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
          (energyTask downstreamTechnology downstreamGraph seed bound) value).re ∧
    (optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
      (energyTask downstreamTechnology downstreamGraph seed bound) value).re ≤
        (SourceConditionalNext.mean (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
          (nextPacket downstreamTechnology downstreamGraph seed bound) upperDecoder value supported).re := by
  rw [SourceConditionalNext.mean_is_conditional, optimal_is_conditional _ _ _ _ supported,
    SourceConditionalNext.mean_is_conditional]
  constructor
  · apply conditional_mono
    intro actor
    exact (energy_interval (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val))).1
  · apply conditional_mono
    intro actor
    exact (energy_interval (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val))).2

end
end FiniteADCWholeJointCurrent.Information.Packet.Interval
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
