import H0mework.Computation.LoadedADCPacket.CapacitySource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Capacity

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem decoder_eventually_fails (epsilon : ℝ) :
    ∃ first : Nat, ∀ bound ≥ first,
      ∀ decoder : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) → ℂ,
        epsilon ^ 2 < error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
          (timeTask downstreamTechnology downstreamGraph seed bound) decoder := by
  let count : ℝ := (2 : ℝ) ^ packetBits (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
  let scale : ℝ := Distortion.tick (hardware := hardware)
  have countPositive : 0 < count := by positivity
  have scalePositive : 0 < scale := Distortion.tick_pos
  have squarePositive : 0 < scale ^ 2 := sq_pos_of_pos scalePositive
  have toleranceNonnegative : 0 ≤ 12 * epsilon ^ 2 / scale ^ 2 := by positivity
  obtain ⟨first, exceeds⟩ := exists_nat_gt (count * (2 + 12 * epsilon ^ 2 / scale ^ 2))
  refine ⟨first, ?_⟩
  intro bound after decoder
  have castAfter : (first : ℝ) ≤ bound := by exact_mod_cast after
  have ratioLarge : 2 + 12 * epsilon ^ 2 / scale ^ 2 < (bound + 1 : ℝ) / count := by
    apply (lt_div_iff₀ countPositive).mpr
    nlinarith only [exceeds, castAfter]
  have gap : 12 * epsilon ^ 2 / scale ^ 2 < ((bound + 1 : ℝ) / count) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((bound + 1 : ℝ) / count - 1)]
  have scaled := mul_lt_mul_of_pos_left gap (div_pos squarePositive (by norm_num : (0 : ℝ) < 12))
  have exactCost : scale ^ 2 / 12 * (12 * epsilon ^ 2 / scale ^ 2) = epsilon ^ 2 := by
    field_simp [squarePositive.ne']
  rw [exactCost] at scaled
  exact scaled.trans_le (decoder_capacity_lower downstreamTechnology downstreamGraph seed bound decoder)

end
end FiniteADCWholeJointCurrent.Information.Packet.Capacity
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
