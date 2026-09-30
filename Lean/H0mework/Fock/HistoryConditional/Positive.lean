import H0mework.Fock.HistoryConditional.InverseObservationPacket.Conditional
import H0mework.Fock.CopyGraph.TimeEnergyEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationPacket

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

theorem clock_sample_energy (depth : Nat) (word : List (Fock.Letter depth)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    (∑ phase : Fin ((copyIndex program.1).val + 1),
      ‖packet depth word (SourceCopyGraph.axes 0 1) phase‖ ^ 2) = (program.1 : ℝ)⁻¹ := by
  dsimp only
  rw [packet_source, SourceCopyTimeEnergy.clock_observation_energy, copy_scale _ (SourceCompiledWordOperator.slope_positive _)]

theorem clock_amplification (depth : Nat) (word : List (Fock.Letter depth))
    (nonunit : 1 < (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    (∑ phase : Fin ((copyIndex program.1).val + 1),
      ‖packet depth word (SourceCopyGraph.axes 0 1) phase‖ ^ 2) <
      ‖restore (program.1 - 1) (copyIndex program.1) (packet depth word (SourceCopyGraph.axes 0 1))‖ ^ 2 := by
  dsimp only
  rw [recovered, packet_source]
  apply SourceCopyTimeEnergy.clock_gap
  change (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1 ≠ 0
  omega

end
end SourceInverseObservationPacket
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
