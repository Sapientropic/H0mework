import H0mework.Chemistry.LAlanineReentry.ProducerCalculationCommutatorCalculation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.NormCalculation.Commutator.Real

open Propagation.Interface

calculateReentryCommutator real

theorem calculatedRows_exact (i : Basis) : calculatedRealRow i = rowTotals i := by
  fin_cases i
  closeCommutatorCalculations

theorem total_exact : (∑ i : Basis, calculatedRealRow i) = 861484667138722952736 :=
  (Finset.sum_congr rfl (fun i _ => calculatedRows_exact i)).trans (by decide +kernel)

end LAlanine40K2025.Reentry.NormCalculation.Commutator.Real
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
