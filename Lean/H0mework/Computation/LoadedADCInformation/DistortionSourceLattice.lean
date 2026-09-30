import H0mework.Probability.Information.Lattice
import H0mework.Computation.LoadedADCInformation.DistortionFibres

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

noncomputable section

export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceUniformFibreVariance.Lattice
  (index_sum index_square_sum index_pair_square_sum lattice_pair_square_sum)

theorem fibre_index_pair_square_sum (bound : Nat) (side : Fin 2) :
    (∑ left ∈ fibre bound side, ∑ right ∈ fibre bound side,
      ((right.val : ℝ) - (left.val : ℝ)) ^ 2) =
      (2 / 3 : ℝ) * (phaseCount bound side : ℝ) ^ 2 * ((phaseCount bound side : ℝ) ^ 2 - 1) := by
  rw [sum_fibre]
  simp_rw [sum_fibre]
  simp only [phaseIndex_val, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  exact lattice_pair_square_sum (phaseCount bound side) (side.val : ℝ)

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
