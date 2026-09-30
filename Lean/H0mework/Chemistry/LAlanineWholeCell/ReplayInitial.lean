import H0mework.Chemistry.LAlanineWholeCell.PartitionGeometry
import H0mework.Chemistry.LAlanineContinuousSource.CellGeometry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceGaussianModel SourceSignedEvaluator WholeCellPartition SourceCellGeometry
open ContinuousParameterMap ContinuousSeed IntervalParameterMap

noncomputable section

/-- The seed and its derivative use only alpha/v; the old certificate's unused time coordinate is retained here. -/
def seedParameter (p : Point) : Point := ![p 0, p 1, (cellLowerQ 2 : ℝ)]

theorem seedParameter_inside (p : Point) (inside : p ∈ fullDomain) : seedParameter p ∈ cellDomain := by
  constructor
  · intro axis
    fin_cases axis
    · exact inside.1 0
    · exact inside.1 1
    · exact le_rfl
  · intro axis
    fin_cases axis
    · exact inside.2 0
    · exact inside.2 1
    · exact Rat.cast_le.mpr (cell_ordered 2).le

theorem initialMap_same_seed (p : Point) : initialMap 0 4 (seedParameter p) = initialMap 0 4 p := rfl
theorem initialDerivative_same_seed (p : Point) :
    bandSeedDerivative 4 (Geometry.Source.epsilon 0) (seedParameter p) =
      bandSeedDerivative 4 (Geometry.Source.epsilon 0) p := rfl

theorem full_initial_jet (p : Point) (inside : p ∈ fullDomain) :
    JetHolds initialJetBox (initialMap 0 4 p) (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p) := by
  have paid := cell_initial_jet (seedParameter p) (seedParameter_inside p inside)
  simpa only [initialMap_same_seed, initialDerivative_same_seed] using paid

def stepSizeInterval (q : Quarter) : Pair :=
  mul (point (1 / (stepCount 0 : ℚ))) (quarterLowerQ q 2, quarterUpperQ q 2)

theorem quarter_step_size (q : Quarter) (p : Point) (inside : p ∈ quarterDomain q) :
    Holds (stepSizeInterval q) (parameterTimeLinear 0 p) := by
  have input : Holds (quarterLowerQ q 2, quarterUpperQ q 2) (p 2) := ⟨inside.1 2, inside.2 2⟩
  have bound := mul_holds _ _ _ _ (point_holds (1 / (stepCount 0 : ℚ))) input
  rw [parameterTime_readout]
  simpa only [stepSizeInterval, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    one_div_mul_eq_div] using bound

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
