import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.GeometryTransverse

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandTransverse

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap ContinuousGradient
open WholeBandSource TrueFlowGeometry Matrix
open scoped Matrix
noncomputable section

theorem all_cell1_normal_lower : ∀ (d : Direction) (i : Step),
    1/20 < normalLower (callAt 1 d i .initial) ∧
    1/20 < normalLower (callAt 1 d i .tube) := by
  decide +kernel

theorem actual_cell1_field_transverse (d : Direction) (i : Step) (role : CallRole) (x : Point)
    (actual : FieldHolds (recordedCallField (callAt 1 d i role)) x) :
    (1/20 : ℝ) < seedNormal ⬝ᵥ sourceGradient x := by
  have report : 1/20 < normalLower (callAt 1 d i role) := by
    cases role
    · exact (all_cell1_normal_lower d i).1
    · exact (all_cell1_normal_lower d i).2
  have lifted : (((1/20 : ℚ) : ℝ)) < (normalLower (callAt 1 d i role) : ℝ) :=
    Rat.cast_lt.mpr report
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at lifted
  exact lifted.trans_le (normal_dot_lower _ x actual)

end
end LAlanine40K2025.BasinRefinement.WholeBandTransverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
