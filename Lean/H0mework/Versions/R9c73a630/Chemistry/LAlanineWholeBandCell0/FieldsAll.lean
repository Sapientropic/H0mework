import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.FieldsDirection0
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.FieldsDirection1

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Fields

open WholeBandSource SourceGaussianModel SourceSignedEvaluator IntervalParameterMap

theorem all_actual_fields (d : Direction) (i : Step) (role : CallRole) (x : Point)
    (inside : InRectangle (callBox (callAt 0 d i role)) x) :
    FieldHolds (recordedCallField (callAt 0 d i role)) x := by
  fin_cases d
  · exact direction0_actual_field i role x inside
  · exact direction1_actual_field i role x inside

end LAlanine40K2025.BasinRefinement.WholeBandCell0Fields
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
