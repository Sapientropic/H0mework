import H0mework.Chemistry.LAlanineBandCall128.FieldMatrixRemainingRows
import H0mework.Chemistry.LAlanineBandCall128.FieldCache

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Call128

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangleChecks SourceFields

open WholeBandMatrix

assembleWholeBandMatrix

/-- The full D3 calculation supplies actual g/H before any report recognition. -/
theorem calculated_field_holds (x : Point)
    (inside : InRectangle (WholeBandSource.callBox 128) x) :
    IntervalParameterMap.FieldHolds (calculatedField matrixRows) x :=
  fieldHolds_of_rows (WholeBandSource.callBox 128) sourceAO matrixRows matrixCertificate
    (fun j b y hy => actual_orbitals j b y hy) x inside

end LAlanine40K2025.BasinRefinement.WholeBandCell2.Call128
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
