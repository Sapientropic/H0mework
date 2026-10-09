import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMatrix.Soundness
import H0mework.Versions.AB.Chemistry.LAlanineBandSource.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandMatrix

open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceFields WholeBandSource
open IntervalParameterMap
noncomputable section

theorem recordedCallFieldHolds (c : FullBandCall) (AO : LowJet → Basis → Pair) (rows : Rows)
    (calculation : RowsCertificate rows AO) (ao_contains : AOContains (callBox c) AO)
    (gradient_eq : ∀ axis, (calculatedField rows).gradient axis =
      callReportedDensity c (WholeCellReplay.gradientIndex axis))
    (hessian_eq : ∀ axis direction, (calculatedField rows).hessian axis direction =
      callReportedDensity c (WholeCellReplay.hessianIndex axis direction))
    (x : Point) (inside : InRectangle (callBox c) x) : FieldHolds (recordedCallField c) x :=
  recorded_fieldHolds (callBox c) AO rows calculation ao_contains (recordedCallField c)
    gradient_eq hessian_eq x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
