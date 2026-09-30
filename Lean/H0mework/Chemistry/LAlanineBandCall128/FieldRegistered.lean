import H0mework.Chemistry.LAlanineBandCall128.FieldField
import H0mework.Chemistry.LAlanineBandMatrix.Recorded

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Call128

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangleChecks SourceFields

open WholeBandMatrix

/-- The source report is recognized after the original full matrix field is generated. -/
theorem matrix_gradient_report : ∀ axis : Fin 3,
    (calculatedField matrixRows).gradient axis =
      WholeBandSource.callReportedDensity 128 (WholeCellReplay.gradientIndex axis) := by
  intro axis
  fin_cases axis <;> decide +kernel

theorem matrix_hessian_report : ∀ axis direction : Fin 3,
    (calculatedField matrixRows).hessian axis direction =
      WholeBandSource.callReportedDensity 128 (WholeCellReplay.hessianIndex axis direction) := by
  intro axis direction
  fin_cases axis <;> fin_cases direction <;> decide +kernel

theorem actual_field (x : Point) (inside : InRectangle (WholeBandSource.callBox 128) x) :
    IntervalParameterMap.FieldHolds (WholeBandSource.recordedCallField 128) x :=
  recordedCallFieldHolds 128 sourceAO matrixRows matrixCertificate
    (fun j b y hy => actual_orbitals j b y hy)
    matrix_gradient_report matrix_hessian_report x inside

end LAlanine40K2025.BasinRefinement.WholeBandCell2.Call128
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
