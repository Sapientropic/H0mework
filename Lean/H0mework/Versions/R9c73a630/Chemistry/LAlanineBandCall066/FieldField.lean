import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCall066.FieldMatrixRemainingRows
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMatrix.Recorded
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCall066.FieldCache

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCache.Call66

open SourceGaussianModel SourceSignedEvaluator SourceFields WholeBandMatrix

assembleWholeBandMatrix

theorem matrix_gradient_report : ∀ axis : Fin 3,
    (calculatedField matrixRows).gradient axis =
      WholeBandSource.callReportedDensity 66 (WholeCellReplay.gradientIndex axis) := by
  intro axis
  fin_cases axis <;> decide +kernel

theorem matrix_hessian_report : ∀ axis direction : Fin 3,
    (calculatedField matrixRows).hessian axis direction =
      WholeBandSource.callReportedDensity 66 (WholeCellReplay.hessianIndex axis direction) := by
  intro axis direction
  fin_cases axis <;> fin_cases direction <;> decide +kernel

theorem actual_field (x : Point) (inside : InRectangle (WholeBandSource.callBox 66) x) :
    IntervalParameterMap.FieldHolds (WholeBandSource.recordedCallField 66) x :=
  recordedCallFieldHolds 66 sourceAO matrixRows matrixCertificate
    (fun j b y hy => actual_orbitals j b y hy)
    matrix_gradient_report matrix_hessian_report x inside

end LAlanine40K2025.BasinRefinement.WholeBandCache.Call66
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
