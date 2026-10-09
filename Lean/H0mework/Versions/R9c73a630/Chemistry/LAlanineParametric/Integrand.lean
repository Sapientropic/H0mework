import H0mework.Versions.AB.Chemistry.LAlanineParametric.ActualMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousParameterMap

open SourceGaussianModel ContinuousGradient ContinuousSeed MeasureTheory Set
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Geometry

noncomputable section

def jacobianMatrix (run : Data.RunIndex) (segment : Segment) (p : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun axis direction => parameterJacobian run segment p (Pi.single direction 1) axis

def signedLaplacian (run : Data.RunIndex) (segment : Segment) (p : Point) : ℝ :=
  laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix (parameterMap run segment p) *
    (jacobianMatrix run segment p).det

theorem jacobianEntry_contDiff (run : Data.RunIndex) (segment : Segment) (axis direction : Fin 3) :
    ContDiff ℝ 2 (fun p => jacobianMatrix run segment p axis direction) :=
  (contDiff_apply ℝ ℝ axis).comp ((parameterJacobian_contDiff run segment).clm_apply contDiff_const)

theorem jacobianDet_contDiff (run : Data.RunIndex) (segment : Segment) :
    ContDiff ℝ 2 (fun p => (jacobianMatrix run segment p).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro permutation _
  exact contDiff_const.mul (contDiff_prod (fun direction _ =>
    jacobianEntry_contDiff run segment (permutation direction) direction))

theorem signedLaplacian_contDiff (run : Data.RunIndex) (segment : Segment) :
    ContDiff ℝ 2 (signedLaplacian run segment) :=
  ((laplacian_contDiff SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix 2).comp
    (parameterMap_contDiff run segment 2)).mul (jacobianDet_contDiff run segment)

def parameterLower (segment : Segment) : Point :=
  ![0, knotCoordinate (firstKnot segment), -(1 / 2)]

def parameterUpper (segment : Segment) : Point :=
  ![1, knotCoordinate (lastKnot segment), 1 / 2]

def sourceDomain (segment : Segment) : Set Point := Icc (parameterLower segment) (parameterUpper segment)

theorem sourceDomain_nonempty (segment : Segment) : (sourceDomain segment).Nonempty := by
  apply nonempty_Icc.mpr
  intro axis
  fin_cases axis
  · norm_num [parameterLower, parameterUpper]
  · change (knotCoordinate (firstKnot segment) : ℝ) ≤ knotCoordinate (lastKnot segment)
    exact_mod_cast (source_knot_geometry.1 segment).le
  · norm_num [parameterLower, parameterUpper]

theorem source_integrand_integrable (run : Data.RunIndex) (segment : Segment) :
    IntegrableOn (signedLaplacian run segment) (sourceDomain segment) :=
  (signedLaplacian_contDiff run segment).continuous.continuousOn.integrableOn_compact isCompact_Icc

def sourceSignedIntegral (run : Data.RunIndex) (segment : Segment) : ℝ :=
  ∫ p in sourceDomain segment, signedLaplacian run segment p

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousParameterMap
