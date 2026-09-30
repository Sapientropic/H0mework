import H0mework.Chemistry.LAlanineBoundary.SourceIntegral
import H0mework.Chemistry.LAlanineBoundary.GeometryFluxGeometry

/-! Source-generated actual boundary geometry, oriented gradient flux and complete signed settlement. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel WholeCellPartition WholeCellSpatial Set
open scoped BigOperators
noncomputable section

structure GradientBoundaryClosure : Prop where
  boundary : frontier fullPatch = ⋃ face : Face, spatialFace face
  nonemptyFaces : ∀ face : Face, ∃ p ∈ spatialFace face, p ∈ frontier fullPatch
  actualTangents : type_of% Geometry.faceTangent_is_actual_derivative
  actualArea : type_of% Geometry.orientedAreaVector_eq_cross
  nonzeroArea : type_of% Geometry.orientedAreaVector_nonzero
  gradientFlux : type_of% Geometry.faceFlux_eq_gradient_dot_area
  smooth : ContDiff ℝ 1 pulledFlux
  divergence : ∀ p : Point, (∑ i : Fin 3, fderiv ℝ pulledFlux p (Pi.single i 1) i) =
    ContinuousParameterMap.signedLaplacian 0 4 p
  spatialIntegral : netFlux = fullLaplacianIntegral
  quarterIntegrals : ∀ q : Quarter, quarterNetFlux q = quarterSignedIntegral q
  quarterSum : netFlux = ∑ q : Quarter, quarterNetFlux q
  seamCancellation : type_of% all_three_seams_cancel
  strict : (-623 / 10000000000 : ℝ) < netFlux ∧ netFlux < (-39 / 10000000000 : ℝ)
  negativeFace : ∃ face : Face, faceIntegral face < 0

theorem sourceGeneratedGradientBoundaryClosure : GradientBoundaryClosure where
  boundary := actual_boundary_eq_six_faces
  nonemptyFaces := every_actual_face_is_nonempty
  actualTangents := Geometry.faceTangent_is_actual_derivative
  actualArea := Geometry.orientedAreaVector_eq_cross
  nonzeroArea := Geometry.orientedAreaVector_nonzero
  gradientFlux := Geometry.faceFlux_eq_gradient_dot_area
  smooth := pulledFlux_contDiff
  divergence := div_pulledFlux
  spatialIntegral := netFlux_eq_spatialIntegral
  quarterIntegrals := quarterFlux_eq_spatialReadout
  quarterSum := netFlux_eq_four_quarters
  seamCancellation := all_three_seams_cancel
  strict := actual_gradient_flux_strict
  negativeFace := actual_negative_face

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
