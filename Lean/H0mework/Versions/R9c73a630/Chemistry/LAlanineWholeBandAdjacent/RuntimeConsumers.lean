import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.RuntimeParentConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime

open AdjacentFlow MeasureTheory
noncomputable section

theorem adjacentSpatialRuntime_geometry :
    type_of% (adjacentSpatialRuntimeFace_factorizes adjacentSpatialRuntimeSeed (.component .certificate)) ∧
    type_of% maps_are_same ∧
    type_of% jacobians_are_same ∧
    type_of% jointMap_injOn ∧
    type_of% jointJacobian_det_ne_zero ∧
    type_of% joint_source_nonempty ∧
    type_of% joint_domain_eq_Icc ∧
    type_of% jointMap_hasFDerivWithinAt ∧
    type_of% jointJacobian_eq_fderivWithin ∧
    type_of% jointImage_compact ∧
    type_of% jointImage_nonempty ∧
    type_of% jointImage_volume_lt_top ∧
    type_of% jointImage_volume_pos ∧
    type_of% jointImage_eq_union :=
  ⟨adjacentSpatialRuntime_sourceCertificate.1,
    adjacentSpatialRuntime_sourceCertificate.2.sameMaps,
    adjacentSpatialRuntime_sourceCertificate.2.sameJacobians,
    adjacentSpatialRuntime_sourceCertificate.2.injective,
    adjacentSpatialRuntime_sourceCertificate.2.nondegenerate,
    adjacentSpatialRuntime_sourceCertificate.2.sourceNonempty,
    adjacentSpatialRuntime_sourceCertificate.2.domain,
    adjacentSpatialRuntime_sourceCertificate.2.derivative,
    adjacentSpatialRuntime_sourceCertificate.2.canonical,
    adjacentSpatialRuntime_sourceCertificate.2.imageCompact,
    adjacentSpatialRuntime_sourceCertificate.2.imageNonempty,
    adjacentSpatialRuntime_sourceCertificate.2.imageFinite,
    adjacentSpatialRuntime_sourceCertificate.2.imagePositive,
    adjacentSpatialRuntime_sourceCertificate.2.unionImage⟩

theorem adjacentSpatialRuntime_seam :
    type_of% (adjacentSpatialRuntimeFace_factorizes adjacentSpatialRuntimeSeed (.component .certificate)) ∧
    type_of% sourceSeam_nonempty ∧
    type_of% actualSeam_nonempty ∧
    type_of% sourceSeam_volume_zero ∧
    type_of% actualSeam_volume_zero ∧
    type_of% actual_intersection_eq_seam ∧
    type_of% actual_intersection_volume_zero ∧
    type_of% actual_images_aeDisjoint ∧
    type_of% joint_volume_eq_sum ∧
    type_of% rightImage_volume_pos ∧
    type_of% joint_volume_strictly_exceeds_left :=
  ⟨adjacentSpatialRuntime_sourceCertificate.1,
    adjacentSpatialRuntime_sourceCertificate.2.sourceSeamNonempty,
    adjacentSpatialRuntime_sourceCertificate.2.actualSeamNonempty,
    adjacentSpatialRuntime_sourceCertificate.2.sourceSeamZero,
    adjacentSpatialRuntime_sourceCertificate.2.actualSeamZero,
    adjacentSpatialRuntime_sourceCertificate.2.exactIntersection,
    adjacentSpatialRuntime_sourceCertificate.2.intersectionZero,
    adjacentSpatialRuntime_sourceCertificate.2.aeDisjoint,
    adjacentSpatialRuntime_sourceCertificate.2.volumeSum,
    adjacentSpatialRuntime_sourceCertificate.2.rightPositive,
    adjacentSpatialRuntime_sourceCertificate.2.strictExpansion⟩

theorem adjacentSpatialRuntime_integrals :
    type_of% (adjacentSpatialRuntimeFace_factorizes adjacentSpatialRuntimeSeed (.component .certificate)) ∧
    type_of% joint_spatial_integral_commutes ∧
    type_of% joint_spatial_integrable_iff ∧
    type_of% joint_spatial_lintegral_commutes ∧
    type_of% joint_volume_eq_jacobian_lintegral ∧
    type_of% joint_integral_eq_sum ∧
    type_of% joint_laplacian_integrable ∧
    type_of% joint_laplacian_no_double_count ∧
    type_of% joint_bilinear_integrable ∧
    type_of% joint_bilinear_no_double_count :=
  ⟨adjacentSpatialRuntime_sourceCertificate.1,
    adjacentSpatialRuntime_sourceCertificate.2.changeVariables,
    adjacentSpatialRuntime_sourceCertificate.2.integrability,
    adjacentSpatialRuntime_sourceCertificate.2.nonnegativeChangeVariables,
    adjacentSpatialRuntime_sourceCertificate.2.jacobianVolume,
    adjacentSpatialRuntime_sourceCertificate.2.additiveIntegral,
    adjacentSpatialRuntime_sourceCertificate.2.laplacianIntegrable,
    adjacentSpatialRuntime_sourceCertificate.2.laplacianSum,
    adjacentSpatialRuntime_sourceCertificate.2.bilinearIntegrable,
    adjacentSpatialRuntime_sourceCertificate.2.bilinearSum⟩

theorem adjacentSpatialRuntime_materialRecognition :
    type_of% (adjacentSpatialRuntimeFace_factorizes adjacentSpatialRuntimeSeed (.component .material)) ∧
    generatedAdjacentSpatialMaterial.domain = (jointDomain) ∧
    generatedAdjacentSpatialMaterial.parameterMap = (jointMap) ∧
    generatedAdjacentSpatialMaterial.jacobians = (jointJacobian) ∧
    generatedAdjacentSpatialMaterial.image = (jointImage) ∧
    generatedAdjacentSpatialMaterial.sourceSeam = (AdjacentFlow.sourceSeam) ∧
    generatedAdjacentSpatialMaterial.actualSeam = (AdjacentFlow.actualSeam) ∧
    generatedAdjacentSpatialMaterial.volume = (MeasureTheory.volume jointImage) ∧
    generatedAdjacentSpatialMaterial.laplacianIntegral = (∫ x in jointImage, SourceGaussianModel.laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix x) ∧
    generatedAdjacentSpatialMaterial.bilinearIntegrals = (fun left right => ∫ x in jointImage, SourceGaussianModel.bilinear SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix left right x) :=
  ⟨adjacentSpatialRuntimeFace_factorizes adjacentSpatialRuntimeSeed (.component .material),rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
