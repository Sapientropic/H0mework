import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationRuntimeParentConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BandConservationRuntime

open SourceGaussianModel AdjacentConservation MeasureTheory
open WholeCellBoundary (Face FacePoint)
noncomputable section

theorem bandConservationRuntime_dynamics :
    type_of% (bandConservationRuntimeFace_factorizes bandConservationRuntimeSeed (.component .certificate)) ∧
    type_of% WholeBandConservation.evolvingJacobian_determinant_evolution ∧
    type_of% WholeBandConservation.actual_time_integral_eq_det_difference ∧
    type_of% WholeBandConservation.retime_sourceResponse ∧
    type_of% WholeBandConservation.actualJacobian_det_pos ∧
    type_of% WholeBandConservation.actual_local_extension_on_time_slab ∧
    type_of% WholeBandConservation.cell0_evolving_source_same ∧
    type_of% WholeBandConservation.cell0_volume_rate_same ∧
    type_of% WholeBandConservation.cell0_determinant_evolution_from_shared ∧
    type_of% WholeBandConservation.cell0_time_integral_from_shared ∧
    type_of% WholeBandConservation.cell0_positive_orientation_from_shared ∧
    type_of% joint_evolvingJacobian_eq_retimed ∧
    type_of% joint_actual_time_integral ∧
    type_of% jointJacobian_det_pos :=
  ⟨bandConservationRuntime_sourceCertificate.1,
    bandConservationRuntime_sourceCertificate.2.coreEvolution,
    bandConservationRuntime_sourceCertificate.2.coreIntegral,
    bandConservationRuntime_sourceCertificate.2.coreRetime,
    bandConservationRuntime_sourceCertificate.2.coreOrientation,
    bandConservationRuntime_sourceCertificate.2.coreChart,
    bandConservationRuntime_sourceCertificate.2.oldMatrix,
    bandConservationRuntime_sourceCertificate.2.oldRate,
    bandConservationRuntime_sourceCertificate.2.oldEvolution,
    bandConservationRuntime_sourceCertificate.2.oldIntegral,
    bandConservationRuntime_sourceCertificate.2.oldOrientation,
    bandConservationRuntime_sourceCertificate.2.jointRetime,
    bandConservationRuntime_sourceCertificate.2.jointIntegral,
    bandConservationRuntime_sourceCertificate.2.jointOrientation⟩

theorem bandConservationRuntime_boundary :
    type_of% (bandConservationRuntimeFace_factorizes bandConservationRuntimeSeed (.component .certificate)) ∧
    type_of% actual_local_extension ∧
    type_of% actual_boundary_image ∧
    type_of% actual_boundary_eq_six_faces ∧
    type_of% actualSpatialFace_nonempty ∧
    type_of% actualFaceMap_hasFDerivWithinAt ∧
    type_of% actualFaceDerivative_rank_two ∧
    type_of% actualFaceTangents_linearIndependent ∧
    type_of% actualOrientedArea_ne_zero ∧
    type_of% actual_side_boundary_flux ∧
    type_of% actualCapFlux_eq_oriented_det ∧
    type_of% actual_upper_cap_flux_pos ∧
    type_of% actual_lower_cap_flux_neg :=
  ⟨bandConservationRuntime_sourceCertificate.1,
    bandConservationRuntime_sourceCertificate.2.localChart,
    bandConservationRuntime_sourceCertificate.2.boundaryImage,
    bandConservationRuntime_sourceCertificate.2.sixFaces,
    bandConservationRuntime_sourceCertificate.2.faceNonempty,
    bandConservationRuntime_sourceCertificate.2.faceDerivative,
    bandConservationRuntime_sourceCertificate.2.faceRank,
    bandConservationRuntime_sourceCertificate.2.tangentsIndependent,
    bandConservationRuntime_sourceCertificate.2.areaNonzero,
    bandConservationRuntime_sourceCertificate.2.sideFlux,
    bandConservationRuntime_sourceCertificate.2.capDet,
    bandConservationRuntime_sourceCertificate.2.upperSign,
    bandConservationRuntime_sourceCertificate.2.lowerSign⟩

theorem bandConservationRuntime_balance :
    type_of% (bandConservationRuntimeFace_factorizes bandConservationRuntimeSeed (.component .certificate)) ∧
    type_of% laplacianPullback_integrable ∧
    type_of% actual_slice_integral_eq_caps ∧
    type_of% actualCapFlux_sum_integrable ∧
    type_of% actual_spatial_laplacian_eq_cap_flux ∧
    type_of% seamParameters_same ∧
    type_of% rightSeam_inside ∧
    type_of% rightSeamMap_actual_derivative ∧
    type_of% actualSeamMaps_same ∧
    type_of% actualSeamAreas_cancel ∧
    type_of% actualSeamFluxes_cancel :=
  ⟨bandConservationRuntime_sourceCertificate.1,
    bandConservationRuntime_sourceCertificate.2.pullbackIntegrable,
    bandConservationRuntime_sourceCertificate.2.sliceIntegral,
    bandConservationRuntime_sourceCertificate.2.capIntegrable,
    bandConservationRuntime_sourceCertificate.2.spatialBalance,
    bandConservationRuntime_sourceCertificate.2.seamParameters,
    bandConservationRuntime_sourceCertificate.2.seamIncidence,
    bandConservationRuntime_sourceCertificate.2.seamDerivative,
    bandConservationRuntime_sourceCertificate.2.seamMap,
    bandConservationRuntime_sourceCertificate.2.seamArea,
    bandConservationRuntime_sourceCertificate.2.seamFlux⟩

theorem bandConservationRuntime_materialRecognition :
    type_of% (bandConservationRuntimeFace_factorizes bandConservationRuntimeSeed (.component .material)) ∧
    generatedBandConservationMaterial.evolvingJacobians = (WholeBandConservation.evolvingJacobian 0) ∧
    generatedBandConservationMaterial.volumeRates = (WholeBandConservation.signedVolumeRate 0) ∧
    generatedBandConservationMaterial.faceParameters = (AdjacentConservation.faceParameter) ∧
    generatedBandConservationMaterial.faceMaps = (actualFaceMap) ∧
    generatedBandConservationMaterial.faceDerivatives = (actualFaceDerivative) ∧
    generatedBandConservationMaterial.faceAreas = (actualOrientedArea) ∧
    generatedBandConservationMaterial.faceFluxes = (actualFaceFlux) ∧
    generatedBandConservationMaterial.spatialFaces = (actualSpatialFace) ∧
    generatedBandConservationMaterial.laplacianPullback = (AdjacentConservation.laplacianPullback) ∧
    generatedBandConservationMaterial.rightSeamMap = (AdjacentConservation.rightSeamMap) ∧
    generatedBandConservationMaterial.rightSeamDerivative = (AdjacentConservation.rightSeamDerivative) ∧
    generatedBandConservationMaterial.rightSeamArea = (AdjacentConservation.rightSeamArea) ∧
    generatedBandConservationMaterial.rightSeamFlux = (AdjacentConservation.rightSeamFlux) :=
  ⟨bandConservationRuntimeFace_factorizes bandConservationRuntimeSeed (.component .material),rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end LAlanine40K2025.BasinRefinement.BandConservationRuntime

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
