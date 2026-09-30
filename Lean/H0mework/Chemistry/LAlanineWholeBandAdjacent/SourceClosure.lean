import H0mework.Chemistry.LAlanineWholeBandAdjacent.Consumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentSpatialSource

open AdjacentFlow
structure AdjacentSpatialClosure : Prop where
  sameMaps : type_of% maps_are_same
  sameJacobians : type_of% jacobians_are_same
  injective : type_of% jointMap_injOn
  nondegenerate : type_of% jointJacobian_det_ne_zero
  sourceNonempty : type_of% joint_source_nonempty
  domain : type_of% joint_domain_eq_Icc
  derivative : type_of% jointMap_hasFDerivWithinAt
  canonical : type_of% jointJacobian_eq_fderivWithin
  imageCompact : type_of% jointImage_compact
  imageNonempty : type_of% jointImage_nonempty
  imageFinite : type_of% jointImage_volume_lt_top
  imagePositive : type_of% jointImage_volume_pos
  unionImage : type_of% jointImage_eq_union
  sourceSeamNonempty : type_of% sourceSeam_nonempty
  actualSeamNonempty : type_of% actualSeam_nonempty
  sourceSeamZero : type_of% sourceSeam_volume_zero
  actualSeamZero : type_of% actualSeam_volume_zero
  exactIntersection : type_of% actual_intersection_eq_seam
  intersectionZero : type_of% actual_intersection_volume_zero
  aeDisjoint : type_of% actual_images_aeDisjoint
  volumeSum : type_of% joint_volume_eq_sum
  rightPositive : type_of% rightImage_volume_pos
  strictExpansion : type_of% joint_volume_strictly_exceeds_left
  changeVariables : type_of% joint_spatial_integral_commutes
  integrability : type_of% joint_spatial_integrable_iff
  nonnegativeChangeVariables : type_of% joint_spatial_lintegral_commutes
  jacobianVolume : type_of% joint_volume_eq_jacobian_lintegral
  additiveIntegral : type_of% joint_integral_eq_sum
  laplacianIntegrable : type_of% joint_laplacian_integrable
  laplacianSum : type_of% joint_laplacian_no_double_count
  bilinearIntegrable : type_of% joint_bilinear_integrable
  bilinearSum : type_of% joint_bilinear_no_double_count

theorem sourceGeneratedAdjacentSpatialClosure : AdjacentSpatialClosure where
  sameMaps := maps_are_same
  sameJacobians := jacobians_are_same
  injective := jointMap_injOn
  nondegenerate := jointJacobian_det_ne_zero
  sourceNonempty := joint_source_nonempty
  domain := joint_domain_eq_Icc
  derivative := jointMap_hasFDerivWithinAt
  canonical := jointJacobian_eq_fderivWithin
  imageCompact := jointImage_compact
  imageNonempty := jointImage_nonempty
  imageFinite := jointImage_volume_lt_top
  imagePositive := jointImage_volume_pos
  unionImage := jointImage_eq_union
  sourceSeamNonempty := sourceSeam_nonempty
  actualSeamNonempty := actualSeam_nonempty
  sourceSeamZero := sourceSeam_volume_zero
  actualSeamZero := actualSeam_volume_zero
  exactIntersection := actual_intersection_eq_seam
  intersectionZero := actual_intersection_volume_zero
  aeDisjoint := actual_images_aeDisjoint
  volumeSum := joint_volume_eq_sum
  rightPositive := rightImage_volume_pos
  strictExpansion := joint_volume_strictly_exceeds_left
  changeVariables := joint_spatial_integral_commutes
  integrability := joint_spatial_integrable_iff
  nonnegativeChangeVariables := joint_spatial_lintegral_commutes
  jacobianVolume := joint_volume_eq_jacobian_lintegral
  additiveIntegral := joint_integral_eq_sum
  laplacianIntegrable := joint_laplacian_integrable
  laplacianSum := joint_laplacian_no_double_count
  bilinearIntegrable := joint_bilinear_integrable
  bilinearSum := joint_bilinear_no_double_count

end LAlanine40K2025.BasinRefinement.AdjacentSpatialSource

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
