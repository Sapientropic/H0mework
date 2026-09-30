import H0mework.Chemistry.LAlanineWholeBandAdjacent.ConservationSpatialBalance
import H0mework.Chemistry.LAlanineWholeBandAdjacent.ConservationSeamCancellation
import H0mework.Chemistry.LAlanineBandContinuation.ConservationCell0Consumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open WholeCellBoundary
noncomputable section

theorem actual_upper_cap_flux_pos (p : FacePoint) (inside : p ∈ faceDomain 2) : 0 < actualFaceFlux (2,true) p := by
  rw [actualCapFlux_eq_oriented_det _ _ inside rfl]
  simpa only [ite_true,one_mul] using jointJacobian_det_pos _ (faceParameter_mem (2,true) p inside)

theorem actual_lower_cap_flux_neg (p : FacePoint) (inside : p ∈ faceDomain 2) : actualFaceFlux (2,false) p < 0 := by
  rw [actualCapFlux_eq_oriented_det _ _ inside rfl]
  simpa only [Bool.false_eq_true,ite_false,neg_mul,one_mul] using
    neg_lt_zero.mpr (jointJacobian_det_pos _ (faceParameter_mem (2,false) p inside))

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
