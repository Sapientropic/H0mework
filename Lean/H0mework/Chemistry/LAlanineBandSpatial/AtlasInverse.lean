import H0mework.Chemistry.LAlanineBandSpatial.AtlasCarrier
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel Set
noncomputable section

def carrierEquiv (fields : Fields) (positive : Normals) : bandDomain ≃ bandImage :=
  (Equiv.Set.imageOfInjOn bandMap bandDomain (bandMap_injOn fields positive)).trans (Equiv.setCongr bandMap_image)

theorem carrierEquiv_continuous (fields : Fields) (bounds : Bounds) (positive : Normals) :
    Continuous (carrierEquiv fields positive) := by
  apply Continuous.subtype_mk
  exact continuousOn_iff_continuous_domRestrict.mp (bandMap_continuousOn fields bounds)

/-- The same physical carrier has a continuous inverse across every original seam. -/
def carrierHomeomorph (fields : Fields) (bounds : Bounds) (positive : Normals) : bandDomain ≃ₜ bandImage := by
  letI : CompactSpace bandDomain := isCompact_iff_compactSpace.mp bandDomain_compact
  exact (carrierEquiv_continuous fields bounds positive).homeoOfEquivCompactToT2

theorem carrierHomeomorph_is_actual (fields : Fields) (bounds : Bounds) (positive : Normals)
    (p : bandDomain) : (carrierHomeomorph fields bounds positive p).val = bandMap p.val := by
  change (carrierEquiv fields positive p).val = bandMap p.val
  rfl

theorem carrier_inverse_recovers (fields : Fields) (bounds : Bounds) (positive : Normals) (p : bandDomain) :
    (carrierHomeomorph fields bounds positive).symm (carrierHomeomorph fields bounds positive p) = p :=
  (carrierHomeomorph fields bounds positive).symm_apply_apply p

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
