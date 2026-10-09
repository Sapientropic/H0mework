import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.SourceReifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All

/-- Finite calculation candidates; SourceCenters proves exact equality to each reifier-owned rawCenter. -/
def calculatedX (i : Fin 13) : Int := (#[
  3826162671687072478425682977691796819499645140992,
  6015065325521571021113019671863300736915404226560,
  13079804116340872415037153868433904124402308481024,
  12834296631854891703885469324655449501309513760768,
  12722513094047442043930695253853875395864488312832,
  15273904935449981452090198520762713827844351328256,
  6405200175080787801598401163905684418745826541568,
  10339701529303358636577704201294295423575828463616,
  10560360006712788294558205629423666538935201300480,
  11155632765272994805132067518410799151840642465792,
  13529282593122887087639915463395475415838968774656,
  9402496470903966462361457763523315642538626383872,
  11041217884844296586514570738877589837646909145088
] : Array Int)[i.val]!

def radiusGrid : Int := 2 ^ (160-20)

theorem calculated_centres_separated :
    ∀ i j : Fin 13, i ≠ j →
      calculatedX i + radiusGrid < calculatedX j - radiusGrid ∨
      calculatedX j + radiusGrid < calculatedX i - radiusGrid := by
  decide +kernel

end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
