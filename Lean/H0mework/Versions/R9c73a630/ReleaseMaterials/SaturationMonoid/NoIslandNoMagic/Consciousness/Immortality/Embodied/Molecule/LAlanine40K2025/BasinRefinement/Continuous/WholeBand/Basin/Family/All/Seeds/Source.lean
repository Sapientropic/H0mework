import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Seeds.Heavy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Seeds.EarlyLight
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Seeds.LateLight
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Seeds.Middle

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel WholeBandAttractor Metric Set
noncomputable section

def sourceSeed (i : Fin 13) : Family.AttractingSeed :=
  if i=0 then atom000Seed else
  if i=1 then atom001Seed else
  if i=2 then atom002Seed else
  if i=3 then atom003Seed else
  if i=4 then atom004Seed else
  if i=5 then atom005Seed else
  if i=6 then Family.atom006Seed else
  if i=7 then Family.atom007Seed else
  if i=8 then Family.atom008Seed else
  if i=9 then Family.atom009Seed else
  if i=10 then atom010Seed else
  if i=11 then atom011Seed else
  atom012Seed

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
