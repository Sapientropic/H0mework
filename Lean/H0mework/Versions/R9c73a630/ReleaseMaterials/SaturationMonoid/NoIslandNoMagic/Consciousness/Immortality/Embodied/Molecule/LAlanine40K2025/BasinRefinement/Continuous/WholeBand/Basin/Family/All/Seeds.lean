import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Seeds.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Fifth.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Geometry

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel WholeBandAttractor Metric Set
noncomputable section

theorem source_zero_inside (i : Fin 13) :
    (sourceSeed i).criticalPoint ∈ closedBall (sourceCentre i) sourceRadius := by
  fin_cases i
  · change Atom000.actualZero.point ∈ closedBall Atom000.centre sourceRadius
    simpa [sourceRadius,Atom000.radius,Atom000.radiusRat] using Atom000.actualZero.inside
  · change Atom001.actualZero.point ∈ closedBall Atom001.centre sourceRadius
    simpa [sourceRadius,Atom001.radius,Atom001.radiusRat] using Atom001.actualZero.inside
  · change Atom002.actualZero.point ∈ closedBall Atom002.centre sourceRadius
    simpa [sourceRadius,Atom002.radius,Atom002.radiusRat] using Atom002.actualZero.inside
  · change Atom003.actualZero.point ∈ closedBall Atom003.centre sourceRadius
    simpa [sourceRadius,Atom003.radius,Atom003.radiusRat] using Atom003.actualZero.inside
  · change Atom004.actualZero.point ∈ closedBall Atom004.centre sourceRadius
    simpa [sourceRadius,Atom004.radius,Atom004.radiusRat] using Atom004.actualZero.inside
  · change Atom005.actualZero.point ∈ closedBall Atom005.centre sourceRadius
    simpa [sourceRadius,Atom005.radius,Atom005.radiusRat] using Atom005.actualZero.inside
  · change Atom006.actualZero.point ∈ closedBall Atom006.centre sourceRadius
    simpa [sourceRadius,Atom006.radius,Atom006.radiusRat] using Atom006.actualZero.inside
  · change Atom007.actualZero.point ∈ closedBall Atom007.centre sourceRadius
    simpa [sourceRadius,Atom007.radius,Atom007.radiusRat] using Atom007.actualZero.inside
  · change Atom008.actualZero.point ∈ closedBall Atom008.centre sourceRadius
    simpa [sourceRadius,Atom008.radius,Atom008.radiusRat] using Atom008.actualZero.inside
  · change Atom009.actualZero.point ∈ closedBall Atom009.centre sourceRadius
    simpa [sourceRadius,Atom009.radius,Atom009.radiusRat] using Atom009.actualZero.inside
  · change Atom010.actualZero.point ∈ closedBall Atom010.centre sourceRadius
    simpa [sourceRadius,Atom010.radius,Atom010.radiusRat] using Atom010.actualZero.inside
  · change Atom011.actualZero.point ∈ closedBall Atom011.centre sourceRadius
    simpa [sourceRadius,Atom011.radius,Atom011.radiusRat] using Atom011.actualZero.inside
  · change Atom012.actualZero.point ∈ closedBall Atom012.centre sourceRadius
    simpa [sourceRadius,Atom012.radius,Atom012.radiusRat] using Atom012.actualZero.inside

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
