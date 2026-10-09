import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A000.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A001.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A002.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A003.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A004.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A005.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A006.Geometry
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.SourceA007Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A008.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A009.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A010.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A011.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A012.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.CoordinateGap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel SourceExponential WholeBandAttractor Set Metric Function
noncomputable section

def sourceCentre (i : Fin 13) : Point :=
  if i=0 then Atom000.centre else
  if i=1 then Atom001.centre else
  if i=2 then Atom002.centre else
  if i=3 then Atom003.centre else
  if i=4 then Atom004.centre else
  if i=5 then Atom005.centre else
  if i=6 then Atom006.centre else
  if i=7 then Atom007.centre else
  if i=8 then Atom008.centre else
  if i=9 then Atom009.centre else
  if i=10 then Atom010.centre else
  if i=11 then Atom011.centre else
  Atom012.centre

def sourceRadius : ℝ := 1/1048576

theorem source_centre_x (i : Fin 13) :
    sourceCentre i 0 = scaledCentreX i := by
  fin_cases i
  · simp [sourceCentre,scaledCentreX,sourceX,Atom000.centre,Atom000.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom001.centre,Atom001.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom002.centre,Atom002.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom003.centre,Atom003.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom004.centre,Atom004.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom005.centre,Atom005.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom006.centre,Atom006.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom007.centre,Atom007.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom008.centre,Atom008.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom009.centre,Atom009.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom010.centre,Atom010.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom011.centre,Atom011.centreRat]
  · simp [sourceCentre,scaledCentreX,sourceX,Atom012.centre,Atom012.centreRat]

theorem source_radius_scaled : sourceRadius=scaledRadius := by
  rw [scaled_radius_actual]
  rfl

theorem source_centre_gap (i j : Fin 13) (different : i ≠ j) :
    sourceCentre i 0+sourceRadius < sourceCentre j 0-sourceRadius ∨
    sourceCentre j 0+sourceRadius < sourceCentre i 0-sourceRadius := by
  rw [source_centre_x i,source_centre_x j,source_radius_scaled]
  exact scaled_centres_gap i j different

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
