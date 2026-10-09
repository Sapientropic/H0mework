import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualModel
import H0mework.Chemistry.LAlanineTrueTubeWhole.SignedGlue

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel TrueTubeActual WholeCellPartition Set
noncomputable section

abbrev BandPoint := {p : Point // p ∈ fullDomain}

def negativeFlow (p : BandPoint) : ℝ → Point := wholeDirectionalFlow 0 (bandInitial 0 p)
def positiveFlow (p : BandPoint) : ℝ → Point := wholeDirectionalFlow 1 (bandInitial 1 p)
def fullFlow (p : BandPoint) : ℝ → Point := LAlanineTrueTube.Signed.full (negativeFlow p) (positiveFlow p)

theorem directions_same_initial (p : BandPoint) : negativeFlow p 0 = positiveFlow p 0 :=
  (wholeDirectionalFlow_starts 0 (bandInitial 0 p)).trans (wholeDirectionalFlow_starts 1 (bandInitial 1 p)).symm

theorem fullFlow_starts (p : BandPoint) : fullFlow p 0 = ContinuousParameterMap.initialMap 0 4 p.val := by
  rw [fullFlow, LAlanineTrueTube.Signed.full_zero]
  exact wholeDirectionalFlow_starts 0 (bandInitial 0 p)

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
