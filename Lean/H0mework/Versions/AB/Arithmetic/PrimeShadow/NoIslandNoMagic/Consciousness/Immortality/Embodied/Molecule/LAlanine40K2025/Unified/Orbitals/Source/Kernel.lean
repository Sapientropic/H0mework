import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Sqrt.Family
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Exp.Family
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Inputs

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.OriginalMetric
open BasinRefinement SourceSignedEvaluator
noncomputable section

def originalIncidence (i : RadialIndex) : Fin 630 × Fin 3654 :=
  SourceInputs.radialIncidenceBounded[i.val]

def originalRoot (i : RadialIndex) : {m : SqrtMaterial // SqrtComputed m} :=
  Sqrt.atIndex (originalIncidence i).1
def originalExp (i : RadialIndex) : {m : ExpMaterial // ExpComputed m} :=
  Exp.atIndex (originalIncidence i).2

def radialMaterial (i : RadialIndex) : RadialMaterial :=
  combineRadial (originalRoot i).val (originalExp i).val

theorem original_radial_contains (i : RadialIndex) :
    Holds (radialMaterial i).interval
      (radialKernel (radialMaterial i).gamma (radialMaterial i).penalty) :=
  combined_radial_contains (originalRoot i).val (originalExp i).val
    (originalRoot i).property (originalExp i).property

end
end LAlanine40K2025.UnifiedOrbitals.OriginalMetric
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
