import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.Table
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source

def stagedFirstPointerTable : IntTable 64 64 := Id.run do
  let root := fromTable (toTable sourceFirstRootInt nativeFin nativeFin) nativeFin nativeFin
  let complement := fromTable (toTable sourceFirstComplementInt nativeFin nativeFin)
    nativeFin nativeFin
  let donor := fromTable (toTable sourceDonorRootInt pairFin pairFin) pairFin pairFin
  let donorComplement := fromTable (toTable sourceDonorComplementInt pairFin pairFin)
    pairFin pairFin
  let free := fromTable (toTable sourceFirstFreeInt nativeFin nativeFin) nativeFin nativeFin
  let donorFree := fromTable (toTable sourceDonorFreeInt pairFin pairFin) pairFin pairFin
  let rotated := fromTable (toTable (rotateInt free root) nativeFin nativeFin)
    nativeFin nativeFin
  let rotatedComplement := fromTable (toTable (rotateInt free complement) nativeFin nativeFin)
    nativeFin nativeFin
  let rotatedDonor := fromTable (toTable (rotateInt donorFree donor) pairFin pairFin)
    pairFin pairFin
  let rotatedDonorComplement := fromTable
    (toTable (rotateInt donorFree donorComplement) pairFin pairFin) pairFin pairFin
  let role := roleBlocksInt (bodyLiftIdentityInt rotated)
    (donorLiftIdentityInt rotatedDonor)
  let complementRole := roleBlocksInt (bodyLiftIdentityInt rotatedComplement)
    (donorLiftIdentityInt rotatedDonorComplement)
  return toTable
    (intFourBlocks role (intNeg complementRole) complementRole role) pointerFin pointerFin

theorem staged_first_pointer_original :
    fromTable stagedFirstPointerTable pointerFin pointerFin=sourceFirstPointerInt := by
  simp [stagedFirstPointerTable,from_to_table,sourceFirstPointerInt,
    sourceFirstRootRoleInt,sourceFirstComplementRoleInt,
    sourceFirstRootRotatedInt,sourceFirstComplementRotatedInt,
    sourceDonorRootRotatedInt,sourceDonorComplementRotatedInt]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
