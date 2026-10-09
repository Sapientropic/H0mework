import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Dynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Carrier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section

def localSupply (k : Sym2 Basis) : Matrix (FullFiber k) (FullFiber k) ℂ :=
  restrict Sectors.reservoirOrbit (donorSector k) PCExecution.supply

def localPointer (k : Sym2 Basis) : Matrix (PointerFiber k) (PointerFiber k) ℂ :=
  restrict Sectors.pointerOrbit (donorSector k) PCExecution.pointer

def localNine (k : Sym2 Basis) : Matrix (PointerFiber k) (PointerFiber k) ℂ :=
  restrict Sectors.pointerOrbit (donorSector k) LoadExecution.nine

def localEleven (k : Sym2 Basis) : Matrix (PointerFiber k) (PointerFiber k) ℂ :=
  restrict Sectors.pointerOrbit (donorSector k) LoadExecution.eleven

def localPC (k : Sym2 Basis) : Matrix (PointerFiber k) (PointerFiber k) ℂ :=
  restrict Sectors.pointerOrbit (donorSector k) Post.finitePCObservable

def localNet (k : Sym2 Basis) : Matrix (PointerFiber k) (PointerFiber k) ℂ :=
  star (localEleven k)*localPC k*localEleven k-star (localNine k)*localPC k*localNine k

def localRootNet (k : Sym2 Basis) : Matrix (PointerFiber k) (PointerFiber k) ℂ :=
  star (localPointer k)*localNet k*localPointer k

def localReadout (k : Sym2 Basis) : Matrix (BodyFiber k) (BodyFiber k) ℂ :=
  (star (localSupply k)*(localRootNet k).submatrix (insertPointer k) (insertPointer k)*localSupply k).submatrix
    (insertDonor k) (insertDonor k)

theorem local_net_exact (k : Sym2 Basis) :
    restrict Sectors.pointerOrbit (donorSector k) LoadExecution.netObservable=localNet k := by
  rw [LoadExecution.netObservable,restriction_sub,restriction_pullback eleven_preserves,
    restriction_pullback nine_preserves]
  rfl

theorem local_root_net_exact (k : Sym2 Basis) :
    restrict Sectors.pointerOrbit (donorSector k) LoadExecution.rootNet=localRootNet k := by
  rw [LoadExecution.rootNet,restriction_pullback pointer_preserves,local_net_exact]
  rfl

theorem local_readout_exact (k : Sym2 Basis) : restrict pceOrbit k LoadExecution.loadedNet=localReadout k := by
  rw [LoadExecution.loadedNet,donor_restriction,restriction_pullback supply_preserves,
    pointer_restriction,local_root_net_exact]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
