import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Observable
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Restriction

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open Propagation.Interface Load.Source Collision
open scoped Matrix
noncomputable section

def donorSector (k : Sym2 Basis) : Sym2 (Sym2 Basis) := s(k,pcOrbit Supply.donorIndex)
abbrev BodyFiber (k : Sym2 Basis) := {i : PairController × Fin 2 // pceOrbit i=k}
abbrev FullFiber (k : Sym2 Basis) := {i : Current.FullIndex // Sectors.reservoirOrbit i=donorSector k}
abbrev PointerFiber (k : Sym2 Basis) := {i : PointerIndex // Sectors.pointerOrbit i=donorSector k}

def insertDonor (k : Sym2 Basis) (i : BodyFiber k) : FullFiber k :=
  ⟨((i.val.1,Supply.donorIndex),i.val.2),congrArg (fun p => s(p,pcOrbit Supply.donorIndex)) i.property⟩

def insertPointer (k : Sym2 Basis) (i : FullFiber k) : PointerFiber k := ⟨Sum.inl i.val,i.property⟩

theorem donorSector_injective : Function.Injective donorSector := fixed_donor_injective _

theorem donor_restriction (k : Sym2 Basis) (O : Current.FullJoint) :
    restrict pceOrbit k (Supply.donorSlice O)=
      (restrict Sectors.reservoirOrbit (donorSector k) O).submatrix (insertDonor k) (insertDonor k) := rfl

theorem pointer_restriction (k : Sym2 Basis) (O : PointerJoint) :
    restrict Sectors.reservoirOrbit (donorSector k) (Prepared.pointerReadout O)=
      (restrict Sectors.pointerOrbit (donorSector k) O).submatrix (insertPointer k) (insertPointer k) := rfl

theorem body_fiber_card (k : Sym2 Basis) : Fintype.card (BodyFiber k) ≤ 8 := pce_fiber_card_le_eight k

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
