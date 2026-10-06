import H0mework.Chemistry.LAlanineHeldForce.SourceSourceBoundLAlanineHeldForce
import H0mework.Versions.AB.Chemistry.LAlanineHeldForce.RuntimeHeldForceParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Runtime

open Propagation.Interface
noncomputable section

/-- A force/energy refresh at fixed physical time, with the old inertial history retained separately. -/
def heldForceRefreshedFrame : Inertia.Interface.NuclearFrame :=
  { heldForceParentFrame with
    force := -Source.rawGradient
    potential := Source.rawEnergy
    total := heldForceParentFrame.kinetic + Source.rawEnergy }

structure HeldForceResult where
  held : Matrix Basis Basis ℂ
  realized : Matrix Basis Basis ℂ
  realizationResidual : Matrix Basis Basis ℂ
  frame : Inertia.Interface.NuclearFrame
  energyLedger : Energy.Interface.MolecularEnergyLedger
  gradientComponents : Array (Array (Array Int))
  gradientPicohartree : Force.Interface.NuclearCoordinates
  forcePicohartree : Force.Interface.NuclearCoordinates
  gradientResidual : Force.Interface.NuclearCoordinates
  stationaryCorrection : Force.Interface.NuclearCoordinates

def heldForceSourceResult : HeldForceResult where
  held := heldForceParentHeld
  realized := Source.realizedHeld
  realizationResidual := Source.realizedHeld - heldForceParentHeld
  frame := heldForceRefreshedFrame
  energyLedger := Source.energyLedger
  gradientComponents := Source.gradientComponentsReadout
  gradientPicohartree := Source.gradientPicohartree
  forcePicohartree := Source.forcePicohartree
  gradientResidual := Source.gradientResidual
  stationaryCorrection := Source.stationaryCorrection

theorem heldForceRefreshedFrame_no_motion :
    heldForceRefreshedFrame.position = heldForceParentFrame.position ∧
    heldForceRefreshedFrame.momentum = heldForceParentFrame.momentum ∧
    heldForceRefreshedFrame.kinetic = heldForceParentFrame.kinetic := ⟨rfl, rfl, rfl⟩

theorem heldForceRefreshedFrame_response :
    heldForceRefreshedFrame.force = -Source.rawGradient ∧
    heldForceRefreshedFrame.potential = Source.rawEnergy ∧
    heldForceRefreshedFrame.total = heldForceRefreshedFrame.kinetic + Source.rawEnergy := ⟨rfl, rfl, rfl⟩

end
end LAlanine40K2025.HeldForce.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
