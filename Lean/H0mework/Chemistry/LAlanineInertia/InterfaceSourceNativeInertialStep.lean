import H0mework.Chemistry.LAlanineInertia.DynamicsVelocityVerlet

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Interface

structure NuclearFrame where
  position : Mechanics.Coordinates
  momentum : Mechanics.Coordinates
  force : Mechanics.Coordinates
  kinetic : ℚ
  potential : ℚ
  total : ℚ

def NuclearFrame.phase (frame : NuclearFrame) : Mechanics.PhasePoint :=
  ⟨frame.position, frame.momentum⟩

/-- Numerical output and residuals are raw source reads, not success premises. -/
structure InertialStepReadout where
  masses : Mechanics.Masses
  duration : ℚ
  current : NuclearFrame
  target : NuclearFrame
  positionResidual : Mechanics.Coordinates
  momentumResidual : Mechanics.Coordinates
  currentLedger : Energy.Interface.MolecularEnergyLedger
  targetLedger : Energy.Interface.MolecularEnergyLedger
  currentNuclei : Array (String × Nat)
  targetNuclei : Array (String × Nat)
  currentPositionPicobohr : Force.Interface.NuclearCoordinates
  targetPositionPicobohr : Force.Interface.NuclearCoordinates
  currentGradientComponents : Array (Array (Array Int))
  targetGradientComponents : Array (Array (Array Int))
  currentGradientRoundingResidual : Force.Interface.NuclearCoordinates
  targetGradientRoundingResidual : Force.Interface.NuclearCoordinates
  currentGradientPicohartree : Force.Interface.NuclearCoordinates
  targetGradientPicohartree : Force.Interface.NuclearCoordinates

end LAlanine40K2025.Inertia.Interface
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
