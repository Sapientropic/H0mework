import H0mework.Chemistry.LAlanineJointNext.SourceSourceBoundJointStep
import H0mework.Chemistry.LAlanineInertia.DynamicsVelocityVerletResidual

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Inertia.Mechanics Inertia.SourceParsing Force.Interface
open LAlanine40K2025.JointNext.Source
noncomputable section

def nuclearReference : PhasePoint :=
  verletStep stepReadout.nuclear.masses stepReadout.nuclear.duration stepReadout.nuclear.current.force
    stepReadout.nuclear.target.force stepReadout.nuclear.current.phase

def nuclearResidual : PhasePoint := ⟨stepReadout.nuclear.positionResidual, stepReadout.nuclear.momentumResidual⟩

theorem nuclearPosition_reconstruction : ∀ atom axis,
    stepReadout.nuclear.target.position atom axis = nuclearReference.position atom axis +
      stepReadout.nuclear.positionResidual atom axis := by
  change ∀ atom axis, coordinateRead _ atom axis = coordinateRead _ atom axis +
    Propagation.Producer.nativeClockStep * coordinateRead _ atom axis / massRead _ atom +
    Propagation.Producer.nativeClockStep ^ 2 * (-coordinateRead _ atom axis) /
      (2 * massRead _ atom) + coordinateRead _ atom axis
  rw [Propagation.Producer.nativeClockStep_exact]
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [massRead, coordinateRead, rationalRead]

theorem nuclearMomentum_reconstruction : ∀ atom axis,
    stepReadout.nuclear.target.momentum atom axis = nuclearReference.momentum atom axis +
      stepReadout.nuclear.momentumResidual atom axis := by
  change ∀ atom axis, coordinateRead _ atom axis = coordinateRead _ atom axis +
    Propagation.Producer.nativeClockStep * (-coordinateRead _ atom axis + -coordinateRead _ atom axis) / 2 +
    coordinateRead _ atom axis
  rw [Propagation.Producer.nativeClockStep_exact]
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [coordinateRead, rationalRead]

theorem nuclearPhase_reconstruction :
    stepReadout.nuclear.target.phase = addResidual nuclearReference nuclearResidual := by
  apply PhasePoint.ext <;> funext atom axis
  · exact nuclearPosition_reconstruction atom axis
  · exact nuclearMomentum_reconstruction atom axis

theorem nuclearPositionResidual_bound : ∀ atom axis,
    |stepReadout.nuclear.positionResidual atom axis| < (3 : ℚ) / 10 ^ 15 := by
  change ∀ atom axis, |coordinateRead _ atom axis| < (3 : ℚ) / 10 ^ 15
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [coordinateRead, rationalRead]

theorem nuclearMomentumResidual_bound : ∀ atom axis,
    |stepReadout.nuclear.momentumResidual atom axis| < (2 : ℚ) / 10 ^ 20 := by
  change ∀ atom axis, |coordinateRead _ atom axis| < (2 : ℚ) / 10 ^ 20
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [coordinateRead, rationalRead]

theorem nuclearPosition_changed : stepReadout.nuclear.target.position ≠ stepReadout.nuclear.current.position := by
  intro same
  have entry := congrFun (congrFun same (0 : Atom)) (0 : Axis)
  change rationalRead _ = rationalRead _ at entry
  norm_num [rationalRead] at entry

theorem nuclearMomentum_changed : stepReadout.nuclear.target.momentum ≠ stepReadout.nuclear.current.momentum := by
  intro same
  have entry := congrFun (congrFun same (0 : Atom)) (0 : Axis)
  change rationalRead _ = rationalRead _ at entry
  norm_num [rationalRead] at entry

theorem nuclearInitialMomentum_not_zero : stepReadout.nuclear.current.momentum ≠ 0 := by
  intro same
  have entry := congrFun (congrFun same (0 : Atom)) (0 : Axis)
  change rationalRead _ = 0 at entry
  norm_num [rationalRead] at entry

theorem nuclearReference_reverse :
    verletStep stepReadout.nuclear.masses (-stepReadout.nuclear.duration) stepReadout.nuclear.target.force
      stepReadout.nuclear.current.force nuclearReference = stepReadout.nuclear.current.phase :=
  verletStep_reverse _ _ _ _ _ Inertia.Producer.masses_nonzero

theorem nuclearActual_reverse_residual :
    verletStep stepReadout.nuclear.masses (-stepReadout.nuclear.duration) stepReadout.nuclear.target.force
      stepReadout.nuclear.current.force stepReadout.nuclear.target.phase =
      addResidual stepReadout.nuclear.current.phase
        (reverseResidual stepReadout.nuclear.masses stepReadout.nuclear.duration nuclearResidual) := by
  rw [nuclearPhase_reconstruction]
  exact verletStep_reverse_residual _ _ _ _ _ _ Inertia.Producer.masses_nonzero

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
