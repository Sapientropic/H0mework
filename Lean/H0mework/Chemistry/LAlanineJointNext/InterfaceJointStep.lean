import H0mework.Chemistry.LAlanineJointNext.DynamicsJointEvolution
import H0mework.Chemistry.LAlanineJointNext.RuntimeParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Interface

open Propagation.Interface LAlanine40K2025.JointNext.Runtime
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

/-- Raw same-event readouts; the new response is not an input to electronic evolution or drift. -/
structure JointStepReadout where
  nuclear : Inertia.Interface.InertialStepReadout
  frozenHamiltonianNumerator : Matrix Basis Basis Int
  crossNumerator : Matrix Basis Basis Int
  targetDensityRealNumerator : Matrix Basis Basis Int
  targetDensityImagNumerator : Matrix Basis Basis Int

def JointStepReadout.frozenHamiltonian (packet : JointStepReadout) : Matrix Basis Basis ℂ :=
  fun i j => (packet.frozenHamiltonianNumerator i j : ℂ) / 1000000000000

def JointStepReadout.crossMatrix (packet : JointStepReadout) : Matrix Basis Basis ℂ :=
  fun i j => (packet.crossNumerator i j : ℂ) / 1000000000000000

def JointStepReadout.targetRealized (packet : JointStepReadout) : Matrix Basis Basis ℂ :=
  fun i j => ((packet.targetDensityRealNumerator i j : ℂ) +
    Complex.I * (packet.targetDensityImagNumerator i j : ℂ)) / 1000000000000000

def duration : ℚ := Propagation.Producer.nativeClockStep
def targetClock : ℚ := jointParentTime + duration

def generatedPosition : Inertia.Mechanics.Coordinates :=
  Inertia.Mechanics.positionNext jointParentMasses duration jointParentFrame.position
    jointParentFrame.momentum jointParentFrame.force

def finishMomentum (targetForce : Inertia.Mechanics.Coordinates) : Inertia.Mechanics.Coordinates :=
  Inertia.Mechanics.momentumNext duration jointParentFrame.momentum jointParentFrame.force targetForce

def exactElectronicTarget (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian)
    (cross : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  Math.electronicAdvance H hermitian (duration : ℝ) cross jointParentHeld

def realizedInputTarget (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian)
    (cross : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  Math.electronicAdvance H hermitian (duration : ℝ) cross jointParentRealization.1

theorem nuclear_stages (targetForce : Inertia.Mechanics.Coordinates) :
    (⟨generatedPosition, finishMomentum targetForce⟩ : Inertia.Mechanics.PhasePoint) =
      Inertia.Mechanics.halfKick duration targetForce
        (Inertia.Mechanics.drift jointParentMasses duration
          (Inertia.Mechanics.halfKick duration jointParentFrame.force jointParentFrame.phase)) :=
  Inertia.Mechanics.verletStep_split jointParentMasses duration jointParentFrame.force
    targetForce jointParentFrame.phase Inertia.Producer.masses_nonzero

theorem targetClock_exact : targetClock = 2 * Propagation.Producer.nativeClockStep := by
  rw [targetClock, jointParent_clock]
  unfold duration
  ring

theorem one_elapsed_clock : targetClock - jointParentTime = duration ∧ 0 < duration :=
  ⟨add_sub_cancel_left _ _, Propagation.Producer.nativeClockStep_positive⟩

theorem elapsed_not_doubled : targetClock - jointParentTime ≠ 2 * duration := by
  rw [one_elapsed_clock.1]
  have positive := one_elapsed_clock.2
  linarith

theorem inherited_realization_error (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian)
    (cross : Matrix Basis Basis ℂ) (close : ‖cross - 1‖ < 1) :
    ‖realizedInputTarget H hermitian cross - exactElectronicTarget H hermitian cross‖ < (8 : ℝ) / 10 ^ 9 := by
  rw [realizedInputTarget, exactElectronicTarget, Math.electronicAdvance_error_eq H hermitian _ _ _ _ close]
  exact jointParentFirstForceReceipt.realizationError

end
end LAlanine40K2025.JointNext.Interface
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
