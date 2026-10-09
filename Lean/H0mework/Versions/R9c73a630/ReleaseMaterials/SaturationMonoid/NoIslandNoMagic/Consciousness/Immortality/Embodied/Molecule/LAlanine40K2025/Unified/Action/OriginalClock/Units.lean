import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.CanonicalUnits
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerElectronic
import H0mework.Versions.AB.Chemistry.LAlanineReentry.SourceSourceBoundReentry

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.OriginalClock
open SaturationMonoid.PhysicsCore Stage10.ActionNormalization
open AtomicScales Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceElapsed (elapsed : ℝ) : ℝ := elapsed * sourceTime

def originalQ : ℝ := (Reentry.Source.stepReadout.nuclear.duration : ℝ)

def nativeQ : ℝ := sourceElapsed originalQ

theorem original_q : originalQ = (Reentry.Continuation.duration : ℝ) := by
  rw [originalQ, Reentry.Source.duration_eq_original]

theorem source_elapsed_energy (elapsed : ℝ) : sourceElapsed elapsed * sourceEnergy = elapsed := by
  rw [sourceElapsed, mul_assoc, source_phase_unit, mul_one]

theorem original_q_source_units : nativeQ * sourceEnergy = originalQ := source_elapsed_energy originalQ

theorem original_q_from_action : nativeQ = originalQ * (phaseMomentum / canonicalHartree) := by
  rw [source_time_from_action]
  rfl

theorem native_clock_unique (duration : ℝ) (phase : duration * sourceEnergy = originalQ) : duration = nativeQ := by
  apply mul_right_cancel₀ energy_positive.ne'
  exact phase.trans original_q_source_units.symm

theorem original_q_positive : 0 < originalQ := by
  rw [original_q]
  exact_mod_cast Propagation.Producer.nativeClockStep_positive

theorem native_q_positive : 0 < nativeQ := mul_pos original_q_positive time_positive

theorem double_native_clock_rejected : (2*nativeQ)*sourceEnergy ≠ originalQ := by
  rw [mul_assoc, original_q_source_units]
  linarith [original_q_positive]


def sourceUnitHamiltonian : Matrix Basis Basis ℂ := sourceEnergy • Reentry.Source.hamiltonian

theorem source_unit_hamiltonian_hermitian : sourceUnitHamiltonian.IsHermitian :=
  Reentry.Producer.sourceHamiltonian_hermitian.smul (isSelfAdjoint_iff.mpr rfl)

def sourceUnitFrozen (duration : ℝ) : Matrix.unitaryGroup Basis ℂ :=
  JointNext.Math.frozenUnitary sourceUnitHamiltonian source_unit_hamiltonian_hermitian duration

private theorem source_time_generator (elapsed : ℝ) (H : Matrix Basis Basis ℂ) :
    sourceElapsed elapsed • (-Complex.I • (sourceEnergy • H)) = elapsed • (-Complex.I • H) := by
  rw [smul_comm (sourceElapsed elapsed) (-Complex.I), smul_smul, source_elapsed_energy, smul_comm]

theorem original_frozen_source_units (elapsed : ℝ) :
    (sourceUnitFrozen (sourceElapsed elapsed) : Matrix Basis Basis ℂ) =
      JointNext.Math.frozenUnitary Reentry.Source.hamiltonian Reentry.Producer.sourceHamiltonian_hermitian elapsed := by
  simp only [sourceUnitFrozen, JointNext.Math.frozenUnitary_eq_exp, sourceUnitHamiltonian, source_time_generator]

theorem source_unit_frozen_hasDerivAt (duration : ℝ) :
    HasDerivAt (fun time => (sourceUnitFrozen time : Matrix Basis Basis ℂ))
      ((sourceUnitFrozen duration : Matrix Basis Basis ℂ) * (-Complex.I • sourceUnitHamiltonian)) duration :=
  JointNext.Math.frozenUnitary_hasDerivAt _ _ _

def sourceUnitJoint : Matrix.unitaryGroup Basis ℂ :=
  ElectronicFrame.Polar.unitary Reentry.Source.crossMatrix Reentry.Producer.sourceCross_close * sourceUnitFrozen nativeQ

theorem original_joint_source_units : sourceUnitJoint = Reentry.Producer.sourceJointUnitary := by
  apply Subtype.ext
  change (ElectronicFrame.Polar.unitary Reentry.Source.crossMatrix Reentry.Producer.sourceCross_close : Matrix Basis Basis ℂ) *
      (sourceUnitFrozen (sourceElapsed originalQ) : Matrix Basis Basis ℂ) = _
  rw [original_frozen_source_units, original_q]
  rfl

theorem original_joint_target_source_units :
    Unitary.conjStarAlgAut ℂ _ sourceUnitJoint Reentry.Runtime.reentryParentHeld = Reentry.Producer.exactTarget := by
  rw [original_joint_source_units]
  exact Reentry.Producer.exactTarget_joint.symm

end
end LAlanine40K2025.UnifiedAction.OriginalClock
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
