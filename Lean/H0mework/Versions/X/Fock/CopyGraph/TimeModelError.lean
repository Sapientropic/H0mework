import H0mework.Versions.X.Fock.CopyGraph.TimeModelFinite

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceOwnedObservationHistory.SourceShift (H)
noncomputable section

theorem axes_sub (firstMass firstClock secondMass secondClock : ℂ) :
    SourceCopyGraph.axes (firstMass - secondMass) (firstClock - secondClock) =
      SourceCopyGraph.axes firstMass firstClock - SourceCopyGraph.axes secondMass secondClock := by
  unfold SourceCopyGraph.axes
  rw [← WithLp.toLp_sub]
  change WithLp.toLp 2 (WithLp.toLp 2 ((0 : H), firstMass - secondMass), firstClock - secondClock) =
    WithLp.toLp 2 (WithLp.toLp 2 ((0 : H), firstMass) - WithLp.toLp 2 ((0 : H), secondMass), firstClock - secondClock)
  rw [← WithLp.toLp_sub]
  change WithLp.toLp 2 (WithLp.toLp 2 ((0 : H), firstMass - secondMass), firstClock - secondClock) =
    WithLp.toLp 2 (WithLp.toLp 2 ((0 : H) - 0, firstMass - secondMass), firstClock - secondClock)
  rw [sub_self]

theorem restore_sub (depth : Nat) (index : Index depth) (left right : Packet depth index) :
    restore depth index (left - right) = restore depth index left - restore depth index right := by
  simp only [restore, Pi.sub_apply, mass, map_sub, mul_sub, axes_sub, Finset.sum_sub_distrib, smul_sub]
  abel

def residuals (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : Packet (inventoryBound runtime) index := fun phase =>
  SourceRecordedEvolution.residual runtime index steps (time phase.val target)

def recoveryErrors (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : Packet (inventoryBound runtime) index := fun phase =>
  SourceCopyGraph.recover (inventoryBound runtime) index (residuals runtime index steps target phase)

theorem recovery_errors_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    recoveryErrors runtime index steps target = phases (inventoryBound runtime) index target - finitePhases runtime index steps target := by
  funext phase
  change SourceCopyGraph.recover (inventoryBound runtime) index
    (SourceRecordedEvolution.residual runtime index steps (time phase.val target)) = _
  rw [SourceRecordedEvolution.residual, SourceCopyCofinal.advanced_action, map_sub, SourceCopyGraph.recover_action]
  simp only [Pi.sub_apply, phase_source, finitePhases]

theorem finite_error_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    target - finiteRestore runtime index steps target =
      restore (inventoryBound runtime) index (recoveryErrors runtime index steps target) := by
  rw [recovery_errors_source, restore_sub, restore_source]
  rfl

theorem finite_next_error_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.action target -
      restore (inventoryBound runtime) index (next (inventoryBound runtime) index (finitePhases runtime index steps target)) =
        restore (inventoryBound runtime) index (next (inventoryBound runtime) index (recoveryErrors runtime index steps target)) := by
  rw [recovery_errors_source, map_sub, restore_sub, next_source, restore_source]

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
