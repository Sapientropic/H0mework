import H0mework.Versions.X.Fock.CopyGraph.Hilbert
import H0mework.Versions.X.Fock.SourceHistoryClock.GraphGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift
noncomputable section

def jointAction (depth : Nat) (index : Index depth) : SourceMassCompletion.Joint →L[ℂ] SourceMassCompletion.Joint :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
    (((hilbertAction depth index).toContinuousLinearMap.comp SourceMassCompletion.firstRead).prod SourceMassCompletion.massRead)

def action (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toContinuousLinearMap.comp
    (((jointAction depth index).comp SourceJointClockGraph.joint).prod
      ((scale depth index : ℂ) • SourceJointClockGraph.clock))

theorem joint_apply (depth : Nat) (index : Index depth) (value : SourceMassCompletion.Joint) :
    jointAction depth index value = WithLp.toLp 2
      (hilbertAction depth index (SourceMassCompletion.firstRead value), SourceMassCompletion.massRead value) := rfl

theorem action_apply (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    action depth index value = WithLp.toLp 2
      (jointAction depth index (SourceJointClockGraph.joint value),
        (scale depth index : ℂ) * SourceJointClockGraph.clock value) := rfl

theorem joint_source (depth : Nat) (index : Index depth) (word : Nat →₀ ℂ) :
    jointAction depth index (SourceMassCompletion.jointRead word) =
      SourceMassCompletion.jointRead (complexAction depth index word) := by
  rw [joint_apply, SourceMassCompletion.firstRead_source, SourceMassCompletion.massRead_source,
    SourceMassCompletion.jointRead_apply, hilbert_source, mass_copy]

theorem action_source (depth : Nat) (index : Index depth) (word : Nat →₀ ℂ) :
    action depth index (SourceJointClockGraph.read word) = SourceJointClockGraph.read (complexAction depth index word) := by
  rw [action_apply, SourceJointClockGraph.joint_source, SourceJointClockGraph.clock_source,
    joint_source, SourceJointClockGraph.read_apply, clock_copy]

theorem action_native (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    action depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative word)) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCopyProgram.action depth index word)) := by
  rw [action_source, complex_native]

theorem joint_norm_sq (depth : Nat) (index : Index depth) (value : SourceMassCompletion.Joint) :
    ‖jointAction depth index value‖ ^ 2 = ‖value‖ ^ 2 := by
  rw [joint_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖hilbertAction depth index (SourceMassCompletion.firstRead value)‖ ^ 2 +
    ‖SourceMassCompletion.massRead value‖ ^ 2 = ‖value‖ ^ 2
  rw [(hilbertAction depth index).norm_map]
  exact (WithLp.prod_norm_sq_eq_of_L2 value).symm

theorem action_energy (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖action depth index value‖ ^ 2 = ‖value‖ ^ 2 +
      ((scale depth index : ℝ) ^ 2 - 1) * ‖SourceJointClockGraph.clock value‖ ^ 2 := by
  rw [action_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖jointAction depth index (SourceJointClockGraph.joint value)‖ ^ 2 +
    ‖(scale depth index : ℂ) * SourceJointClockGraph.clock value‖ ^ 2 = _
  rw [joint_norm_sq, norm_mul, Complex.norm_natCast, SourceJointClockGraph.norm_sq]
  ring

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
