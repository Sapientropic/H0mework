import H0mework.Fock.HistoryConditional.MinimumSharedNextConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumWindowError

open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (realize retained residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (Window decode)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def readout (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Window runtime index →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (realize runtime index steps).comp (decode runtime index nonunit steps)

theorem readout_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    readout runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) target) =
      retained runtime index steps target := by
  rw [readout, LinearMap.comp_apply, SourceOperatorObservationAcquisition.decode_source]
  rfl

theorem readout_retained (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Window runtime index) :
    retained runtime index steps (readout runtime index nonunit steps samples) =
      readout runtime index nonunit steps samples := by
  simp only [readout, LinearMap.comp_apply, retained, SourceCopyCurrentCoordinates.realize_source]

theorem error_vector (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (target : SourceJointClockGraph.Carrier) (error : Window runtime index) :
    target - readout runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) target + error) =
      -readout runtime index nonunit steps error + residual runtime index steps target := by
  rw [map_add, readout_source]
  calc
    _ = (retained runtime index steps target + residual runtime index steps target) -
      (retained runtime index steps target + readout runtime index nonunit steps error) :=
        congrArg (fun value => value - (retained runtime index steps target + readout runtime index nonunit steps error))
          (SourceCopyCurrentCoordinates.reconstruction runtime index steps target).symm
    _ = _ := by abel

theorem readout_orthogonal (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (target : SourceJointClockGraph.Carrier) (error : Window runtime index) :
    ⟪readout runtime index nonunit steps error, residual runtime index steps target⟫_ℂ = 0 := by
  have paid := SourceCopyCurrentCoordinates.retained_orthogonal runtime index steps
    (readout runtime index nonunit steps error) target
  rwa [readout_retained] at paid

theorem error_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (target : SourceJointClockGraph.Carrier) (error : Window runtime index) :
    ‖target - readout runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) target + error)‖ ^ 2 =
      ‖residual runtime index steps target‖ ^ 2 + ‖readout runtime index nonunit steps error‖ ^ 2 := by
  rw [error_vector, norm_add_sq (𝕜 := ℂ), inner_neg_left, readout_orthogonal, neg_zero, RCLike.zero_re, mul_zero, add_zero, norm_neg]
  exact add_comm _ _

end
end SourceMinimumWindowError
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
