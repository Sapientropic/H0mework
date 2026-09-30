import H0mework.Versions.X.Fock.HistoryConditional.VectorConditional
import H0mework.Probability.Source.MomentCollision

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalVector

open SourceConditionalModel (Actors NextModel nextRead dynamicRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyNativeModelStep (sourceValue)
open SourceOwnedObservationHistory.SourceShift (basis H)
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem native_form (runtime : LivingRuntimeState process) :
    sourceValue runtime = WithLp.toLp 2 (WithLp.toLp 2 (basis runtime.state, (1 : ℂ)), (runtime.state : ℂ) + 1) := by
  rw [sourceValue, SourceOperationNative.point, SourceOperationNative.statePoint, SourceClockComplex.ofNative_single]
  simp only [Int.cast_one, SourceJointClockGraph.read_apply, SourceMassCompletion.jointRead_single,
    SourceClockComplex.clock_single, one_smul, one_mul]
  simp only [SourceClockModel.rawClock, Int.cast_add, Int.cast_natCast, Int.cast_one]

theorem pair_distance (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    ‖realizeModel runtime (nextRead runtime 0) -
      realizeModel runtime (nextRead runtime (SourceConditionalModel.two runtime enough))‖ ^ 2 = 6 := by
  simp only [realized_next, actor, SourceCopyNativeModelStep.source_value_next]
  change ‖sourceValue (runtimeAt 1) - sourceValue (runtimeAt 3)‖ ^ 2 = 6
  rw [native_form, native_form, runtimeAt_state, runtimeAt_state, ← WithLp.toLp_sub]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖WithLp.toLp 2 (basis 1, (1 : ℂ)) - WithLp.toLp 2 (basis 3, (1 : ℂ))‖ ^ 2 +
    ‖(((1 : Nat) : ℂ) + 1) - (((3 : Nat) : ℂ) + 1)‖ ^ 2 = 6
  rw [← WithLp.toLp_sub, WithLp.prod_norm_sq_eq_of_L2]
  change (‖basis 1 - basis 3‖ ^ 2 + ‖(1 : ℂ) - 1‖ ^ 2) +
    ‖(((1 : Nat) : ℂ) + 1) - (((3 : Nat) : ℂ) + 1)‖ ^ 2 = 6
  have orthogonal : inner ℂ (basis 1) (basis 3) = 0 := by
    change inner ℂ (lp.single (E := fun _ : Nat => ℂ) 2 1 1) (lp.single (E := fun _ : Nat => ℂ) 2 3 1) = 0
    rw [lp.inner_single_left]
    norm_num [lp.single_apply, inner]
  rw [norm_sub_sq (𝕜 := ℂ), orthogonal]
  norm_num [basis, lp.norm_single]

def dynamicError (runtime : LivingRuntimeState process) (depth : Nat)
    (decoder : Field parity → SourceJointClockGraph.Carrier) : ℝ :=
  ∑ i : Actors runtime, (historyPMF (inventoryBound runtime) i).toReal *
    ‖realizeModel runtime (nextRead runtime i) - decoder (dynamicRead runtime depth i)‖ ^ 2

theorem dynamic_error_lower (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime)
    (depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    3 / (inventoryBound runtime + 1 : ℝ) ≤ dynamicError runtime depth decoder := by
  have paid := SourceVectorMoment.equal_weight_pair (historyPMF (inventoryBound runtime))
    (realizeModel runtime ∘ nextRead runtime) (decoder ∘ dynamicRead runtime depth)
    0 (SourceConditionalModel.two runtime enough) (SourceConditionalModel.two_ne_zero runtime enough).symm
    (congrArg decoder (SourceConditionalModel.dynamic_same runtime enough depth)) (by rw [historyPMF_apply, historyPMF_apply])
  simp only [Function.comp_apply, pair_distance] at paid
  convert paid using 1
  · rw [historyPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    push_cast
    ring
  · rfl

end
end SourceConditionalVector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
