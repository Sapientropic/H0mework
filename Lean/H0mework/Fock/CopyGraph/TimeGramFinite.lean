import H0mework.Fock.CopyGraph.TimeGramModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index)
open SourceCopyTimeModel (Packet phases finitePhases recoveryErrors)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Filter
open scoped Topology
noncomputable section

theorem continuous_decode (depth : Nat) (index : Index depth) : Continuous (decode depth index) := by
  unfold decode solve synthesis SourceCopyTimeEnergy.part SourceCopyTimeModel.mass SourceCopyTimeModel.hilbert
  fun_prop

def finiteDecode (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  decode (inventoryBound runtime) index (finitePhases runtime index steps target)

theorem finite_source_error (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    target - finiteDecode runtime index steps target =
      decode (inventoryBound runtime) index (recoveryErrors runtime index steps target) := by
  rw [SourceCopyTimeModel.recovery_errors_source, decode_sub, decode_source]
  rfl

theorem finite_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) : Tendsto (fun steps => finiteDecode runtime index steps target) atTop (𝓝 target) := by
  have converges := (continuous_decode (inventoryBound runtime) index).continuousAt.tendsto.comp
    (SourceCopyTimeModel.finite_phases_tendsto runtime index target)
  simpa only [Function.comp_def, decode_source, finiteDecode] using converges

theorem finite_minimum (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target proposal : SourceJointClockGraph.Carrier) :
    ‖residual (inventoryBound runtime) index (finitePhases runtime index steps target)‖ ^ 2 ≤
      ‖WithLp.toLp 2 (finitePhases runtime index steps target) - analysis (inventoryBound runtime) index proposal‖ ^ 2 :=
  minimum _ index _ proposal

theorem finite_old_comparison (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    ‖WithLp.toLp 2 (finitePhases runtime index steps target) -
      analysis (inventoryBound runtime) index (SourceCopyTimeModel.finiteRestore runtime index steps target)‖ ^ 2 =
    ‖residual (inventoryBound runtime) index (finitePhases runtime index steps target)‖ ^ 2 +
      ‖analysis (inventoryBound runtime) index
        (finiteDecode runtime index steps target - SourceCopyTimeModel.finiteRestore runtime index steps target)‖ ^ 2 :=
  error_energy _ index _ _

theorem finite_next_correction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    type_of% (model_next_correction (inventoryBound runtime) index (finitePhases runtime index steps target)) ∧
      type_of% (SourceCopyTimeEnergy.whole_residual_budget runtime index steps target) ∧
      type_of% (SourceCopyTimeEnergy.finite_next_budget runtime index steps target) :=
  ⟨model_next_correction _ index _, SourceCopyTimeEnergy.whole_residual_budget runtime index steps target,
    SourceCopyTimeEnergy.finite_next_budget runtime index steps target⟩

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
