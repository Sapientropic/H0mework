import H0mework.Fock.CopyGraph.Field
import H0mework.Fock.CopyGraph.Geometry
import H0mework.Fock.CopyGraph.Effect
import H0mework.Versions.I.Fock.HistoryCopy.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceCyclicModule SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def NativeAt (round : Nat) (index : Index (sourceDepth round)) (target : Nat →₀ ℤ) : Prop :=
    let depth := sourceDepth round
    type_of% (action_native depth index target) ∧
      type_of% (original_recovery_realization round depth index target) ∧
      type_of% (original_residual_realization round depth index target) ∧
      type_of% (SourceCopyProgram.original_residual_consumed round index target) ∧
      type_of% (original_program_consumed round (SourceCyclicModule.coefficients.symm
        (SourceCopyProgram.recover depth index target))) ∧
      type_of% (original_program_consumed round (SourceCyclicModule.coefficients.symm
        (SourceCopyProgram.action depth index target)))

theorem original_native_consumed (round : Nat) (index : Index (sourceDepth round)) (target : Nat →₀ ℤ) :
    NativeAt round index target := by
  dsimp only [NativeAt]
  exact ⟨action_native _ index target, original_recovery_realization round _ index target,
    original_residual_realization round _ index target, SourceCopyProgram.original_residual_consumed round index target,
    original_program_consumed round _, original_program_consumed round _⟩

def RecoveryAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    type_of% (copy_current round) ∧
      (∀ index : Index depth,
        type_of% (material_program depth index) ∧ type_of% (copy_written_program depth index) ∧
        (∀ value : SourceJointClockGraph.Carrier,
          type_of% (recover_action depth index value) ∧ type_of% (reconstruction depth index value) ∧
          type_of% (action_energy depth index value) ∧ type_of% (retained_energy depth index value) ∧
          type_of% (source_norm_le depth index value) ∧ type_of% (action_range depth index value) ∧
          ∀ proposal : SourceJointClockGraph.Carrier, type_of% (exact_fibre depth index value proposal)) ∧
        (∀ value : FieldSpace depth depth, FieldAt round depth depth index value) ∧
        (∀ target : Nat →₀ ℤ, NativeAt round index target) ∧
        ∀ nonunit : index.val ≠ 0,
          type_of% (action_not_isometry depth index nonunit) ∧
            type_of% (native_residual_moments_retained depth index nonunit) ∧
            type_of% (residual_not_native_residual depth index nonunit)) ∧
      type_of% (SourceCopyObservation.sourceGeneratedCopyObservationRecovery round) ∧
      type_of% (coversAt_factorizes (roundRuntime round) .particleWave) ∧
      type_of% (coversAt_factorizes (roundRuntime round).tick.next .particleWave)

theorem sourceGeneratedCopyGraphRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨copy_current round,
    (fun index => ⟨material_program _ index, copy_written_program _ index,
      (fun value => ⟨recover_action _ index value, reconstruction _ index value,
        action_energy _ index value, retained_energy _ index value, source_norm_le _ index value,
        action_range _ index value, exact_fibre _ index value⟩),
      original_field_consumed round _ _ index, original_native_consumed round index,
      fun nonunit => ⟨action_not_isometry _ index nonunit, native_residual_moments_retained _ index nonunit,
        residual_not_native_residual _ index nonunit⟩⟩),
    SourceCopyObservation.sourceGeneratedCopyObservationRecovery round,
    coversAt_factorizes (roundRuntime round) .particleWave,
    coversAt_factorizes (roundRuntime round).tick.next .particleWave⟩

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
