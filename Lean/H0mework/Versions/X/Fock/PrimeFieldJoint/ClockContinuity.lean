import H0mework.Versions.X.Fock.PrimeFieldJoint.ClockField
import H0mework.Versions.X.Fock.SourceHistoryClock.ComplexMoment

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointClock

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open SourceGeneratedAcquisitionJoint SourceClockComplex SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime Filter
open scoped Topology
noncomputable section

def scaledDensity (runtime : LivingRuntimeState process) : FieldSpace (depth runtime) (inventoryBound runtime) :=
  densityScale (inventoryBound runtime) • sourceDensity runtime

theorem scaled_density_word (runtime : LivingRuntimeState process) :
    word (depth runtime) (inventoryBound runtime) (scaledDensity runtime) =
      densityScale (inventoryBound runtime) • meanWord (inventoryBound runtime) := by
  change word _ _ (densityScale _ • density _ _) = _
  rw [LinearMap.map_smul_of_tower, density_word]

theorem scaled_density_joint (runtime : LivingRuntimeState process) :
    joint (depth runtime) (inventoryBound runtime) (scaledDensity runtime) =
      SourceMassCompletion.jointRead (densityScale (inventoryBound runtime) • meanWord (inventoryBound runtime)) :=
  congrArg SourceMassCompletion.jointRead (scaled_density_word runtime)

theorem scaled_density_clock (runtime : LivingRuntimeState process) :
    SourceClockComplex.clock (word (depth runtime) (inventoryBound runtime) (scaledDensity runtime)) = 1 := by
  rw [scaled_density_word, density_clock]

theorem actual_scaled_joint_tendsto (round : Nat) :
    Tendsto (fun future =>
      let runtime := roundRuntime (round + future)
      joint (depth runtime) (inventoryBound runtime) (scaledDensity runtime)) atTop
      (𝓝 (0 : SourceMassCompletion.Joint)) := by
  have future : Tendsto (fun future : Nat => round + future) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat round
  have actual := scaled_joint_tendsto.comp (inventory_cofinal.comp future)
  simpa only [Function.comp_def, scaled_density_joint] using actual

/-- This excludes a continuous read on the H/mass completion over all actual future source images. -/
theorem no_continuous_clock_recovery (round : Nat) (reader : SourceMassCompletion.Joint → ℂ)
    (continuous : ContinuousAt reader 0) :
    ¬ ∀ future : Nat, ∀ value : FieldSpace (depth (roundRuntime (round + future)))
      (inventoryBound (roundRuntime (round + future))),
      reader (joint (depth (roundRuntime (round + future))) (inventoryBound (roundRuntime (round + future))) value) =
        SourceClockComplex.clock (word (depth (roundRuntime (round + future)))
          (inventoryBound (roundRuntime (round + future))) value) := by
  intro recovered
  have atZero : reader 0 = 0 := by simpa only [map_zero] using recovered 0 0
  have limit := continuous.tendsto.comp (actual_scaled_joint_tendsto round)
  have readsOne (future : Nat) :
      reader (joint (depth (roundRuntime (round + future))) (inventoryBound (roundRuntime (round + future)))
        (scaledDensity (roundRuntime (round + future)))) = 1 :=
    (recovered future _).trans (scaled_density_clock _)
  have oneLimit : Tendsto (fun future =>
      reader (joint (depth (roundRuntime (round + future))) (inventoryBound (roundRuntime (round + future)))
        (scaledDensity (roundRuntime (round + future))))) atTop (𝓝 (1 : ℂ)) := by
    simpa only [readsOne] using (tendsto_const_nhds (x := (1 : ℂ)))
  exact one_ne_zero ((tendsto_nhds_unique oneLimit limit).trans atZero)

theorem native_realization (round : Nat) (sourceWord : Nat →₀ ℤ) :
    let runtime := sourceRound round (ofNative sourceWord)
    let value := realizeWord round (ofNative sourceWord)
    SourceClockComplex.clock (word (depth runtime) (inventoryBound runtime) value) =
        (SourceClockModel.clockRead (SourceClockModel.projection sourceWord) : ℂ) ∧
      joint (depth runtime) (inventoryBound runtime) value = SourceMassCompletion.nativeRead sourceWord ∧
      SourceClockComplex.clock (word (depth runtime) (inventoryBound runtime) value) =
        (SourcePrimeClockResidual.clockRead
          (SourceGeneratedActionObservationHistory.sourceMap SourcePrimeHistoryRecovery.nativeAction
            SourcePrimeClockResidual.jointObservation sourceWord) : ℂ) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [realization_word]
    exact model_source sourceWord
  · rw [realization_joint]
    exact joint_native sourceWord
  · rw [realization_word, clock_native, SourcePrimeClockSplitting.clock_source]

end
end SourceGeneratedJointClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
