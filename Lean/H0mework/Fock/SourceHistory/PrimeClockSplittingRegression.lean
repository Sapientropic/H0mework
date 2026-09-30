import H0mework.Fock.PrimeField.ClockSplittingReading

/-! Full action fidelity and the original unit prevent treating the section as a free dynamical reset. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery SourcePrimeClockResidual
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

theorem joint_action_injective : Function.Injective (fieldAction (process := process) jointRead) := by
  intro left right same
  have prime := congrArg primeProjection same
  rw [projection_action, projection_action] at prime
  have samePrime := SourcePrimeCompletion.field_action_injective sourceOwner prime
  apply joint_ext left right samePrime
  have clock := congrArg clockRead same
  rw [clock_action, clock_action, samePrime] at clock
  exact add_right_cancel clock

theorem no_preimage_native_unit : ¬ ∃ value : JointField,
    fieldAction (process := process) jointRead value = fieldPoint (process := process) jointRead 0 := by
  rintro ⟨value, same⟩
  have prime := congrArg primeProjection same
  rw [projection_action] at prime
  have unit : primeProjection (fieldPoint (process := process) jointRead 0) = fieldPoint (process := process) rawField 0 :=
    projection_source (SourceOperationNative.statePoint process 0)
  rw [unit] at prime
  exact SourcePrimeCompletion.no_preimage_original_unit sourceOwner ⟨primeProjection value, prime⟩

theorem section_not_equivariant :
    fieldAction (process := process) jointRead (sectionMap (fieldPoint (process := process) rawField 0)) ≠
      sectionMap (fieldAction (process := process) rawField (fieldPoint (process := process) rawField 0)) := by
  intro same
  have clock := congrArg clockRead same
  rw [unit_section_action_defect.1, unit_section_action_defect.2] at clock
  exact one_ne_zero clock

theorem native_unit_keeps_clock :
    (coordinates (fieldPoint (process := process) jointRead 0)).2 = 1 :=
  congrArg Prod.snd (native_coordinates runtimeSeed)

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
