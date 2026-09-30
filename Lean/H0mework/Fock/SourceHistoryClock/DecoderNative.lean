import H0mework.Fock.SourceHistoryClock.DecoderError

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointClockDecoder

open SourceJointClockGraph SourceOwnedObservationHistory SourceOwnedObservationHistory.SourceShift
open SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_next_minimum (runtime : LivingRuntimeState process) (decoder : SourceJointClockGraph.Carrier) :
    IsMinOn (fun proposal => ‖read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next)) -
      action proposal‖ ^ 2) Set.univ decoder ↔
      decoder = read (SourceClockComplex.ofNative (SourceOperationNative.point runtime)) := by
  rw [unique_minimum, ← native_next, recover_action]

theorem native_next_cost (runtime : LivingRuntimeState process) :
    ‖read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next)) -
      action (read (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))‖ ^ 2 = 0 := by
  rw [native_next, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem root_unit_cost :
    ‖residual (read (SourceClockComplex.ofNative (sourcePoint 0)))‖ ^ 2 = 1 := by
  rw [SourceJointClockGraph.residual_norm_sq, joint_source, SourceClockComplex.joint_native,
    SourceMassCompletion.nativeRead_point, SourceMassCompletion.jointRead_single, one_smul]
  change ‖basis 0 0‖ ^ 2 = 1
  simp [basis, lp.single_apply]

theorem root_recovery_not_finite :
    recover (read (SourceClockComplex.ofNative (sourcePoint 0))) ∉ read.range := by
  rw [root_unit_recovery]
  rintro ⟨word, same⟩
  have first := congrArg (fun value : SourceJointClockGraph.Carrier => SourceMassCompletion.firstRead (joint value)) same
  change readWord word = 0 at first
  have zeroWord : word = 0 := readWord_injective (first.trans (map_zero _).symm)
  have mass := congrArg (fun value : SourceJointClockGraph.Carrier => SourceMassCompletion.massRead (joint value)) same
  change SourceSuccessorBoundary.mass ℂ word = 1 at mass
  rw [zeroWord, map_zero] at mass
  exact zero_ne_one mass

theorem finite_root_cost_strict (word : Nat →₀ ℂ) :
    1 < ‖read (SourceClockComplex.ofNative (sourcePoint 0)) - action (read word)‖ ^ 2 := by
  have lower := decoder_lower (read (SourceClockComplex.ofNative (sourcePoint 0))) (read word)
  rw [root_unit_cost] at lower
  apply lt_of_le_of_ne lower
  intro equal
  have attained : ‖read (SourceClockComplex.ofNative (sourcePoint 0)) - action (read word)‖ ^ 2 =
      ‖residual (read (SourceClockComplex.ofNative (sourcePoint 0)))‖ ^ 2 := by
    rw [root_unit_cost]
    exact equal.symm
  have same := (minimum_fibre _ _).mp attained
  exact root_recovery_not_finite ⟨word, same⟩

end
end SourceJointClockDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
