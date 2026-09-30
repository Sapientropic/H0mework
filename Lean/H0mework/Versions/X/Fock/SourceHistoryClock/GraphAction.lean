import H0mework.Versions.X.Fock.SourceHistoryClock.GraphCarrier

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointClockGraph

open SourceJointTransfer SourceSuccessorBoundary
noncomputable section

def action : Carrier →L[ℂ] Carrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toContinuousLinearMap.comp
    ((SourceMassCompletion.action.toContinuousLinearMap.comp joint).prod
      (clock + SourceMassCompletion.massRead.comp joint))

def recover : Carrier →L[ℂ] Carrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toContinuousLinearMap.comp
    ((wholeTransfer.comp joint).prod (clock - SourceMassCompletion.massRead.comp joint))

def residual : Carrier →L[ℂ] Carrier := ContinuousLinearMap.id ℂ Carrier - action.comp recover

theorem action_apply (value : Carrier) :
    action value = WithLp.toLp 2 (SourceMassCompletion.action (joint value),
      clock value + SourceMassCompletion.massRead (joint value)) := rfl

theorem recover_apply (value : Carrier) :
    recover value = WithLp.toLp 2 (wholeTransfer (joint value),
      clock value - SourceMassCompletion.massRead (joint value)) := rfl

theorem action_source (word : Nat →₀ ℂ) : action (read word) = read (push ℂ word) := by
  rw [action_apply, joint_source, clock_source, read_apply, SourceMassCompletion.action_source,
    SourceClockComplex.clock_push]
  rfl

theorem recover_action (value : Carrier) : recover (action value) = value := by
  rw [recover_apply, action_apply]
  change WithLp.toLp 2 (wholeTransfer (SourceMassCompletion.action (joint value)),
    (clock value + SourceMassCompletion.massRead (joint value)) -
      SourceMassCompletion.massRead (SourceMassCompletion.action (joint value))) = value
  rw [IsometricRetainedTransfer.transfer_pullback, SourceMassCompletion.massRead_action, add_sub_cancel_right]
  change WithLp.toLp 2 (WithLp.ofLp value) = value
  exact WithLp.toLp_ofLp 2 value

theorem action_recover (value : Carrier) :
    action (recover value) = WithLp.toLp 2
      (SourceMassCompletion.action (wholeTransfer (joint value)), clock value) := by
  rw [action_apply, recover_apply]
  change WithLp.toLp 2 (SourceMassCompletion.action (wholeTransfer (joint value)),
    (clock value - SourceMassCompletion.massRead (joint value)) +
      SourceMassCompletion.massRead (wholeTransfer (joint value))) = _
  have mass : SourceMassCompletion.massRead (wholeTransfer (joint value)) =
      SourceMassCompletion.massRead (joint value) := by
    rw [whole_transfer]
    rfl
  rw [mass, sub_add_cancel]

theorem residual_formula (value : Carrier) :
    residual value = WithLp.toLp 2 (wholeResidual (joint value), (0 : ℂ)) := by
  change value - action (recover value) = _
  rw [action_recover]
  change WithLp.toLp 2 (WithLp.ofLp value) -
    WithLp.toLp 2 (SourceMassCompletion.action (wholeTransfer (joint value)), clock value) = _
  rw [← WithLp.toLp_sub]
  change WithLp.toLp 2 (joint value - SourceMassCompletion.action (wholeTransfer (joint value)),
    clock value - clock value) = _
  rw [sub_self]
  rfl

theorem reconstruction (value : Carrier) : action (recover value) + residual value = value := by
  change action (recover value) + (value - action (recover value)) = value
  abel

theorem range_joint_iff (value : Carrier) :
    value ∈ action.toLinearMap.range ↔ joint value ∈ SourceMassCompletion.action.toLinearMap.range := by
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨joint source, rfl⟩
  · rintro ⟨source, sourceEq⟩
    change SourceMassCompletion.action source = joint value at sourceEq
    refine ⟨WithLp.toLp 2 (source, clock value - SourceMassCompletion.massRead source), ?_⟩
    change action (WithLp.toLp 2 (source, clock value - SourceMassCompletion.massRead source)) = value
    rw [action_apply]
    change WithLp.toLp 2 (SourceMassCompletion.action source,
      (clock value - SourceMassCompletion.massRead source) + SourceMassCompletion.massRead source) = value
    rw [sourceEq, sub_add_cancel]
    change WithLp.toLp 2 (WithLp.ofLp value) = value
    exact WithLp.toLp_ofLp 2 value

theorem action_range (value : Carrier) :
    value ∈ action.toLinearMap.range ↔ SourceMassCompletion.firstRead (joint value) 0 = 0 :=
  (range_joint_iff value).trans (SourceJointTransfer.action_range (joint value))

theorem native_word_action (word : Nat →₀ ℤ) :
    SourceClockComplex.ofNative (push ℤ word) = push ℂ (SourceClockComplex.ofNative word) := by
  change Finsupp.linearCombination ℤ (fun index => Finsupp.single index (1 : ℂ))
      (Finsupp.mapDomain Nat.succ word) =
    ((push ℂ).restrictScalars ℤ)
      (Finsupp.linearCombination ℤ (fun index => Finsupp.single index (1 : ℂ)) word)
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  congr 1
  apply congrArg (Finsupp.linearCombination ℤ)
  funext index
  change Finsupp.single (index + 1) (1 : ℂ) = push ℂ (Finsupp.single index 1)
  simp only [push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem native_next
    (runtime : LivingRuntimeState NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.process) :
    action (read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))) =
      read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next)) := by
  rw [action_source, ← native_word_action]
  change read (SourceClockComplex.ofNative
    (SourceOperationNative.sourceAction NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.process
      (SourceOperationNative.point runtime))) = _
  rw [SourceOperationNative.sourceAction_point]

end
end SourceJointClockGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
