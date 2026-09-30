import H0mework.Versions.X.Fock.HistoryConditional.GWordProgramSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGProgramInverse

open SourceOwnedObservationHistory.SourceShift
open scoped InnerProductSpace
noncomputable section

def hilbertRecover (program : Nat × Nat) (positive : 0 < program.1) : H →L[ℂ] H :=
  IsometricRetainedTransfer.transfer (SourceGWordProgram.hilbertAction program positive)

def jointRecover (program : Nat × Nat) (positive : 0 < program.1) : SourceMassCompletion.Joint →L[ℂ] SourceMassCompletion.Joint :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
    (((hilbertRecover program positive).comp SourceMassCompletion.firstRead).prod SourceMassCompletion.massRead)

def recover (program : Nat × Nat) (positive : 0 < program.1) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toContinuousLinearMap.comp
    (((jointRecover program positive).comp SourceJointClockGraph.joint).prod
      (((program.1 : ℂ)⁻¹) • (SourceJointClockGraph.clock -
        (program.2 : ℂ) • (SourceMassCompletion.massRead.comp SourceJointClockGraph.joint))))

theorem recover_coordinate (program : Nat × Nat) (positive : 0 < program.1) (value : H) (coordinate : Nat) :
    hilbertRecover program positive value coordinate = value (SourceCopyWordAffine.execute program coordinate) := by
  have same : ⟪lp.single 2 coordinate (1 : ℂ), hilbertRecover program positive value⟫_ℂ =
      ⟪lp.single 2 (SourceCopyWordAffine.execute program coordinate) (1 : ℂ), value⟫_ℂ := by
    change ⟪lp.single 2 coordinate (1 : ℂ), (SourceGWordProgram.hilbertAction program positive).toContinuousLinearMap.adjoint value⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact congrArg (fun source : H => inner ℂ source value) (SourceGWordProgram.hilbert_single program positive coordinate 1)
  rw [lp.inner_single_left, lp.inner_single_left] at same
  simpa using same

theorem recover_apply (program : Nat × Nat) (positive : 0 < program.1) (value : SourceJointClockGraph.Carrier) :
    recover program positive value = WithLp.toLp 2
      (WithLp.toLp 2 (hilbertRecover program positive (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value)),
        SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
        (program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock value -
          (program.2 : ℂ) * SourceMassCompletion.massRead (SourceJointClockGraph.joint value))) := rfl

theorem recover_action (program : Nat × Nat) (positive : 0 < program.1) (value : SourceJointClockGraph.Carrier) :
    recover program positive (SourceGWordProgram.action program positive value) = value := by
  change WithLp.toLp 2 (WithLp.toLp 2
    (hilbertRecover program positive (SourceGWordProgram.hilbertAction program positive
      (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))),
      SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
    (program.1 : ℂ)⁻¹ * (((program.1 : ℂ) * SourceJointClockGraph.clock value +
      (program.2 : ℂ) * SourceMassCompletion.massRead (SourceJointClockGraph.joint value)) -
      (program.2 : ℂ) * SourceMassCompletion.massRead (SourceJointClockGraph.joint value))) = _
  rw [hilbertRecover, IsometricRetainedTransfer.transfer_pullback, add_sub_cancel_right,
    inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr positive.ne')]
  exact WithLp.toLp_ofLp 2 value

end
end SourceGProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
