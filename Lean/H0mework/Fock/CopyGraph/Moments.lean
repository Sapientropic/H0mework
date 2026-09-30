import H0mework.Fock.CopyGraph.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift
noncomputable section

def axes (massValue clockValue : ℂ) : SourceJointClockGraph.Carrier :=
  WithLp.toLp 2 (WithLp.toLp 2 ((0 : H), massValue), clockValue)

theorem native_residual_hilbert (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    hilbertResidual depth index (readWord (SourceClockComplex.ofNative word)) =
      readWord (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)) := by
  change readWord (SourceClockComplex.ofNative word) -
    hilbertAction depth index (hilbertRecover depth index (readWord (SourceClockComplex.ofNative word))) = _
  rw [recover_native_source, hilbert_source, ← complex_native]
  change _ = readWord (SourceClockComplex.ofNative (word - SourceCopyProgram.action depth index (SourceCopyProgram.recover depth index word)))
  rw [map_sub, map_sub]

theorem native_mass_balance (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    mass ℂ (SourceClockComplex.ofNative (SourceCopyProgram.recover depth index word)) +
      mass ℂ (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)) =
        mass ℂ (SourceClockComplex.ofNative word) := by
  have generated := congrArg (fun value : Nat →₀ ℤ => mass ℂ (SourceClockComplex.ofNative value))
    (SourceCopyProgram.reconstruct depth index word)
  change mass ℂ (SourceClockComplex.ofNative
    (SourceCopyProgram.action depth index (SourceCopyProgram.recover depth index word) + SourceCopyProgram.residual depth index word)) = _ at generated
  rw [map_add, map_add, complex_native, mass_copy] at generated
  exact generated

theorem native_clock_balance (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    (scale depth index : ℂ) * SourceClockComplex.clock (SourceClockComplex.ofNative (SourceCopyProgram.recover depth index word)) +
      SourceClockComplex.clock (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)) =
        SourceClockComplex.clock (SourceClockComplex.ofNative word) := by
  have generated := congrArg (fun value : Nat →₀ ℤ => SourceClockComplex.clock (SourceClockComplex.ofNative value))
    (SourceCopyProgram.reconstruct depth index word)
  change SourceClockComplex.clock (SourceClockComplex.ofNative
    (SourceCopyProgram.action depth index (SourceCopyProgram.recover depth index word) + SourceCopyProgram.residual depth index word)) = _ at generated
  rw [map_add, map_add, complex_native, clock_copy] at generated
  exact generated

theorem recovery_native_moments (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    recover depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative word)) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCopyProgram.recover depth index word)) +
        axes (mass ℂ (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)))
          ((scale depth index : ℂ)⁻¹ * SourceClockComplex.clock (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word))) := by
  have clock := native_clock_balance depth index word
  have clockEq : (scale depth index : ℂ)⁻¹ * SourceClockComplex.clock (SourceClockComplex.ofNative word) =
      SourceClockComplex.clock (SourceClockComplex.ofNative (SourceCopyProgram.recover depth index word)) +
        (scale depth index : ℂ)⁻¹ * SourceClockComplex.clock (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)) := by
    rw [← clock, mul_add, inv_mul_cancel_left₀ (scale_nonzero depth index)]
  rw [recover_apply, SourceJointClockGraph.joint_source, SourceJointClockGraph.clock_source,
    SourceMassCompletion.firstRead_source, SourceMassCompletion.massRead_source, recover_native_source,
    SourceJointClockGraph.read_apply, SourceMassCompletion.jointRead_apply]
  unfold axes
  rw [← WithLp.toLp_add]
  change WithLp.toLp 2 (WithLp.toLp 2 (_, mass ℂ (SourceClockComplex.ofNative word)),
      (scale depth index : ℂ)⁻¹ * SourceClockComplex.clock (SourceClockComplex.ofNative word)) =
    WithLp.toLp 2 (WithLp.toLp 2 _ + WithLp.toLp 2 _, _)
  rw [← WithLp.toLp_add]
  change WithLp.toLp 2 (WithLp.toLp 2 (_, mass ℂ (SourceClockComplex.ofNative word)), _) =
    WithLp.toLp 2 (WithLp.toLp 2 (readWord (SourceClockComplex.ofNative (SourceCopyProgram.recover depth index word)) + 0,
      mass ℂ (SourceClockComplex.ofNative (SourceCopyProgram.recover depth index word)) +
        mass ℂ (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word))), _)
  rw [add_zero, native_mass_balance, clockEq]

theorem residual_native_moments (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    residual depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative word)) +
      axes (mass ℂ (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)))
        (SourceClockComplex.clock (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word))) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)) := by
  rw [residual_apply, SourceJointClockGraph.joint_source, SourceMassCompletion.firstRead_source, native_residual_hilbert,
    SourceJointClockGraph.read_apply, SourceMassCompletion.jointRead_apply]
  unfold axes
  rw [← WithLp.toLp_add]
  change WithLp.toLp 2 (WithLp.toLp 2 _ + WithLp.toLp 2 _, _) = _
  rw [← WithLp.toLp_add]
  change WithLp.toLp 2 (WithLp.toLp 2
    (readWord (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index word)) + 0, 0 + _), 0 + _) = _
  rw [add_zero, zero_add, zero_add]

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
