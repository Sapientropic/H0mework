import H0mework.Versions.X.Fock.PrimeField.ClockResidualClock

/-! The full paired-to-prime fibre is exactly the generated clock unit, with its native action retained. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedScalarCofinalTopology.NativeProbability
open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem joint_ext (left right : JointField) (samePrime : primeProjection left = primeProjection right)
    (sameClock : clockRead left = clockRead right) : left = right := by
  apply Limits.Concrete.limit_ext (jointData.quotientTower jointLaws)
  intro stage
  apply jointData.stageRealization_injective stage.unop
  change stageRead nativeAction jointObservation stage.unop left = stageRead nativeAction jointObservation stage.unop right
  funext index
  apply Prod.ext
  · have source := congrFun (congrArg (stageRead nativeAction observation stage.unop) samePrime) index
    rw [projection_prefix, projection_prefix] at source
    exact source
  · rw [clock_prefix_read, clock_prefix_read, clock_law, clock_law, sameClock, samePrime]

theorem kernel_exact (value : JointField) (hidden : primeProjection value = 0) :
    value = clockRead value • residual := by
  apply joint_ext
  · rw [map_zsmul, residual_prime_zero, zsmul_zero, hidden]
  · simp only [map_zsmul, residual_clock_unit, zsmul_eq_mul, Int.cast_id, mul_one]

theorem fibre_exact (left right : JointField) :
    primeProjection left = primeProjection right ↔
      left - right = (clockRead left - clockRead right) • residual := by
  constructor
  · intro same
    have hidden : primeProjection (left - right) = 0 := by rw [map_sub, same, sub_self]
    simpa only [map_sub] using kernel_exact (left - right) hidden
  · intro same
    have projected := congrArg primeProjection same
    rw [map_sub, map_zsmul, residual_prime_zero, zsmul_zero] at projected
    exact sub_eq_zero.mp projected

theorem residual_fixed : fieldAction (process := process) jointRead residual = residual := by
  apply Limits.Concrete.limit_ext (jointData.quotientTower jointLaws)
  intro stage
  apply jointData.stageRealization_injective stage.unop
  change stageRead nativeAction jointObservation stage.unop (fieldAction (process := process) jointRead residual) =
    stageRead nativeAction jointObservation stage.unop residual
  calc
    _ = dropFirst (R := ℤ) stage.unop (stageRead nativeAction jointObservation (stage.unop + 1) residual) :=
      endomorphism_reads_dropFirst nativeAction jointObservation stage.unop residual
    _ = _ := by rw [residual_read, residual_read]; rfl

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
