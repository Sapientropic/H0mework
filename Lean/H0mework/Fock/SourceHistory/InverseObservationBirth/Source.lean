import H0mework.Fock.SourceHistory.InverseObservationBirth.Native
import H0mework.Fock.SourceHistory.InverseObservationNative.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationBirth

theorem birth_source {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (previous : SourceInverseDistributionStream.State Key bound) :
    SourceInverseDistributionStream.source (bound + 1) (birth read bound program steps previous) =
      SourceConditionalNativeObservers.advance read bound (SourceInverseDistributionStream.source bound previous) :=
  SourceInverseObservationNative.fromState_source (bound + 1) program steps _

theorem birth_generated {Key : Type*} [DecidableEq Key] (read : Nat → Key) (word : List (Option Nat)) (bound phase : Nat) :
    let program := SourceCopyWordAffine.compile word
    birth read bound program (program.2 + phase) (SourceInverseObservationNative.generate read word bound phase) =
      SourceInverseObservationNative.generate read word (bound + 1) phase := by
  dsimp only
  rw [SourceInverseObservationNative.generated_source, SourceInverseObservationNative.generated_source,
    birth, SourceInverseObservationNative.fromState_source, SourceConditionalNativeObservers.generated_next]

theorem step_birth {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (previous : SourceInverseDistributionStream.State Key bound) :
    SourceInverseObservationNative.step (bound + 1) program steps (birth read bound program steps previous) =
      birth read bound program (steps + 1) (SourceInverseObservationNative.step bound program steps previous) := by
  rw [SourceInverseObservationNative.step, birth_source, birth, SourceInverseObservationNative.step,
    SourceInverseObservationNative.fromState_source]

end SourceInverseObservationBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
