import H0mework.Fock.InverseDistribution.Native
import H0mework.Fock.InverseDistribution.StreamNative
import H0mework.Fock.HistoryConditional.NativeObserversUpdate
import H0mework.Fock.HistoryConditional.WordAffineNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationNative

def position (steps : Nat) {bound : Nat} (actor : Fin (bound + 1)) : Nat := actor.val + 1 + steps

def fromState {Key : Type*} (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) : SourceInverseDistributionStream.State Key bound := fun key =>
  ((source key).1, fun actor => SourceNativeInverseDistribution.splitEntry program (position steps actor) ((source key).2 actor))

def step {Key : Type*} (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (previous : SourceInverseDistributionStream.State Key bound) : SourceInverseDistributionStream.State Key bound :=
  fromState bound program (steps + 1) (SourceInverseDistributionStream.source bound previous)

def generate {Key : Type*} [DecidableEq Key] (read : Nat → Key) (word : List (Option Nat)) (bound : Nat) : Nat → SourceInverseDistributionStream.State Key bound :=
  let source := SourceConditionalNativeObservers.generate read bound
  let program := SourceCopyWordAffine.compile word
  Nat.rec (fromState bound program program.2 source)
    (fun phase previous => step bound program (program.2 + phase) previous)

theorem generated_next {Key : Type*} [DecidableEq Key] (read : Nat → Key) (word : List (Option Nat)) (bound phase : Nat) :
    generate read word bound (phase + 1) =
      step bound (SourceCopyWordAffine.compile word) ((SourceCopyWordAffine.compile word).2 + phase)
        (generate read word bound phase) := rfl

end SourceInverseObservationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
