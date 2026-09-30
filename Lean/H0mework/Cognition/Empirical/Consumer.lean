import H0mework.Foundation.Relations.ConsumerQuotient

/-!
# Independent operational consumer for the TruthChild two-branch run

The consumer sees only the second forward and the independently durable world
effect.  It does not import the runtime producer, the six-point manifest, the
formal Teaching closure, or any consciousness verdict.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Closure
namespace Empirical
namespace TruthChild
namespace Consumer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

/-- The registered history and its write-back-deleted causal control. -/
inductive TruthChildEmpiricalOccurrence where
  | registered
  | writebackDeleted
  deriving DecidableEq, Repr

/-- Externally selected action together with the complete internal-logits
identity.  The candidate probabilities remain in the manifest readout. -/
structure TruthChildObserverExperienceReadout where
  selectedAction : String
  fullLogitsSha256 : String
  deriving DecidableEq, Repr

/-- A world-side measurement made by the independent durable receiver. -/
structure TruthChildReceiverEffectReadout where
  effectKind : String
  authoritative : Bool
  doorState : String
  deriving DecidableEq, Repr

def truthChildObserverExperienceReadAt :
    TruthChildEmpiricalOccurrence → TruthChildObserverExperienceReadout
  | .registered =>
      { selectedAction := "O"
        fullLogitsSha256 :=
          "9ec8bc76547e6c77d7399b6775aa242c8cafd014cde9156b732ef533a839e006" }
  | .writebackDeleted =>
      { selectedAction := "N"
        fullLogitsSha256 :=
          "b55037ccbd1c97a79045109db0b559f6f82ba66724c431d4e2466e926fce3452" }

def truthChildReceiverEffectReadAt :
    TruthChildEmpiricalOccurrence → TruthChildReceiverEffectReadout
  | .registered =>
      { effectKind := "DOOR_OPENED"
        authoritative := true
        doorState := "OPEN" }
  | .writebackDeleted =>
      { effectKind := "WAIT"
        authoritative := false
        doorState := "CLOSED" }

inductive TruthChildOperationalConsumer where
  | observerExperience
  | receivedActualEffect
  deriving DecidableEq, Repr

def TruthChildOperationalOutput : TruthChildOperationalConsumer → Type
  | .observerExperience => TruthChildObserverExperienceReadout
  | .receivedActualEffect => TruthChildReceiverEffectReadout

def truthChildOperationalReadAt :
    (consumer : TruthChildOperationalConsumer) →
      TruthChildEmpiricalOccurrence → TruthChildOperationalOutput consumer
  | .observerExperience => truthChildObserverExperienceReadAt
  | .receivedActualEffect => truthChildReceiverEffectReadAt

/-- Explicitly nonempty consumer family, declared before the six-point source
receipt. -/
def truthChildOperationalConsumers :
    IndependentConsumerSystem TruthChildEmpiricalOccurrence where
  Consumer := TruthChildOperationalConsumer
  Output := TruthChildOperationalOutput
  read := truthChildOperationalReadAt
  positive := ⟨.observerExperience⟩

/-- Operational positivity uses only the independent observer and receiver
readouts. -/
def TruthChildOperationalPositiveAt
    (occurrence : TruthChildEmpiricalOccurrence) : Prop :=
  truthChildObserverExperienceReadAt occurrence =
      truthChildObserverExperienceReadAt .registered ∧
    truthChildReceiverEffectReadAt occurrence =
      truthChildReceiverEffectReadAt .registered

theorem truthChildOperationalIndistinguishable_iff
    (occurrence : TruthChildEmpiricalOccurrence) :
    truthChildOperationalConsumers.Indistinguishable occurrence .registered ↔
      TruthChildOperationalPositiveAt occurrence := by
  constructor
  · intro indistinguishable
    exact ⟨indistinguishable .observerExperience,
      indistinguishable .receivedActualEffect⟩
  · intro positive consumer
    cases consumer with
    | observerExperience => exact positive.1
    | receivedActualEffect => exact positive.2

theorem truthChildOperationalPositive_iff_registered
    (occurrence : TruthChildEmpiricalOccurrence) :
    TruthChildOperationalPositiveAt occurrence ↔ occurrence = .registered := by
  cases occurrence <;>
    simp [TruthChildOperationalPositiveAt, truthChildObserverExperienceReadAt,
      truthChildReceiverEffectReadAt]

theorem truthChildWritebackDeleted_isNotOperationalPositive :
    ¬ TruthChildOperationalPositiveAt .writebackDeleted := by
  exact (truthChildOperationalPositive_iff_registered .writebackDeleted).not.mpr
    (by decide)

end Consumer
end TruthChild
end Empirical
end Closure
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Consumer.truthChildOperationalPositive_iff_registered
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Consumer.truthChildWritebackDeleted_isNotOperationalPositive
