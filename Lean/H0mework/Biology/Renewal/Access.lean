import H0mework.Foundation.Relations.ConsumerFace

/-!
# Exact regenerative-access kernel

Regenerative access has two independent receiving ends.  Replicable service
capacity records whether another real delivery can be generated.  The
constitutional coordinate records whether admission, scarcity, appeal,
revision, capture and newcomer standing remain governed.  Neither coordinate
is allowed to stand in for the other.

The records below contain propositions rather than completed evidence.  A
source occurrence chooses the propositions; a faithful access certificate
must then inhabit every one of them.  This lets concrete roots install their
literal receipts without accepting a pre-filled success verdict.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Access

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

/-- The service-side readout.  It says that one delivery is real and that its
production mouth remains available for another round. -/
structure ReplicableServiceCapacityReadout where
  nextServiceOccurrenceGenerated : Prop
  deliveryCapacityRegenerated : Prop
  serviceSlotResourceBacked : Prop
  recipientRouteGenerated : Prop
  nextRoundProvisionGenerated : Prop

/-- The constitutional receiving end.  Purchasing power, declarations and
captured responses cannot substitute for source-governed admission. -/
structure ConstitutionalAccessReadout where
  admissionStandingSourceGoverned : Prop
  purchasingPowerCannotSubstituteServiceCapacity : Prop
  scarcityDispositionInstalled : Prop
  appealAvailable : Prop
  capacityRevisionAvailable : Prop
  antiCaptureEnforced : Prop
  newcomerStandingProtected : Prop

/-- One source occurrence presents both independent access coordinates. -/
structure RegenerativeAccessReadout where
  service : ReplicableServiceCapacityReadout
  constitution : ConstitutionalAccessReadout

/-- Every service-capacity responsibility is paid at the output. -/
structure ReplicableServiceCapacityAt
    (readout : ReplicableServiceCapacityReadout) : Prop where
  nextServiceOccurrenceGenerated : readout.nextServiceOccurrenceGenerated
  deliveryCapacityRegenerated : readout.deliveryCapacityRegenerated
  serviceSlotResourceBacked : readout.serviceSlotResourceBacked
  recipientRouteGenerated : readout.recipientRouteGenerated
  nextRoundProvisionGenerated : readout.nextRoundProvisionGenerated

/-- Every constitutional access responsibility is paid independently of the
service-capacity certificate. -/
structure ConstitutionalAccessAt
    (readout : ConstitutionalAccessReadout) : Prop where
  admissionStandingSourceGoverned : readout.admissionStandingSourceGoverned
  purchasingPowerCannotSubstituteServiceCapacity :
    readout.purchasingPowerCannotSubstituteServiceCapacity
  scarcityDispositionInstalled : readout.scarcityDispositionInstalled
  appealAvailable : readout.appealAvailable
  capacityRevisionAvailable : readout.capacityRevisionAvailable
  antiCaptureEnforced : readout.antiCaptureEnforced
  newcomerStandingProtected : readout.newcomerStandingProtected

/-- Faithful access is the conjunction of the two independently readable
coordinates. -/
structure FaithfulRegenerativeAccessAt
    (readout : RegenerativeAccessReadout) : Prop where
  replicableServiceCapacity : ReplicableServiceCapacityAt readout.service
  constitutionalAccess : ConstitutionalAccessAt readout.constitution

/-- The two positive independent consumers.  This family is nonempty even if
one of the two coordinates happens to fail at a concrete occurrence. -/
inductive RegenerativeAccessConsumer
  | replicableServiceCapacity
  | constitutionalAccess
  deriving DecidableEq

def regenerativeAccessConsumers :
    IndependentConsumerSystem RegenerativeAccessReadout where
  Consumer := RegenerativeAccessConsumer
  Output
    | .replicableServiceCapacity => ReplicableServiceCapacityReadout
    | .constitutionalAccess => ConstitutionalAccessReadout
  read
    | .replicableServiceCapacity => RegenerativeAccessReadout.service
    | .constitutionalAccess => RegenerativeAccessReadout.constitution
  positive := ⟨.replicableServiceCapacity⟩

/-- The two registered consumers distinguish the entire access occurrence. -/
theorem regenerativeAccessIndistinguishable_iff_eq
    (left right : RegenerativeAccessReadout) :
    regenerativeAccessConsumers.Indistinguishable left right ↔
      left = right := by
  constructor
  · intro same
    cases left with
    | mk leftService leftConstitution =>
      cases right with
      | mk rightService rightConstitution =>
        have serviceEq : leftService = rightService :=
          same .replicableServiceCapacity
        have constitutionEq : leftConstitution = rightConstitution :=
          same .constitutionalAccess
        cases serviceEq
        cases constitutionEq
        rfl
  · rintro rfl consumer
    rfl

/-- Exact kernel of the canonical two-coordinate access carrier. -/
theorem regenerativeAccessKernelExact :
    FaceKernelExactAt regenerativeAccessConsumers
      regenerativeAccessConsumers.canonicalRead :=
  regenerativeAccessConsumers.canonicalKernelExact

/-- The access quotient is exactly the range of its canonical readout. -/
noncomputable def regenerativeAccessQuotientEquivRange :
    regenerativeAccessConsumers.Quotient ≃
      Set.range regenerativeAccessConsumers.canonicalRead :=
  regenerativeAccessConsumers.canonicalQuotientEquivRange

/-- Each of the two independent receivers has a unique readout through the
canonical access carrier. -/
theorem everyRegenerativeAccessConsumer_uniqueFactorization
    (consumer : regenerativeAccessConsumers.Consumer) :
    ∃! factor : Set.range regenerativeAccessConsumers.canonicalRead →
        regenerativeAccessConsumers.Output consumer,
      ∀ occurrence,
        factor ⟨regenerativeAccessConsumers.canonicalRead occurrence,
          occurrence, rfl⟩ =
          regenerativeAccessConsumers.read consumer occurrence :=
  regenerativeAccessConsumers.everyConsumer_uniqueFactorization consumer

end Access
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Access.regenerativeAccessIndistinguishable_iff_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Access.regenerativeAccessKernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Access.regenerativeAccessQuotientEquivRange
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Access.everyRegenerativeAccessConsumer_uniqueFactorization
