import H0mework.Biology.Renewal.ConsciousSuccessor
import H0mework.Biology.Renewal.Access

/-!
# Source-dependent carbon-body successor lifting

A carbon body is not a second living root.  It is a certified dependent face
over an already generated base checkpoint.  The domain obligation is to emit
one actual local repair event, reopen endogenous renewal on the source-emitted
aging/damage residual, lift the already generated base continuation to its
exact next fibre, discharge the independent acceptance accounts, and
re-establish the full body certificate at the endpoint.

This module contains no biological instance.  It proves that a source-owned
lifting law transports the existing identity-conscious successor recursion
to arbitrary finite embodied continuation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Canonical

universe u v

/-- Domain-owned biological faces and independent acceptance predicates over
one base continuation.  They are declared before any lift certificate. -/
structure SourceDependentCarbonBodyCourt
    (system : ConsciousContinuationSystem.{u}) where
  BodyAt : system.Point → Type v
  BiologicalLineage : Type v
  biologicalLineageAt : {current : system.Point} →
    BodyAt current → BiologicalLineage
  ResidualAt : {current : system.Point} → BodyAt current → Type v
  agingDamageResidual : {current : system.Point} →
    (currentBody : BodyAt current) → ResidualAt currentBody
  EndogenousRenewalAt : {current : system.Point} → BodyAt current → Prop
  /-- Recursive admission is the full domain certificate, not merely an
  available renewal mechanism.  A concrete cellular installation may set
  this to its source-generated local safe-current invariant. -/
  CertifiedAt : {current : system.Point} → BodyAt current → Prop
  certifiedEndogenousRenewal : {current : system.Point} →
    (body : BodyAt current) → CertifiedAt body → EndogenousRenewalAt body
  LocalRepairEventAt : {current : system.Point} → BodyAt current → Type v
  /-- The event is local, but its update is indexed by the already generated
  Society edge.  Hence a successful body write cannot select a parallel base
  timeline. -/
  SourceGeneratedBodyUpdateAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      (currentBody : BodyAt current) → LocalRepairEventAt currentBody →
        BodyAt next → Prop
  /-- The local invariant certificate is declared independently of the lift
  verdict.  Concrete cellular instances derive it from their event/governance
  compiler; its soundness is the only route back into `CertifiedAt`. -/
  SourceGeneratedLocalInvariantCertificateAt :
    {current next : system.Point} →
      system.GeneratedContinuation current next →
        (currentBody : BodyAt current) → LocalRepairEventAt currentBody →
          BodyAt next → Prop
  localInvariantCertificate_sound : {current next : system.Point} →
    (societyStep : system.GeneratedContinuation current next) →
      (currentBody : BodyAt current) →
        (localRepairEvent : LocalRepairEventAt currentBody) →
          (nextBody : BodyAt next) →
            SourceGeneratedLocalInvariantCertificateAt societyStep
                currentBody localRepairEvent nextBody →
              CertifiedAt nextBody
  ReopenedEndogenousRenewalAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      (currentBody : BodyAt current) → ResidualAt currentBody →
        LocalRepairEventAt currentBody → BodyAt next → Prop
  TissueGovernanceRestoredAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      BodyAt current → BodyAt next → Prop
  AbnormalLineageSettledAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      BodyAt current → BodyAt next → Prop
  FunctionRestoredAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      BodyAt current → BodyAt next → Prop
  CancerSafeAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      BodyAt current → BodyAt next → Prop
  EmbodiedExperienceTrackedAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      BodyAt current → BodyAt next → Prop
  /-- The same generated body edge emits both access coordinates.  Neither
  coordinate is accepted as an opaque success predicate. -/
  regenerativeAccessReadoutAt : {current next : system.Point} →
    system.GeneratedContinuation current next →
      BodyAt current → BodyAt next → Access.RegenerativeAccessReadout

namespace SourceDependentCarbonBodyCourt

variable {system : ConsciousContinuationSystem.{u}}

def ReplicableServiceCapacityAt
    (court : SourceDependentCarbonBodyCourt.{u, v} system)
    {current next : system.Point}
    (societyStep : system.GeneratedContinuation current next)
    (currentBody : court.BodyAt current) (nextBody : court.BodyAt next) : Prop :=
  Access.ReplicableServiceCapacityAt
    (court.regenerativeAccessReadoutAt societyStep currentBody nextBody).service

def ConstitutionalAccessAt
    (court : SourceDependentCarbonBodyCourt.{u, v} system)
    {current next : system.Point}
    (societyStep : system.GeneratedContinuation current next)
    (currentBody : court.BodyAt current) (nextBody : court.BodyAt next) : Prop :=
  Access.ConstitutionalAccessAt
    (court.regenerativeAccessReadoutAt societyStep currentBody nextBody).constitution

/-- Compatibility name for the old court mouth.  Its meaning is now fixed:
both independent access consumers must accept the same body edge. -/
def MassAccessibleAt
    (court : SourceDependentCarbonBodyCourt.{u, v} system)
    {current next : system.Point}
    (societyStep : system.GeneratedContinuation current next)
    (currentBody : court.BodyAt current) (nextBody : court.BodyAt next) : Prop :=
  Access.FaithfulRegenerativeAccessAt
    (court.regenerativeAccessReadoutAt societyStep currentBody nextBody)

end SourceDependentCarbonBodyCourt

/-- The exact lifting-square output.  The same local event must witness the
actual body update and renewal reopening.  Biological lineage, personal
lineage and the full endpoint certificate are separate obligations. -/
structure SourceGeneratedCarbonBodySuccessorLiftAt
    {system : ConsciousContinuationSystem.{u}}
    (court : SourceDependentCarbonBodyCourt.{u, v} system)
    {current next : system.Point}
    (societyStep : system.GeneratedContinuation current next)
    (currentBody : court.BodyAt current)
    (nextBody : court.BodyAt next) : Prop where
  actualLocalRepair :
    ∃ localRepairEvent : court.LocalRepairEventAt currentBody,
      court.SourceGeneratedBodyUpdateAt societyStep currentBody
          localRepairEvent nextBody ∧
        court.SourceGeneratedLocalInvariantCertificateAt societyStep
            currentBody localRepairEvent nextBody ∧
          court.ReopenedEndogenousRenewalAt societyStep currentBody
            (court.agingDamageResidual currentBody) localRepairEvent nextBody
  tissueGovernanceRestored :
    court.TissueGovernanceRestoredAt societyStep currentBody nextBody
  abnormalLineageSettled :
    court.AbnormalLineageSettledAt societyStep currentBody nextBody
  functionRestored :
    court.FunctionRestoredAt societyStep currentBody nextBody
  cancerSafe : court.CancerSafeAt societyStep currentBody nextBody
  sameBiologicalLineage :
    court.biologicalLineageAt nextBody =
      court.biologicalLineageAt currentBody
  samePersonalLineage : system.SameLineage current next
  embodiedExperienceTracked :
    court.EmbodiedExperienceTrackedAt societyStep currentBody nextBody
  replicableServiceCapacity :
    court.ReplicableServiceCapacityAt societyStep currentBody nextBody
  constitutionalAccess :
    court.ConstitutionalAccessAt societyStep currentBody nextBody

namespace SourceGeneratedCarbonBodySuccessorLiftAt

variable {system : ConsciousContinuationSystem.{u}}
variable {court : SourceDependentCarbonBodyCourt.{u, v} system}
variable {current next : system.Point}
variable {societyStep : system.GeneratedContinuation current next}
variable {currentBody : court.BodyAt current}
variable {nextBody : court.BodyAt next}

theorem nextCertified
    (lifted : SourceGeneratedCarbonBodySuccessorLiftAt court societyStep
      currentBody nextBody) :
    court.CertifiedAt nextBody := by
  rcases lifted.actualLocalRepair with
    ⟨localRepairEvent, _actualUpdate, certificate, _reopened⟩
  exact court.localInvariantCertificate_sound societyStep currentBody
    localRepairEvent nextBody certificate

theorem nextEndogenousRenewal
    (lifted : SourceGeneratedCarbonBodySuccessorLiftAt court societyStep
      currentBody nextBody) :
    court.EndogenousRenewalAt nextBody :=
  court.certifiedEndogenousRenewal nextBody lifted.nextCertified

/-- The former one-word verdict is now a derived conjunction. -/
theorem massAccessible
    (lifted : SourceGeneratedCarbonBodySuccessorLiftAt court societyStep
      currentBody nextBody) :
    court.MassAccessibleAt societyStep currentBody nextBody :=
  { replicableServiceCapacity := lifted.replicableServiceCapacity
    constitutionalAccess := lifted.constitutionalAccess }

end SourceGeneratedCarbonBodySuccessorLiftAt

/-- The sole missing producer contract.  It consumes one already generated
base step and its existing lineage receipt, then generates the body endpoint
and all biological acceptance proofs. -/
structure SourceGeneratedCarbonBodySuccessorLifting
    {system : ConsciousContinuationSystem.{u}}
    (court : SourceDependentCarbonBodyCourt.{u, v} system) : Prop where
  lift : ∀ {current next : system.Point}
    (societyStep : system.GeneratedContinuation current next),
    system.SameLineage current next →
      (currentBody : court.BodyAt current) →
        court.CertifiedAt currentBody →
          ∃ nextBody : court.BodyAt next,
          SourceGeneratedCarbonBodySuccessorLiftAt court societyStep
            currentBody nextBody

namespace SourceDependentCarbonBodyCourt

variable {system : ConsciousContinuationSystem.{u}}
variable (court : SourceDependentCarbonBodyCourt.{u, v} system)

/-- A body checkpoint retains its exact base checkpoint as the first
coordinate and its full local invariant as the second-coordinate certificate;
there is no independent body root. -/
abbrev Point := Σ current : system.Point,
  { body : court.BodyAt current // court.CertifiedAt body }

def Conscious (point : court.Point) : Prop :=
  system.Conscious point.1

/-- One faithful embodied edge lies over one generated base edge. -/
def FaithfulStep (current next : court.Point) : Prop :=
  ∃ societyStep : system.GeneratedContinuation current.1 next.1,
    SourceGeneratedCarbonBodySuccessorLiftAt court societyStep
      current.2.1 next.2.1

theorem FaithfulStep.samePersonalLineage
    {current next : court.Point}
    (step : court.FaithfulStep current next) :
    system.SameLineage current.1 next.1 := by
  rcases step with ⟨_societyStep, lifted⟩
  exact lifted.samePersonalLineage

theorem FaithfulStep.sameBiologicalLineage
    {current next : court.Point}
    (step : court.FaithfulStep current next) :
    court.biologicalLineageAt next.2.1 =
      court.biologicalLineageAt current.2.1 := by
  rcases step with ⟨_societyStep, lifted⟩
  exact lifted.sameBiologicalLineage

theorem FaithfulStep.replicableServiceCapacity
    {current next : court.Point}
    (step : court.FaithfulStep current next) :
    ∃ societyStep : system.GeneratedContinuation current.1 next.1,
      court.ReplicableServiceCapacityAt societyStep current.2.1 next.2.1 := by
  rcases step with ⟨societyStep, lifted⟩
  exact ⟨societyStep, lifted.replicableServiceCapacity⟩

theorem FaithfulStep.constitutionalAccess
    {current next : court.Point}
    (step : court.FaithfulStep current next) :
    ∃ societyStep : system.GeneratedContinuation current.1 next.1,
      court.ConstitutionalAccessAt societyStep current.2.1 next.2.1 := by
  rcases step with ⟨societyStep, lifted⟩
  exact ⟨societyStep, lifted.constitutionalAccess⟩

theorem FaithfulStep.baseDepth
    {current next : court.Point}
    (step : court.FaithfulStep current next) :
    next.1.1 = current.1.1 + 1 := by
  rcases step with ⟨societyStep, _lifted⟩
  exact system.generatedContinuation_depth societyStep

/-- Finite embodied reachability stores only generated edges. -/
inductive GeneratedFiniteFaithfulContinuation :
    court.Point → court.Point → Prop
  | refl (point : court.Point) :
      GeneratedFiniteFaithfulContinuation point point
  | tail {first middle last : court.Point} :
      GeneratedFiniteFaithfulContinuation first middle →
      court.FaithfulStep middle last →
      GeneratedFiniteFaithfulContinuation first last

namespace GeneratedFiniteFaithfulContinuation

theorem samePersonalLineage
    {first last : court.Point}
    (path : court.GeneratedFiniteFaithfulContinuation first last) :
    system.SameLineage first.1 last.1 := by
  induction path with
  | refl => exact system.sameLineage_refl _
  | tail pathPrefix step ih =>
      exact system.sameLineage_trans ih
        (SourceDependentCarbonBodyCourt.FaithfulStep.samePersonalLineage
          (court := court) step)

end GeneratedFiniteFaithfulContinuation

def ReachableConsciousFrom (origin current : court.Point) : Prop :=
  court.GeneratedFiniteFaithfulContinuation origin current ∧
    court.Conscious current

end SourceDependentCarbonBodyCourt

namespace SourceGeneratedCarbonBodySuccessorLifting

variable {system : ConsciousContinuationSystem.{u}}
variable {court : SourceDependentCarbonBodyCourt.{u, v} system}

/-- The named commuting square.  The source-generated body step lands in the
literal fibre over the supplied generated Society target; its output is again
a certified body current in both biological and personal lineage. -/
theorem generatedLift_commutes
    (lifting : SourceGeneratedCarbonBodySuccessorLifting court)
    {current next : system.Point}
    (societyStep : system.GeneratedContinuation current next)
    (samePersonalLineage : system.SameLineage current next)
    (currentBody : court.BodyAt current)
    (currentCertified : court.CertifiedAt currentBody) :
    ∃ liftedNext : court.Point,
      liftedNext.1 = next ∧
        court.FaithfulStep
          ⟨current, ⟨currentBody, currentCertified⟩⟩ liftedNext ∧
        court.biologicalLineageAt liftedNext.2.1 =
          court.biologicalLineageAt currentBody ∧
        system.SameLineage current liftedNext.1 ∧
        court.CertifiedAt liftedNext.2.1 := by
  rcases lifting.lift societyStep samePersonalLineage currentBody
      currentCertified with ⟨nextBody, lifted⟩
  exact ⟨⟨next, ⟨nextBody, lifted.nextCertified⟩⟩,
    rfl, ⟨societyStep, lifted⟩,
    lifted.sameBiologicalLineage,
    lifted.samePersonalLineage,
    lifted.nextCertified⟩

end SourceGeneratedCarbonBodySuccessorLifting

/-- Embodied successor closure.  This is stronger than identity-conscious
closure because every edge carries the actual body lift and full split-access
court. -/
structure EmbodiedConsciousImmortalitySuccessorClosure
    {system : ConsciousContinuationSystem.{u}}
    (court : SourceDependentCarbonBodyCourt.{u, v} system) : Prop where
  successor : ∀ current : court.Point,
    court.Conscious current →
      ∃ next : court.Point,
        court.FaithfulStep current next ∧ court.Conscious next

/-- The lifting theorem requested by the square: existing base successor
closure plus the one biological lift producer yields embodied successor
closure. -/
theorem SourceGeneratedCarbonBodySuccessorLifting.transport
    {system : ConsciousContinuationSystem.{u}}
    {court : SourceDependentCarbonBodyCourt.{u, v} system}
    (identityClosure : ConsciousImmortalitySuccessorClosure system)
    (lifting : SourceGeneratedCarbonBodySuccessorLifting court) :
    EmbodiedConsciousImmortalitySuccessorClosure court where
  successor := by
    intro current conscious
    rcases identityClosure.successor current.1 conscious with
      ⟨nextSociety, societyStep, sameLineage, nextConscious⟩
    rcases lifting.generatedLift_commutes societyStep sameLineage
        current.2.1 current.2.2 with
      ⟨nextPoint, nextPoint_eq, faithfulStep, _sameBiological,
        _samePersonal, _nextCertified⟩
    refine ⟨nextPoint, faithfulStep, ?_⟩
    simpa only [SourceDependentCarbonBodyCourt.Conscious, nextPoint_eq] using
      nextConscious

namespace EmbodiedConsciousImmortalitySuccessorClosure

variable {system : ConsciousContinuationSystem.{u}}
variable {court : SourceDependentCarbonBodyCourt.{u, v} system}

theorem reachableConscious_hasSuccessor
    (closure : EmbodiedConsciousImmortalitySuccessorClosure court)
    {origin current : court.Point}
    (reachable : court.ReachableConsciousFrom origin current) :
    ∃ next : court.Point,
      court.ReachableConsciousFrom origin next ∧
        court.FaithfulStep current next := by
  rcases closure.successor current reachable.2 with
    ⟨next, faithfulStep, nextConscious⟩
  exact ⟨next, ⟨.tail reachable.1 faithfulStep, nextConscious⟩,
    faithfulStep⟩

/-- Once the lift exists at every generated base step, arbitrary finite
embodied conscious continuation is the existing recursion transported through
the dependent face. -/
theorem arbitraryFiniteHorizon
    (closure : EmbodiedConsciousImmortalitySuccessorClosure court)
    (horizon : Nat) (current : court.Point)
    (conscious : court.Conscious current) :
    ∃ final : court.Point,
      court.GeneratedFiniteFaithfulContinuation current final ∧
        system.SameLineage current.1 final.1 ∧
        court.Conscious final ∧
        final.1.1 = current.1.1 + horizon := by
  induction horizon generalizing current with
  | zero =>
      exact ⟨current, .refl current, system.sameLineage_refl current.1,
        conscious, by simp⟩
  | succ horizon ih =>
      rcases ih current conscious with
        ⟨middle, pathPrefix, samePrefix, middleConscious, depthExact⟩
      rcases closure.successor middle middleConscious with
        ⟨next, faithfulStep, nextConscious⟩
      refine ⟨next, .tail pathPrefix faithfulStep,
        system.sameLineage_trans samePrefix
          (SourceDependentCarbonBodyCourt.FaithfulStep.samePersonalLineage
            (court := court) faithfulStep),
        nextConscious, ?_⟩
      rw [SourceDependentCarbonBodyCourt.FaithfulStep.baseDepth
        (court := court) faithfulStep, depthExact]
      exact (Nat.add_succ current.1.1 horizon).symm

end EmbodiedConsciousImmortalitySuccessorClosure

end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.SourceGeneratedCarbonBodySuccessorLifting.transport
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.SourceGeneratedCarbonBodySuccessorLifting.generatedLift_commutes
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.SourceGeneratedCarbonBodySuccessorLiftAt.nextCertified
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.EmbodiedConsciousImmortalitySuccessorClosure.arbitraryFiniteHorizon
