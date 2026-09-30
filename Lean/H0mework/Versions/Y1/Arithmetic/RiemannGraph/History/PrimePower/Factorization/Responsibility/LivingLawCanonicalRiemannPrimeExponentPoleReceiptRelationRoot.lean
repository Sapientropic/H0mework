import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleRootEffectProjectionRoot
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Coupling.Relation.LivingLawCanonicalRiemannStageThreeArithmeticMellinActionBoundary

/-!
# Fixed-root activation of the receipt-rooted energy/vertical relation

The complete family of certified arithmetic receipt relations is installed
as one component coface of the existing Riesz-effect root.  Every cursor still
contains its original certified-row occurrence; the coface does not replace
it with a bare index table.  The source emitter, inherited effect face,
whole ledger, and generated next remain unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History
namespace PrimePowerCurrent
namespace ReceiptRelation

open CanonicalUnitArithmeticRoot
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure

noncomputable section

/-- The occurrence type shared by the previous effect root and this coface. -/
abbrev PrimeExponentPoleReceiptRootOccurrenceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (current : Current) :=
  (runtimePrimeExponentPoleRootEffectAuthoritySource
    observation nontrivial
    ).restructuringSource.source.toRootSource.actual.OccurrenceAt current

/-- A receipt request is admissible only at its compiler-generated runtime
current.  The caller cannot pair a certified arithmetic cursor with an
unrelated root occurrence. -/
structure PrimeExponentPoleReceiptRelationRequestAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (_occurrence : PrimeExponentPoleReceiptRootOccurrenceAt
      observation nontrivial current) where
  cursor : Nat
  current_eq : current =
    (CanonicalUnitArithmeticRoot.finiteVisit
      (PrimePower.Runtime.primePowerRuntimeStage
        (scheduledPrime cursor) (scheduledExponent cursor))).current

/-- Exact occurrences of the canonical unit source are unique at a fixed
current. -/
theorem primeExponentPoleReceiptRootOccurrence_unique
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : PrimeExponentPoleReceiptRootOccurrenceAt
      observation nontrivial current) :
    occurrence = CanonicalUnitArithmeticRoot.emitted current := by
  rcases occurrence with ⟨support, event⟩
  rcases event with ⟨support_eq, actionTrace, actionTrace_eq⟩
  cases support_eq
  cases actionTrace_eq
  rfl

/-- Universe-safe installed payload.  High-universe certified-row data are
reconstructed canonically, while the payload stores only proof fields tying
that reconstruction to this exact emitted occurrence. -/
structure PrimeExponentPoleReceiptRelationInstalledAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : PrimeExponentPoleReceiptRootOccurrenceAt
      observation nontrivial current)
    (request : PrimeExponentPoleReceiptRelationRequestAt
      observation nontrivial occurrence) : Type where
  occurrence_eq : HEq occurrence
    (Consumer.primePowerRuntimeOccurrence observation nontrivial
      (scheduledPrime request.cursor) (scheduledExponent request.cursor))
  certifiedRow_projection :
    (primeExponentPoleReceiptRelationOccurrence observation nontrivial
      request.cursor).map
        PrimeExponentPoleReceiptRelationPointAt.certifiedRow =
      certifiedRowOccurrence request.cursor
  relation_mem : retainedEnergyVerticalPresentedEvent ∈
    (primeExponentPoleReceiptPresentedRelationOccurrence
      observation nontrivial request.cursor).trace
  whole_fold_zero :
    (primeExponentPoleReceiptPresentedRelationOccurrence
      observation nontrivial request.cursor).fold
        (receiptWholeOccurrenceNodeAlgebra
          observation nontrivial request.cursor) = 0
  source_coordinate_projection : type_of%
    (Source.zeroOwnedReceiptCoordinateOccurrence_projects_boundary
      observation nontrivial request.cursor)
  source_allPrime_projection : type_of%
    (Source.zeroOwnedReceiptCoordinateOccurrence_projects_allPrime
      observation nontrivial request.cursor)
  source_role_specialization : ∀ role,
    (Source.zeroOwnedReceiptCoordinateOccurrence observation nontrivial
      request.cursor).root.2.roleValue role =
        receiptRoleValue observation nontrivial request.cursor role
  source_root_relation : type_of%
    (Source.zeroOwnedReceiptRelation_root observation nontrivial
      (scheduledPrime request.cursor) (scheduledExponent request.cursor)
        (scheduledExponent_positive request.cursor))
  source_halfDensity_normalization : type_of%
    (Source.zeroOwnedReceipt_halfDensity_normalization_root
      observation nontrivial
      (scheduledPrime request.cursor) (scheduledExponent request.cursor)
        (scheduledExponent_positive request.cursor))
  cofinal_root_projection : type_of%
    (Cofinal.receiptCofinalFace_projects_allPrime observation nontrivial)
  cofinal_role_readback : ∀ cursor role,
    (Cofinal.receiptCofinalFace observation nontrivial).root.root.2.table
        cursor role =
      receiptRoleValue observation nontrivial cursor role
  cofinal_global_component_readback : type_of%
    (Cofinal.zeroOwnedReceiptGlobalComponent_readback observation nontrivial)
  cofinal_global_relation : ∀ cursor,
    type_of% (Cofinal.zeroOwnedReceiptGlobalComponent_relation
      observation nontrivial cursor)
  exact_envelope_source_injective : type_of%
    (Cofinal.receiptEnvelopeSourceMap_injective observation nontrivial)
  exact_envelope_source_readback : ∀ table,
    type_of% (Cofinal.receiptEnvelopeSourceMap_doubleDual_readback
      observation nontrivial table)
  arithmetic_observation :
    Observation.ZeroOwnedRoleSeparatedArithmeticObservationCertificate
      observation nontrivial
  factorization_cokernel_observation :
    Cofiber.ZeroOwnedReceiptFactorizationCokernelCertificate
      observation nontrivial
  arithmetic_complexification_residual :
    Arithmetic.ZeroOwnedReceiptArithmeticComplexificationResidualCertificate
      observation nontrivial
  arithmetic_character_perfectification :
    Arithmetic.Character.ZeroOwnedReceiptArithmeticCharacterPerfectificationCertificate
      observation nontrivial
  stage_three_arithmetic_character :
    Arithmetic.Character.ZeroOwnedReceiptStageThreeArithmeticCharacterCertificate
      observation nontrivial
  stage_three_arithmetic_mellin_common_action :
    Arithmetic.Character.CommonAction.ZeroOwnedStageThreeArithmeticMellinCommonActionCertificate
      observation nontrivial
  stage_three_arithmetic_mellin_action_boundary :
    Arithmetic.Character.CommonAction.Boundary.ZeroOwnedStageThreeArithmeticMellinActionBoundaryCertificate
      observation nontrivial

def generatePrimeExponentPoleReceiptRelationInstalledAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : PrimeExponentPoleReceiptRootOccurrenceAt
      observation nontrivial current)
    (request : PrimeExponentPoleReceiptRelationRequestAt
      observation nontrivial occurrence) :
    PrimeExponentPoleReceiptRelationInstalledAt
      observation nontrivial occurrence request := by
  rcases request with ⟨cursor, rfl⟩
  have occurrenceEq := primeExponentPoleReceiptRootOccurrence_unique
    observation nontrivial occurrence
  refine ⟨?_,
    primeExponentPoleReceiptRelationOccurrence_projects_certifiedRow
      observation nontrivial cursor,
    retainedEnergyVerticalPresentedEvent_mem_trace
      observation nontrivial cursor,
    receiptWholeOccurrenceFold_eq_zero
      observation nontrivial cursor,
    Source.zeroOwnedReceiptCoordinateOccurrence_projects_boundary
      observation nontrivial cursor,
    Source.zeroOwnedReceiptCoordinateOccurrence_projects_allPrime
      observation nontrivial cursor,
    Source.zeroOwnedReceiptCoordinateOccurrence_root_specializes
      observation nontrivial cursor,
    Source.zeroOwnedReceiptRelation_root observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor),
    Source.zeroOwnedReceipt_halfDensity_normalization_root
      observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor),
    Cofinal.receiptCofinalFace_projects_allPrime observation nontrivial,
    Cofinal.receiptCofinalFace_root_table observation nontrivial,
    Cofinal.zeroOwnedReceiptGlobalComponent_readback observation nontrivial,
    Cofinal.zeroOwnedReceiptGlobalComponent_relation observation nontrivial,
    Cofinal.receiptEnvelopeSourceMap_injective observation nontrivial,
    Cofinal.receiptEnvelopeSourceMap_doubleDual_readback
      observation nontrivial,
    Observation.generateZeroOwnedRoleSeparatedArithmeticObservationCertificate
      observation nontrivial,
    Cofiber.generateZeroOwnedReceiptFactorizationCokernelCertificate
      observation nontrivial,
    Arithmetic.generateZeroOwnedReceiptArithmeticComplexificationResidualCertificate
      observation nontrivial,
    Arithmetic.Character.generateZeroOwnedReceiptArithmeticCharacterPerfectificationCertificate
      observation nontrivial,
    Arithmetic.Character.generateZeroOwnedReceiptStageThreeArithmeticCharacterCertificate
      observation nontrivial,
    Arithmetic.Character.CommonAction.generateZeroOwnedStageThreeArithmeticMellinCommonActionCertificate
      observation nontrivial,
    Arithmetic.Character.CommonAction.Boundary.generateZeroOwnedStageThreeArithmeticMellinActionBoundaryCertificate
      observation nontrivial⟩
  exact heq_of_eq occurrenceEq

def runtimePrimeExponentPoleReceiptRelationProjectionLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw
      (runtimePrimeExponentPoleRootEffectAuthoritySource
        observation nontrivial).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} occurrence _active =>
    (request : PrimeExponentPoleReceiptRelationRequestAt
      observation nontrivial occurrence) →
        PrimeExponentPoleReceiptRelationInstalledAt
          observation nontrivial occurrence request
  project := fun _projection {_current} occurrence _active request =>
    generatePrimeExponentPoleReceiptRelationInstalledAt
      observation nontrivial occurrence request

@[simp] theorem runtimePrimeExponentPoleReceiptRelationProjectionLaw_outcomeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (runtimePrimeExponentPoleRootEffectAuthoritySource
        observation nontrivial).restructuringSource.source.toRootSource.actual.OccurrenceAt
          current) :
    (runtimePrimeExponentPoleReceiptRelationProjectionLaw
      observation nontrivial).outcomeAt PUnit.unit occurrence =
        .inl ⟨PUnit.unit,
          fun request => generatePrimeExponentPoleReceiptRelationInstalledAt
            observation nontrivial occurrence request⟩ :=
  rfl

def runtimePrimeExponentPoleReceiptRelationAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimePrimeExponentPoleRootEffectAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimePrimeExponentPoleReceiptRelationProjectionLaw
        observation nontrivial)

def runtimePrimeExponentPoleReceiptRelationLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimePrimeExponentPoleReceiptRelationAuthoritySource
    observation nontrivial
  terminalHandoff :=
    (runtimePrimeExponentPoleReceiptRelationAuthoritySource
      observation nontrivial).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimePrimeExponentPoleReceiptRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimePrimeExponentPoleReceiptRelationLivingSource
    observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimePrimeExponentPoleReceiptRelationRoot_reuses_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
        ).emitted = emitted :=
  ⟨rfl, rfl⟩

def runtimePrimeExponentPoleReceiptRelationInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleReceiptRelationProjectionLaw
        observation nontrivial)
      (runtimePrimeExponentPoleReceiptRelationAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimePrimeExponentPoleRootEffectAuthoritySource observation nontrivial)
    (runtimePrimeExponentPoleReceiptRelationProjectionLaw
      observation nontrivial)

def runtimePrimeExponentPoleReceiptRelationInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleRootEffectAuthoritySource observation nontrivial
        ).projectionLaw
      (runtimePrimeExponentPoleReceiptRelationAuthoritySource
        observation nontrivial).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimePrimeExponentPoleRootEffectAuthoritySource observation nontrivial)
    (runtimePrimeExponentPoleReceiptRelationProjectionLaw
      observation nontrivial)

def runtimePrimeExponentPoleRootEffectInstallationAtReceiptRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimePrimeExponentPoleRootEffectProjectionLaw observation nontrivial)
      (runtimePrimeExponentPoleReceiptRelationAuthoritySource
        observation nontrivial).projectionLaw :=
  (runtimePrimeExponentPoleRootEffectInstallation
    observation nontrivial).trans
      (runtimePrimeExponentPoleReceiptRelationInheritedInstallation
        observation nontrivial)

def runtimePrimeExponentPoleReceiptRelationVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

theorem runtimePrimeExponentPoleReceiptRelation_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleReceiptRelationRoot
      observation nontrivial
    let visit := runtimePrimeExponentPoleReceiptRelationVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          ((runtimePrimeExponentPoleReceiptRelationInstallation
            observation nontrivial).embed PUnit.unit))
        ((runtimePrimeExponentPoleReceiptRelationProjectionLaw
          observation nontrivial).outcomeAt PUnit.unit
            (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleReceiptRelationVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimePrimeExponentPoleReceiptRelationInstallation
        observation nontrivial)
      PUnit.unit

theorem runtimePrimeExponentPoleRootEffect_factorizes_atReceiptRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let root := runtimePrimeExponentPoleReceiptRelationRoot
      observation nontrivial
    let visit := runtimePrimeExponentPoleReceiptRelationVisitAt
      observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    HEq (evolution.generated.projectionOutcome
          ((runtimePrimeExponentPoleRootEffectInstallationAtReceiptRelationRoot
            observation nontrivial).embed PUnit.unit))
        ((runtimePrimeExponentPoleRootEffectProjectionLaw
          observation nontrivial).outcomeAt PUnit.unit
            (root.emitted visit.current)) := by
  dsimp only
  exact
    ((runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
      ).canonicalCausalAnswerAndNext
        (ULift.up (runtimePrimeExponentPoleReceiptRelationVisitAt
          observation nontrivial depth))).installedSubsystemAuthority_factorizes
      (runtimePrimeExponentPoleRootEffectInstallationAtReceiptRelationRoot
        observation nontrivial)
      PUnit.unit |>.2.1

end
end ReceiptRelation
end PrimePowerCurrent
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
