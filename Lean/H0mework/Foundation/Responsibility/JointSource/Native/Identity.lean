import H0mework.Foundation.Ledger.Restructuring

/-! Identity-scoped source certification determines the actual ledger maps.
Finite coverage alone supplies neither injectivity statement. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Identity

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {source : SourceNativeSource N V} {current : V.Current}
  {occurrence : source.toRootSource.actual.OccurrenceAt current}
  {sourceLedger targetLedger : CompleteLiveLedgerAt N}
  {evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger}
variable (defaultAnchor : N.Anchor)
  (openAt_subsingleton : (support : N.Support) → (responsibility : N.Responsibility) →
    Subsingleton (N.OpenAt support responsibility))
  (certificate : ExactLedgerRestructuringCertificationAt
    (identityOnlyWorldLedgerRestructuringLaw source defaultAnchor openAt_subsingleton) occurrence evolution)

include defaultAnchor openAt_subsingleton certificate

theorem origin_injective : Function.Injective
    (fun entry : targetLedger.Entry => (evolution.origin entry).1) := by
  intro left right same
  cases certificate.split left right same with
  | identity equal => exact equal
  | split coverage => exact nomatch coverage.receipt.coverage

theorem destination_injective : Function.Injective
    (fun entry : sourceLedger.Entry => (evolution.destination entry).1) := by
  intro left right same
  cases certificate.merge left right same with
  | identity equal => exact equal
  | merge coverage => exact nomatch coverage.receipt.coverage

end RootGeneratedDebtActivationJointSource.Native.Identity
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
