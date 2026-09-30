import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.Construction
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.RowRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace MotherNativeAuthority

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)

/-- Entry material remains an original source-inventory input; the row is generated internally. -/
def formInitial
    (entry : EntryAt root root.toAuthoritativeRoot.toRoot.source.initial) :
    Option (MaterialTotal root (.finite root.toAuthoritativeRoot.toRoot.initialVisit)) :=
  ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit)).canonicalGeneratedEntryRow? entry).map
    (fun row => ⟨entry, .initialAdmission entry row⟩)

def formCofinalAt
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : EntryAt root visit.current) :
    Option (MaterialTotal root (.cofinal visit)) :=
  ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal visit)).canonicalGeneratedEntryRow? entry).map
    (fun row => ⟨entry, .cofinalAdmission row⟩)

theorem formInitial_recovers
    (entry : EntryAt root root.toAuthoritativeRoot.toRoot.source.initial)
    (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt entry) :
    formInitial root entry = some ⟨entry, Material.initialAdmission entry row⟩ := by
  exact congrArg (fun optional : Option ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt entry) =>
    optional.map (fun sourceRow =>
    (⟨entry, Material.initialAdmission entry sourceRow⟩ :
      MaterialTotal root (.finite root.toAuthoritativeRoot.toRoot.initialVisit))))
    (row_selector_recovers (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit)) entry row)

theorem formCofinalAt_recovers
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : EntryAt root visit.current)
    (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal visit)).GeneratedEntryRowAt entry) :
    formCofinalAt root visit entry = some ⟨entry, Material.cofinalAdmission row⟩ := by
  exact congrArg (fun optional : Option ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal visit)).GeneratedEntryRowAt entry) => optional.map (fun sourceRow =>
    (⟨entry, Material.cofinalAdmission sourceRow⟩ : MaterialTotal root (.cofinal visit))))
    (row_selector_recovers (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal visit)) entry row)

theorem initial_consumed
    (entry : EntryAt root root.toAuthoritativeRoot.toRoot.source.initial)
    (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt entry) :
    (formInitial root entry).map assembleTotal =
      some ⟨entry, SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
        root entry row⟩ := by
  exact congrArg (Option.map assembleTotal) (formInitial_recovers root entry row)

theorem cofinal_consumed
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : EntryAt root visit.current)
    (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal visit)).GeneratedEntryRowAt entry) :
    (formCofinalAt root visit entry).map assembleTotal =
      some ⟨entry, SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromCofinalRow
        root visit entry row⟩ := by
  exact congrArg (Option.map assembleTotal) (formCofinalAt_recovers root visit entry row)

end MotherNativeAuthority
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
