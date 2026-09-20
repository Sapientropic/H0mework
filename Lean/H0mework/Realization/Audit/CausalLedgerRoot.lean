import H0mework.Realization.Audit.LivingAuthority

/-!
# Provenance-carrying residual audit ledger root

The concrete audit event stores the exact lower origin selected by its source
law.  Its compiler generates one distinguished residual row while every
inherited row remains in the identity remainder.  This is a source/ledger
mechanism; causal authority is added only by a generated transition whose
type fixes the origin.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedCausalResidualAudit

open RootGeneratedResidualAdmission
open RootGeneratedResidualAuditLedger

universe u

section

variable (N : WorldRelationNetwork.{u}) (focus : N.Support)
variable (Residual : Type u) (distinguished : Residual)
variable [Subsingleton Residual]
variable (Origin : Type u) (distinguishedOrigin : Origin)

/-- An audit event carries the exact lower occurrence that generated the
residual.  The equality is event data, so provenance is not reconstructed
from a current label after the audit root has been chosen. -/
structure CausalAuditEventAt
    (_current : AuditV.Current) (support : N.Support) : Type u where
  origin : Origin
  origin_eq : origin = distinguishedOrigin
  support_eq : support = focus

def causalAuditEventLaw :
    SourceNativeEventAlgebra (ExtendedNetwork N focus Residual) AuditV where
  EventAt := CausalAuditEventAt N focus Origin distinguishedOrigin
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_current} {support} _event =>
    OpenResponsibilityAt (ExtendedNetwork N focus Residual) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := fun _ => N.anchorAt focus
  incidenceKey := fun _ => N.incidenceAt focus
  lineageKey := fun _ => N.lineageAt focus
  anchor_commutes := by
    intro _current support event
    cases event.support_eq
    rfl
  incidence_commutes := by
    intro _current support event
    cases event.support_eq
    rfl
  lineage_commutes := by
    intro _current support event
    cases event.support_eq
    rfl

def causalAuditSource :
    SourceNativeSource (ExtendedNetwork N focus Residual) AuditV where
  initial := ULift.up false
  law := causalAuditEventLaw N focus Residual Origin distinguishedOrigin

def causalAuditEmitted
    (current : AuditV.Current) :
    (causalAuditSource N focus Residual Origin distinguishedOrigin
      ).toRootSource.actual.OccurrenceAt current :=
  ⟨focus,
    { origin := distinguishedOrigin
      origin_eq := rfl
      support_eq := rfl }⟩

omit [Subsingleton Residual] in
theorem causalAuditOccurrence_eq_emitted
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    occurrence = causalAuditEmitted N focus Residual Origin
      distinguishedOrigin current := by
  rcases occurrence with ⟨support, event⟩
  rcases event with ⟨origin, origin_eq, support_eq⟩
  cases origin_eq
  cases support_eq
  rfl

/-- The admitted audit occurrence reads its concrete lower cause literally. -/
def causalAuditOccurrenceOrigin
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) : Origin :=
  occurrence.2.origin

omit [Subsingleton Residual] in
@[simp] theorem causalAuditOccurrenceOrigin_emitted
    (current : AuditV.Current) :
    causalAuditOccurrenceOrigin N focus Residual Origin distinguishedOrigin
        (causalAuditEmitted N focus Residual Origin distinguishedOrigin current) =
      distinguishedOrigin :=
  rfl

abbrev CausalAuditExactTransitionAt
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current)
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      targetSupport) :=
  AuditCarriedRowAt (ExtendedNetwork N focus Residual) sourceEntry targetEntry

def causalAuditRowSource : LedgerWriteRowSourceAt
    (causalAuditSource N focus Residual Origin distinguishedOrigin)
    (CausalAuditExactTransitionAt N focus Residual Origin
      distinguishedOrigin) where
  IncidenceOccurrenceAt := CausalAuditExactTransitionAt N focus Residual
    Origin distinguishedOrigin
  compileEvolution := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry event
    exact .carried event.support_eq event.entry_eq
  compileExact := fun event => event

def causalAuditTerminalRowSource : LedgerTerminalRowSourceAt
    (causalAuditSource N focus Residual Origin distinguishedOrigin) :=
  LedgerTerminalRowSourceAt.empty _

def causalAuditResidualEntry
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.account.supportOf occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event.support_eq
  exact residualEntry focus distinguished

def causalAuditGeneratedRow
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    GeneratedLedgerWriteRowAt
      (causalAuditRowSource N focus Residual Origin distinguishedOrigin)
      occurrence
      (causalAuditResidualEntry N focus Residual distinguished Origin
        distinguishedOrigin occurrence)
      (causalAuditResidualEntry N focus Residual distinguished Origin
        distinguishedOrigin occurrence) :=
  (causalAuditRowSource N focus Residual Origin distinguishedOrigin).generate
    ⟨rfl, HEq.rfl⟩

def causalAuditRows
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt
      (causalAuditRowSource N focus Residual Origin distinguishedOrigin)
      occurrence
      ⟨(causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.account.supportOf occurrence⟩ where
  size := 1
  sourceEntryAt := fun _ => causalAuditResidualEntry N focus Residual
    distinguished Origin distinguishedOrigin occurrence
  targetEntryAt := fun _ => causalAuditResidualEntry N focus Residual
    distinguished Origin distinguishedOrigin occurrence
  rowAt := fun _ => causalAuditGeneratedRow N focus Residual distinguished
    Origin distinguishedOrigin occurrence

private theorem residualEntry_eq_of_new
    (token : Residual)
    (opened : ULift.{u, 0} (PLift (focus = focus))) :
    (⟨Sum.inr token, opened⟩ :
      OpenResponsibilityAt (ExtendedNetwork N focus Residual) focus) =
        residualEntry focus distinguished := by
  cases Subsingleton.elim token distinguished
  apply Sigma.ext
  · rfl
  · change HEq opened (ULift.up (PLift.up rfl))
    exact heq_of_eq (Subsingleton.elim _ _)

def causalResidualIndex
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current)
    (entry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.account.supportOf occurrence)) :
    Option { index : Fin
        (causalAuditRows N focus Residual distinguished Origin
          distinguishedOrigin occurrence).size //
      (causalAuditRows N focus Residual distinguished Origin
          distinguishedOrigin occurrence).sourceEntryAt index = entry } := by
  cases causalAuditOccurrence_eq_emitted N focus Residual Origin
    distinguishedOrigin occurrence
  change Option { index : Fin 1 // residualEntry focus distinguished = entry }
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl _ => exact none
  | inr token =>
      exact some ⟨0, (residualEntry_eq_of_new N focus Residual distinguished
        token opened).symm⟩

def causalAuditCoverage
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    LedgerIdentityRemainderCoverageAt
      (causalAuditRows N focus Residual distinguished Origin
        distinguishedOrigin occurrence) where
  destinationIndex := causalResidualIndex N focus Residual distinguished
    Origin distinguishedOrigin occurrence
  originIndex := causalResidualIndex N focus Residual distinguished
    Origin distinguishedOrigin occurrence

def causalAuditPatch
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt
      (causalAuditRowSource N focus Residual Origin distinguishedOrigin)
      occurrence
      ⟨(causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.account.supportOf occurrence⟩ :=
  .identityRemainder
    (causalAuditRows N focus Residual distinguished Origin
      distinguishedOrigin occurrence)
    (causalAuditCoverage N focus Residual distinguished Origin
      distinguishedOrigin occurrence)

def causalAuditGenerated
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt
      (causalAuditSource N focus Residual Origin distinguishedOrigin)
      occurrence := by
  cases causalAuditOccurrence_eq_emitted N focus Residual Origin
    distinguishedOrigin occurrence
  exact .nativeWrite PUnit.unit rfl
    (causalAuditEmitted N focus Residual Origin distinguishedOrigin
      (ULift.up true))
    (causalAuditPatch N focus Residual distinguished Origin distinguishedOrigin
      (causalAuditEmitted N focus Residual Origin distinguishedOrigin current)
      ).toLedgerWriteEvolution

def causalAuditCompiler : SourceNativeLedgerCompiler
    (causalAuditSource N focus Residual Origin distinguishedOrigin) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := CausalAuditExactTransitionAt N focus Residual Origin
    distinguishedOrigin
  exact_incidence := fun {_} {_} {_} {_} {_} _ => PUnit.unit
  exact_lineage := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry exact
    exact congrArg (ExtendedNetwork N focus Residual).lineageAt exact.support_eq
  writeRowSource := causalAuditRowSource N focus Residual Origin
    distinguishedOrigin
  terminalRowSource := causalAuditTerminalRowSource N focus Residual Origin
    distinguishedOrigin
  compile := causalAuditGenerated N focus Residual distinguished Origin
    distinguishedOrigin
  compilePatch := by
    intro current occurrence
    cases causalAuditOccurrence_eq_emitted N focus Residual Origin
      distinguishedOrigin occurrence
    change { patch : FiniteGeneratedLedgerWritePatchAt
        (causalAuditRowSource N focus Residual Origin distinguishedOrigin)
        (causalAuditEmitted N focus Residual Origin distinguishedOrigin current)
          ⟨focus⟩ //
      patch.toLedgerWriteEvolution =
        (causalAuditPatch N focus Residual distinguished Origin
          distinguishedOrigin
          (causalAuditEmitted N focus Residual Origin distinguishedOrigin current)
          ).toLedgerWriteEvolution }
    exact ⟨causalAuditPatch N focus Residual distinguished Origin
      distinguishedOrigin
      (causalAuditEmitted N focus Residual Origin distinguishedOrigin current),
      rfl⟩

def causalAuditLedgerSource : SourceNativeLedgerSource
    (ExtendedNetwork N focus Residual) AuditV where
  source := causalAuditSource N focus Residual Origin distinguishedOrigin
  ledgerCompiler := causalAuditCompiler N focus Residual distinguished Origin
    distinguishedOrigin

def causalAuditLedgerRoot : SourceNativeLedgerRootClosure
    (ExtendedNetwork N focus Residual) AuditV where
  source := causalAuditLedgerSource N focus Residual distinguished Origin
    distinguishedOrigin
  emitted := causalAuditEmitted N focus Residual Origin distinguishedOrigin
  compiler_commutes := fun _ => rfl

/-- Every inherited row remains in the identity remainder; only the
distinguished residual row is selected by the generated finite patch. -/
theorem causalOldEntry_is_identityRemainder
    (entry : OpenResponsibilityAt N focus) :
    sourceNativeFiniteLedgerPatchGeneratedEntry?
      (causalAuditSource N focus Residual Origin distinguishedOrigin)
      (causalAuditCompiler N focus Residual distinguished Origin
        distinguishedOrigin).ExactTransitionAt
      (causalAuditCompiler N focus Residual distinguished Origin
        distinguishedOrigin).writeRowSource
      (causalAuditCompiler N focus Residual distinguished Origin
        distinguishedOrigin).terminalRowSource
      ((causalAuditCompiler N focus Residual distinguished Origin
        distinguishedOrigin).compile
          (causalAuditEmitted N focus Residual Origin distinguishedOrigin
            (ULift.up false)))
      ((causalAuditCompiler N focus Residual distinguished Origin
        distinguishedOrigin).compilePatch
          (causalAuditEmitted N focus Residual Origin distinguishedOrigin
            (ULift.up false)))
      (oldEntry entry) = none := by
  rfl

end

end RootGeneratedCausalResidualAudit
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
