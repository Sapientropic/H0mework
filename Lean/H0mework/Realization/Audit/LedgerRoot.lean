import H0mework.Foundation.Inquiry.ResidualCoface
import H0mework.Foundation.Ledger.CompilerFacade

/-!
# Root-generated residual audit ledger root

The free residual-world coface supplies a distinguished, source-indexed
residual coordinate.  When that coordinate family is a subsingleton, this
kernel generates a two-chart audit root whose canonical finite patch selects
exactly that residual row.  Every inherited row is the definitionally carried
identity remainder, so an infinite old ledger is never smuggled into a finite
patch.

This is ledger-root authority, not yet a living/causal authority source.  The
next layer must install the operational theory/projection inventory and reuse
the generated row in the U7 commuting square.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedResidualAuditLedger

open RootGeneratedResidualAdmission

universe u

section

variable (N : WorldRelationNetwork.{u}) (focus : N.Support)
variable (Residual : Type u) (distinguished : Residual)
variable [Subsingleton Residual]

def auditVocabulary : Vocabulary.{u} where
  Current := ULift.{u, 0} Bool
  Anchor := PUnit
  Incidence := PUnit
  Lineage := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := fun _ => PUnit.unit
  lineageAt := fun _ => PUnit.unit
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun _ => ULift.up true
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev AuditV : Vocabulary.{u} := auditVocabulary.{u}

inductive AuditEventAt
    (Support : Type u) (focus : Support)
    (current : AuditV.Current) : Support → Type u
  | emitted : AuditEventAt Support focus current focus

def auditEventLaw
    (N : WorldRelationNetwork.{u}) (focus : N.Support)
    (Residual : Type u) :
    SourceNativeEventAlgebra (ExtendedNetwork N focus Residual) AuditV where
  EventAt := AuditEventAt N.Support focus
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_current} {support} _event =>
    OpenResponsibilityAt (ExtendedNetwork N focus Residual) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := fun _ => N.anchorAt focus
  incidenceKey := fun _ => N.incidenceAt focus
  lineageKey := fun _ => N.lineageAt focus
  anchor_commutes := by
    intro _current _support event
    cases event
    rfl
  incidence_commutes := by
    intro _current _support event
    cases event
    rfl
  lineage_commutes := by
    intro _current _support event
    cases event
    rfl

def auditSource
    (N : WorldRelationNetwork.{u}) (focus : N.Support)
    (Residual : Type u) :
    SourceNativeSource (ExtendedNetwork N focus Residual) AuditV where
  initial := ULift.up false
  law := auditEventLaw N focus Residual

def auditEmitted
    (N : WorldRelationNetwork.{u}) (focus : N.Support)
    (Residual : Type u) (current : AuditV.Current) :
    (auditSource N focus Residual).toRootSource.actual.OccurrenceAt current :=
  ⟨focus, AuditEventAt.emitted⟩

omit [Subsingleton Residual] in
theorem auditOccurrence_eq_emitted
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current) :
    occurrence = auditEmitted N focus Residual current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

structure AuditCarriedRowAt
    (W : WorldRelationNetwork.{u})
    {sourceSupport targetSupport : W.Support}
    (sourceEntry : OpenResponsibilityAt W sourceSupport)
    (targetEntry : OpenResponsibilityAt W targetSupport) : Type u where
  support_eq : sourceSupport = targetSupport
  entry_eq : HEq sourceEntry targetEntry

abbrev AuditExactTransitionAt
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current)
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((auditSource N focus Residual).toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      targetSupport) :=
  AuditCarriedRowAt (ExtendedNetwork N focus Residual) sourceEntry targetEntry

def auditRowSource : LedgerWriteRowSourceAt
    (auditSource N focus Residual)
    (AuditExactTransitionAt N focus Residual) where
  IncidenceOccurrenceAt := AuditExactTransitionAt N focus Residual
  compileEvolution := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry event
    exact .carried event.support_eq event.entry_eq
  compileExact := fun event => event

def auditTerminalRowSource : LedgerTerminalRowSourceAt
    (auditSource N focus Residual) :=
  LedgerTerminalRowSourceAt.empty _

def auditResidualEntry
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current) :
    OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((auditSource N focus Residual).toRootSource.account.supportOf occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact residualEntry focus distinguished

def auditGeneratedRow
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current) :
    GeneratedLedgerWriteRowAt (auditRowSource N focus Residual) occurrence
      (auditResidualEntry N focus Residual distinguished occurrence)
      (auditResidualEntry N focus Residual distinguished occurrence) :=
  (auditRowSource N focus Residual).generate ⟨rfl, HEq.rfl⟩

def auditRows
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current) :
    FiniteGeneratedLedgerWriteRowsAt
      (auditRowSource N focus Residual) occurrence
      ⟨(auditSource N focus Residual).toRootSource.account.supportOf
        occurrence⟩ where
  size := 1
  sourceEntryAt := fun _ =>
    auditResidualEntry N focus Residual distinguished occurrence
  targetEntryAt := fun _ =>
    auditResidualEntry N focus Residual distinguished occurrence
  rowAt := fun _ => auditGeneratedRow N focus Residual distinguished occurrence

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

def residualIndex
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current)
    (entry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((auditSource N focus Residual).toRootSource.account.supportOf
        occurrence)) :
    Option { index : Fin (auditRows N focus Residual distinguished occurrence).size //
      (auditRows N focus Residual distinguished occurrence).sourceEntryAt index =
        entry } := by
  rcases occurrence with ⟨support, event⟩
  cases event
  change Option { index : Fin 1 // residualEntry focus distinguished = entry }
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl _ => exact none
  | inr token =>
      exact some ⟨0, (residualEntry_eq_of_new N focus Residual distinguished
        token opened).symm⟩

def auditCoverage
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current) :
    LedgerIdentityRemainderCoverageAt
      (auditRows N focus Residual distinguished occurrence) where
  destinationIndex := residualIndex N focus Residual distinguished occurrence
  originIndex := residualIndex N focus Residual distinguished occurrence

def auditPatch
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current) :
    FiniteGeneratedLedgerWritePatchAt
      (auditRowSource N focus Residual) occurrence
      ⟨(auditSource N focus Residual).toRootSource.account.supportOf
        occurrence⟩ :=
  .identityRemainder
    (auditRows N focus Residual distinguished occurrence)
    (auditCoverage N focus Residual distinguished occurrence)

def auditGenerated
    {current : AuditV.Current}
    (occurrence : (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      current) :
    SourceNativeLedgerEvolutionAt (auditSource N focus Residual) occurrence := by
  cases auditOccurrence_eq_emitted N focus Residual occurrence
  exact .nativeWrite PUnit.unit rfl
    (auditEmitted N focus Residual (ULift.up true))
    (auditPatch N focus Residual distinguished
      (auditEmitted N focus Residual current)).toLedgerWriteEvolution

def auditCompiler : SourceNativeLedgerCompiler
    (auditSource N focus Residual) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := AuditExactTransitionAt N focus Residual
  exact_incidence := fun {_} {_} {_} {_} {_} _ => PUnit.unit
  exact_lineage := by
    intro _current _occurrence _targetSupport _sourceEntry _targetEntry exact
    exact congrArg (ExtendedNetwork N focus Residual).lineageAt exact.support_eq
  writeRowSource := auditRowSource N focus Residual
  terminalRowSource := auditTerminalRowSource N focus Residual
  compile := auditGenerated N focus Residual distinguished
  compilePatch := by
    intro current occurrence
    cases auditOccurrence_eq_emitted N focus Residual occurrence
    change { patch : FiniteGeneratedLedgerWritePatchAt
        (auditRowSource N focus Residual)
        (auditEmitted N focus Residual current) ⟨focus⟩ //
      patch.toLedgerWriteEvolution =
        (auditPatch N focus Residual distinguished
          (auditEmitted N focus Residual current)).toLedgerWriteEvolution }
    exact ⟨auditPatch N focus Residual distinguished
      (auditEmitted N focus Residual current), rfl⟩

def auditLedgerSource : SourceNativeLedgerSource
    (ExtendedNetwork N focus Residual) AuditV where
  source := auditSource N focus Residual
  ledgerCompiler := auditCompiler N focus Residual distinguished

/-- Actual enlarged ledger root.  The first chart is the residual audit and
the generated target chart is the canonical `true` occurrence. -/
def auditLedgerRoot : SourceNativeLedgerRootClosure
    (ExtendedNetwork N focus Residual) AuditV where
  source := auditLedgerSource N focus Residual distinguished
  emitted := auditEmitted N focus Residual
  compiler_commutes := fun _ => rfl

def initialOccurrence :
    (auditSource N focus Residual).toRootSource.actual.OccurrenceAt
      (ULift.up false) :=
  auditEmitted N focus Residual (ULift.up false)

abbrev initialResidualEntry :
    OpenResponsibilityAt (ExtendedNetwork N focus Residual) focus :=
  residualEntry focus distinguished

/-- The distinguished residual row is selected by the same finite-patch
coverage function that folds the whole ledger. -/
def residualGeneratedRow :
    SourceNativeFiniteLedgerPatchGeneratedEntryAt
      (auditSource N focus Residual)
      (auditCompiler N focus Residual distinguished).ExactTransitionAt
      (auditCompiler N focus Residual distinguished).writeRowSource
      (auditCompiler N focus Residual distinguished).terminalRowSource
      ((auditCompiler N focus Residual distinguished).compile
        (initialOccurrence N focus Residual))
      ((auditCompiler N focus Residual distinguished).compilePatch
        (initialOccurrence N focus Residual))
      (initialResidualEntry N focus Residual distinguished) :=
  (sourceNativeFiniteLedgerPatchGeneratedEntry?
    (auditSource N focus Residual)
    (auditCompiler N focus Residual distinguished).ExactTransitionAt
    (auditCompiler N focus Residual distinguished).writeRowSource
    (auditCompiler N focus Residual distinguished).terminalRowSource
    ((auditCompiler N focus Residual distinguished).compile
      (initialOccurrence N focus Residual))
    ((auditCompiler N focus Residual distinguished).compilePatch
      (initialOccurrence N focus Residual))
    (initialResidualEntry N focus Residual distinguished)).get (by rfl)

theorem residualGeneratedRow_commutes_with_world :
    (residualGeneratedRow N focus Residual distinguished).CommutesWithWorld :=
  (residualGeneratedRow N focus Residual distinguished).commutes_with_world

/-- Inherited rows remain visible in the complete ledger but are not falsely
promoted to the one generated residual incidence. -/
theorem oldEntry_is_identity_remainder
    (entry : OpenResponsibilityAt N focus) :
    sourceNativeFiniteLedgerPatchGeneratedEntry?
      (auditSource N focus Residual)
      (auditCompiler N focus Residual distinguished).ExactTransitionAt
      (auditCompiler N focus Residual distinguished).writeRowSource
      (auditCompiler N focus Residual distinguished).terminalRowSource
      ((auditCompiler N focus Residual distinguished).compile
        (initialOccurrence N focus Residual))
      ((auditCompiler N focus Residual distinguished).compilePatch
        (initialOccurrence N focus Residual))
      (oldEntry entry) = none := by
  rfl

end

end RootGeneratedResidualAuditLedger
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
