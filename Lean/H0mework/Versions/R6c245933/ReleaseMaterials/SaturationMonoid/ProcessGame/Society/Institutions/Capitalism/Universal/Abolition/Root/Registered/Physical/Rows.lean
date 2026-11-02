import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Patch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (start : Cursor Party Good Port Technology Instrument)

abbrev RowSeed := Continuation.RowSeed input (Migration.frame input depth count)

def sourceRow (current : Cursor Party Good Port Technology Instrument) (index : RowSeed input depth count) :
    OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit current) :=
  (Continuation.originalImage input (Migration.frame input depth count)).rows.sourceEntryAt index

def targetRow (current : Cursor Party Good Port Technology Instrument) (index : RowSeed input depth count) :
    OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit (next current)) :=
  (Continuation.originalImage input (Migration.frame input depth count)).rows.sourceEntryAt index

def rowEvolution (current : Cursor Party Good Port Technology Instrument) (index : RowSeed input depth count) :
    LedgerEntryEvolutionAt (N input depth count) (sourceRow input depth count prefixLimit renewalLimit current index)
      (targetRow input depth count prefixLimit renewalLimit current index) :=
  .transferred ((Migration.frame input depth count).native.disposition
    (Continuation.oldSupport input (Migration.frame input depth count)) .transfer) rfl rfl (Nat.le_refl _)

inductive RawRowAt :
    {current : (V input depth count prefixLimit renewalLimit).Current} →
    (occurrence : (sourceAt input depth count prefixLimit renewalLimit start).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N input depth count).Support} →
    OpenResponsibilityAt (N input depth count) occurrence.1 →
    OpenResponsibilityAt (N input depth count) targetSupport → Type
  | generated (current : Cursor Party Good Port Technology Instrument) (index : RowSeed input depth count) :
      RawRowAt (emitted input depth count prefixLimit renewalLimit start current)
        (sourceRow input depth count prefixLimit renewalLimit current index)
        (targetRow input depth count prefixLimit renewalLimit current index)

def rowSource : LedgerWriteRowSourceAt (sourceAt input depth count prefixLimit renewalLimit start)
    (RawRowAt input depth count prefixLimit renewalLimit start) where
  IncidenceOccurrenceAt := RawRowAt input depth count prefixLimit renewalLimit start
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated index => exact rowEvolution input depth count prefixLimit renewalLimit _ index
  compileExact := fun event => event

def rows (current : Cursor Party Good Port Technology Instrument) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource input depth count prefixLimit renewalLimit start)
      (emitted input depth count prefixLimit renewalLimit start current)
      ⟨supportAt input depth count prefixLimit renewalLimit (next current)⟩ where
  size := (Continuation.originalImage input (Migration.frame input depth count)).rows.size
  sourceEntryAt := sourceRow input depth count prefixLimit renewalLimit current
  targetEntryAt := targetRow input depth count prefixLimit renewalLimit current
  rowAt := fun index => (rowSource input depth count prefixLimit renewalLimit start).generate (.generated current index)

def coverage (current : Cursor Party Good Port Technology Instrument) :
    LedgerCompleteFiniteCoverageAt (rows input depth count prefixLimit renewalLimit start current) where
  destinationIndex := (Continuation.originalImage input (Migration.frame input depth count)).coverage.destinationIndex
  originIndex := (Continuation.originalImage input (Migration.frame input depth count)).coverage.destinationIndex
  destination_sound := (Continuation.originalImage input (Migration.frame input depth count)).coverage.destination_sound
  origin_sound := (Continuation.originalImage input (Migration.frame input depth count)).coverage.destination_sound

def patch (current : Cursor Party Good Port Technology Instrument) :
    FiniteGeneratedLedgerWritePatchAt (rowSource input depth count prefixLimit renewalLimit start)
      (emitted input depth count prefixLimit renewalLimit start current)
      ⟨supportAt input depth count prefixLimit renewalLimit (next current)⟩ :=
  .complete (rows input depth count prefixLimit renewalLimit start current)
    (coverage input depth count prefixLimit renewalLimit start current)

theorem destination_is_original_entry (current : Cursor Party Good Port Technology Instrument)
    (entry : OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit current)) :
    ((patch input depth count prefixLimit renewalLimit start current).toLedgerWriteEvolution.destination entry).1 = entry :=
  (Continuation.originalImage input (Migration.frame input depth count)).coverage.destination_sound entry

theorem origin_is_original_entry (current : Cursor Party Good Port Technology Instrument)
    (entry : OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit (next current))) :
    ((patch input depth count prefixLimit renewalLimit start current).toLedgerWriteEvolution.origin entry).1 = entry :=
  (Continuation.originalImage input (Migration.frame input depth count)).coverage.destination_sound entry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical
