import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

abbrev RowSeed := Continuation.RowSeed input (frame input depth count)

def sourceRow (current : (V input depth count prefixLimit renewalLimit).Current) (index : RowSeed input depth count) :
    OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit current) :=
  (Continuation.originalImage input (frame input depth count)).rows.sourceEntryAt index

def targetRow (current : (V input depth count prefixLimit renewalLimit).Current) (index : RowSeed input depth count) :
    OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit (current + 1)) :=
  (Continuation.originalImage input (frame input depth count)).rows.sourceEntryAt index

def rowEvolution (current : (V input depth count prefixLimit renewalLimit).Current) (index : RowSeed input depth count) :
    LedgerEntryEvolutionAt (N input depth count) (sourceRow input depth count prefixLimit renewalLimit current index)
      (targetRow input depth count prefixLimit renewalLimit current index) :=
  .transferred ((frame input depth count).native.disposition
    (Continuation.oldSupport input (frame input depth count)) .transfer) rfl rfl (Nat.le_refl _)

inductive RawRowAt :
    {current : (V input depth count prefixLimit renewalLimit).Current} →
    (occurrence : (source input depth count prefixLimit renewalLimit).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N input depth count).Support} →
    OpenResponsibilityAt (N input depth count) occurrence.1 →
    OpenResponsibilityAt (N input depth count) targetSupport → Type
  | generated (current : (V input depth count prefixLimit renewalLimit).Current) (index : RowSeed input depth count) :
      RawRowAt (emitted input depth count prefixLimit renewalLimit current)
        (sourceRow input depth count prefixLimit renewalLimit current index) (targetRow input depth count prefixLimit renewalLimit current index)

def rowSource : LedgerWriteRowSourceAt (source input depth count prefixLimit renewalLimit) (RawRowAt input depth count prefixLimit renewalLimit) where
  IncidenceOccurrenceAt := RawRowAt input depth count prefixLimit renewalLimit
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated index => exact rowEvolution input depth count prefixLimit renewalLimit _ index
  compileExact := fun event => event

def rows (current : (V input depth count prefixLimit renewalLimit).Current) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource input depth count prefixLimit renewalLimit)
      (emitted input depth count prefixLimit renewalLimit current) ⟨supportAt input depth count prefixLimit renewalLimit (current + 1)⟩ where
  size := (Continuation.originalImage input (frame input depth count)).rows.size
  sourceEntryAt := sourceRow input depth count prefixLimit renewalLimit current
  targetEntryAt := targetRow input depth count prefixLimit renewalLimit current
  rowAt := fun index => (rowSource input depth count prefixLimit renewalLimit).generate (.generated current index)

def coverage (current : (V input depth count prefixLimit renewalLimit).Current) :
    LedgerCompleteFiniteCoverageAt (rows input depth count prefixLimit renewalLimit current) where
  destinationIndex := (Continuation.originalImage input (frame input depth count)).coverage.destinationIndex
  originIndex := (Continuation.originalImage input (frame input depth count)).coverage.destinationIndex
  destination_sound := (Continuation.originalImage input (frame input depth count)).coverage.destination_sound
  origin_sound := (Continuation.originalImage input (frame input depth count)).coverage.destination_sound

def patch (current : (V input depth count prefixLimit renewalLimit).Current) :
    FiniteGeneratedLedgerWritePatchAt (rowSource input depth count prefixLimit renewalLimit)
      (emitted input depth count prefixLimit renewalLimit current) ⟨supportAt input depth count prefixLimit renewalLimit (current + 1)⟩ :=
  .complete (rows input depth count prefixLimit renewalLimit current) (coverage input depth count prefixLimit renewalLimit current)

theorem destination_is_original_entry (current : (V input depth count prefixLimit renewalLimit).Current)
    (entry : OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit current)) :
    ((patch input depth count prefixLimit renewalLimit current).toLedgerWriteEvolution.destination entry).1 = entry :=
  (Continuation.originalImage input (frame input depth count)).coverage.destination_sound entry

theorem origin_is_original_entry (current : (V input depth count prefixLimit renewalLimit).Current)
    (entry : OpenResponsibilityAt (N input depth count) (supportAt input depth count prefixLimit renewalLimit (current + 1))) :
    ((patch input depth count prefixLimit renewalLimit current).toLedgerWriteEvolution.origin entry).1 = entry :=
  (Continuation.originalImage input (frame input depth count)).coverage.destination_sound entry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration
