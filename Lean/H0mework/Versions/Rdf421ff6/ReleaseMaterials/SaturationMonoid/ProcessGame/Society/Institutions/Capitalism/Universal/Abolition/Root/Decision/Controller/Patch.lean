import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count))
  (limit : Nat)

abbrev RowSeed := Continuation.RowSeed input (Admission.frame input depth count)

def sourceRow (current : (V input depth count datum limit).Current) (index : RowSeed input depth count) :
    OpenResponsibilityAt (N input depth count) (supportAt input depth count datum current) :=
  (Continuation.originalImage input (Admission.frame input depth count)).rows.sourceEntryAt index

def targetRow (current : (V input depth count datum limit).Current) (index : RowSeed input depth count) :
    OpenResponsibilityAt (N input depth count) (supportAt input depth count datum (next input depth count datum limit current)) :=
  (Continuation.originalImage input (Admission.frame input depth count)).rows.sourceEntryAt index

def rowEvolution (current : (V input depth count datum limit).Current) (index : RowSeed input depth count) :
    LedgerEntryEvolutionAt (N input depth count) (sourceRow input depth count datum limit current index)
      (targetRow input depth count datum limit current index) :=
  .transferred ((Admission.frame input depth count).native.disposition
    (Continuation.oldSupport input (Admission.frame input depth count)) .transfer) rfl rfl (Nat.le_refl _)

inductive RawRowAt :
    {current : (V input depth count datum limit).Current} →
    (occurrence : (source input depth count datum limit).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N input depth count).Support} →
    OpenResponsibilityAt (N input depth count) occurrence.1 →
    OpenResponsibilityAt (N input depth count) targetSupport → Type
  | generated (current : (V input depth count datum limit).Current) (index : RowSeed input depth count) :
      RawRowAt (emitted input depth count datum limit current)
        (sourceRow input depth count datum limit current index) (targetRow input depth count datum limit current index)

def rowSource : LedgerWriteRowSourceAt (source input depth count datum limit) (RawRowAt input depth count datum limit) where
  IncidenceOccurrenceAt := RawRowAt input depth count datum limit
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated index => exact rowEvolution input depth count datum limit _ index
  compileExact := fun event => event

def rows (current : (V input depth count datum limit).Current) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource input depth count datum limit)
      (emitted input depth count datum limit current) ⟨supportAt input depth count datum (next input depth count datum limit current)⟩ where
  size := (Continuation.originalImage input (Admission.frame input depth count)).rows.size
  sourceEntryAt := sourceRow input depth count datum limit current
  targetEntryAt := targetRow input depth count datum limit current
  rowAt := fun index => (rowSource input depth count datum limit).generate (.generated current index)

def coverage (current : (V input depth count datum limit).Current) :
    LedgerCompleteFiniteCoverageAt (rows input depth count datum limit current) where
  destinationIndex := (Continuation.originalImage input (Admission.frame input depth count)).coverage.destinationIndex
  originIndex := (Continuation.originalImage input (Admission.frame input depth count)).coverage.destinationIndex
  destination_sound := (Continuation.originalImage input (Admission.frame input depth count)).coverage.destination_sound
  origin_sound := (Continuation.originalImage input (Admission.frame input depth count)).coverage.destination_sound

def patch (current : (V input depth count datum limit).Current) :
    FiniteGeneratedLedgerWritePatchAt (rowSource input depth count datum limit)
      (emitted input depth count datum limit current) ⟨supportAt input depth count datum (next input depth count datum limit current)⟩ :=
  .complete (rows input depth count datum limit current) (coverage input depth count datum limit current)

theorem destination_is_original_entry (current : (V input depth count datum limit).Current)
    (entry : OpenResponsibilityAt (N input depth count) (supportAt input depth count datum current)) :
    ((patch input depth count datum limit current).toLedgerWriteEvolution.destination entry).1 = entry :=
  (Continuation.originalImage input (Admission.frame input depth count)).coverage.destination_sound entry

theorem origin_is_original_entry (current : (V input depth count datum limit).Current)
    (entry : OpenResponsibilityAt (N input depth count) (supportAt input depth count datum (next input depth count datum limit current))) :
    ((patch input depth count datum limit current).toLedgerWriteEvolution.origin entry).1 = entry :=
  (Continuation.originalImage input (Admission.frame input depth count)).coverage.destination_sound entry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller
