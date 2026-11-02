import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.Runtime.Frame input)
  (request : Request Party Good Port Technology Instrument)

def originalImage := frame.native.program.emit frame.visit.current

abbrev RowSeed := Fin (originalImage input frame).rows.size

def sourceRow (current : (V input frame request).Current) (index : RowSeed input frame) :
    OpenResponsibilityAt (N input frame) (supportAt input frame current) :=
  (originalImage input frame).rows.sourceEntryAt index

def targetRow (current : (V input frame request).Current) (index : RowSeed input frame) :
    OpenResponsibilityAt (N input frame) (supportAt input frame (next input request current)) :=
  (originalImage input frame).rows.sourceEntryAt index

def rowEvolution (current : (V input frame request).Current) (index : RowSeed input frame) :
    LedgerEntryEvolutionAt (N input frame) (sourceRow input frame request current index)
      (targetRow input frame request current index) :=
  .transferred (frame.native.disposition (oldSupport input frame) .transfer) rfl rfl (Nat.le_refl _)

inductive RawRowAt :
    {current : (V input frame request).Current} →
    (occurrence : (source input frame request).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N input frame).Support} →
    OpenResponsibilityAt (N input frame) occurrence.1 →
    OpenResponsibilityAt (N input frame) targetSupport → Type
  | generated (current : (V input frame request).Current) (index : RowSeed input frame) :
      RawRowAt (emitted input frame request current)
        (sourceRow input frame request current index) (targetRow input frame request current index)

def rowSource : LedgerWriteRowSourceAt (source input frame request) (RawRowAt input frame request) where
  IncidenceOccurrenceAt := RawRowAt input frame request
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated index => exact rowEvolution input frame request _ index
  compileExact := fun event => event

def rows (current : (V input frame request).Current) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource input frame request)
      (emitted input frame request current) ⟨supportAt input frame (next input request current)⟩ where
  size := (originalImage input frame).rows.size
  sourceEntryAt := sourceRow input frame request current
  targetEntryAt := targetRow input frame request current
  rowAt := fun index => (rowSource input frame request).generate (.generated current index)

def coverage (current : (V input frame request).Current) :
    LedgerCompleteFiniteCoverageAt (rows input frame request current) where
  destinationIndex := (originalImage input frame).coverage.destinationIndex
  originIndex := (originalImage input frame).coverage.destinationIndex
  destination_sound := (originalImage input frame).coverage.destination_sound
  origin_sound := (originalImage input frame).coverage.destination_sound

def patch (current : (V input frame request).Current) :
    FiniteGeneratedLedgerWritePatchAt (rowSource input frame request)
      (emitted input frame request current) ⟨supportAt input frame (next input request current)⟩ :=
  .complete (rows input frame request current) (coverage input frame request current)

theorem destination_is_original_entry (current : (V input frame request).Current)
    (entry : OpenResponsibilityAt (N input frame) (supportAt input frame current)) :
    ((patch input frame request current).toLedgerWriteEvolution.destination entry).1 = entry :=
  (originalImage input frame).coverage.destination_sound entry

theorem origin_is_original_entry (current : (V input frame request).Current)
    (entry : OpenResponsibilityAt (N input frame) (supportAt input frame (next input request current))) :
    ((patch input frame request current).toLedgerWriteEvolution.origin entry).1 = entry :=
  (originalImage input frame).coverage.destination_sound entry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation
