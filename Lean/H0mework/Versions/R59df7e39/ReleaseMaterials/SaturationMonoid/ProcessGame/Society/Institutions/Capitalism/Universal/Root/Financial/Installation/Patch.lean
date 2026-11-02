import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Finiteness
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

abbrev RowSeed (current : Current input start) :=
  OpenResponsibilityAt (N input start) (supportAt input start current) ⊕
    OpenResponsibilityAt (N input start) (supportAt input start (next input start current))

@[instance_reducible] noncomputable def rowFintype (current : Current input start) : Fintype (RowSeed input start current) := by
  letI := entryFintype input start current
  letI := entryFintype input start (next input start current)
  exact inferInstance

noncomputable def rowCount (current : Current input start) : Nat :=
  @Fintype.card (RowSeed input start current) (rowFintype input start current)

noncomputable def rowEnum (current : Current input start) :
    RowSeed input start current ≃ Fin (rowCount input start current) :=
  @Fintype.equivFin (RowSeed input start current) (rowFintype input start current)

def sourceRow (current : Current input start) : RowSeed input start current →
    OpenResponsibilityAt (N input start) (supportAt input start current)
  | .inl entry => entry
  | .inr entry => ((wholeEvolution input start current).origin entry).1

def targetRow (current : Current input start) : RowSeed input start current →
    OpenResponsibilityAt (N input start) (supportAt input start (next input start current))
  | .inl entry => ((wholeEvolution input start current).destination entry).1
  | .inr entry => entry

def rowEvolution (current : Current input start) (seed : RowSeed input start current) :
    LedgerEntryEvolutionAt (N input start) (sourceRow input start current seed)
      (targetRow input start current seed) :=
  match seed with
  | .inl entry => ((wholeEvolution input start current).destination entry).2
  | .inr entry => ((wholeEvolution input start current).origin entry).2

inductive RawRowAt :
    {current : Current input start} →
    (occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N input start).Support} →
    OpenResponsibilityAt (N input start) occurrence.1 →
    OpenResponsibilityAt (N input start) targetSupport → Type
  | generated (current : Current input start) (seed : RowSeed input start current) :
      RawRowAt (emitted input start startPositive current)
        (sourceRow input start current seed) (targetRow input start current seed)

def rowSource : LedgerWriteRowSourceAt (source input start startPositive) (RawRowAt input start startPositive) where
  IncidenceOccurrenceAt := RawRowAt input start startPositive
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated seed => exact rowEvolution input start _ seed
  compileExact := fun event => event

noncomputable def rows (current : Current input start) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource input start startPositive)
      (emitted input start startPositive current) ⟨supportAt input start (next input start current)⟩ where
  size := rowCount input start current
  sourceEntryAt := fun index => sourceRow input start current ((rowEnum input start current).symm index)
  targetEntryAt := fun index => targetRow input start current ((rowEnum input start current).symm index)
  rowAt := fun index => (rowSource input start startPositive).generate
    (.generated current ((rowEnum input start current).symm index))

noncomputable def coverage (current : Current input start) :
    LedgerCompleteFiniteCoverageAt (rows input start startPositive current) where
  destinationIndex := fun entry => rowEnum input start current (.inl entry)
  originIndex := fun entry => rowEnum input start current (.inr entry)
  destination_sound := by
    intro entry
    change sourceRow input start current
      ((rowEnum input start current).symm ((rowEnum input start current) (.inl entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl
  origin_sound := by
    intro entry
    change targetRow input start current
      ((rowEnum input start current).symm ((rowEnum input start current) (.inr entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl

noncomputable def patch (current : Current input start) :
    FiniteGeneratedLedgerWritePatchAt (rowSource input start startPositive)
      (emitted input start startPositive current) ⟨supportAt input start (next input start current)⟩ :=
  .complete (rows input start startPositive current) (coverage input start startPositive current)

private theorem destination_selected (current : Current input start)
    (entry : OpenResponsibilityAt (N input start) (supportAt input start current))
    (seed : RowSeed input start current) (selected : seed = .inl entry)
    (entry_eq : sourceRow input start current seed = entry) :
    (⟨targetRow input start current seed,
      Eq.mp (congrArg (fun before => LedgerEntryEvolutionAt (N input start) before
        (targetRow input start current seed)) entry_eq) (rowEvolution input start current seed)⟩ :
      Σ targetEntry : OpenResponsibilityAt (N input start) (supportAt input start (next input start current)),
        LedgerEntryEvolutionAt (N input start) entry targetEntry) =
      (wholeEvolution input start current).destination entry := by
  cases selected
  rfl

private theorem origin_selected (current : Current input start)
    (entry : OpenResponsibilityAt (N input start) (supportAt input start (next input start current)))
    (seed : RowSeed input start current) (selected : seed = .inr entry)
    (entry_eq : targetRow input start current seed = entry) :
    (⟨sourceRow input start current seed,
      Eq.mp (congrArg (fun after => LedgerEntryEvolutionAt (N input start)
        (sourceRow input start current seed) after) entry_eq) (rowEvolution input start current seed)⟩ :
      Σ sourceEntry : OpenResponsibilityAt (N input start) (supportAt input start current),
        LedgerEntryEvolutionAt (N input start) sourceEntry entry) =
      (wholeEvolution input start current).origin entry := by
  cases selected
  rfl

theorem patch_destination (current : Current input start) :
    (patch input start startPositive current).toLedgerWriteEvolution.destination =
      (wholeEvolution input start current).destination := by
  funext entry
  exact destination_selected input start current entry _
    ((rowEnum input start current).symm_apply_apply (.inl entry))
    ((coverage input start startPositive current).destination_sound entry)

theorem patch_origin (current : Current input start) :
    (patch input start startPositive current).toLedgerWriteEvolution.origin =
      (wholeEvolution input start current).origin := by
  funext entry
  exact origin_selected input start current entry _
    ((rowEnum input start current).symm_apply_apply (.inr entry))
    ((coverage input start startPositive current).origin_sound entry)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource
