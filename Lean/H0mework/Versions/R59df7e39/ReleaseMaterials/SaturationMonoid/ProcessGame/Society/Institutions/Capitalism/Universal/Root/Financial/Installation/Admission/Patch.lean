import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Finiteness
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

abbrev RowSeed (current : Current input frame registered) :=
  OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current) ⊕
    OpenResponsibilityAt (N input frame registered) (supportAt input frame registered (next input frame registered current))

@[instance_reducible] noncomputable def rowFintype (current : Current input frame registered) : Fintype (RowSeed input frame registered current) := by
  letI := entryFintype input frame registered current
  letI := entryFintype input frame registered (next input frame registered current)
  exact inferInstance

noncomputable def rowCount (current : Current input frame registered) : Nat :=
  @Fintype.card (RowSeed input frame registered current) (rowFintype input frame registered current)

noncomputable def rowEnum (current : Current input frame registered) :
    RowSeed input frame registered current ≃ Fin (rowCount input frame registered current) :=
  @Fintype.equivFin (RowSeed input frame registered current) (rowFintype input frame registered current)

def sourceRow (current : Current input frame registered) : RowSeed input frame registered current →
    OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current)
  | .inl entry => entry
  | .inr entry => ((wholeEvolution input frame registered current).origin entry).1

def targetRow (current : Current input frame registered) : RowSeed input frame registered current →
    OpenResponsibilityAt (N input frame registered) (supportAt input frame registered (next input frame registered current))
  | .inl entry => ((wholeEvolution input frame registered current).destination entry).1
  | .inr entry => entry

def rowEvolution (current : Current input frame registered) (seed : RowSeed input frame registered current) :
    LedgerEntryEvolutionAt (N input frame registered) (sourceRow input frame registered current seed)
      (targetRow input frame registered current seed) :=
  match seed with
  | .inl entry => ((wholeEvolution input frame registered current).destination entry).2
  | .inr entry => ((wholeEvolution input frame registered current).origin entry).2

inductive RawRowAt :
    {current : Current input frame registered} →
    (occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N input frame registered).Support} →
    OpenResponsibilityAt (N input frame registered) occurrence.1 →
    OpenResponsibilityAt (N input frame registered) targetSupport → Type
  | generated (current : Current input frame registered) (seed : RowSeed input frame registered current) :
      RawRowAt (emitted input frame registered current)
        (sourceRow input frame registered current seed) (targetRow input frame registered current seed)

def rowSource : LedgerWriteRowSourceAt (source input frame registered) (RawRowAt input frame registered) where
  IncidenceOccurrenceAt := RawRowAt input frame registered
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated seed => exact rowEvolution input frame registered _ seed
  compileExact := fun event => event

noncomputable def rows (current : Current input frame registered) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource input frame registered)
      (emitted input frame registered current) ⟨supportAt input frame registered (next input frame registered current)⟩ where
  size := rowCount input frame registered current
  sourceEntryAt := fun index => sourceRow input frame registered current ((rowEnum input frame registered current).symm index)
  targetEntryAt := fun index => targetRow input frame registered current ((rowEnum input frame registered current).symm index)
  rowAt := fun index => (rowSource input frame registered).generate
    (.generated current ((rowEnum input frame registered current).symm index))

noncomputable def coverage (current : Current input frame registered) :
    LedgerCompleteFiniteCoverageAt (rows input frame registered current) where
  destinationIndex := fun entry => rowEnum input frame registered current (.inl entry)
  originIndex := fun entry => rowEnum input frame registered current (.inr entry)
  destination_sound := by
    intro entry
    change sourceRow input frame registered current
      ((rowEnum input frame registered current).symm ((rowEnum input frame registered current) (.inl entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl
  origin_sound := by
    intro entry
    change targetRow input frame registered current
      ((rowEnum input frame registered current).symm ((rowEnum input frame registered current) (.inr entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl

noncomputable def patch (current : Current input frame registered) :
    FiniteGeneratedLedgerWritePatchAt (rowSource input frame registered)
      (emitted input frame registered current) ⟨supportAt input frame registered (next input frame registered current)⟩ :=
  .complete (rows input frame registered current) (coverage input frame registered current)

private theorem destination_selected (current : Current input frame registered)
    (entry : OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current))
    (seed : RowSeed input frame registered current) (selected : seed = .inl entry)
    (entry_eq : sourceRow input frame registered current seed = entry) :
    (⟨targetRow input frame registered current seed,
      Eq.mp (congrArg (fun before => LedgerEntryEvolutionAt (N input frame registered) before
        (targetRow input frame registered current seed)) entry_eq) (rowEvolution input frame registered current seed)⟩ :
      Σ targetEntry : OpenResponsibilityAt (N input frame registered) (supportAt input frame registered (next input frame registered current)),
        LedgerEntryEvolutionAt (N input frame registered) entry targetEntry) =
      (wholeEvolution input frame registered current).destination entry := by
  cases selected
  rfl

private theorem origin_selected (current : Current input frame registered)
    (entry : OpenResponsibilityAt (N input frame registered) (supportAt input frame registered (next input frame registered current)))
    (seed : RowSeed input frame registered current) (selected : seed = .inr entry)
    (entry_eq : targetRow input frame registered current seed = entry) :
    (⟨sourceRow input frame registered current seed,
      Eq.mp (congrArg (fun after => LedgerEntryEvolutionAt (N input frame registered)
        (sourceRow input frame registered current seed) after) entry_eq) (rowEvolution input frame registered current seed)⟩ :
      Σ sourceEntry : OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current),
        LedgerEntryEvolutionAt (N input frame registered) sourceEntry entry) =
      (wholeEvolution input frame registered current).origin entry := by
  cases selected
  rfl

theorem patch_destination (current : Current input frame registered) :
    (patch input frame registered current).toLedgerWriteEvolution.destination =
      (wholeEvolution input frame registered current).destination := by
  funext entry
  exact destination_selected input frame registered current entry _
    ((rowEnum input frame registered current).symm_apply_apply (.inl entry))
    ((coverage input frame registered current).destination_sound entry)

theorem patch_origin (current : Current input frame registered) :
    (patch input frame registered current).toLedgerWriteEvolution.origin =
      (wholeEvolution input frame registered current).origin := by
  funext entry
  exact origin_selected input frame registered current entry _
    ((rowEnum input frame registered current).symm_apply_apply (.inr entry))
    ((coverage input frame registered current).origin_sound entry)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
