import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Finite
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "W" => N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "C" => Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "supp" => supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "advance" => next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "evolution" => wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "src" => source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

abbrev RowSeed (current : C) := OpenResponsibilityAt W (supp current) ⊕ OpenResponsibilityAt W (supp (advance current))

@[instance_reducible] private def rowFintype (current : C) : Fintype (RowSeed (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) := by
  letI := entryFintype (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  letI := entryFintype (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (advance current)
  exact inferInstance

private def rowCount (current : C) := @Fintype.card _ (rowFintype (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
private def rowEnum (current : C) := @Fintype.equivFin _ (rowFintype (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)

local notation "Seed" => RowSeed (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "enumerate" => rowEnum (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def sourceRow (current : C) : Seed current → OpenResponsibilityAt W (supp current)
  | .inl entry => entry
  | .inr entry => ((evolution current).origin entry).1

def targetRow (current : C) : Seed current → OpenResponsibilityAt W (supp (advance current))
  | .inl entry => ((evolution current).destination entry).1
  | .inr entry => entry

local notation "beforeRow" => sourceRow (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "afterRow" => targetRow (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def rowEvolution (current : C) (seed : Seed current) : LedgerEntryEvolutionAt W (beforeRow current seed) (afterRow current seed) :=
  match seed with
  | .inl entry => ((evolution current).destination entry).2
  | .inr entry => ((evolution current).origin entry).2

inductive RawRowAt : {current : C} → (occurrence : (src).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (W).Support} → OpenResponsibilityAt W occurrence.1 → OpenResponsibilityAt W targetSupport → Type
  | generated (current : C) (seed : Seed current) : RawRowAt (emit current) (beforeRow current seed) (afterRow current seed)

local notation "rawRows" => RawRowAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def rowSource : LedgerWriteRowSourceAt src rawRows where
  IncidenceOccurrenceAt := rawRows
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated seed => exact rowEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition _ seed
  compileExact := fun event => event

local notation "rowCompiler" => rowSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def rows (current : C) : FiniteGeneratedLedgerWriteRowsAt rowCompiler (emit current) ⟨supp (advance current)⟩ where
  size := rowCount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  sourceEntryAt := fun index => beforeRow current ((enumerate current).symm index)
  targetEntryAt := fun index => afterRow current ((enumerate current).symm index)
  rowAt := fun index => (rowCompiler).generate (.generated current ((enumerate current).symm index))

local notation "allRows" => rows (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def coverage (current : C) : LedgerCompleteFiniteCoverageAt (allRows current) where
  destinationIndex := fun entry => enumerate current (.inl entry)
  originIndex := fun entry => enumerate current (.inr entry)
  destination_sound := by
    intro entry
    change beforeRow current ((enumerate current).symm (enumerate current (.inl entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl
  origin_sound := by
    intro entry
    change afterRow current ((enumerate current).symm (enumerate current (.inr entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl

def patch (current : C) : FiniteGeneratedLedgerWritePatchAt rowCompiler (emit current) ⟨supp (advance current)⟩ :=
  .complete (allRows current) (coverage (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)

private theorem destination_selected (current : C) (entry : OpenResponsibilityAt W (supp current))
    (seed : Seed current) (selected : seed = .inl entry) (entry_eq : beforeRow current seed = entry) :
    (⟨afterRow current seed,
      Eq.mp (congrArg (fun before => LedgerEntryEvolutionAt W before (afterRow current seed)) entry_eq)
        (rowEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current seed)⟩ :
      Σ targetEntry : OpenResponsibilityAt W (supp (advance current)), LedgerEntryEvolutionAt W entry targetEntry) =
      (evolution current).destination entry := by
  cases selected
  rfl

private theorem origin_selected (current : C) (entry : OpenResponsibilityAt W (supp (advance current)))
    (seed : Seed current) (selected : seed = .inr entry) (entry_eq : afterRow current seed = entry) :
    (⟨beforeRow current seed,
      Eq.mp (congrArg (fun after => LedgerEntryEvolutionAt W (beforeRow current seed) after) entry_eq)
        (rowEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current seed)⟩ :
      Σ sourceEntry : OpenResponsibilityAt W (supp current), LedgerEntryEvolutionAt W sourceEntry entry) =
      (evolution current).origin entry := by
  cases selected
  rfl

theorem patch_destination (current : C) :
    (patch (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).toLedgerWriteEvolution.destination =
      (evolution current).destination := by
  funext entry
  exact destination_selected (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current entry _
    ((enumerate current).symm_apply_apply (.inl entry))
    ((coverage (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).destination_sound entry)

theorem patch_origin (current : C) :
    (patch (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).toLedgerWriteEvolution.origin =
      (evolution current).origin := by
  funext entry
  exact origin_selected (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current entry _
    ((enumerate current).symm_apply_apply (.inr entry))
    ((coverage (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).origin_sound entry)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
