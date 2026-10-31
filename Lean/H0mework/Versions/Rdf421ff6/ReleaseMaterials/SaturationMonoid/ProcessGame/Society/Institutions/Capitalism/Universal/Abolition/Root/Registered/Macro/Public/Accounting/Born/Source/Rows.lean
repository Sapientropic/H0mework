import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)


local notation "C" => State origin registered
local notation "supp" => supportAt prior origin registered
local notation "advance" => next origin registered
local notation "evolution" => wholeEvolution prior origin registered

local notation "src" => source prior origin registered
local notation "emit" => emitted prior origin registered
local notation "Seed" => RowSeed prior origin registered
local notation "beforeRow" => sourceRow prior origin registered
local notation "afterRow" => targetRow prior origin registered
local notation "enumerate" => rowEnum prior origin registered

inductive RawRowAt : {current : C} → (occurrence : (src).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (Born.N prior origin registered).Support} → OpenResponsibilityAt (Born.N prior origin registered) occurrence.1 → OpenResponsibilityAt (Born.N prior origin registered) targetSupport → Type
  | generated (current : C) (seed : Seed current) : RawRowAt (emit current) (beforeRow current seed) (afterRow current seed)

local notation "rawRows" => RawRowAt prior origin registered

def rowSource : LedgerWriteRowSourceAt src rawRows where
  IncidenceOccurrenceAt := rawRows
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated seed => exact rowEvolution prior origin registered _ seed
  compileExact := fun event => event

local notation "rowCompiler" => rowSource prior origin registered

def rows (current : C) : FiniteGeneratedLedgerWriteRowsAt rowCompiler (emit current) ⟨supp (advance current)⟩ where
  size := rowCount prior origin registered current
  sourceEntryAt := fun index => beforeRow current ((enumerate current).symm index)
  targetEntryAt := fun index => afterRow current ((enumerate current).symm index)
  rowAt := fun index => (rowCompiler).generate (.generated current ((enumerate current).symm index))

local notation "allRows" => rows prior origin registered

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
  .complete (allRows current) (coverage prior origin registered current)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
