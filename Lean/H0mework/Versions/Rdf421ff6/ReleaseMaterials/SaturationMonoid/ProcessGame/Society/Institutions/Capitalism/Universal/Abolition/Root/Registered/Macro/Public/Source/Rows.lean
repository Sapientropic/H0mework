import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

local notation "C" => Accounting.Current input depth count anchor
local notation "supp" => Accounting.support input depth count family
local notation "advance" => Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start
local notation "evolution" => Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start family

local notation "src" => source input depth count prefixLimit renewalLimit oldPast start family
local notation "emit" => emitted input depth count prefixLimit renewalLimit oldPast start family
local notation "Seed" => RowSeed input depth count prefixLimit renewalLimit oldPast start family
local notation "beforeRow" => sourceRow input depth count prefixLimit renewalLimit oldPast start family
local notation "afterRow" => targetRow input depth count prefixLimit renewalLimit oldPast start family
local notation "enumerate" => rowEnum input depth count prefixLimit renewalLimit oldPast start family

inductive RawRowAt : {current : C} → (occurrence : (src).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : world.Support} → OpenResponsibilityAt world occurrence.1 → OpenResponsibilityAt world targetSupport → Type
  | generated (current : C) (seed : Seed current) : RawRowAt (emit current) (beforeRow current seed) (afterRow current seed)

local notation "rawRows" => RawRowAt input depth count prefixLimit renewalLimit oldPast start family

def rowSource : LedgerWriteRowSourceAt src rawRows where
  IncidenceOccurrenceAt := rawRows
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated seed => exact rowEvolution input depth count prefixLimit renewalLimit oldPast start family _ seed
  compileExact := fun event => event

local notation "rowCompiler" => rowSource input depth count prefixLimit renewalLimit oldPast start family

def rows (current : C) : FiniteGeneratedLedgerWriteRowsAt rowCompiler (emit current) ⟨supp (advance current)⟩ where
  size := rowCount input depth count prefixLimit renewalLimit oldPast start family current
  sourceEntryAt := fun index => beforeRow current ((enumerate current).symm index)
  targetEntryAt := fun index => afterRow current ((enumerate current).symm index)
  rowAt := fun index => (rowCompiler).generate (.generated current ((enumerate current).symm index))

local notation "allRows" => rows input depth count prefixLimit renewalLimit oldPast start family

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
  .complete (allRows current) (coverage input depth count prefixLimit renewalLimit oldPast start family current)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
