import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {N : WorldRelationNetwork} (F : Flow N)



local notation "C" => F.Current
local notation "supp" => F.support
local notation "advance" => F.next
local notation "evolution" => F.evolution

local notation "src" => source F
local notation "emit" => emitted F
local notation "Seed" => RowSeed F
local notation "beforeRow" => sourceRow F
local notation "afterRow" => targetRow F
local notation "enumerate" => rowEnum F

inductive RawRowAt : {current : C} → (occurrence : (src).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N).Support} → OpenResponsibilityAt (N) occurrence.1 → OpenResponsibilityAt (N) targetSupport → Type
  | generated (current : C) (seed : Seed current) : RawRowAt (emit current) (beforeRow current seed) (afterRow current seed)

local notation "rawRows" => RawRowAt F

def rowSource : LedgerWriteRowSourceAt src rawRows where
  IncidenceOccurrenceAt := rawRows
  compileEvolution := by
    intro current occurrence targetSupport before after event
    cases event with
    | generated seed => exact rowEvolution F _ seed
  compileExact := fun event => event

local notation "rowCompiler" => rowSource F

def rows (current : C) : FiniteGeneratedLedgerWriteRowsAt rowCompiler (emit current) ⟨supp (advance current)⟩ where
  size := rowCount F current
  sourceEntryAt := fun index => beforeRow current ((enumerate current).symm index)
  targetEntryAt := fun index => afterRow current ((enumerate current).symm index)
  rowAt := fun index => (rowCompiler).generate (.generated current ((enumerate current).symm index))

local notation "allRows" => rows F

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
  .complete (allRows current) (coverage F current)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
