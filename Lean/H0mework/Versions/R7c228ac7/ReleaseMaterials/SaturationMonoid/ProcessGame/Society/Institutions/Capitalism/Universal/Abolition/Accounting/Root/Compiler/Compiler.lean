import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Exact

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

local notation "V₀" => V F
local notation "rawRows" => RawRowAt F
local notation "rowCompiler" => rowSource F
local notation "wholePatch" => patch F
local notation "sourceWrites" => F.writes

def terminalRowSource : LedgerTerminalRowSourceAt src where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def sourcePacket {current : (V₀).Current} (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt src occurrence,
      SourceNativeFiniteLedgerPatchAt src rawRows rowCompiler
        (terminalRowSource F) image := by
  cases occurrence_eq_emitted F occurrence
  exact if active : sourceWrites current = true then
    ⟨.nativeWrite ⟨active⟩ (by rw [source_choice F]; exact dif_pos active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩
  else
    ⟨.continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ (by rw [source_choice F]; exact dif_neg active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler src where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := rawRows
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (rowEvolution F _ seed).toDebtLineage.lineage_eq
  writeRowSource := rowCompiler
  terminalRowSource := terminalRowSource F
  compile := fun occurrence => (sourcePacket F occurrence).1
  compilePatch := fun occurrence => (sourcePacket F occurrence).2

def ledgerSource : SourceNativeLedgerSource (N) V₀ where
  source := src
  ledgerCompiler := ledgerCompiler F

def ledgerRoot : SourceNativeLedgerRootClosure (N) V₀ where
  source := ledgerSource F
  emitted := emit
  compiler_commutes := by
    intro current
    change ((ledgerCompiler F).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
