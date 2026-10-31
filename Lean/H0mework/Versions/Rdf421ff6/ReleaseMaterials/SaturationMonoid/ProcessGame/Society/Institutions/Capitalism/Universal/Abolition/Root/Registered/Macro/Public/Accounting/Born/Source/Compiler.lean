import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Exact

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

local notation "V₀" => V prior origin registered
local notation "rawRows" => RawRowAt prior origin registered
local notation "rowCompiler" => rowSource prior origin registered
local notation "wholePatch" => patch prior origin registered
local notation "sourceWrites" => writes origin registered

def terminalRowSource : LedgerTerminalRowSourceAt src where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def sourcePacket {current : (V₀).Current} (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt src occurrence,
      SourceNativeFiniteLedgerPatchAt src rawRows rowCompiler
        (terminalRowSource prior origin registered) image := by
  cases occurrence_eq_emitted prior origin registered occurrence
  exact if active : sourceWrites current = true then
    ⟨.nativeWrite ⟨active⟩ (by rw [source_choice prior origin registered]; exact dif_pos active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩
  else
    ⟨.continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ (by rw [source_choice prior origin registered]; exact dif_neg active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler src where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := rawRows
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (rowEvolution prior origin registered _ seed).toDebtLineage.lineage_eq
  writeRowSource := rowCompiler
  terminalRowSource := terminalRowSource prior origin registered
  compile := fun occurrence => (sourcePacket prior origin registered occurrence).1
  compilePatch := fun occurrence => (sourcePacket prior origin registered occurrence).2

def ledgerSource : SourceNativeLedgerSource (Born.N prior origin registered) V₀ where
  source := src
  ledgerCompiler := ledgerCompiler prior origin registered

def ledgerRoot : SourceNativeLedgerRootClosure (Born.N prior origin registered) V₀ where
  source := ledgerSource prior origin registered
  emitted := emit
  compiler_commutes := by
    intro current
    change ((ledgerCompiler prior origin registered).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
