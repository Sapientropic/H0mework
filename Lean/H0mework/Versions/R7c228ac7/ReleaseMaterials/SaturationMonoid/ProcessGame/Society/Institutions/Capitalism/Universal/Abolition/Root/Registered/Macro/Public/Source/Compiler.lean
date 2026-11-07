import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Exact

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

local notation "V₀" => V input depth count prefixLimit renewalLimit oldPast start family
local notation "rawRows" => RawRowAt input depth count prefixLimit renewalLimit oldPast start family
local notation "rowCompiler" => rowSource input depth count prefixLimit renewalLimit oldPast start family
local notation "wholePatch" => patch input depth count prefixLimit renewalLimit oldPast start family
local notation "sourceWrites" => writes input depth count prefixLimit renewalLimit oldPast start

def terminalRowSource : LedgerTerminalRowSourceAt src where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def sourcePacket {current : (V₀).Current} (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt src occurrence,
      SourceNativeFiniteLedgerPatchAt src rawRows rowCompiler
        (terminalRowSource input depth count prefixLimit renewalLimit oldPast start family) image := by
  cases occurrence_eq_emitted input depth count prefixLimit renewalLimit oldPast start family occurrence
  exact if active : sourceWrites current = true then
    ⟨.nativeWrite ⟨active⟩ (by rw [source_choice input depth count prefixLimit renewalLimit oldPast start family]; exact dif_pos active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩
  else
    ⟨.continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ (by rw [source_choice input depth count prefixLimit renewalLimit oldPast start family]; exact dif_neg active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler src where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := rawRows
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (rowEvolution input depth count prefixLimit renewalLimit oldPast start family _ seed).toDebtLineage.lineage_eq
  writeRowSource := rowCompiler
  terminalRowSource := terminalRowSource input depth count prefixLimit renewalLimit oldPast start family
  compile := fun occurrence => (sourcePacket input depth count prefixLimit renewalLimit oldPast start family occurrence).1
  compilePatch := fun occurrence => (sourcePacket input depth count prefixLimit renewalLimit oldPast start family occurrence).2

def ledgerSource : SourceNativeLedgerSource world V₀ where
  source := src
  ledgerCompiler := ledgerCompiler input depth count prefixLimit renewalLimit oldPast start family

def ledgerRoot : SourceNativeLedgerRootClosure world V₀ where
  source := ledgerSource input depth count prefixLimit renewalLimit oldPast start family
  emitted := emit
  compiler_commutes := by
    intro current
    change ((ledgerCompiler input depth count prefixLimit renewalLimit oldPast start family).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
