import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Rows

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
local notation "V₀" => V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "advance" => next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "src" => source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "rawRows" => RawRowAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "rowCompiler" => rowSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "wholePatch" => patch (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "sourceWrites" => writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

theorem source_choice (current : C) : (src).toRootSource.actual.compile (emit current) =
    if active : sourceWrites current = true then
      EvolutionAt.nativeWrite (V := V₀) ⟨active⟩
    else .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ := rfl

def terminalRowSource : LedgerTerminalRowSourceAt src where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def sourcePacket {current : (V₀).Current} (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt src occurrence,
      SourceNativeFiniteLedgerPatchAt src rawRows rowCompiler
        (terminalRowSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) image := by
  cases occurrence_eq_emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition occurrence
  exact if active : sourceWrites current = true then
    ⟨.nativeWrite ⟨active⟩ (by rw [source_choice (review := review)]; exact dif_pos active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩
  else
    ⟨.continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ (by rw [source_choice (review := review)]; exact dif_neg active)
      (emit (advance current)) (wholePatch current).toLedgerWriteEvolution, ⟨wholePatch current, rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler src where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := rawRows
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (rowEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition _ seed).toDebtLineage.lineage_eq
  writeRowSource := rowCompiler
  terminalRowSource := terminalRowSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  compile := fun occurrence => (sourcePacket (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition occurrence).1
  compilePatch := fun occurrence => (sourcePacket (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition occurrence).2

def ledgerSource : SourceNativeLedgerSource W V₀ where
  source := src
  ledgerCompiler := ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def ledgerRoot : SourceNativeLedgerRootClosure W V₀ where
  source := ledgerSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  emitted := emit
  compiler_commutes := by
    intro current
    change ((ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
