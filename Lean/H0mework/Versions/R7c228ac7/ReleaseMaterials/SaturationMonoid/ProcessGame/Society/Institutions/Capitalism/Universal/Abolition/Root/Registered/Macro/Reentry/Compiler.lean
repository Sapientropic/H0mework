import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.FiniteRows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  {review : Option (ReviewPhase.ContextAt input)}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (seed_eq : Accounting.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 = anchor)

local notation "src" => source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "V₀" => V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "advance" => Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0
local notation "writes" => Accounting.writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0

def rowsData : FiniteRows.Data src where
  emitted := emit
  next := advance
  evolution := wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
  finite := fun current => family.entries_finite current.account
    (nativeTail (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal seed_eq current)

local notation "data" => rowsData (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

def terminalRowSource : LedgerTerminalRowSourceAt src where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def sourcePacket {current : (V₀).Current} (occurrence : (src).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt src occurrence,
      SourceNativeFiniteLedgerPatchAt src (FiniteRows.RawRowAt data) (FiniteRows.rowSource data)
        (terminalRowSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq) image := by
  cases occurrence_eq_emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq occurrence
  exact if written : writes current = true then
    ⟨.nativeWrite ⟨written⟩ (by rw [source_choice]; exact dif_pos written)
      (emit (advance current)) (FiniteRows.patch data current).toLedgerWriteEvolution,
      ⟨FiniteRows.patch data current, rfl⟩⟩
  else
    ⟨.continuedTransport ⟨Bool.eq_false_of_not_eq_true written⟩ (by rw [source_choice]; exact dif_neg written)
      (emit (advance current)) (FiniteRows.patch data current).toLedgerWriteEvolution,
      ⟨FiniteRows.patch data current, rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler src where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := FiniteRows.RawRowAt data
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (FiniteRows.rowEvolution data _ seed).toDebtLineage.lineage_eq
  writeRowSource := FiniteRows.rowSource data
  terminalRowSource := terminalRowSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
  compile := fun occurrence => (sourcePacket (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq occurrence).1
  compilePatch := fun occurrence => (sourcePacket (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq occurrence).2

def ledgerSource : SourceNativeLedgerSource world V₀ where
  source := src
  ledgerCompiler := ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

theorem patch_keys (current : (V₀).Current) :
    Financial.Installation.KeepsKeys (FiniteRows.patch data current).toLedgerWriteEvolution := by
  unfold Financial.Installation.KeepsKeys
  rw [FiniteRows.patch_destination, FiniteRows.patch_origin]
  exact whole_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry
