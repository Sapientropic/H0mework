import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalCoordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source)

abbrev TerminalItem (point : Point source) := Σ entry : OpenResponsibilityAt N point.2.1, rows.IncidenceOccurrenceAt point.2 entry
abbrev TerminalBody (point : Point source) := Σ size : Nat, Fin size → TerminalItem rows point
abbrev TerminalBodies := (point : Point source) → TerminalBody rows point

def terminalBody {point : Point source} (patch : FiniteGeneratedLedgerTerminalPatchAt rows point.2) : TerminalBody rows point :=
  ⟨patch.size, fun index => ⟨patch.entryAt index, (patch.rowAt index).event⟩⟩

abbrev TerminalIndices {point : Point source} (body : TerminalBody rows point) :=
  (entry : OpenResponsibilityAt N point.2.1) → { index : Fin body.1 // (body.2 index).1 = entry }

def terminalFinite {point : Point source} (body : TerminalBody rows point) (indices : TerminalIndices rows body) :
    FiniteGeneratedLedgerTerminalPatchAt rows point.2 where
  size := body.1
  entryAt := fun index => (body.2 index).1
  rowAt := fun index => rows.generate (body.2 index).2
  entryIndex := fun entry => (indices entry).1
  entry_sound := fun entry => (indices entry).2

def terminalIndices {point : Point source} (patch : FiniteGeneratedLedgerTerminalPatchAt rows point.2) :
    TerminalIndices rows (terminalBody rows patch) := fun entry => ⟨patch.entryIndex entry, patch.entry_sound entry⟩

theorem terminalFinite_original {point : Point source} (patch : FiniteGeneratedLedgerTerminalPatchAt rows point.2) :
    terminalFinite rows (terminalBody rows patch) (terminalIndices rows patch) = patch := by
  have sealed : (fun index => rows.generate (patch.rowAt index).event) = patch.rowAt := by
    funext index
    exact (terminalSealEquiv rows ⟨point, patch.entryAt index⟩).symm_apply_apply (patch.rowAt index)
  exact congrArg (fun rowAt => (⟨patch.size, patch.entryAt, rowAt, patch.entryIndex, patch.entry_sound⟩ :
    FiniteGeneratedLedgerTerminalPatchAt rows point.2)) sealed

def terminalItemAddress (ledger : LedgerCoordinates N) (eventCode : ∀ context, RowEvents rows context ↪ B)
    (point : Point source) : TerminalItem rows point ↪ B where
  toFun := fun item => MotherHigherLawFamily.pair (ledger.entry point.2.1 item.1, eventCode ⟨point, item.1⟩ item.2)
  inj' := by
    rintro ⟨entry, event⟩ ⟨entry', event'⟩ same
    have pairEq := MotherHigherLawFamily.pair_injective same
    have same := (ledger.entry point.2.1).injective (congrArg Prod.fst pairEq)
    cases same
    have same := (eventCode ⟨point, entry⟩).injective (congrArg Prod.snd pairEq)
    cases same
    rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
