import H0mework.Versions.X.Fock.HistoryModel.SourceWord.NativeAlignment.Face

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordNativeAlignment

open CanonicalUnitArithmeticRoot
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem generated_row_is_native_transfer (current : Current) :
    HEq ((generatedRowsAtOccurrence (emitted current)).rowAt (0 : Fin 1)).evolution
      (LedgerEntryEvolutionAt.transferred
        (RootDispositionAt.transfer (nativeWriteAt current))
        rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt N (rootLedgerEntry current)
            (rootLedgerEntry (next current))) := by
  let rows := generatedRowsAtOccurrence (emitted current)
  have sourceEq : rows.sourceEntryAt (0 : Fin 1) = rootLedgerEntry current :=
    rootLedgerEntry_unique current _
  have targetEq : rows.targetEntryAt (0 : Fin 1) = rootLedgerEntry (next current) :=
    rootLedgerEntry_unique (next current) _
  cases sourceEq
  cases targetEq
  rfl

theorem root_disposition_uses_generated_row (current : Current) :
    HEq ((generatedLedgerEvolution (emitted current)).entryDisposition
      (rootLedgerEntry current))
      (LedgerEntryDispositionAt.evolved
        ((generatedRowsAtOccurrence (emitted current)).rowAt (0 : Fin 1)).evolution) := by
  rfl

theorem root_entry_disposition_native_transfer (current : Current) :
    HEq ((generatedLedgerEvolution (emitted current)).entryDisposition
      (rootLedgerEntry current))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred
          (RootDispositionAt.transfer (nativeWriteAt current))
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt N (rootLedgerEntry current)
              (rootLedgerEntry (next current)))) := by
  have row := generated_row_is_native_transfer current
  have disposition := root_disposition_uses_generated_row current
  cases row
  exact disposition

theorem installed_root_entry_disposition (depth : Nat) :
    let runtime := runtimeAt depth
    let current := runtime.current.visit.current
    HEq (runtime.tick.generated.wholeLedgerWriteBack.entryDisposition
      (rootLedgerEntry current))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred
          (RootDispositionAt.transfer (nativeWriteAt current))
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt N (rootLedgerEntry current)
              (rootLedgerEntry (next current)))) := by
  change HEq ((generatedLedgerEvolution
      (emitted (runtimeAt depth).current.visit.current)).entryDisposition
      (rootLedgerEntry (runtimeAt depth).current.visit.current)) _
  exact root_entry_disposition_native_transfer _

theorem same_write_observer (depth : Nat) :
    SourceWordNativeAlignment.nativeObservation (runtimePayload depth) =
      SourceWordObservedCode.observe
        (nativeWriteAt (runtimeAt depth).current.visit.current).target := rfl

end
end SourceWordNativeAlignment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
