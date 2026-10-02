import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Patches

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)

def patchInventory {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {target : CompleteLiveLedgerAt N} (patch : FiniteGeneratedLedgerWritePatchAt rows event target) :
    FiniteGeneratedLedgerWriteRowsAt rows event target := by
  cases patch with
  | identityRemainder inventory _ => exact inventory
  | complete inventory _ => exact inventory
  | transportedRemainder inventory _ _ => exact inventory

def patchSelections {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {target : CompleteLiveLedgerAt N} (patch : FiniteGeneratedLedgerWritePatchAt rows event target) :
    LedgerTransportedRemainderCoverageAt (patchInventory rows patch) := by
  cases patch with
  | identityRemainder _ coverage => exact {
      destinationIndex := coverage.destinationIndex
      originIndex := coverage.originIndex }
  | complete _ coverage => exact {
      destinationIndex := fun entry => some ⟨coverage.destinationIndex entry, coverage.destination_sound entry⟩
      originIndex := fun entry => some ⟨coverage.originIndex entry, coverage.origin_sound entry⟩ }
  | transportedRemainder _ coverage _ => exact coverage

def patchKind {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {target : CompleteLiveLedgerAt N} (patch : FiniteGeneratedLedgerWritePatchAt rows event target) : Nat := by
  cases patch with
  | identityRemainder => exact 0
  | complete => exact 1
  | transportedRemainder => exact 2

theorem patch_recovered {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {target : CompleteLiveLedgerAt N} (patch : FiniteGeneratedLedgerWritePatchAt rows event target) :
    patchOfKind? rows (⟨current, event⟩, target.support) (patchInventory rows patch) (patchSelections rows patch) (patchKind rows patch) =
      some patch := by
  cases patch with
  | identityRemainder inventory coverage =>
      simp only [patchKind, patchInventory, patchSelections, patchOfKind?]
      have same : event.1 = source.toRootSource.account.supportOf event := rfl
      rw [dif_pos same]
      rfl
  | complete inventory coverage =>
      simp only [patchKind, patchInventory, patchSelections, patchOfKind?]
      have total : (∀ entry, (some (⟨coverage.destinationIndex entry, coverage.destination_sound entry⟩ :
          { index : Fin inventory.size // inventory.sourceEntryAt index = entry })).isSome = true) ∧
          (∀ entry, (some (⟨coverage.originIndex entry, coverage.origin_sound entry⟩ :
          { index : Fin inventory.size // inventory.targetEntryAt index = entry })).isSome = true) :=
        ⟨fun _ => rfl, fun _ => rfl⟩
      unfold completeOfPartial?
      rw [dif_pos total]
      rfl
  | transportedRemainder inventory coverage remainder =>
      simp only [patchKind, patchInventory, patchSelections, patchOfKind?]
      exact congrArg (Option.map (fun value : GeneratedLedgerTransportedRemainderAt rows event target =>
        FiniteGeneratedLedgerWritePatchAt.transportedRemainder inventory coverage value))
        (remainder_generated (point := ⟨current, event⟩) remainder)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
