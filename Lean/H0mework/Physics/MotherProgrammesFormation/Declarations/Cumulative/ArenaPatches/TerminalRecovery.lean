import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.TerminalCoverage
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalRecovery

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

namespace TerminalRequestEncoding
open MotherPatchInventory.TerminalRequestEncoding (body index kind)
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source)

variable (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N)
    (desired : (point : Point source) → Option (SourceGeneratedLedgerTerminalPatchAt rows point.2))

def indexReader (code : B) (_tag : Nat) : ℝ :=
  Function.extend (MotherArenaPrograms.rowContextEmbedding coordinates ledger)
    (fun context => (index rows context.1 (desired context.1) context.2 : ℝ)) (fun _ => 0) code

theorem index_read {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = indexReader rows coordinates ledger desired)
    (point : Point source) (entry : OpenResponsibilityAt N point.2.1) :
    indexFor coordinates ledger material point entry = index rows point (desired point) entry := by
  unfold indexFor
  rw [hm]
  dsimp only [indexReader]
  rw [(MotherArenaPrograms.rowContextEmbedding coordinates ledger).injective.extend_apply, Nat.floor_natCast]

theorem finite_checked {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = indexReader rows coordinates ledger desired)
    (point : Point source) (patch : FiniteGeneratedLedgerTerminalPatchAt rows point.2)
    (selected : desired point = some (.finite patch)) :
    TerminalIndexCheck rows coordinates ledger material point (terminalBody rows patch) := by
  intro entry
  refine ⟨patch.entryIndex entry, ⟨?_, patch.entry_sound entry⟩, ?_⟩
  · rw [index_read rows coordinates ledger desired hm, selected]
    rfl
  · intro chosen aligned
    apply Fin.ext
    exact aligned.1.trans (by rw [index_read rows coordinates ledger desired hm, selected]; rfl)

theorem finite_indices {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = indexReader rows coordinates ledger desired)
    (point : Point source) (patch : FiniteGeneratedLedgerTerminalPatchAt rows point.2)
    (selected : desired point = some (.finite patch)) :
    generatedTerminalIndices rows coordinates ledger material point (terminalBody rows patch)
      (finite_checked rows coordinates ledger desired hm point patch selected) = terminalIndices rows patch := by
  funext entry
  apply Subtype.ext
  apply Fin.ext
  exact (Classical.choose_spec (finite_checked rows coordinates ledger desired hm point patch selected entry)).1.1.trans
    (by rw [index_read rows coordinates ledger desired hm, selected]; rfl)

theorem recovered {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = indexReader rows coordinates ledger desired) (point : Point source) :
    terminalPatchOfKind? rows coordinates ledger material point (body rows point (desired point)) (kind rows point (desired point)) = desired point := by
  cases selected : desired point with
  | none => rfl
  | some patch =>
      cases patch with
      | finite patch =>
          simp only [body, kind, terminalPatchOfKind?]
          unfold finiteTerminal?
          rw [dif_pos (finite_checked rows coordinates ledger desired hm point patch selected)]
          have same := congrArg (terminalFinite rows (terminalBody rows patch))
            (finite_indices rows coordinates ledger desired hm point patch selected)
          exact congrArg (fun value => some (SourceGeneratedLedgerTerminalPatchAt.finite value))
            (same.trans (terminalFinite_original rows patch))
      | supportSettlement value =>
          exact congrArg (Option.map SourceGeneratedLedgerTerminalPatchAt.supportSettlement)
            (settlement_generated (point := point) value)

end TerminalRequestEncoding
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
