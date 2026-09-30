import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalCoverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

namespace TerminalRequestEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source)

def body (point : Point source) (request : Option (SourceGeneratedLedgerTerminalPatchAt rows point.2)) : TerminalBody rows point :=
  match request with
  | some (.finite patch) => terminalBody rows patch
  | _ => ⟨0, fun index => index.elim0⟩

def index (point : Point source) (request : Option (SourceGeneratedLedgerTerminalPatchAt rows point.2))
    (entry : OpenResponsibilityAt N point.2.1) : Nat :=
  match request with
  | some (.finite patch) => (patch.entryIndex entry).val
  | _ => 0

def kind (point : Point source) (request : Option (SourceGeneratedLedgerTerminalPatchAt rows point.2)) : Nat :=
  match request with
  | some (.finite _) => 0
  | some (.supportSettlement _) => 1
  | none => 2

variable (coordinates : Coordinates source) (ledger : LedgerCoordinates N)
    (desired : (point : Point source) → Option (SourceGeneratedLedgerTerminalPatchAt rows point.2))

def indexReader (code : B) (_tag : Nat) : ℝ :=
  Function.extend (rowContextEmbedding coordinates ledger)
    (fun context => (index rows context.1 (desired context.1) context.2 : ℝ)) (fun _ => 0) code

theorem index_read {material : M}
    (hm : MotherHigherLawFormation.read material = indexReader rows coordinates ledger desired)
    (point : Point source) (entry : OpenResponsibilityAt N point.2.1) :
    indexFor coordinates ledger material point entry = index rows point (desired point) entry := by
  unfold indexFor
  rw [hm]
  dsimp only [indexReader]
  rw [(rowContextEmbedding coordinates ledger).injective.extend_apply, Nat.floor_natCast]

theorem finite_checked {material : M}
    (hm : MotherHigherLawFormation.read material = indexReader rows coordinates ledger desired)
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

theorem finite_indices {material : M}
    (hm : MotherHigherLawFormation.read material = indexReader rows coordinates ledger desired)
    (point : Point source) (patch : FiniteGeneratedLedgerTerminalPatchAt rows point.2)
    (selected : desired point = some (.finite patch)) :
    generatedTerminalIndices rows coordinates ledger material point (terminalBody rows patch)
      (finite_checked rows coordinates ledger desired hm point patch selected) = terminalIndices rows patch := by
  funext entry
  apply Subtype.ext
  apply Fin.ext
  exact (Classical.choose_spec (finite_checked rows coordinates ledger desired hm point patch selected entry)).1.1.trans
    (by rw [index_read rows coordinates ledger desired hm, selected]; rfl)

theorem recovered {material : M}
    (hm : MotherHigherLawFormation.read material = indexReader rows coordinates ledger desired) (point : Point source) :
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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
