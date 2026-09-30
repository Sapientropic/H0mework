import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.TerminalBody
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalFactory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source) (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N)
    (eventCode : ∀ context, RowEvents rows context ↪ MotherArenaHigher.Base rank)

def terminalSize (material : M) (point : Point source) : Nat :=
  Nat.floor ((MotherArenaHigher.read rank) material (coordinates.occurrence point) 0)

def TerminalBodyCheck (material : M) : Prop :=
  ∀ point, ∀ index : Fin (terminalSize coordinates material point), ∃! item : TerminalItem rows point,
    r2 material (1 + index.val) (coordinates.occurrence point) (terminalItemAddress rows ledger eventCode point item)

def generatedTerminalBodies (material : M) (checked : TerminalBodyCheck rows coordinates ledger eventCode material) :
    TerminalBodies rows := fun point => ⟨terminalSize coordinates material point, fun index => Classical.choose (checked point index)⟩

def indexFor (material : M) (point : Point source) (entry : OpenResponsibilityAt N point.2.1) : Nat :=
  Nat.floor ((MotherArenaHigher.read rank) material
    (MotherArenaPrograms.rowContextEmbedding coordinates ledger ⟨point, entry⟩) 0)

def TerminalIndexCheck (material : M) (point : Point source) (body : TerminalBody rows point) : Prop :=
  ∀ entry : OpenResponsibilityAt N point.2.1, ∃! index : Fin body.1,
    index.val = indexFor coordinates ledger material point entry ∧ (body.2 index).1 = entry

def generatedTerminalIndices (material : M) (point : Point source) (body : TerminalBody rows point)
    (checked : TerminalIndexCheck rows coordinates ledger material point body) : TerminalIndices rows body :=
  fun entry => ⟨Classical.choose (checked entry), (Classical.choose_spec (checked entry)).1.2⟩

def finiteTerminal? (material : M) (point : Point source) (body : TerminalBody rows point) :
    Option (FiniteGeneratedLedgerTerminalPatchAt rows point.2) :=
  if checked : TerminalIndexCheck rows coordinates ledger material point body then
    some (terminalFinite rows body (generatedTerminalIndices rows coordinates ledger material point body checked))
  else none

def terminalPatchOfKind? (material : M) (point : Point source) (body : TerminalBody rows point) :
    Nat → Option (SourceGeneratedLedgerTerminalPatchAt rows point.2)
  | 0 => (finiteTerminal? rows coordinates ledger material point body).map SourceGeneratedLedgerTerminalPatchAt.finite
  | 1 => (rows.generateSupportSettlement? point.2).map SourceGeneratedLedgerTerminalPatchAt.supportSettlement
  | _ => none

def formAllRequestParts (parent bodyMaterial indexMaterial kindMaterial : M) : Option AllRequestValue :=
  (formPatchRequests parent).pbind (fun value formed =>
    let programme := requestProgramme value
    let programmeFormed := requests_programmes_formed parent value formed
    let coordinates := sourceCoordinates (requestParent parent) programme programmeFormed
    let ledger := ledgerCoordinates (requestParent parent) programme programmeFormed
    let eventCode := terminalAddresses (requestParent parent) programme programmeFormed
    if checked : TerminalBodyCheck programme.2.2.1 coordinates ledger eventCode bodyMaterial then
      let bodies := generatedTerminalBodies programme.2.2.1 coordinates ledger eventCode bodyMaterial checked
      some ⟨value, fun point => terminalPatchOfKind? programme.2.2.1 coordinates ledger indexMaterial point (bodies point)
        (Nat.floor ((MotherArenaHigher.read rank) kindMaterial (coordinates.occurrence point) 0))⟩
    else none)

/-- All continuing and terminal patch requests share their original source
programmes. Finite terminal rows are sealed by the original generator;
support settlement comes only from the source-selected occurrence. -/
def formAllRequests (material : M) : Option AllRequestValue :=
  let first := (MotherArenaHigher.split rank) material
  let second := (MotherArenaHigher.split rank) first.2
  let third := (MotherArenaHigher.split rank) second.2
  formAllRequestParts first.1 second.1 third.1 third.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
