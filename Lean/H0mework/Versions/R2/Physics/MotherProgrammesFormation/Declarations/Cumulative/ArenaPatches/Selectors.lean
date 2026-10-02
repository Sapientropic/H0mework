import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Selectors

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
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (inventories : FiniteSection rows)

def selectionCode (material : M) (tag : Nat) (context : RemainderContext source) (entryAddress : B) : Nat :=
  Nat.floor ((MotherArenaHigher.read rank) material
    ((MotherArenaHigher.pair rank) (MotherArenaExact.remainderContextEmbedding coordinates ledger context, entryAddress)) tag)

def destinationSelection? (material : M) (context : RemainderContext source) (entry : OpenResponsibilityAt N context.1.2.1) :=
  decodeIndex (inventories context).size (inventories context).sourceEntryAt entry
    (selectionCode coordinates ledger material 0 context (ledger.entry context.1.2.1 entry))

def originSelection? (material : M) (context : RemainderContext source) (entry : OpenResponsibilityAt N context.2) :=
  decodeIndex (inventories context).size (inventories context).targetEntryAt entry
    (selectionCode coordinates ledger material 1 context (ledger.entry context.2 entry))

structure SelectionCheck (material : M) : Prop where
  destination : ∀ context entry, (destinationSelection? rows coordinates ledger inventories material context entry).isSome = true
  origin : ∀ context entry, (originSelection? rows coordinates ledger inventories material context entry).isSome = true

def transportedCoverage (material : M) (checked : SelectionCheck rows coordinates ledger inventories material)
    (context : RemainderContext source) : LedgerTransportedRemainderCoverageAt (inventories context) where
  destinationIndex := fun entry => (destinationSelection? rows coordinates ledger inventories material context entry).get
    (checked.destination context entry)
  originIndex := fun entry => (originSelection? rows coordinates ledger inventories material context entry).get
    (checked.origin context entry)

def identityCoverage (material : M) (checked : SelectionCheck rows coordinates ledger inventories material)
    (point : Point source) : LedgerIdentityRemainderCoverageAt (inventories (point, point.2.1)) where
  destinationIndex := (transportedCoverage rows coordinates ledger inventories material checked (point, point.2.1)).destinationIndex
  originIndex := (transportedCoverage rows coordinates ledger inventories material checked (point, point.2.1)).originIndex

def completeCoverage? (material : M) (checked : SelectionCheck rows coordinates ledger inventories material)
    (context : RemainderContext source) : Option (LedgerCompleteFiniteCoverageAt (inventories context)) :=
  let selected := transportedCoverage rows coordinates ledger inventories material checked context
  if total : (∀ entry, (selected.destinationIndex entry).isSome = true) ∧ (∀ entry, (selected.originIndex entry).isSome = true) then
    some {
      destinationIndex := fun entry => ((selected.destinationIndex entry).get (total.1 entry)).val
      originIndex := fun entry => ((selected.originIndex entry).get (total.2 entry)).val
      destination_sound := fun entry => ((selected.destinationIndex entry).get (total.1 entry)).property
      origin_sound := fun entry => ((selected.originIndex entry).get (total.2 entry)).property }
  else none

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
