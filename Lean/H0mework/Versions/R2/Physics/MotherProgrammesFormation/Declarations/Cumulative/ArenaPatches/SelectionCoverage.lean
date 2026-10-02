import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.Selectors
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.SelectionCoverage

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

namespace SelectionEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (inventories : FiniteSection rows)

def destinationKey : (Σ context : RemainderContext source, OpenResponsibilityAt N context.1.2.1) ↪ B where
  toFun := fun ⟨context, entry⟩ => (MotherArenaHigher.pair rank) (MotherArenaExact.remainderContextEmbedding coordinates ledger context, ledger.entry context.1.2.1 entry)
  inj' := by
    rintro ⟨context, entry⟩ ⟨other, value⟩ same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    have contextEq := (MotherArenaExact.remainderContextEmbedding coordinates ledger).injective (congrArg Prod.fst pairEq)
    cases contextEq
    have entryEq := (ledger.entry context.1.2.1).injective (congrArg Prod.snd pairEq)
    cases entryEq
    rfl

def originKey : (Σ context : RemainderContext source, OpenResponsibilityAt N context.2) ↪ B where
  toFun := fun ⟨context, entry⟩ => (MotherArenaHigher.pair rank) (MotherArenaExact.remainderContextEmbedding coordinates ledger context, ledger.entry context.2 entry)
  inj' := by
    rintro ⟨context, entry⟩ ⟨other, value⟩ same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    have contextEq := (MotherArenaExact.remainderContextEmbedding coordinates ledger).injective (congrArg Prod.fst pairEq)
    cases contextEq
    have entryEq := (ledger.entry context.2).injective (congrArg Prod.snd pairEq)
    cases entryEq
    rfl

variable (desired : ∀ context, LedgerTransportedRemainderCoverageAt (inventories context))

def reader (code : B) (tag : Nat) : ℝ :=
  if tag = 0 then Function.extend (destinationKey coordinates ledger)
    (fun query => (indexCode ((desired query.1).destinationIndex query.2) : ℝ)) (fun _ => 0) code
  else Function.extend (originKey coordinates ledger)
    (fun query => (indexCode ((desired query.1).originIndex query.2) : ℝ)) (fun _ => 0) code

theorem destination_parse {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger inventories desired)
    (context : RemainderContext source) (entry : OpenResponsibilityAt N context.1.2.1) :
    destinationSelection? rows coordinates ledger inventories material context entry = some ((desired context).destinationIndex entry) := by
  unfold destinationSelection? selectionCode
  rw [hm]
  simp only [reader]
  change decodeIndex _ _ _ (Nat.floor
    (Function.extend (destinationKey coordinates ledger)
      (fun query => (indexCode ((desired query.1).destinationIndex query.2) : ℝ)) (fun _ => 0)
      (destinationKey coordinates ledger ⟨context, entry⟩))) = _
  rw [(destinationKey coordinates ledger).injective.extend_apply, Nat.floor_natCast]
  exact decode_indexCode _ _ _ _

theorem origin_parse {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger inventories desired)
    (context : RemainderContext source) (entry : OpenResponsibilityAt N context.2) :
    originSelection? rows coordinates ledger inventories material context entry = some ((desired context).originIndex entry) := by
  unfold originSelection? selectionCode
  rw [hm]
  simp only [reader, Nat.one_ne_zero, if_false]
  change decodeIndex _ _ _ (Nat.floor
    (Function.extend (originKey coordinates ledger)
      (fun query => (indexCode ((desired query.1).originIndex query.2) : ℝ)) (fun _ => 0)
      (originKey coordinates ledger ⟨context, entry⟩))) = _
  rw [(originKey coordinates ledger).injective.extend_apply, Nat.floor_natCast]
  exact decode_indexCode _ _ _ _

theorem checked {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger inventories desired) :
    SelectionCheck rows coordinates ledger inventories material where
  destination := fun context entry => by
    rw [destination_parse rows coordinates ledger inventories desired hm context entry]
    rfl
  origin := fun context entry => by
    rw [origin_parse rows coordinates ledger inventories desired hm context entry]
    rfl

theorem destination_eq {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger inventories desired)
    (context : RemainderContext source) (entry : OpenResponsibilityAt N context.1.2.1) :
    (transportedCoverage rows coordinates ledger inventories material (checked rows coordinates ledger inventories desired hm) context).destinationIndex entry =
      (desired context).destinationIndex entry :=
  Option.some.inj ((Option.some_get _).trans (destination_parse rows coordinates ledger inventories desired hm context entry))

theorem origin_eq {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger inventories desired)
    (context : RemainderContext source) (entry : OpenResponsibilityAt N context.2) :
    (transportedCoverage rows coordinates ledger inventories material (checked rows coordinates ledger inventories desired hm) context).originIndex entry =
      (desired context).originIndex entry :=
  Option.some.inj ((Option.some_get _).trans (origin_parse rows coordinates ledger inventories desired hm context entry))

theorem coverage_eq {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger inventories desired)
    (context : RemainderContext source) :
    transportedCoverage rows coordinates ledger inventories material (checked rows coordinates ledger inventories desired hm) context = desired context := by
  have hd := funext (destination_eq rows coordinates ledger inventories desired hm context)
  have ho := funext (origin_eq rows coordinates ledger inventories desired hm context)
  exact congrArg₂ (fun destinationIndex originIndex =>
    ({ destinationIndex, originIndex } : LedgerTransportedRemainderCoverageAt (inventories context))) hd ho

end SelectionEncoding
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
