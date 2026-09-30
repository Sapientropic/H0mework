import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Nodes.Source
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Operations.Consumer

/-! The complete node family is read from actual projections of a single
joined material. The original node origins supply their already formed
inquiry readers; all active/answered selectors run on the new projections. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroFamily
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

def readNode {node : RootInquiryProcessNode.{0}} (origin : MotherMacroNodes.Origin node)
    (material : MotherReceiptHigher.Material origin.rank) : Option RootInquiryProcessNode :=
  MotherMacroNodes.form origin.inquiry.readWorld (MotherMacroNodes.queryCode (MotherMacroNodes.headerOf node) origin.inquiry)
    (MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank () material)

theorem readNode_formed {node : RootInquiryProcessNode.{0}} (origin : MotherMacroNodes.Origin node) :
    readNode origin origin.material = some origin.read := by
  unfold readNode
  rw [origin.retained.2, origin.formed, origin.read_eq]

variable {Index Low : Type} (ranks : Index → Ordinal.{3}) (low : Low → Ordinal.{0})
    (readers : (index : Index) → MotherReceiptHigher.Material (ranks index) → Option RootInquiryProcessNode.{0})

/-- This family consumer receives already formed child readers. It reads
every index, including members absent from the active execution history. -/
def formNodes (material : MotherReceiptHigher.Material (MotherMaterialJoin.Mixed.sharedRank ranks low)) :
    Option (Index → RootInquiryProcessNode.{0}) :=
  if available : ∀ index,
      (readers index (MotherMaterialJoin.Mixed.restrictHigh ranks low index material)).isSome then
    some (fun index =>
      (readers index (MotherMaterialJoin.Mixed.restrictHigh ranks low index material)).get (available index))
  else none

theorem formNodes_formed
    (highMaterials : (index : Index) → MotherReceiptHigher.Material (ranks index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index))
    (nodes : Index → RootInquiryProcessNode.{0})
    (formed : ∀ index, readers index (highMaterials index) = some (nodes index)) :
    formNodes ranks low readers (MotherMaterialJoin.Mixed.combine ranks low highMaterials lowMaterials) = some nodes := by
  have available : ∀ index, (readers index
      (MotherMaterialJoin.Mixed.restrictHigh ranks low index
        (MotherMaterialJoin.Mixed.combine ranks low highMaterials lowMaterials))).isSome := by
    intro index
    rw [MotherMaterialJoin.Mixed.restrictHigh_combine, formed]
    rfl
  rw [formNodes, dif_pos available]
  apply congrArg some
  funext index
  apply Option.some.inj
  exact (Option.some_get (available index)).trans
    ((congrArg (readers index) (MotherMaterialJoin.Mixed.restrictHigh_combine ranks low highMaterials lowMaterials index)).trans
      (formed index))

private theorem reindexed_heq {First Last : Type} {Value : Type _} (same : First = Last) (read : Last → Value) :
    HEq (fun index : First => read (Equiv.cast same index)) read := by
  cases same
  rfl

theorem nodes_heq {rank : Ordinal.{0}} {first last : MotherArenaHigher.Material rank}
    (same : first = last) (nodes : MotherMacroOperations.Nodes last) :
    HEq (fun index : MotherMacroOperations.State first =>
      nodes (Equiv.cast (congrArg MotherMacroOperations.State same) index)) nodes :=
  reindexed_heq _ nodes

/-- Event addresses move only along the actual domain and node equalities;
the full state/query pair survives this dependent change of coordinates. -/
def transportEvent {rank : Ordinal.{0}} {first last : MotherArenaHigher.Material rank}
    (same : first = last) {actual : MotherMacroOperations.Nodes first}
    {original : MotherMacroOperations.Nodes last} (nodesSame : HEq actual original)
    (event : MotherMacroOperations.Event original ↪ MotherArenaHigher.Base rank) :
    MotherMacroOperations.Event actual ↪ MotherArenaHigher.Base rank := by
  cases same
  cases eq_of_heq nodesSame
  exact event

theorem operations_commute {rank : Ordinal.{0}} {first last : MotherArenaHigher.Material rank}
    (same : first = last) {actual : MotherMacroOperations.Nodes first}
    {original : MotherMacroOperations.Nodes last} (nodesSame : HEq actual original)
    (event : MotherMacroOperations.Event original ↪ MotherArenaHigher.Base rank)
    (material : MotherArenaHigher.Material rank) :
    MotherMacroOperations.formProcess first actual (transportEvent same nodesSame event) material =
      MotherMacroOperations.formProcess last original event material := by
  cases same
  cases eq_of_heq nodesSame
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroFamily
