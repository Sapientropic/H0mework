import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Fibers
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Higher

/-! One extended material retains an entire existing rank material and the
complete high-universe receipt family. The old material occurs only in
coverage; both readouts consume the same actual packed material. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptHigher
open scoped Classical
noncomputable section
universe u

def includeArena (oldRank : Ordinal.{0}) (rank : Ordinal.{u})
    (address : MotherArenaHigher.Base oldRank ↪ Base rank)
    (material : MotherArenaHigher.Material oldRank) : Material rank :=
  (readEquiv rank).symm
    (Function.extend address (MotherArenaHigher.read oldRank material) (fun _ => 0))

theorem includeArena_read (oldRank : Ordinal.{0}) (rank : Ordinal.{u})
    (address : MotherArenaHigher.Base oldRank ↪ Base rank)
    (material : MotherArenaHigher.Material oldRank) (base : MotherArenaHigher.Base oldRank) :
    read rank (includeArena oldRank rank address material) (address base) =
      MotherArenaHigher.read oldRank material base := by
  change readEquiv rank ((readEquiv rank).symm _) (address base) = _
  rw [Equiv.apply_symm_apply]
  exact address.injective.extend_apply _ _ base

def restrictArena (oldRank : Ordinal.{0}) (rank : Ordinal.{u})
    (address : MotherArenaHigher.Base oldRank ↪ Base rank) (material : Material rank) :
    MotherArenaHigher.Material oldRank :=
  (MotherArenaHigher.readEquiv oldRank).symm (fun base => read rank material (address base))

theorem restrictArena_read (oldRank : Ordinal.{0}) (rank : Ordinal.{u})
    (address : MotherArenaHigher.Base oldRank ↪ Base rank) (material : Material rank) :
    MotherArenaHigher.read oldRank (restrictArena oldRank rank address material) =
      fun base => read rank material (address base) :=
  (MotherArenaHigher.readEquiv oldRank).apply_symm_apply _

theorem restrict_includeArena (oldRank : Ordinal.{0}) (rank : Ordinal.{u})
    (address : MotherArenaHigher.Base oldRank ↪ Base rank)
    (material : MotherArenaHigher.Material oldRank) :
    restrictArena oldRank rank address (includeArena oldRank rank address material) = material := by
  apply (MotherArenaHigher.read_uniformEmbedding oldRank).injective
  rw [restrictArena_read]
  funext base
  exact includeArena_read oldRank rank address material base

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptHigher

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
open scoped Classical
noncomputable section

def formJoint {rank : Ordinal.{3}} (material : MotherReceiptHigher.Material rank) : Option (Value rank) :=
  form (MotherReceiptHigher.split rank material).2

def readArena {rank : Ordinal.{3}} (oldRank : Ordinal.{0})
    (address : MotherArenaHigher.Base oldRank ↪ MotherReceiptHigher.Base rank)
    (material : MotherReceiptHigher.Material rank) : MotherArenaHigher.Material oldRank :=
  MotherReceiptHigher.restrictArena oldRank rank address (MotherReceiptHigher.split rank material).1

theorem every_payload_and_arena (oldRank : Ordinal.{0}) (oldMaterial : MotherArenaHigher.Material oldRank)
    (I : Type) (F : I → Type 3) (selected : Sigma F) :
    ∃ rank : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material rank,
      ∃ value : Value rank, ∃ originalAddress : MotherArenaHigher.Base oldRank ↪ MotherReceiptHigher.Base rank,
        formJoint material = some value ∧ readArena oldRank originalAddress material = oldMaterial ∧
        Nonempty (Presentation I F selected value) ∧
        Function.LeftInverse (MotherReceiptHigher.restrictArena oldRank rank originalAddress)
          (MotherReceiptHigher.includeArena oldRank rank originalAddress) := by
  let Total := (ULift.{3, 0} I ⊕ Sigma F) ⊕ ULift.{3, 0} (MotherArenaHigher.Base oldRank)
  let rank := MotherReceiptHigher.carrierRank Total
  let shared := MotherReceiptHigher.carrierAddress Total
  let indexCode : I ↪ MotherReceiptHigher.Base rank :=
    ⟨fun value => shared (.inl (.inl (ULift.up value))), fun _ _ same =>
      congrArg ULift.down (Sum.inl.inj (Sum.inl.inj (shared.injective same)))⟩
  let valueCode : (Sigma F) ↪ MotherReceiptHigher.Base rank :=
    ⟨fun value => shared (.inl (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inl.inj (shared.injective same))⟩
  let originalAddress : MotherArenaHigher.Base oldRank ↪ MotherReceiptHigher.Base rank :=
    ⟨fun value => shared (.inr (ULift.up value)), fun _ _ same =>
      congrArg ULift.down (Sum.inr.inj (shared.injective same))⟩
  obtain ⟨receiptMaterial, value, formed, presentation⟩ := every_payload_at I F selected indexCode valueCode
  let material := MotherReceiptHigher.pack rank
    (MotherReceiptHigher.includeArena oldRank rank originalAddress oldMaterial, receiptMaterial)
  refine ⟨rank, material, value, originalAddress, ?_, ?_, presentation,
    MotherReceiptHigher.restrict_includeArena oldRank rank originalAddress⟩
  · simpa only [formJoint, material, MotherReceiptHigher.split_pack] using formed
  · simp only [readArena, material, MotherReceiptHigher.split_pack, MotherReceiptHigher.restrict_includeArena]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
