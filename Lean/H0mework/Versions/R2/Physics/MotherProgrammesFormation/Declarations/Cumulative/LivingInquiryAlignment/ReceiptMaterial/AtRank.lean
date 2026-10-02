import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Joint

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
open scoped Classical
noncomputable section

/-- Shared-rank form used by complete query sections: the outer coverage
pays all fibres at once, and each field uses this same actual reader. -/
theorem payload_and_arena_at {rank : Ordinal.{3}} (oldRank : Ordinal.{0})
    (oldMaterial : MotherArenaHigher.Material oldRank) (I : Type) (F : I → Type 3) (selected : Sigma F)
    (indexCode : I ↪ MotherReceiptHigher.Base rank)
    (valueCode : (Sigma F) ↪ MotherReceiptHigher.Base rank)
    (originalAddress : MotherArenaHigher.Base oldRank ↪ MotherReceiptHigher.Base rank) :
    ∃ material : MotherReceiptHigher.Material rank, ∃ value : Value rank,
      formJoint material = some value ∧ readArena oldRank originalAddress material = oldMaterial ∧
      Nonempty (Presentation I F selected value) := by
  obtain ⟨receiptMaterial, value, formed, presentation⟩ := every_payload_at I F selected indexCode valueCode
  let material := MotherReceiptHigher.pack rank
    (MotherReceiptHigher.includeArena oldRank rank originalAddress oldMaterial, receiptMaterial)
  refine ⟨material, value, ?_, ?_, presentation⟩
  · simpa only [formJoint, material, MotherReceiptHigher.split_pack] using formed
  · simp only [readArena, material, MotherReceiptHigher.split_pack, MotherReceiptHigher.restrict_includeArena]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
