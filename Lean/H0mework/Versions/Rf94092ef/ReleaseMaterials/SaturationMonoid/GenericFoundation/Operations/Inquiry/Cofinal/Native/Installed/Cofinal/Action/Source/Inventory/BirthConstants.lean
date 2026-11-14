import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.ConstantTransport

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction

open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
namespace CT
export OriginalSourceConstantTransport (constant_update additionCertificate effectValueMap)
end CT

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
attribute [local instance] familyGroups
variable (factory : SF.Factory W X s)
variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))

/-- The old constants, the actual birth effect and its addition relations produce the full table. -/
def birthConstantTable :
    Formal ℤ (L.Value W packet.1) X s →ₗ[ℤ] (L.Value W (packet.1+1) s →₀ ℤ) :=
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selected factory packet).activeEnvironment
  let delta := birthIncrement factory packet
  ((valueMap (R := ℤ) before + CT.effectValueMap before delta) -
    (ScalarRelationPresentation.relationMap (R := ℤ) (L.Value W (packet.1+1) s)).comp
      (CT.additionCertificate before delta)).comp (sourceWordAction packet)

theorem birth_constant_table_decoded (word : Formal ℤ (L.Value W packet.1) X s) :
    birthConstantTable factory packet word =
      valueMap (R := ℤ) (Value := L.Value W (packet.1+1)) (Var := packet.2.2.1.LowVar)
        (sourceBorn factory packet).2.1.1.activeEnvironment (sourceWordAction packet word) := by
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selected factory packet).activeEnvironment
  let delta := birthIncrement factory packet
  let acted := sourceWordAction packet word
  let next := valueMap (R := ℤ) (before+delta) acted
  let old := valueMap (R := ℤ) before acted
  let effect := CT.effectValueMap before delta acted
  let correction := ScalarRelationPresentation.relationMap (R := ℤ) (L.Value W (packet.1+1) s)
    (CT.additionCertificate before delta acted)
  have equation : old+effect-next = correction :=
    LinearMap.congr_fun (CT.constant_update (sort := s) before delta) acted
  have readback : old+effect-correction = next :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp equation).trans (add_comm _ _))
  exact readback.trans (congrArg (fun environment => valueMap (R := ℤ) environment acted)
    (birth_decoded_environment factory packet))

theorem birth_constant_table_value (word : Formal ℤ (L.Value W packet.1) X s) :
    ScalarRelationPresentation.freeEvaluation (R := ℤ) (L.Value W (packet.1+1) s)
      (birthConstantTable factory packet word) =
      (birthWordInventory factory packet word).1+(birthWordInventory factory packet word).2 := by
  rw [birth_constant_table_decoded]
  exact (LinearMap.congr_fun (valueMap_evaluation (R := ℤ)
    (sourceBorn factory packet).2.1.1.activeEnvironment) (sourceWordAction packet word)).trans
    (birth_word_reads_written factory packet word).symm

end ActualCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
