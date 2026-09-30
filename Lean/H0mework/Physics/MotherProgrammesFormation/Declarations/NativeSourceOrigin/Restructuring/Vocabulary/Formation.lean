import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Transport

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open MotherNetworkFactory ResponsibilityLifecycle
noncomputable section

/-- The source-only vocabulary factory consumes all twelve carriers,
all thirty-one dependent evidence families and every original operation. -/
theorem every_original_vocabulary (R : RestructuringVocabulary.{0})
    (sortCode : (Σ index, sortsOf R.base index) ↪ B) (familyCode : FamilyTotal (familiesOf R) ↪ B) :
    ∃ material base families : M,
      ∃ ops : Operations (formedSorts base) (formedFamilies base families),
      ∃ sortMap : (index : Fin 12) → sortsOf R.base index ≃ formedSorts base index,
      ∃ familyMap : FamilyMap sortMap (familiesOf R) (formedFamilies base families),
        OperationsAcross sortMap familyMap (operationsOf R) ops ∧
        formVocabulary material = some (restructuring (formedSorts base) (formedFamilies base families) ops) := by
  obtain ⟨base, ⟨sortMap⟩⟩ := every_sorts (sortsOf R.base) sortCode
  let transported := transportFamilies sortMap (familiesOf R)
  let code := (familyTotalEquiv sortMap (familiesOf R)).symm.toEmbedding.trans familyCode
  obtain ⟨families, ⟨formedMembers⟩⟩ := every_families base transported code
  let familyMap : FamilyMap sortMap (familiesOf R) (formedFamilies base families) :=
    fun index args => (transportedMember sortMap (familiesOf R) index args).trans
      (formedMembers index (argsEquiv sortMap (signature index) args))
  let ops := transportOperations sortMap familyMap (operationsOf R)
  obtain ⟨operationMaterial, formed⟩ := every_operations base families ops
  refine ⟨MotherHigherLawValue.pack (base, MotherHigherLawValue.pack (families, operationMaterial)),
    base, families, ops, sortMap, familyMap, transported_operations sortMap familyMap (operationsOf R), ?_⟩
  simpa only [formVocabulary, MotherHigherLawValue.split_pack] using formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
