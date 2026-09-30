import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Anchors

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open MotherNetworkFactory ResponsibilityLifecycle
noncomputable section

/-- The complete original vocabulary reaches native registered source
anchors and obstruction-generated demands. It preserves every evidence
family; split/merge source certifications consume these materials next. -/
theorem formed_vocabulary_consumes_original_registration (R : RestructuringVocabulary.{0})
    (sortCode : (Σ index, sortsOf R.base index) ↪ B) (familyCode : FamilyTotal (familiesOf R) ↪ B) :
    ∃ material base families : M,
      ∃ ops : Operations (formedSorts base) (formedFamilies base families),
      ∃ sortMap : (index : Fin 12) → sortsOf R.base index ≃ formedSorts base index,
      ∃ familyMap : FamilyMap sortMap (familiesOf R) (formedFamilies base families),
      ∃ p : OperationsAcross sortMap familyMap (operationsOf R) ops,
        let generated := restructuring (formedSorts base) (formedFamilies base families) ops
        formVocabulary material = some generated ∧
        (∀ source, anchorEquiv sortMap familyMap p (R.base.sourceAnchor source) = generated.base.sourceAnchor (sortMap 0 source)) ∧
        (∀ demand : ProducerDemand R.base,
          (demandEquiv sortMap familyMap (original := operationsOf R) (output := ops) demand).content = sortMap 1 demand.content ∧
          (demandEquiv sortMap familyMap (original := operationsOf R) (output := ops) demand).residual = sortMap 2 demand.residual) := by
  obtain ⟨material, base, families, ops, sortMap, familyMap, p, formed⟩ := every_original_vocabulary R sortCode familyCode
  exact ⟨material, base, families, ops, sortMap, familyMap, p, formed,
    sourceAnchor_mapped sortMap familyMap p,
    fun demand => ⟨demand_content sortMap familyMap p demand, demand_residual sortMap familyMap p demand⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
