import H0mework.Physics.MotherProgrammesFormation.Declarations.PhysicalSource.Coverage

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CofinalHistorySettlementFace CofinalFaithfulSettlementFace MotherClosedRestrictions

noncomputable section

/-- The original constructors and all their dependent classification outputs
are formed uniformly over the full raw current and positive-duration event fibre. -/
theorem every_declaration_consumed
    (roots : ExposureFamily) (rootExact : RootExact roots)
    (seeds : SeedFamily) (continuations : ContinuationFamily) (evaluators : EvaluatorFamily) :
    let actual : SourceNativeCofinalFaithfulMaterialLaw ledgerSource Carrier :=
      .create (.create Generator roots rootExact seeds continuations) evaluators
    ∃ law : MotherPhysicalLaws.Law, materialLaw law = actual ∧
      (∀ {current : Current} (occurrence : OccurrenceAt current),
        HEq ((materialLaw law).toProjectionLaw.outcomeAt PUnit.unit occurrence)
          (actual.toProjectionLaw.outcomeAt PUnit.unit occurrence) ∧
        HEq ((materialLaw law).faithfulAt occurrence).settle (actual.faithfulAt occurrence).settle ∧
        HEq ((materialLaw law).faithfulAt occurrence).settleWithResidual
          (actual.faithfulAt occurrence).settleWithResidual) ∧
      ∀ input : Input, firstStream (MotherPhysicalLaws.eval law (inputAt input)) = sideSamples input.2 := by
  obtain ⟨law, rootsFormed, seedsFormed, continuationsFormed, evaluatorsFormed, keyed⟩ :=
    every_fields roots rootExact seeds continuations evaluators
  dsimp only
  have declared : materialLaw law = SourceNativeCofinalFaithfulMaterialLaw.create
      (SourceNativeCofinalHistoryMaterialLaw.create Generator roots rootExact seeds continuations)
      evaluators := by
    let build (rootData : {roots : ExposureFamily // RootExact roots}) (seeds : SeedFamily)
        (continuations : ContinuationFamily) (evaluators : EvaluatorFamily) :
        SourceNativeCofinalFaithfulMaterialLaw ledgerSource Carrier :=
      .create (.create Generator rootData.val rootData.property seeds continuations) evaluators
    have rootSame : (⟨@rootExposureAt law, rootExposure_root law⟩ : {roots : ExposureFamily // RootExact roots}) =
        ⟨@roots, rootExact⟩ := Subtype.ext rootsFormed
    change build ⟨@rootExposureAt law, rootExposure_root law⟩ (@seedAt law) (@continuationAt law) (@evaluatorAt law) =
      build ⟨@roots, rootExact⟩ (@seeds) (@continuations) (@evaluators)
    rw [rootSame, seedsFormed, continuationsFormed, evaluatorsFormed]
  refine ⟨law, declared, ?_, keyed⟩
  intro current occurrence
  rw [declared]
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource
