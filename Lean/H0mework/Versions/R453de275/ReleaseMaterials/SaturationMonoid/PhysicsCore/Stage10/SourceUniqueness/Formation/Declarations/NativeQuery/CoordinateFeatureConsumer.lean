import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.CoordinateFeature

/-!
# The original duration inquiry consumes every coordinate feature

Each test/scale obtains its own source-generated complex Gram and coherent
readback; the complete family has exactly the kernel of the original whole
conductor evaluator. The source's full function pairing, answer residual,
whole ledger and canonical next remain at the same duration occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RawGeneratedRoot.CofinalAction
open SourceGeneratedIntegralCoherentCompletion
open SourceGeneratedComplexFeaturePerfectification
open scoped ComplexConjugate

noncomputable section

theorem runtime_all_coordinate_features_original_consumer
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (query : QueryAt law runtime.state)
    (left right : MotherPhysicalSource.Generator)
    (leftCoefficient rightCoefficient : ℤ) :
    let anchor := anchorAt law runtime.state
    let key : Key law := ⟨anchor, query⟩
    let sourceLaw := MotherPhysicalSource.receiptAction law
    (∀ word : MotherPhysicalSource.Generator →₀ ℤ,
      (∀ test : Test, ∀ scale : ℝ,
        coordinateFamily law anchor.2 test scale word = 0) ↔
        ((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation word = 0) ∧
    (∀ test : Test, ∀ scale : ℝ,
      ∀ first last : MotherPhysicalSource.Generator →₀ ℤ,
        gramEvaluation (complexifiedFeature (coordinateFeature law anchor.2 test scale))
            (1 ⊗ₜ[ℤ] first) (1 ⊗ₜ[ℤ] last) =
          inner ℂ
            ((((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation first) test scale)
            ((((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation last) test scale)) ∧
    (∀ test : Test, ∀ scale : ℝ,
      ∀ first last : MotherPhysicalSource.Generator →₀ ℤ,
        gramEvaluation (complexifiedFeature (coordinateFeature law anchor.2 test scale))
            (1 ⊗ₜ[ℤ] first) (1 ⊗ₜ[ℤ] last) -
          (valuePairing sourceLaw anchor.2 first last) test scale =
            (conj (((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation first
              test scale) -
              (((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation first
                test scale)) *
              (((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation last
                test scale)) ∧
    (∀ test : Test, ∀ scale : ℝ,
      ∀ word : MotherPhysicalSource.Generator →₀ ℤ,
        coherentCompletionRealization (coordinateFeature law anchor.2 test scale)
            (discreteToCoherentCompletion (coordinateFeature law anchor.2 test scale) word) =
          (((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation word) test scale) ∧
    (∀ word : MotherPhysicalSource.Generator →₀ ℤ,
      recoverWholeValue law anchor.2 word =
        ((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation word) ∧
    valuePairing sourceLaw anchor.2
        (Finsupp.single left leftCoefficient)
        (Finsupp.single right rightCoefficient) =
      (leftCoefficient • (MotherPhysicalSource.evaluatorAt law anchor.2).root left) *
        (rightCoefficient • (MotherPhysicalSource.evaluatorAt law anchor.2).root right) ∧
    (answer law key).2.1 =
      ((faithfulLaw sourceLaw).faithfulAt anchor.2).settleWithResidual ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.current.visit.current) ∧
    runtime.tick.nextCurrent =
      (process law).stateAt ((process law).successor runtime.state) := by
  obtain ⟨_installed, pairing, _materialInventory, _queryInventory,
      residual, _compiled, whole, next⟩ :=
    runtime_value_pairing_receipt_consumer law runtime query
      left right leftCoefficient rightCoefficient
  exact ⟨fun word => coordinateFamily_joint_kernel law
      (anchorAt law runtime.state).2 word,
    fun test scale first last => coordinate_generated_gram law
      (anchorAt law runtime.state).2 test scale first last,
    fun test scale first last => coordinate_hermitian_correction law
      (anchorAt law runtime.state).2 test scale first last,
    fun test scale word => coordinate_coherent_readback law
      (anchorAt law runtime.state).2 test scale word,
    fun word => recoverWholeValue_eq_actual law
      (anchorAt law runtime.state).2 word,
    pairing, residual, whole, next⟩

#print axioms runtime_all_coordinate_features_original_consumer

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
