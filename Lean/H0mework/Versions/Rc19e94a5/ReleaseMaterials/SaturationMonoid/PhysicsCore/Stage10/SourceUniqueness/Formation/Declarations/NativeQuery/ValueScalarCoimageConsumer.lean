import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValueScalarCoimage
import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.ValuePairingKernelConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RawGeneratedRoot.CofinalAction

noncomputable section

theorem runtime_value_scalar_coimage_original_consumer
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (query : QueryAt law runtime.state)
    (left right : MotherPhysicalSource.Generator)
    (leftCoefficient rightCoefficient : ℤ) :
    let anchor := anchorAt law runtime.state
    let key : Key law := ⟨anchor, query⟩
    let sourceLaw := MotherPhysicalSource.receiptAction law
    let occurrence := RawGeneratedRoot.emitted dynamics anchor.1
    anchor.2 = occurrence ∧
    (∀ word : ValueWords sourceLaw,
      valueWordCoimageRecovery sourceLaw occurrence
        (SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing sourceLaw occurrence) word) =
        valueWordEvaluation sourceLaw occurrence word) ∧
    (∀ first last : sourceLaw.Generator →₀ ℤ,
      valueWordPairing sourceLaw occurrence
        (integerToValueWords sourceLaw first)
        (integerToValueWords sourceLaw last) =
          valuePairing sourceLaw anchor.2 first last) ∧
    (∀ word : sourceLaw.Generator →₀ ℤ,
      valueWordCoimageRecovery sourceLaw occurrence
        (SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing sourceLaw occurrence)
          (integerToValueWords sourceLaw word)) =
        recoverWholeValue law anchor.2 word) ∧
    (answer law key).2.1 =
      ((faithfulLaw sourceLaw).faithfulAt anchor.2).settleWithResidual ∧
    HEq ((inquiryAt law runtime.state).compileInquiry query).answerReadout
      (answer law key) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.current.visit.current) ∧
    runtime.tick.nextCurrent =
      (process law).stateAt ((process law).successor runtime.state) := by
  dsimp only
  let anchor := anchorAt law runtime.state
  let sourceLaw := MotherPhysicalSource.receiptAction law
  let occurrence := RawGeneratedRoot.emitted dynamics anchor.1
  obtain ⟨_installed, _basis, _material, _query,
      residual, compiled, whole, next⟩ :=
    runtime_value_pairing_receipt_consumer law runtime query
      left right leftCoefficient rightCoefficient
  refine ⟨rfl, ?_, ?_, ?_, residual, compiled, whole, next⟩
  · intro word
    exact LinearMap.congr_fun
      (SourceGeneratedScalarPerfectification.canonicalFactor_comp
        (valueWordPairing sourceLaw occurrence)
        (valueWordEvaluation sourceLaw occurrence)
        (valueWordPairing_kernel_eq_evaluation_kernel sourceLaw occurrence).le) word
  · intro first last
    have same : anchor.2 = occurrence := rfl
    rw [same]
    exact valueWordPairing_integer_square sourceLaw occurrence first last
  · intro word
    exact (valueWordCoimageRecovery_integer_source sourceLaw occurrence word).trans
      (recoverWholeValue_eq_actual law anchor.2 word).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
