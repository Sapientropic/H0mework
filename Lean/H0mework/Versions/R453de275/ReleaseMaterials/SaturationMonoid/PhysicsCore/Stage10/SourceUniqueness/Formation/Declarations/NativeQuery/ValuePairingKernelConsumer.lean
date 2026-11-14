import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.CoordinateFeatureConsumer
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairingDescent

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RawGeneratedRoot.CofinalAction

noncomputable section

/-- The original function-valued pairing detects the complete evaluator's
zero fibre, while the original query, residual, ledger and next consume that
same duration receipt. No test or scale is chosen as source authority. -/
theorem runtime_value_pairing_exact_kernel_consumer
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (query : QueryAt law runtime.state)
    (left right : MotherPhysicalSource.Generator)
    (leftCoefficient rightCoefficient : ℤ) :
    let anchor := anchorAt law runtime.state
    let key : Key law := ⟨anchor, query⟩
    let sourceLaw := MotherPhysicalSource.receiptAction law
    let occurrence := RawGeneratedRoot.emitted dynamics anchor.1
    let history := (historyLaw sourceLaw).historyAt occurrence
    let canDescend := ∃ factor : history.CompletionCarrier →ₗ[ℤ]
        ((sourceLaw.Generator →₀ ℤ) →ₗ[ℤ] MotherPhysicalSource.Carrier),
      factor.comp history.completionProjection =
        valuePairingOnClosure sourceLaw occurrence
    (∀ word : MotherPhysicalSource.Generator →₀ ℤ,
      (valuePairing sourceLaw anchor.2 word word = 0 ↔
        recoverWholeValue law anchor.2 word = 0) ∧
      ((∀ right : MotherPhysicalSource.Generator →₀ ℤ,
        valuePairing sourceLaw anchor.2 word right = 0) ↔
          ∀ test : Test, ∀ scale : ℝ,
            coordinateFamily law anchor.2 test scale word = 0)) ∧
    LinearMap.ker (valuePairing sourceLaw anchor.2) =
      LinearMap.ker (((faithfulLaw sourceLaw).faithfulAt anchor.2).freeEvaluation) ∧
    (∀ first last : MotherPhysicalSource.Generator →₀ ℤ,
      valuePairing sourceLaw anchor.2 first =
          valuePairing sourceLaw anchor.2 last ↔
        recoverWholeValue law anchor.2 first =
          recoverWholeValue law anchor.2 last) ∧
    (∀ first last : MotherPhysicalSource.Generator →₀ ℤ,
      valuePairing sourceLaw anchor.2 first =
          valuePairing sourceLaw anchor.2 last ↔
        recoverWholeValue law anchor.2 first -
            recoverWholeValue law anchor.2 last ∈
          valuePairingAnnihilator sourceLaw anchor.2) ∧
    (∀ word : MotherPhysicalSource.Generator →₀ ℤ,
      recoverWholeValue law anchor.2 word ∈
          valuePairingAnnihilator sourceLaw anchor.2 ↔
        recoverWholeValue law anchor.2 word = 0) ∧
    (∀ word : MotherPhysicalSource.Generator →₀ ℤ,
      valuePairingRangeRecovery sourceLaw anchor.2
          ⟨valuePairing sourceLaw anchor.2 word, ⟨word, rfl⟩⟩ =
        recoverWholeValue law anchor.2 word) ∧
    anchor.2 = occurrence ∧
    ((∃ factor : ((historyLaw sourceLaw).historyAt occurrence).CompletionCarrier →ₗ[ℤ]
        ((sourceLaw.Generator →₀ ℤ) →ₗ[ℤ] MotherPhysicalSource.Carrier),
      factor.comp ((historyLaw sourceLaw).historyAt occurrence).completionProjection =
        valuePairingOnClosure sourceLaw occurrence) ↔
      ∃ factor : ((historyLaw sourceLaw).historyAt occurrence).CompletionCarrier →ₗ[ℤ]
          MotherPhysicalSource.Carrier,
        ∀ word : ((historyLaw sourceLaw).historyAt occurrence).generatorClosure,
          factor (((historyLaw sourceLaw).historyAt occurrence).completionProjection word) =
            ((faithfulLaw sourceLaw).faithfulAt occurrence).freeEvaluation word.1) ∧
    (match (answer law key).2.1 with
      | .faithful _ _ _ => canDescend
      | .unsound _ _ => ¬ canDescend
      | .kernelResidual _ _ _ => canDescend
      | .coverageResidual _ _ _ => canDescend) ∧
    (livingRoot law).toAuthoritativeRoot.source.projectionLaw.outcomeAt
        ((valuePairingInstallation law).embed PUnit.unit)
        runtime.emittedOccurrence =
      .inl ⟨PUnit.unit, valuePairing sourceLaw anchor.2⟩ ∧
    valuePairing sourceLaw anchor.2
        (Finsupp.single left leftCoefficient)
        (Finsupp.single right rightCoefficient) =
      (leftCoefficient • (MotherPhysicalSource.evaluatorAt law anchor.2).root left) *
        (rightCoefficient • (MotherPhysicalSource.evaluatorAt law anchor.2).root right) ∧
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
  let history := (historyLaw sourceLaw).historyAt occurrence
  obtain ⟨installed, basis, _materialInventory, _queryInventory,
      residual, compiled, whole, next⟩ :=
    runtime_value_pairing_receipt_consumer law runtime query
      left right leftCoefficient rightCoefficient
  refine ⟨?_, valuePairing_kernel_eq_freeEvaluation_kernel sourceLaw anchor.2,
    ?_, ?_, ?_, ?_, rfl,
    valuePairing_descent_iff_evaluator_descent sourceLaw anchor.1,
    ?_, installed, basis, residual, compiled, whole, next⟩
  · intro word
    constructor
    · rw [recoverWholeValue_eq_actual]
      exact valuePairing_self_zero_iff sourceLaw anchor.2 word
    · exact (valuePairing_left_kernel_iff sourceLaw anchor.2 word).trans
        (coordinateFamily_joint_kernel law anchor.2 word).symm
  · intro first last
    simpa only [recoverWholeValue_eq_actual] using
      (valuePairing_fibre_iff_freeEvaluation_fibre sourceLaw anchor.2 first last)
  · intro first last
    simpa only [recoverWholeValue_eq_actual] using
      (valuePairing_fibre_iff_annihilator sourceLaw anchor.2 first last)
  · intro word
    simpa only [recoverWholeValue_eq_actual] using
      (valuePairingAnnihilator_source_value_iff_zero sourceLaw anchor.2 word)
  · intro word
    exact (valuePairingRangeRecovery_actual sourceLaw anchor.2 word).trans
      (recoverWholeValue_eq_actual law anchor.2 word).symm
  · have generated := valuePairing_generated_disposition sourceLaw anchor.1
    have same : anchor.2 = occurrence := rfl
    have faceEq :
        ((faithfulLaw sourceLaw).faithfulAt occurrence) =
          (MotherPhysicalSource.materialLaw law).faithfulAt anchor.2 := by
      have materialEq := MotherPhysicalSource.receipt_material_eq_original law
      cases materialEq
      cases same
      rfl
    have answerEq : (answer law ⟨anchor, query⟩).2.1 =
        ((faithfulLaw sourceLaw).faithfulAt occurrence).settleWithResidual := by
      change ((MotherPhysicalSource.materialLaw law).faithfulAt
        anchor.2).settleWithResidual = _
      rw [faceEq]
      rfl
    rw [answerEq]
    dsimp only at generated
    dsimp only [anchor, sourceLaw] at generated
    cases outcome : ((faithfulLaw (MotherPhysicalSource.receiptAction law)).faithfulAt
      (RawGeneratedRoot.emitted MotherDurationExposure.dynamics
        (anchorAt law runtime.state).1)).settleWithResidual with
    | faithful _ _ _ => simpa only [dynamics, outcome] using generated
    | unsound _ _ => simpa only [dynamics, outcome] using generated
    | kernelResidual _ _ _ => simpa only [dynamics, outcome] using generated
    | coverageResidual _ _ _ => simpa only [dynamics, outcome] using generated

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
