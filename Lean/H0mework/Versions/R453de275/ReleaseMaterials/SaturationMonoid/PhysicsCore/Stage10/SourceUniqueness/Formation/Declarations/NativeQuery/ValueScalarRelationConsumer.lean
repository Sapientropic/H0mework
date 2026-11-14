import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValueScalarRelationCoimage
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.ValueScalarCoimageConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RawGeneratedRoot.CofinalAction

noncomputable section

/-- The original duration inquiry consumes the actual relation's scalar
extension and the full coimage at its existing receipt. The old relation
completion, answer disposition, whole ledger and next remain the same visit. -/
theorem runtime_value_scalar_relation_original_consumer
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
    let compatible := ∃ factor : valueRelationCompletion sourceLaw occurrence →ₗ[MotherPhysicalSource.Carrier]
        valueWordCoimage sourceLaw occurrence,
      factor.comp (valueRelationProjection sourceLaw occurrence) =
        SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing sourceLaw occurrence)
    anchor.2 = occurrence ∧
    (oldCompletionToValueRelation sourceLaw occurrence).comp
        history.completionProjection =
      oldClosureValueProjection sourceLaw occurrence ∧
    (match (answer law key).2.1 with
      | .faithful _ _ _ => compatible
      | .unsound _ _ =>
          ∃ relation : history.relationClosure,
            valueRelationProjection sourceLaw occurrence
              (integerToValueWords sourceLaw
                (installedRelationAction sourceLaw occurrence relation).1) = 0 ∧
            SourceGeneratedScalarPerfectification.canonicalMap
                (valueWordPairing sourceLaw occurrence)
              (integerToValueWords sourceLaw
                (installedRelationAction sourceLaw occurrence relation).1) ≠ 0
      | .kernelResidual _ _ _ => compatible
      | .coverageResidual _ _ _ => compatible) ∧
    (answer law key).2.1 =
      ((faithfulLaw sourceLaw).faithfulAt occurrence).settleWithResidual ∧
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
  obtain ⟨same, _recovery, _pairing, _oldRecovery,
      residual, compiled, whole, next⟩ :=
    runtime_value_scalar_coimage_original_consumer law runtime query
      left right leftCoefficient rightCoefficient
  have faceEq :
      ((faithfulLaw sourceLaw).faithfulAt occurrence) =
        (MotherPhysicalSource.materialLaw law).faithfulAt anchor.2 := by
    have materialEq := MotherPhysicalSource.receipt_material_eq_original law
    cases materialEq
    cases same
    rfl
  have answerSame : (answer law ⟨anchor, query⟩).2.1 =
      ((faithfulLaw sourceLaw).faithfulAt occurrence).settleWithResidual := by
    change ((MotherPhysicalSource.materialLaw law).faithfulAt
      anchor.2).settleWithResidual = _
    rw [faceEq]
    rfl
  refine ⟨same, oldCompletion_value_relation_square sourceLaw occurrence,
    ?_, answerSame, compiled, whole, next⟩
  rw [answerSame]
  have generated := valueRelationCoimage_generated_disposition sourceLaw anchor.1
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
