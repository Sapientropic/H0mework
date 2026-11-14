import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.CanonicalRuntime

/-!
# The original duration inquiry consumes its installed cochain action

The query source now inherits its old material and full answer while adjoining
the differential computed from the same positive-duration receipt. The
canonical runtime reads that differential, the original answer residual, the
whole ledger and the generated next at one exact duration occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RawGeneratedRoot.CofinalAction
open CofinalRelationGeneratedComplex

noncomputable section

theorem runtime_cochain_receipt_inquiry_consumer
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (query : QueryAt law runtime.state)
    (generator : MotherPhysicalSource.Generator) (coefficient : ℤ) :
    let anchor := anchorAt law runtime.state
    let key : Key law := ⟨anchor, query⟩
    let sourceLaw := MotherPhysicalSource.receiptAction law
    let history := (historyLaw sourceLaw).historyAt anchor.2
    let face := (faithfulLaw sourceLaw).faithfulAt anchor.2
    (livingRoot law).toAuthoritativeRoot.source.projectionLaw.outcomeAt
        ((cochainInstallation law).embed PUnit.unit) runtime.emittedOccurrence =
      .inl ⟨PUnit.unit, installedRelationAction sourceLaw anchor.2⟩ ∧
    (∀ projection : (materialSource law).projectionLaw.Projection,
      HEq ((declarationSource law).projectionLaw.outcomeAt
        ((historyInstallation law).embed projection) anchor.2)
        ((materialSource law).projectionLaw.outcomeAt projection anchor.2)) ∧
    (∀ projection : (projectionLaw law).Projection,
      HEq ((declarationSource law).projectionLaw.outcomeAt
        ((queryInstallation law).embed projection) anchor.2)
        ((projectionLaw law).outcomeAt projection anchor.2)) ∧
    ((natComplex history).d 0 1).hom = installedRelationAction sourceLaw anchor.2 ∧
    ((∀ relation : history.relationClosure,
      face.freeEvaluation (installedRelationAction sourceLaw anchor.2 relation).1 = 0) ↔
      ∃ factor : history.CompletionCarrier →ₗ[ℤ] MotherPhysicalSource.Carrier,
        ∀ value : history.generatorClosure,
          factor (history.completionProjection value) =
            face.freeEvaluation value.1) ∧
    (answer law key).2.1 = face.settleWithResidual ∧
    HEq ((inquiryAt law runtime.state).compileInquiry query).answerReadout
      (answer law key) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.current.visit.current) ∧
    runtime.tick.nextCurrent =
      (process law).stateAt ((process law).successor runtime.state) := by
  have cochain := generated_cochain_kernel_exact
    (MotherPhysicalSource.receiptAction law) runtime.current.visit.current
  have descent := generated_differential_descent_iff
    (MotherPhysicalSource.receiptAction law) runtime.current.visit.current
  obtain ⟨_equation, _readout, residual, compiled, whole, _row, next, _oldNext⟩ :=
    runtime_receipt_inquiry_consumer law runtime query generator coefficient
  exact ⟨rfl,
    fun projection => (historyInstallation law).outcome_heq _ projection,
    fun projection => (queryInstallation law).outcome_heq _ projection,
    cochain.1, descent, residual, compiled, whole, next⟩

#print axioms runtime_cochain_receipt_inquiry_consumer

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
