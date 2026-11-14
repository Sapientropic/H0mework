import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.CochainReceiptConsumer

/-!
# Original duration inquiry consumes its full function-valued pairing

The native duration receipt yields the complete conductor evaluator as a
function of every Schwartz test and real scale. Multiplying two evaluated
free words gives a function-valued, integer-bilinear pairing at the same
occurrence. The old query, cochain, residual, ledger and next remain installed.
No test/scale is selected here and no Hilbert Gram or norm is asserted.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RawGeneratedRoot.CofinalAction

noncomputable section

theorem runtime_value_pairing_receipt_consumer
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (query : QueryAt law runtime.state)
    (left right : MotherPhysicalSource.Generator)
    (leftCoefficient rightCoefficient : ℤ) :
    let anchor := anchorAt law runtime.state
    let key : Key law := ⟨anchor, query⟩
    let sourceLaw := MotherPhysicalSource.receiptAction law
    (livingRoot law).toAuthoritativeRoot.source.projectionLaw.outcomeAt
        ((valuePairingInstallation law).embed PUnit.unit)
        runtime.emittedOccurrence =
      .inl ⟨PUnit.unit, valuePairing sourceLaw anchor.2⟩ ∧
    valuePairing sourceLaw anchor.2
        (Finsupp.single left leftCoefficient)
        (Finsupp.single right rightCoefficient) =
      (leftCoefficient • (MotherPhysicalSource.evaluatorAt law anchor.2).root left) *
        (rightCoefficient • (MotherPhysicalSource.evaluatorAt law anchor.2).root right) ∧
    (∀ projection : (materialSource law).projectionLaw.Projection,
      HEq ((declarationSource law).projectionLaw.outcomeAt
        ((historyInstallation law).embed projection) anchor.2)
        ((materialSource law).projectionLaw.outcomeAt projection anchor.2)) ∧
    (∀ projection : (projectionLaw law).Projection,
      HEq ((declarationSource law).projectionLaw.outcomeAt
        ((queryInstallation law).embed projection) anchor.2)
        ((projectionLaw law).outcomeAt projection anchor.2)) ∧
    (answer law key).2.1 =
      ((faithfulLaw sourceLaw).faithfulAt anchor.2).settleWithResidual ∧
    HEq ((inquiryAt law runtime.state).compileInquiry query).answerReadout
      (answer law key) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.current.visit.current) ∧
    runtime.tick.nextCurrent =
      (process law).stateAt ((process law).successor runtime.state) := by
  let current := runtime.current.visit.current
  let sourceLaw := MotherPhysicalSource.receiptAction law
  have generated := generated_value_pairing_basis sourceLaw current
    left right leftCoefficient rightCoefficient
  have fields := (MotherPhysicalSource.receiptAction_raw_fields law
    (RawGeneratedRoot.emitted dynamics current)).2.2.2
  change (sourceLaw.evaluatorAt (dynamics.emit current)) =
    MotherPhysicalSource.evaluatorAt law (RawGeneratedRoot.emitted dynamics current)
      at fields
  rw [fields] at generated
  obtain ⟨_cochain, materialInventory, queryInventory, _differential,
      _descent, residual, compiled, whole, next⟩ :=
    runtime_cochain_receipt_inquiry_consumer law runtime query left leftCoefficient
  exact ⟨rfl, generated, materialInventory, queryInventory,
    residual, compiled, whole, next⟩

#print axioms runtime_value_pairing_receipt_consumer

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
