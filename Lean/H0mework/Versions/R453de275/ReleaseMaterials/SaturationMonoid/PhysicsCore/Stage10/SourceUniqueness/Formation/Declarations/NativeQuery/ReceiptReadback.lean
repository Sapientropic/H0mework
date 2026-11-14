import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.Inquiry
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.PhysicalSource.ReceiptCofinal

/-!
# Original native inquiry from the duration receipt

The existing inquiry root already installs the physical material and its
answer as dependent faces of the original duration occurrence. This consumer
identifies the answer's residual with the receipt-generated faithful face;
its old whole-ledger row and next are read from the same inquiry root.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RawGeneratedRoot.CofinalAction

noncomputable section

theorem same_duration_lower_and_emitter (law : MotherPhysicalLaws.Law) :
    (livingRoot law).toAuthoritativeRoot.toLedgerRoot =
        (RawGeneratedRoot.root dynamics).toAuthoritativeRoot.toLedgerRoot ∧
      (livingRoot law).emitted = RawGeneratedRoot.emitted dynamics :=
  ⟨rfl, rfl⟩

theorem original_inquiry_receipt_readback
    (law : MotherPhysicalLaws.Law) (depth : ℕ)
    (query : QueryAt law depth) :
    let current := (visitAt law depth).current
    let anchor := anchorAt law depth
    let key : Key law := ⟨anchor, query⟩
    (answer law key).2.1 =
      ((RawGeneratedRoot.CofinalAction.faithfulLaw
        (MotherPhysicalSource.receiptAction law)).faithfulAt
          anchor.2).settleWithResidual ∧
    HEq ((inquiryAt law depth).compileInquiry query).answerReadout
      (answer law key) ∧
    HEq (((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
      current).entryDisposition (RawGeneratedRoot.entry dynamics current))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (dynamics.emit current)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt N
              (RawGeneratedRoot.entry dynamics current)
              (RawGeneratedRoot.entry dynamics
                (dynamics.update (dynamics.emit current))))) ∧
    ((livingRoot law).toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? =
      some (dynamics.update (dynamics.emit current)) := by
  have material_eq := MotherPhysicalSource.receipt_material_eq_original law
  have classified_heq : HEq
      ((RawGeneratedRoot.CofinalAction.faithfulLaw
        (MotherPhysicalSource.receiptAction law)).faithfulAt
          (anchorAt law depth).2).settleWithResidual
      ((MotherPhysicalSource.materialLaw law).faithfulAt
          (anchorAt law depth).2).settleWithResidual := by
    cases material_eq
    exact HEq.rfl
  have classified_eq :
      ((RawGeneratedRoot.CofinalAction.faithfulLaw
        (MotherPhysicalSource.receiptAction law)).faithfulAt
          (anchorAt law depth).2).settleWithResidual =
      ((MotherPhysicalSource.materialLaw law).faithfulAt
          (anchorAt law depth).2).settleWithResidual :=
    eq_of_heq classified_heq
  refine ⟨?_, complete_answer law depth query, HEq.rfl, rfl⟩
  exact classified_eq.symm

#print axioms original_inquiry_receipt_readback
#print axioms same_duration_lower_and_emitter

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
