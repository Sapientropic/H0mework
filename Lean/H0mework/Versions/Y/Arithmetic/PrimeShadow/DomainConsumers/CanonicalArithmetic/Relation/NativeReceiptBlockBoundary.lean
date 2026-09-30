import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptFactorization
import H0mework.Versions.Y.Arithmetic.BlockSpecialization.CokernelNaturality

/-!
# The original unit action first emits a surviving prime-three boundary

At stage one the old current has no prime-three factor. Its executable unit
sibling changes the native target, and the old transfer receipt yields the
complete factor inventory. A key from that very receipt evaluates the already
installed full-Euler boundary to one, so the existing block-action cokernel
consumer reads a nonzero class. The class survives the actual next-stage
restriction. This is a dependent effect of the old transfer, not a new
same-debt settlement in its zero-budget ledger row.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitNativeReceiptBlockBoundary

open ArithmeticGeneration
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationInverseFibre
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitNativeReceiptFactorization
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockArithmeticSpecializationEndpoint
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelNaturality

noncomputable section

/-- The arithmetic material is read from the named canonical runtime's
installed face. The inactive branch is empty under this fixed source law. -/
def installedMaterialWhole (stage : Nat) : UnitHistory :=
  match runtimeFacade.readoutAt (runtimeAt stage) .material with
  | .inl ⟨_, material⟩ => material.down.whole
  | .inr empty => PEmpty.elim empty

theorem installedMaterialWhole_eq_receiptTarget (stage : Nat) :
    installedMaterialWhole stage =
      transferActionTarget (runtimeReceipt stage) := by
  rfl

private theorem priorShadow :
    (runtimeAt 1).current.visit.current.cardinalShadow = 2 := by
  rfl

private theorem before_no_three :
    ¬ ∃ index : PrimeIndex ((runtimeAt 1).current.visit.current),
      index.1 = 3 := by
  rintro ⟨index, eqThree⟩
  have included :
      factorization ((runtimeAt 1).current.visit.current) index.1 ≠ 0 :=
    Finsupp.mem_support_iff.mp index.2
  have includedThree :
      factorization ((runtimeAt 1).current.visit.current) 3 ≠ 0 := by
    simpa only [eqThree] using included
  have zero : (Nat.factorial 2).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have cardEq : factorization ((runtimeAt 1).current.visit.current) 3 =
      (Nat.factorial 2).factorization 3 := by
    change factorization (CanonicalUnitArithmeticRoot.next initialCurrent) 3 = _
    rw [factorization_eq_cardinal_factorization]
    rfl
  exact includedThree (cardEq.trans zero)

/-- Removing the unit sibling leaves the old current without a three-row. -/
theorem unadvanced_no_three :
    ¬ ∃ index : PrimeIndex
        (nativeActionTarget (.zero ((runtimeAt 1).current.visit.current))),
      index.1 = 3 := by
  change ¬ ∃ index : PrimeIndex ((runtimeAt 1).current.visit.current),
    index.1 = 3
  exact before_no_three

/-- The original receipt generates the three-row key and its raw boundary
coordinate. No key, endpoint result, or nonzero certificate is an input. -/
def receiptThreeBoundaryEffect :
    {key : TransferFactorKey (runtimeReceipt 1) //
      ((rowPrime (rowOfReceiptKey 1 (runtimeReceipt 1) key) : Nat) = 3) ∧
      (integralBoundaryCoordinate 1
        (rowOfReceiptKey 1 (runtimeReceipt 1) key)
        (factorizationDifferential seedOccurrence.root 1
          (localEndpointVertexMap 1 leftEndpointBase)) = 1)} := by
  refine ⟨keyThree, rfl, ?_⟩
  rw [factorizationDifferential_leftEndpoint]
  exact integralBoundaryCoordinate_endpoint 1
    (rowOfReceiptKey 1 (runtimeReceipt 1) keyThree)

/-- The existing independent block-action cokernel consumes that actual row. -/
theorem receipt_three_nonzero :
    blockRelationActionCokernelArithmeticRead 1
      (localEndpointBoundaryCokernelClass 1) ≠ 0 :=
  mappedBlockEndpointClass_ne_zero_at_three 1
    (rowOfReceiptKey 1 (runtimeReceipt 1) receiptThreeBoundaryEffect.val)
    receiptThreeBoundaryEffect.property.1

/-- The same boundary class remains nonzero under the source successor's
already installed restriction square. -/
theorem next_boundary_class_nonzero :
    specializedIntegralEndpointBoundaryClass 2 ≠ 0 := by
  intro zero
  have mapped := congrArg (integralRelationOperatorCokernelRestriction 1) zero
  rw [map_zero, integralRelationOperatorCokernelRestriction_endpointClass] at mapped
  exact specializedIntegralEndpointBoundaryClass_ne_zero_at_three 1
    (rowOfReceiptKey 1 (runtimeReceipt 1) receiptThreeBoundaryEffect.val)
    receiptThreeBoundaryEffect.property.1 mapped

theorem next_stage_is_runtime :
    (runtimeAt 1).tick.next = runtimeAt 2 := by
  rfl

/-- The original compiler still writes its exact transfer row and literal
next while the dependent block consumer reads the new three-row effect. -/
theorem receipt_three_class_ledger_next :
    let runtime := runtimeAt 1
    let current := runtime.current.visit.current
    let receipt := runtimeReceipt 1
    installedMaterialWhole 1 = transferActionTarget receipt ∧
      HEq (runtimeFacade.readoutAt runtime .material)
        (runtime.tick.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .material).embed
            (runtimeFacade.projectionAt runtime .material))) ∧
      blockRelationActionCokernelArithmeticRead 1
        (localEndpointBoundaryCokernelClass 1) ≠ 0 ∧
      specializedIntegralEndpointBoundaryClass 2 ≠ 0 ∧
      runtime.tick.next = runtimeAt 2 ∧
      HEq (runtime.tick.generated.wholeLedgerWriteBack.entryDisposition
        (rootLedgerEntry current))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred receipt
            rfl rfl (Nat.le_refl _) :
              LedgerEntryEvolutionAt N (rootLedgerEntry current)
                (rootLedgerEntry (next current)))) ∧
      runtime.tick.nextCurrent =
        CanonicalUnitArithmeticRoot.runtimeFacade.process.stateAt
          (CanonicalUnitArithmeticRoot.runtimeFacade.process.successor
            runtime.state) := by
  exact ⟨installedMaterialWhole_eq_receiptTarget 1,
    (coversAt_factorizes (runtimeAt 1) .material).2.2.2.1,
    receipt_three_nonzero, next_boundary_class_nonzero,
    next_stage_is_runtime,
    (runtimeReceipt_inventory_ledger_equation_next 1).2.2.2.1,
    (runtimeReceipt_inventory_ledger_equation_next 1).2.2.2.2⟩

end
end CanonicalUnitNativeReceiptBlockBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
