import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptGlobalCompression
import H0mework.Foundation.Relations.ScalarDifferentialResidual

/-!
# The native global class enters the existing scalar coimage engine

The source-seeded global integral class is visible at the original unit
receipt's new prime-three row, while every member of the chosen finite
complexification family reads it as zero. The family is one actual ℤ-linear
observation, so the existing generic coimage produces its exact minimal
observable carrier and universal factorization. Its kernel contains the
nonzero original class. Mapping the existing global occurrence into that
coimage keeps the source occurrence, the original class, and the lost
quotient coordinate together; it does not install a new unit-root ledger row.
-/

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitNativeReceiptObservedCoimage

open CanonicalUnitNativeReceiptGlobalCompression
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalTower
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence
open NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic
open SourceGeneratedScalarDifferentialResidual
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

abbrev FiniteComplexFamily :=
  (stage : Nat) → ComplexIntegralRelationOperatorCokernel stage

/-- The existing stagewise tensor read is additive as a complete family. -/
def finiteComplexReadAdd :
    RestrictedArithmeticGlobalCokernel →+ FiniteComplexFamily where
  toFun := finiteComplexRead
  map_zero' := by
    funext stage
    simp only [finiteComplexRead, Pi.zero_apply, map_zero]
    exact TensorProduct.tmul_zero (IntegralRelationOperatorCokernel stage) (1 : ℂ)
  map_add' := by
    intro left right
    funext stage
    simp only [finiteComplexRead, Pi.add_apply, map_add]
    exact TensorProduct.tmul_add (1 : ℂ)
      ((limit.π restrictedArithmeticCokernelDiagram
        (Opposite.op stage)).hom left)
      ((limit.π restrictedArithmeticCokernelDiagram
        (Opposite.op stage)).hom right)

/-- The same observation in the generic integral coimage language. -/
def finiteComplexReadLinear :
    RestrictedArithmeticGlobalCokernel →ₗ[ℤ] FiniteComplexFamily :=
  finiteComplexReadAdd.toIntLinearMap

/-- A source-derived nonzero class belongs to the exact observation kernel. -/
theorem global_in_kernel :
    globalSpecializedIntegralEndpointBoundaryClass ∈
      LinearMap.ker finiteComplexReadLinear := by
  rw [LinearMap.mem_ker]
  exact finiteComplexRead_global_zero

theorem global_nonzero_in_kernel :
    ∃ value : RestrictedArithmeticGlobalCokernel,
      value ≠ 0 ∧ value ∈ LinearMap.ker finiteComplexReadLinear :=
  ⟨globalSpecializedIntegralEndpointBoundaryClass,
    receipt_global_nonzero, global_in_kernel⟩

/-- The canonical observable quotient erases precisely this source class. -/
theorem global_coimage_zero :
    canonicalResidual finiteComplexReadLinear
      globalSpecializedIntegralEndpointBoundaryClass = 0 := by
  exact (canonicalResidual_eq_zero_iff finiteComplexReadLinear
    globalSpecializedIntegralEndpointBoundaryClass).2
      finiteComplexRead_global_zero

abbrev ObservedCoimage := ResidualCarrier finiteComplexReadLinear

/-- Consume the existing universal coimage theorem on this actual map. -/
theorem every_compatible_reader_factors
    {Q : Type*} [AddCommGroup Q] [Module ℤ Q]
    (reader : RestrictedArithmeticGlobalCokernel →ₗ[ℤ] Q)
    (compatible : LinearMap.ker finiteComplexReadLinear ≤
      LinearMap.ker reader) :
    ∃! factor : ObservedCoimage →ₗ[ℤ] Q,
      factor.comp (canonicalResidual finiteComplexReadLinear) = reader :=
  universal_factorization finiteComplexReadLinear reader compatible

/-- The observed quotient cannot freely reconstruct the complete source. -/
theorem no_identity_recovery_from_coimage :
    ¬ ∃ decoder : ObservedCoimage →ₗ[ℤ]
        RestrictedArithmeticGlobalCokernel,
      decoder.comp (canonicalResidual finiteComplexReadLinear) =
        LinearMap.id := by
  rintro ⟨decoder, recovers⟩
  have atClass := LinearMap.congr_fun recovers
    globalSpecializedIntegralEndpointBoundaryClass
  rw [LinearMap.comp_apply, global_coimage_zero, map_zero,
    LinearMap.id_apply] at atClass
  exact receipt_global_nonzero atClass.symm

/-- Retain the original global occurrence while installing its coimage read. -/
def sourceObservedCoimageOccurrence :=
  residualOccurrence globalSpecializedIntegralEndpointBoundaryOccurrence
    (fun _ => finiteComplexReadLinear) (fun source => source.2)

theorem sourceObservedCoimageOccurrence_projects :
    sourceObservedCoimageOccurrence.map Sigma.fst =
      globalSpecializedIntegralEndpointBoundaryOccurrence :=
  residualOccurrence_projects _ _ _

/-- The same occurrence keeps a nonzero integral coordinate whose chosen
complex observation quotient reads zero. -/
theorem sourceObservedCoimageOccurrence_loss :
    sourceObservedCoimageOccurrence.root.1.2 ≠ 0 ∧
      sourceObservedCoimageOccurrence.root.2 = 0 := by
  constructor
  · exact receipt_global_nonzero
  · exact global_coimage_zero

end
end CanonicalUnitNativeReceiptObservedCoimage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
