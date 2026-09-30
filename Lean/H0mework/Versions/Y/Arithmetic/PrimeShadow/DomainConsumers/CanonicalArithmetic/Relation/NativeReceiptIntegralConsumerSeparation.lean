import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptObservedCoimage

/-!
# The original integral block consumer rejects finite complex compression

The stage-one prime-three row of the original unit receipt makes the global
integral endpoint class nonzero. The complete finite complex observation
family kills that same class. Hence the actual stage-one integral reader is
incompatible with the observation kernel and cannot factor through either
the family or its exact coimage, even by an arbitrary function. This is an
observer-specific separation, not a new unit-root ledger settlement.
-/

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitNativeReceiptIntegralConsumerSeparation

open CanonicalUnitNativeReceiptGlobalCompression
open CanonicalUnitNativeReceiptObservedCoimage
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalTower
open SourceGeneratedScalarDifferentialResidual
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

def stageOneIntegralRead : RestrictedArithmeticGlobalCokernel →
    IntegralRelationOperatorCokernel 1 :=
  (limit.π restrictedArithmeticCokernelDiagram
    (Opposite.op 1)).hom

def stageOneIntegralReadAdd :
    RestrictedArithmeticGlobalCokernel →+
      IntegralRelationOperatorCokernel 1 where
  toFun := stageOneIntegralRead
  map_zero' := by
    exact (limit.π restrictedArithmeticCokernelDiagram
      (Opposite.op 1)).hom.map_zero
  map_add' := by
    intro left right
    exact (limit.π restrictedArithmeticCokernelDiagram
      (Opposite.op 1)).hom.map_add left right

def stageOneIntegralReadLinear :
    RestrictedArithmeticGlobalCokernel →ₗ[ℤ]
      IntegralRelationOperatorCokernel 1 :=
  stageOneIntegralReadAdd.toIntLinearMap

theorem original_consumer_nonzero :
    stageOneIntegralReadLinear
      globalSpecializedIntegralEndpointBoundaryClass ≠ 0 :=
  stageOne_integral_read_nonzero

theorem incompatible_kernel :
    ¬ LinearMap.ker finiteComplexReadLinear ≤
      LinearMap.ker stageOneIntegralReadLinear := by
  intro compatible
  have vanished := compatible global_in_kernel
  exact original_consumer_nonzero (LinearMap.mem_ker.mp vanished)

theorem no_factor_through_complex_family :
    ¬ ∃ consumer : FiniteComplexFamily → IntegralRelationOperatorCokernel 1,
      ∀ value : RestrictedArithmeticGlobalCokernel,
        consumer (finiteComplexReadLinear value) =
          stageOneIntegralReadLinear value := by
  rintro ⟨consumer, factors⟩
  have same : finiteComplexReadLinear
      globalSpecializedIntegralEndpointBoundaryClass =
        finiteComplexReadLinear 0 := by
    rw [LinearMap.mem_ker.mp global_in_kernel, map_zero]
  have sameRead := (factors globalSpecializedIntegralEndpointBoundaryClass).symm.trans
    ((congrArg consumer same).trans (factors 0))
  rw [map_zero] at sameRead
  exact original_consumer_nonzero sameRead

theorem no_factor_through_coimage :
    ¬ ∃ consumer : ObservedCoimage → IntegralRelationOperatorCokernel 1,
      ∀ value : RestrictedArithmeticGlobalCokernel,
        consumer (canonicalResidual finiteComplexReadLinear value) =
          stageOneIntegralReadLinear value := by
  rintro ⟨consumer, factors⟩
  have same : canonicalResidual finiteComplexReadLinear
      globalSpecializedIntegralEndpointBoundaryClass =
        canonicalResidual finiteComplexReadLinear 0 := by
    rw [global_coimage_zero, map_zero]
  have sameRead := (factors globalSpecializedIntegralEndpointBoundaryClass).symm.trans
    ((congrArg consumer same).trans (factors 0))
  rw [map_zero] at sameRead
  exact original_consumer_nonzero sameRead

end
end CanonicalUnitNativeReceiptIntegralConsumerSeparation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
