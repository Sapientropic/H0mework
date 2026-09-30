import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptBlockBoundary
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Arithmetic.LivingLawCanonicalRiemannReceiptArithmeticComplexificationResidual

/-!
# The native unit receipt excludes free recovery from finite complex reads

The global integral action-cokernel is a source-process readout, not a
completed payload at one finite visit. The original stage-one unit receipt
supplies an actual prime-three row witnessing that its global endpoint class
is nonzero. The existing arithmetic determinant kills every finite complex
read of that same class. Thus the complete family of finite complex reads
is not faithful and has no universal decoder. This consumes no Riemann-zero
observation and does not change the old unit row's disposition.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitNativeReceiptGlobalCompression

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitNativeReceiptFactorization
open CanonicalUnitNativeReceiptBlockBoundary
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalTower
open NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

/-- All finite complexified reads of one global arithmetic class. -/
def finiteComplexRead (value : RestrictedArithmeticGlobalCokernel) :
    (stage : Nat) → ComplexIntegralRelationOperatorCokernel stage :=
  fun stage => (1 : ℂ) ⊗ₜ[ℤ]
    (limit.π restrictedArithmeticCokernelDiagram
      (Opposite.op stage)).hom value

/-- The original stage-one receipt makes the integral projection nonzero. -/
theorem stageOne_integral_read_nonzero :
    (limit.π restrictedArithmeticCokernelDiagram (Opposite.op 1)).hom
      globalSpecializedIntegralEndpointBoundaryClass ≠ 0 := by
  rw [globalSpecializedIntegralEndpointBoundaryClass_restriction]
  have consumed := (receipt_three_class_ledger_next).2.2.1
  rw [blockRelationActionCokernelArithmeticRead_endpointClass] at consumed
  exact consumed

/-- The original stage-one receipt, rather than a selected zero point,
witnesses nonvanishing of the source-seeded global class. -/
theorem receipt_global_nonzero :
    globalSpecializedIntegralEndpointBoundaryClass ≠ 0 := by
  intro vanished
  apply stageOne_integral_read_nonzero
  rw [vanished, map_zero]

/-- Scalarization loses that source-seeded class at every finite stage. -/
theorem finiteComplexRead_global_zero :
    finiteComplexRead globalSpecializedIntegralEndpointBoundaryClass = 0 := by
  funext stage
  exact globalArithmeticEndpoint_complexLocalRead_zero stage

/-- The full finite complex observation family is not faithful. -/
theorem finiteComplexRead_not_injective :
    ¬ Function.Injective finiteComplexRead := by
  intro injective
  apply receipt_global_nonzero
  apply injective
  rw [finiteComplexRead_global_zero]
  funext stage
  simp only [Pi.zero_apply, finiteComplexRead, map_zero]
  exact (TensorProduct.tmul_zero (IntegralRelationOperatorCokernel stage)
    (1 : ℂ)).symm

/-- No decoder can recover every global arithmetic class from that family. -/
theorem no_full_decoder :
    ¬ ∃ decoder : ((stage : Nat) → ComplexIntegralRelationOperatorCokernel stage) →
        RestrictedArithmeticGlobalCokernel,
      ∀ value, decoder (finiteComplexRead value) = value := by
  rintro ⟨decoder, recovers⟩
  apply finiteComplexRead_not_injective
  intro left right same
  calc
    left = decoder (finiteComplexRead left) := (recovers left).symm
    _ = decoder (finiteComplexRead right) := congrArg decoder same
    _ = right := recovers right

end
end CanonicalUnitNativeReceiptGlobalCompression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
