import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptIntegralConsumerSeparation

/-!
# The original integral consumer is retained by a source-derived joint coimage

The actual complex observation and the stage-one integral block read act on
the same source-seeded global class. Their product has the exact intersection
kernel. The existing scalar coimage engine therefore gives the smallest
carrier for both readouts: the integral consumer factors uniquely, and the
original class survives. Forgetting its integral coordinate returns to the
complex coimage and is noninjective. No new root or ledger row is introduced.
-/

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitNativeReceiptJointConsumerCoimage

open CanonicalUnitNativeReceiptIntegralConsumerSeparation
open CanonicalUnitNativeReceiptObservedCoimage
open CanonicalUnitNativeReceiptGlobalCompression
open CanonicalUnitNativeReceiptBlockBoundary
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalTower
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence
open SourceGeneratedScalarDifferentialResidual

noncomputable section

def jointReadLinear : RestrictedArithmeticGlobalCokernel →ₗ[ℤ]
    (FiniteComplexFamily × IntegralRelationOperatorCokernel 1) :=
  finiteComplexReadLinear.prod stageOneIntegralReadLinear

theorem joint_kernel_exact :
    LinearMap.ker jointReadLinear =
      LinearMap.ker finiteComplexReadLinear ⊓
        LinearMap.ker stageOneIntegralReadLinear := by
  ext value
  simp only [LinearMap.mem_ker, Submodule.mem_inf]
  change (finiteComplexReadLinear value,
    stageOneIntegralReadLinear value) = (0, 0) ↔
      finiteComplexReadLinear value = 0 ∧
        stageOneIntegralReadLinear value = 0
  constructor
  · intro both
    exact ⟨congrArg Prod.fst both, congrArg Prod.snd both⟩
  · rintro ⟨left, right⟩
    exact Prod.ext left right

theorem joint_kernel_le_integral :
    LinearMap.ker jointReadLinear ≤
      LinearMap.ker stageOneIntegralReadLinear := by
  rw [joint_kernel_exact]
  exact inf_le_right

theorem joint_kernel_le_complex :
    LinearMap.ker jointReadLinear ≤
      LinearMap.ker finiteComplexReadLinear := by
  rw [joint_kernel_exact]
  exact inf_le_left

abbrev JointCoimage := ResidualCarrier jointReadLinear

def jointToIntegral : JointCoimage →ₗ[ℤ]
    IntegralRelationOperatorCokernel 1 :=
  (LinearMap.ker jointReadLinear).liftQ stageOneIntegralReadLinear
    joint_kernel_le_integral

theorem jointToIntegral_exact :
    jointToIntegral.comp (canonicalResidual jointReadLinear) =
      stageOneIntegralReadLinear := by
  apply LinearMap.ext
  intro value
  rfl

theorem jointToIntegral_unique :
    ∃! consumer : JointCoimage →ₗ[ℤ]
        IntegralRelationOperatorCokernel 1,
      consumer.comp (canonicalResidual jointReadLinear) =
        stageOneIntegralReadLinear :=
  universal_factorization jointReadLinear stageOneIntegralReadLinear
    joint_kernel_le_integral

theorem original_class_joint_nonzero :
    canonicalResidual jointReadLinear
      globalSpecializedIntegralEndpointBoundaryClass ≠ 0 := by
  rw [canonicalResidual_ne_zero_iff]
  intro vanished
  have right := congrArg Prod.snd vanished
  exact original_consumer_nonzero right

theorem joint_integral_consumer_nonzero :
    jointToIntegral (canonicalResidual jointReadLinear
      globalSpecializedIntegralEndpointBoundaryClass) ≠ 0 := by
  change stageOneIntegralReadLinear
    globalSpecializedIntegralEndpointBoundaryClass ≠ 0
  exact original_consumer_nonzero

def jointToComplexCoimage : JointCoimage →ₗ[ℤ] ObservedCoimage :=
  (LinearMap.ker jointReadLinear).liftQ
    (canonicalResidual finiteComplexReadLinear) (by
      intro value inKernel
      rw [LinearMap.mem_ker]
      exact (canonicalResidual_eq_zero_iff finiteComplexReadLinear value).2
        (LinearMap.mem_ker.mp (joint_kernel_le_complex inKernel)))

theorem jointToComplexCoimage_exact :
    jointToComplexCoimage.comp (canonicalResidual jointReadLinear) =
      canonicalResidual finiteComplexReadLinear := by
  apply LinearMap.ext
  intro value
  rfl

theorem jointToComplexCoimage_not_injective :
    ¬ Function.Injective jointToComplexCoimage := by
  intro injective
  apply original_class_joint_nonzero
  have vanished : jointToComplexCoimage
      (canonicalResidual jointReadLinear
        globalSpecializedIntegralEndpointBoundaryClass) = 0 := by
    have square := LinearMap.congr_fun jointToComplexCoimage_exact
      globalSpecializedIntegralEndpointBoundaryClass
    simpa only [LinearMap.comp_apply, global_coimage_zero] using square
  apply injective
  exact vanished.trans (map_zero jointToComplexCoimage).symm

def sourceJointOccurrence :=
  residualOccurrence globalSpecializedIntegralEndpointBoundaryOccurrence
    (fun _ => jointReadLinear) (fun source => source.2)

theorem sourceJointOccurrence_projects :
    sourceJointOccurrence.map Sigma.fst =
      globalSpecializedIntegralEndpointBoundaryOccurrence :=
  residualOccurrence_projects _ _ _

/-- The joint source occurrence reads the original stage-one block-action
consumer itself, not merely an unrelated nonzero integer coordinate. -/
theorem joint_reads_original_block_action :
    jointToIntegral sourceJointOccurrence.root.2 =
      blockRelationActionCokernelArithmeticRead 1
        (localEndpointBoundaryCokernelClass 1) := by
  change stageOneIntegralReadLinear
    globalSpecializedIntegralEndpointBoundaryClass = _
  exact (globalSpecializedIntegralEndpointBoundaryClass_restriction 1).trans
    (blockRelationActionCokernelArithmeticRead_endpointClass 1).symm

theorem sourceJointOccurrence_integral_nonzero :
    jointToIntegral sourceJointOccurrence.root.2 ≠ 0 := by
  rw [joint_reads_original_block_action]
  exact receipt_three_nonzero

end
end CanonicalUnitNativeReceiptJointConsumerCoimage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
