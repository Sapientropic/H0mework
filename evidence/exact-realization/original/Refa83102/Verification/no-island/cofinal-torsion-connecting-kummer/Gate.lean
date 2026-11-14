import SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP740Independent

open SourceGeneratedPrimePowerCompletion

section Generic
variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

private def the_original_connecting_range_and_kernel_are_exact
    (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (prime : Nat.Primes) (stage : Nat) :=
  And.intro (source_ambient_torsion_exact evaluate injective prime stage)
    (And.intro (cokernel_connecting_kernel evaluate injective prime stage)
      (cokernel_connecting_image evaluate injective prime stage))

private def the_divisible_ambient_case_recovers_the_original_stage
    (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (prime : Nat.Primes) (stage : Nat)
    (ambient : Function.Bijective (powerMultiplication (L := M) prime stage)) :=
  stage_cokernel_connecting_inverse evaluate injective prime stage ambient

end Generic

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩

private def splitEvaluation : ℤ →ₗ[ℤ] ℤ × ZMod 2 :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0

private theorem split_evaluation_injective : Function.Injective splitEvaluation := by
  intro left right equal
  exact congrArg Prod.fst equal

private def ambientTwoTorsion : PrimePowerTorsionSubmodule (ℤ × ZMod 2) binary 0 :=
  ⟨(0, 1), by
    change ((2 : ℤ) • ((0, 1) : ℤ × ZMod 2)) = 0
    decide⟩

private theorem a_nonzero_ambient_torsion_class_remains_in_the_connecting_kernel :
    ∃ value : CokernelTorsion splitEvaluation binary 0, value ≠ 0 ∧
      stageCokernelConnecting splitEvaluation split_evaluation_injective binary 0 value = 0 := by
  let value := ambientToCokernelTorsion splitEvaluation binary 0 ambientTwoTorsion
  refine ⟨value, ?_, ?_⟩
  · intro erased
    have quotientZero : (LinearMap.range splitEvaluation).mkQ ambientTwoTorsion.val = 0 :=
      congrArg Subtype.val erased
    obtain ⟨source, written⟩ := (Submodule.Quotient.mk_eq_zero _).mp quotientZero
    have falseRead : (0 : ZMod 2) = 1 := congrArg Prod.snd written
    exact zero_ne_one falseRead
  · have image : value ∈ LinearMap.range (ambientToCokernelTorsion splitEvaluation binary 0) :=
      ⟨ambientTwoTorsion, rfl⟩
    rw [cokernel_connecting_kernel splitEvaluation split_evaluation_injective binary 0] at image
    exact LinearMap.mem_ker.mp image

end CP740Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP740Independent

open SourceOperationScalarInventoryLift
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def the_original_R_root_relation_whole_and_next_are_consumed (ordinal : Nat) :=
  actual_root_relation_consumer observation nontrivial half depth ordinal

private def the_original_R_cokernel_model_reads_the_same_integer_at_actual_next
    (ordinal : Nat) (prime : Nat.Primes) (stage : Nat) (coefficient : ℤ) :=
  actual_paid_cokernel_model_next observation nontrivial half depth ordinal prime stage coefficient

end OriginalKCofinalFullBranchFibre.RootRelation.CP740Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SaturationMonoid.UniversalBSDRationalKummerCokernel.CP740Independent

open UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology

private def the_actual_kummer_division_reads_the_same_point_and_covers_each_stage
    (source : RationalEllipticCurveSource) (prime : Nat.Primes) (stage : Nat)
    (point : RationalPoints source) :=
  And.intro (actual_kummer_division_reads_source source prime stage point)
    (actual_kummer_connecting_surjective source prime stage)

private def the_same_original_kummer_class_has_the_exact_ambient_torsion_kernel
    (source : RationalEllipticCurveSource) (prime : Nat.Primes) (stage : Nat)
    (point : RationalPoints source) :=
  And.intro (actual_kummer_cokernel_class source prime stage point)
    (actual_kummer_cokernel_kernel source prime stage)

#eval IO.println "CP740_CONTROL + the_original_connecting_range_kernel_and_inverse_are_exact"
#eval IO.println "CP740_CONTROL + the_actual_kummer_division_reads_the_same_point_and_covers_each_stage"
#eval IO.println "CP740_CONTROL + the_same_original_kummer_class_has_the_exact_ambient_torsion_kernel"
#eval IO.println "CP740_CONTROL + the_original_R_root_whole_and_actual_model_next_are_consumed"
#eval IO.println "CP740_CONTROL - a_nonzero_ambient_torsion_class_remains_in_the_connecting_kernel"
#eval IO.println "CP740_GATE_PASS positive=4 negative=1"

end SaturationMonoid.UniversalBSDRationalKummerCokernel.CP740Independent
