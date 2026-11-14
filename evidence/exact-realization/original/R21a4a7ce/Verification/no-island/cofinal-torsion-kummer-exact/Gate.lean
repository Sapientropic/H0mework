import SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.CompletionExact
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP742Independent

open CategoryTheory CategoryTheory.Limits
open SourceGeneratedPrimePowerCompletion
open private torsion_lift_coordinates from
  SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentKernel

section Generic
variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]
variable (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)

private def restriction_pays_the_prime_power_for_any_coherent_stage
    (p : Nat.Primes) (j d : Nat) (value : PrimePowerTorsionCompletion M p) :=
  torsion_restriction_power p j d value

private def bounded_source_exactness
    (p : Nat.Primes) (d : Nat)
    (bounded : ∀ j (value : PrimePowerTorsionSubmodule L p j), (p.1 : ℤ)^d • value.val = 0) :=
  And.intro (cokernel_connecting_limit_kernel_of_bounded evaluate injective p d bounded)
    (ambient_to_cokernel_limit_injective_of_bounded evaluate injective p d bounded)

private def noetherian_source_stabilization_and_exactness [IsNoetherian ℤ (Submodule.torsion ℤ L)]
    (p : Nat.Primes) :=
  And.intro (source_prime_torsion_bounded (L := L) p)
    (And.intro (cokernel_connecting_limit_kernel evaluate injective p)
      (ambient_to_cokernel_limit_injective evaluate injective p))

end Generic

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩
private def integerInRat : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap
private abbrev RatModInteger := ℚ ⧸ LinearMap.range integerInRat
private def modInteger : ℚ →ₗ[ℤ] RatModInteger := (LinearMap.range integerInRat).mkQ
private def identityEval : RatModInteger →ₗ[ℤ] RatModInteger := LinearMap.id

private theorem rational_half_not_integral : modInteger (1 / 2) ≠ 0 := by
  intro erased
  obtain ⟨integer, written⟩ := (Submodule.Quotient.mk_eq_zero _).mp erased
  change (integer : ℚ) = (1 / 2 : ℚ) at written
  have rational : (2 : ℚ) * (integer : ℚ) = 1 := by rw [written]; norm_num
  have impossible : (2 : ℤ) * integer = 1 := by exact_mod_cast rational
  have notDvd : ¬ (2 : ℤ) ∣ 1 := by norm_num
  exact notDvd ⟨integer, impossible.symm⟩

private def dyadicAt (j : Nat) : PrimePowerTorsionSubmodule RatModInteger binary j :=
  ⟨modInteger (((2 : ℚ) ^ (j+1))⁻¹), by
    change ((2 : Nat) : ℤ)^(j+1) • modInteger (((2 : ℚ) ^ (j+1))⁻¹) = 0
    have paysOne : ((2 : Nat) : ℤ)^(j+1) • (((2 : ℚ) ^ (j+1))⁻¹) = 1 := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul, Int.cast_pow]
      exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))
    rw [← map_smul modInteger, paysOne]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨1, by
      change ((1 : ℤ) : ℚ) = 1
      norm_num⟩⟩

private theorem dyadic_drops (j : Nat) :
    primePowerTorsionRestriction binary j (dyadicAt (j+1)) = dyadicAt j := by
  apply Subtype.ext
  change ((2 : Nat) : ℤ) • modInteger (((2 : ℚ) ^ (j+1+1))⁻¹) =
    modInteger (((2 : ℚ) ^ (j+1))⁻¹)
  rw [← map_smul modInteger]
  apply congrArg modInteger
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
  change (2 : ℚ) * (((2 : ℚ) ^ (j+1+1))⁻¹) = ((2 : ℚ) ^ (j+1))⁻¹
  rw [pow_succ (2 : ℚ) (j+1)]
  field_simp [pow_ne_zero (j+1) (by norm_num : (2 : ℚ) ≠ 0)]

private theorem unbounded_dyadic_torsion_destroys_uniqueness_even_for_identity :
    ∃ value : PrimePowerTorsionCompletion RatModInteger binary,
      value ≠ 0 ∧ ambientToCokernelAtLimit identityEval binary value = 0 := by
  obtain ⟨value, reads⟩ := torsion_lift_coordinates binary dyadicAt dyadic_drops
  refine ⟨value, ?_, ?_⟩
  · intro erased
    have halfZero : dyadicAt 0 = 0 :=
      (reads 0).symm.trans ((congrArg (torsionCompletionRestriction RatModInteger binary 0).hom erased).trans
        (map_zero _))
    apply rational_half_not_integral
    have halfRead : (dyadicAt 0).val = modInteger (1 / 2) := by
      change modInteger (((2 : ℚ) ^ (0+1 : Nat))⁻¹) = modInteger (1 / 2)
      congr 1
      norm_num
    exact halfRead.symm.trans (congrArg Subtype.val halfZero)
  · let C := RatModInteger ⧸ LinearMap.range identityEval
    apply Concrete.limit_ext (primePowerTorsionTower C binary)
    rintro ⟨j⟩
    change (torsionCompletionRestriction C binary j).hom
      (ambientToCokernelAtLimit identityEval binary value) = (torsionCompletionRestriction C binary j).hom 0
    rw [torsion_limit_map_restriction, reads, map_zero]
    apply Subtype.ext
    change (LinearMap.range identityEval).mkQ (dyadicAt j).val = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(dyadicAt j).val, rfl⟩

end CP742Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP742Independent

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

end OriginalKCofinalFullBranchFibre.RootRelation.CP742Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SaturationMonoid.UniversalBSDRationalKummerCokernel.CP742Independent

open UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion

private theorem all_actual_H_one_classes_determine_one_coherent_geometric_difference
    (source : RationalEllipticCurveSource) (prime : Nat.Primes)
    (left right : PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) prime) :
    (∀ stage, cokernelKummer source prime stage
        ((torsionCompletionRestriction (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source))
          prime stage).hom left) =
      cokernelKummer source prime stage
        ((torsionCompletionRestriction (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source))
          prime stage).hom right)) ↔
    ∃! difference : PrimePowerTorsionCompletion (GeometricPoints source) prime,
      ambientToCokernelAtLimit (pointEvaluation source) prime difference = left - right :=
  actual_kummer_completion_class_fibre source prime left right

private def actual_height_source_installs_the_complete_kernel
    (source : RationalEllipticCurveSource) (prime : Nat.Primes) :=
  actual_kummer_completion_kernel source prime

#eval IO.println "CP742_CONTROL + bounded_source_exactness_and_actual_prime_power_restriction"
#eval IO.println "CP742_CONTROL + noetherian_source_stabilization_and_exactness"
#eval IO.println "CP742_CONTROL + all_actual_H_one_classes_determine_one_coherent_geometric_difference"
#eval IO.println "CP742_CONTROL + the_original_R_root_relation_whole_and_next_are_consumed"
#eval IO.println "CP742_CONTROL - unbounded_dyadic_torsion_destroys_uniqueness_even_for_identity"
#eval IO.println "CP742_GATE_PASS positive=4 negative=1"

end SaturationMonoid.UniversalBSDRationalKummerCokernel.CP742Independent
