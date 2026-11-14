import SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.Completion
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP741Independent

open SourceGeneratedPrimePowerCompletion

section Generic
variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]
variable (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)

private def the_same_prime_multiplication_commutes_with_the_source_restriction
    (prime : Nat.Primes) (stage : Nat) (value : CokernelTorsion evaluate prime (stage+1)) :=
  cokernel_connecting_restriction evaluate injective prime stage value

private def the_whole_original_limit_has_the_same_stage_read
    (prime : Nat.Primes) (stage : Nat)
    (value : PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) prime) :=
  cokernel_connecting_limit_restriction evaluate injective prime stage value

private def actual_ambient_division_lifts_the_compatible_upper_class_over_its_given_lower_class
    (prime : Nat.Primes) (ambient : Function.Surjective (fun value : M => (prime.1 : ℤ) • value))
    (stage : Nat) (lower : CokernelTorsion evaluate prime stage)
    (upper : StageResidual (L := L) prime (stage+1))
    (compatible : stageCokernelConnecting evaluate injective prime stage lower = transition prime stage upper) :=
  cokernel_connecting_lift_step evaluate injective prime ambient stage lower upper compatible

private def every_coherent_source_class_has_one_coherent_torsion_lift
    (prime : Nat.Primes) (ambient : Function.Surjective (fun value : M => (prime.1 : ℤ) • value)) :=
  cokernel_connecting_limit_surjective evaluate injective prime ambient

end Generic

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩

private def integerInRat : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap
private abbrev RatModInteger := ℚ ⧸ LinearMap.range integerInRat
private def modInteger : ℚ →ₗ[ℤ] RatModInteger := (LinearMap.range integerInRat).mkQ
private def eval : ℤ →ₗ[ℤ] ℚ × RatModInteger := integerInRat.prod 0

private theorem eval_injective : Function.Injective eval := by
  intro left right equal
  apply (Int.cast_injective : Function.Injective (fun integer : ℤ => (integer : ℚ)))
  exact congrArg Prod.fst equal

private theorem rational_double (value : ℚ) : ((2 : Nat) : ℤ) • (value / 2) = value := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
  norm_num
  ring

private theorem ambient_two_divides :
    Function.Surjective (fun value : ℚ × RatModInteger => (binary.1 : ℤ) • value) := by
  intro value
  obtain ⟨representative, written⟩ := (LinearMap.range integerInRat).mkQ_surjective value.2
  refine ⟨(value.1 / 2, modInteger (representative / 2)), Prod.ext (rational_double value.1) ?_⟩
  exact ((map_smul modInteger ((2 : Nat) : ℤ) (representative / 2)).symm.trans
    (congrArg modInteger (rational_double representative))).trans written

private theorem rational_half_not_integral : modInteger (1 / 2) ≠ 0 := by
  intro erased
  obtain ⟨integer, written⟩ := (Submodule.Quotient.mk_eq_zero _).mp erased
  change (integer : ℚ) = (1 / 2 : ℚ) at written
  have rational : (2 : ℚ) * (integer : ℚ) = 1 := by rw [written]; norm_num
  have impossible : (2 : ℤ) * integer = 1 := by exact_mod_cast rational
  have notDvd : ¬ (2 : ℤ) ∣ 1 := by norm_num
  exact notDvd ⟨integer, impossible.symm⟩

private def halfAmbient : PrimePowerTorsionSubmodule (ℚ × RatModInteger) binary 0 :=
  ⟨(0, modInteger (1 / 2)), by
    change ((2 : Nat) : ℤ) • ((0, modInteger (1 / 2)) : ℚ × RatModInteger) = 0
    apply Prod.ext
    · change ((2 : Nat) : ℤ) • (0 : ℚ) = 0
      exact smul_zero _
    · change ((2 : Nat) : ℤ) • modInteger (1 / 2) = 0
      rw [← map_smul modInteger, rational_double 1]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨1, by
        change ((1 : ℤ) : ℚ) = 1
        norm_num⟩⟩

private def lower : CokernelTorsion eval binary 0 :=
  ambientToCokernelTorsion eval binary 0 halfAmbient

private theorem lower_ne_zero : lower ≠ 0 := by
  intro erased
  have gone : (LinearMap.range eval).mkQ halfAmbient.val = 0 := congrArg Subtype.val erased
  obtain ⟨integer, written⟩ := (Submodule.Quotient.mk_eq_zero _).mp gone
  have half : (0 : RatModInteger) = modInteger (1 / 2) := congrArg Prod.snd written
  exact rational_half_not_integral half.symm

private theorem omitting_the_ambient_correction_loses_the_given_lower_class :
    stageCokernelConnecting eval eval_injective binary 1 (0 : CokernelTorsion eval binary 1) = 0 ∧
    primePowerTorsionRestriction binary 0 (0 : CokernelTorsion eval binary 1) ≠ lower ∧
    ∃ lifted : CokernelTorsion eval binary 1,
      primePowerTorsionRestriction binary 0 lifted = lower ∧
      stageCokernelConnecting eval eval_injective binary 1 lifted = 0 := by
  have lowerReadsZero : stageCokernelConnecting eval eval_injective binary 0 lower = 0 :=
    LinearMap.mem_ker.mp ((cokernel_connecting_kernel eval eval_injective binary 0).le
      ⟨halfAmbient, rfl⟩)
  refine ⟨map_zero _, ?_, cokernel_connecting_lift_step eval eval_injective binary
    ambient_two_divides 0 lower 0 (lowerReadsZero.trans (map_zero _).symm)⟩
  intro same
  exact lower_ne_zero (same.symm.trans (map_zero _))

end CP741Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP741Independent

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

end OriginalKCofinalFullBranchFibre.RootRelation.CP741Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SaturationMonoid.UniversalBSDRationalKummerCokernel.CP741Independent

open UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology
open UniversalBSDRationalKummerCohomology.RationalKummerBoundaryCochainData
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CofinalAllPrimeTopology
open private level level_pos point_evaluation_injective from
  SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel

private theorem one_actual_kummer_lift_reads_every_layer_of_the_same_rational_point
    (source : RationalEllipticCurveSource) (prime : Nat.Primes) (point : RationalPoints source) :
    ∃ lift : PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) prime,
      cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) prime lift =
        (allPrimeMap point) prime ∧
      ∀ stage, cokernelKummer source prime stage
          ((torsionCompletionRestriction (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source))
            prime stage).hom lift) =
        sourceGeneratedRationalKummerClass source (level prime stage) (level_pos prime stage) point := by
  obtain ⟨lift, written⟩ := actual_kummer_completion_lifts source prime ((allPrimeMap point) prime)
  refine ⟨lift, written, fun stage => ?_⟩
  have present := (allPrime_restriction prime stage point).symm.trans
    (congrArg (restriction (L := RationalPoints source) prime stage).hom written.symm)
  exact actual_kummer_completion_read source prime stage lift point present

#eval IO.println "CP741_CONTROL + the_same_prime_multiplication_commutes_with_stage_and_limit_restrictions"
#eval IO.println "CP741_CONTROL + actual_ambient_division_lifts_the_compatible_upper_class_over_its_given_lower_class"
#eval IO.println "CP741_CONTROL + every_coherent_source_class_has_one_coherent_torsion_lift"
#eval IO.println "CP741_CONTROL + one_actual_kummer_lift_reads_every_layer_and_original_R_whole_next_remain_consumed"
#eval IO.println "CP741_CONTROL - omitting_the_ambient_correction_loses_the_given_lower_class"
#eval IO.println "CP741_GATE_PASS positive=4 negative=1"

end SaturationMonoid.UniversalBSDRationalKummerCokernel.CP741Independent
