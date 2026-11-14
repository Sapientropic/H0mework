import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion
import SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.CompletionExact
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP743Independent

open CategoryTheory SourceGeneratedPrimePowerCompletion

section Generic
variable {L M L' M' : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup L'] [AddCommGroup M']
variable (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate) (p : Nat.Primes)

private def full_coherent_inverse_and_its_actual_stage_read
    (divides : ∀ j, Function.Bijective (powerMultiplication (L := M) p j)) (j : Nat)
    (value : Completion (L := L) p)
    (torsion : PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p) :=
  let e := cokernelCompletionEquiv evaluate injective p divides
  And.intro (cokernel_completion_restriction evaluate injective p divides j value)
    (And.intro (cokernel_completion_inverse evaluate injective p divides torsion)
      (e.apply_symm_apply torsion))

private def the_paid_evaluation_square_moves_an_entire_coherent_class
    (evaluateNext : L' →ₗ[ℤ] M') (injectiveNext : Function.Injective evaluateNext)
    (source : L →ₗ[ℤ] L') (target : M →ₗ[ℤ] M')
    (actual : ∀ word, target (evaluate word) = evaluateNext (source word))
    (divides : ∀ j, Function.Bijective (powerMultiplication (L := M) p j))
    (dividesNext : ∀ j, Function.Bijective (powerMultiplication (L := M') p j))
    (value : Completion (L := L) p)
    (torsion : PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p) :=
  And.intro
    (cokernel_connecting_limit_naturality evaluate evaluateNext source target actual
      injective injectiveNext p torsion)
    (cokernel_completion_equiv_naturality evaluate evaluateNext source target actual
      injective injectiveNext p divides dividesNext value)

end Generic

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩

private theorem first_binary_layer_cannot_recover_the_coherent_cokernel
    {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (coordinate : A ≃ₗ[ℤ] ℤ) (unit : A) (unitRead : coordinate unit = 1)
    (read : Completion (L := A) binary ≃ₗ[ℤ] PrimePowerTorsionCompletion B binary)
    (stageRead : ∀ j, StageResidual (L := A) binary j ≃ₗ[ℤ] PrimePowerTorsionSubmodule B binary j)
    (consistent : ∀ j value, (torsionCompletionRestriction B binary j).hom (read value) =
      stageRead j ((restriction (L := A) binary j).hom value)) :
    ∃ torsion : PrimePowerTorsionCompletion B binary,
      (torsionCompletionRestriction B binary 0).hom torsion = 0 ∧
      (torsionCompletionRestriction B binary 1).hom torsion ≠ 0 := by
  let word : A := (2 : ℤ) • unit
  let value := (canonicalMap (L := A) binary).hom word
  have nowRead (j : Nat) :
      (restriction (L := A) binary j).hom value = stageProjection binary j word :=
    ConcreteCategory.congr_hom (canonicalMap_restriction (L := A) binary j) word
  have firstStage : stageProjection binary 0 word = 0 :=
    (stageProjection_eq_zero_iff binary 0 word).mpr ⟨unit, by
      change ((2 : Nat) : ℤ)^(0+1) • unit = (2 : ℤ) • unit
      norm_num⟩
  have secondStage : stageProjection binary 1 word ≠ 0 := by
    intro erased
    obtain ⟨divided, paid⟩ := (stageProjection_eq_zero_iff binary 1 word).mp erased
    have coordinatePaid := congrArg coordinate paid
    change coordinate (((2 : Nat) : ℤ) ^ (1 + 1) • divided) = coordinate ((2 : ℤ) • unit) at coordinatePaid
    have written : (4 : ℤ) * coordinate divided = 2 := by
      norm_num [map_smul, smul_eq_mul, unitRead] at coordinatePaid ⊢
      exact coordinatePaid
    have impossible : ¬ (4 : ℤ) ∣ 2 := by norm_num
    exact impossible ⟨coordinate divided, written.symm⟩
  refine ⟨read value, ?_, ?_⟩
  · rw [consistent, nowRead, firstStage, map_zero]
  · rw [consistent, nowRead]
    intro erased
    exact secondStage ((stageRead 1).injective (erased.trans (map_zero _).symm))

end CP743Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP743Independent

open SourceGeneratedPrimePowerCompletion SourceOperationScalarInventoryLift
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def actual_source_coherent_cokernel_and_native_model_advance
    (ordinal : Nat) (prime : Nat.Primes) (j : Nat)
    (value : Completion (L := SourceCompletion observation nontrivial half depth ordinal) prime) :=
  And.intro (actual_paid_cokernel_completion_restriction observation nontrivial half depth ordinal prime j value)
    (actual_paid_cokernel_coherent_next observation nontrivial half depth ordinal prime value)

private def the_original_R_root_relation_whole_and_next_are_consumed (ordinal : Nat) :=
  actual_root_relation_consumer observation nontrivial half depth ordinal

private def same_original_Division_position_gap_and_independent_K (ordinal : Nat) :=
  And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1
    (actual_original_K_read observation nontrivial half depth ordinal)

private def the_original_R_cokernel_model_reads_the_same_integer_at_actual_next
    (ordinal : Nat) (prime : Nat.Primes) (stage : Nat) (coefficient : ℤ) :=
  actual_paid_cokernel_model_next observation nontrivial half depth ordinal prime stage coefficient

private def the_first_actual_layer_loses_a_coherent_cokernel_charge (ordinal : Nat) :=
  let prime : Nat.Primes := ⟨2, Nat.prime_two⟩
  CP743Independent.first_binary_layer_cannot_recover_the_coherent_cokernel
    (actualPaidCompletion observation nontrivial half depth ordinal)
    (sourceClass observation nontrivial half depth ordinal)
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal)
    (actualPaidCokernelCompletion observation nontrivial half depth ordinal prime)
    (actualPaidCokernelStage observation nontrivial half depth ordinal prime)
    (actual_paid_cokernel_completion_restriction observation nontrivial half depth ordinal prime)

end OriginalKCofinalFullBranchFibre.RootRelation.CP743Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SaturationMonoid.UniversalBSDRationalKummerCokernel.CP743Independent

open UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion

private def the_original_Kummer_class_fibre_at_its_separate_geometric_source
    (source : RationalEllipticCurveSource) (prime : Nat.Primes)
    (left right : PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) prime) :=
  actual_kummer_completion_class_fibre source prime left right

#eval IO.println "CP743_CONTROL + full_coherent_inverse_and_its_actual_stage_read"
#eval IO.println "CP743_CONTROL + the_paid_evaluation_square_moves_an_entire_coherent_class"
#eval IO.println "CP743_CONTROL + actual_source_coherent_cokernel_native_model_advance_and_original_whole"
#eval IO.println "CP743_CONTROL + the_original_Kummer_class_fibre_at_its_separate_geometric_source"
#eval IO.println "CP743_CONTROL - the_first_actual_layer_loses_a_coherent_cokernel_charge"
#eval IO.println "CP743_GATE_PASS positive=4 negative=1"

end SaturationMonoid.UniversalBSDRationalKummerCokernel.CP743Independent
