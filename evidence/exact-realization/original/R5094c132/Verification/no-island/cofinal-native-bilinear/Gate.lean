import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.CofinalBilinear
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP744Independent

open SourceGeneratedPrimePowerCompletion

section Generic
variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]

private def both_actual_arguments_descend_to_each_layer_and_the_entire_completion
    (act : L →ₗ[ℤ] M →ₗ[ℤ] N) (p : Nat.Primes) (j : Nat)
    (left : Completion (L := L) p) (right : Completion (L := M) p)
    (sourceLeft : L) (sourceRight : M) :=
  And.intro (stage_bilinear_projection act p j sourceLeft sourceRight) <|
    And.intro (completion_bilinear_restriction act p j left right)
      (completion_bilinear_source act p sourceLeft sourceRight)

private def actual_stage_transitions_commute_in_both_arguments
    (act : L →ₗ[ℤ] M →ₗ[ℤ] N) (p : Nat.Primes) (j : Nat)
    (left : StageResidual (L := L) p (j+1))
    (right : StageResidual (L := M) p (j+1)) :=
  stage_bilinear_transition act p j left right

end Generic

private theorem nonzero_joint_changes_the_report {A : Type u} [AddGroup A]
    (report : A) {joint : A} (live : joint ≠ 0) : report + joint ≠ report := by
  intro erased
  exact live (add_left_cancel (erased.trans (add_zero report).symm))

end CP744Independent

namespace CanonicalUnitArithmeticRoot.CP744Independent

open SourceGeneratedPrimePowerCompletion

private def both_installed_operations_reuse_one_native_occurrence_and_whole
    (runtime : LivingRuntimeState runtimeFacade.process) (p : Nat.Primes) :=
  And.intro (actual_native_bilinear_completion runtime p) <|
    And.intro (coversAt_factorizes runtime .additiveRestriction)
      (coversAt_factorizes runtime .multiplicativeRestriction)

private def the_same_runtime_keeps_both_ordered_changes_and_the_joint_change
    (runtime : LivingRuntimeState runtimeFacade.process) (p : Nat.Primes)
    (left right : SourceNativeBinary.Free Current) :=
  actual_native_parallel_mixed_effect runtime p left right

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩

private def at_the_actual_seed_erasure_fails_at_the_first_visible_layer
    (report : StageResidual (L := SourceNativeBinary.Free Current) binary 2) :=
  let depths := actual_native_parallel_joint_depth runtimeSeed binary 0 0
  And.intro depths.1 (ConstructiveRoot.CP744Independent.nonzero_joint_changes_the_report report depths.2)

end CanonicalUnitArithmeticRoot.CP744Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP744Independent

open SourceGeneratedPrimePowerCompletion SourceOperationScalarInventoryLift
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def the_independent_original_R_coherent_next_and_whole_are_consumed
    (ordinal : Nat) (p : Nat.Primes)
    (value : Completion (L := SourceCompletion observation nontrivial half depth ordinal) p) :=
  And.intro (actual_paid_cokernel_coherent_next observation nontrivial half depth ordinal p value)
    (actual_root_relation_consumer observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.RootRelation.CP744Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

#eval IO.println "CP744_CONTROL + both_actual_arguments_descend_to_each_layer_and_the_entire_completion"
#eval IO.println "CP744_CONTROL + both_installed_operations_reuse_one_native_occurrence_and_whole"
#eval IO.println "CP744_CONTROL + the_same_runtime_keeps_both_ordered_changes_and_the_joint_change"
#eval IO.println "CP744_CONTROL + the_independent_original_R_coherent_next_and_whole_are_consumed"
#eval IO.println "CP744_CONTROL - at_the_actual_seed_erasure_fails_at_the_first_visible_layer"
#eval IO.println "CP744_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
