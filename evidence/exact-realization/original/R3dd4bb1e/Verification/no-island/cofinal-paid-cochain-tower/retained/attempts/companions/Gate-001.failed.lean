import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCofinalCochain
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP749Independent

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion

private def the_coherent_map_is_the_universal_lift_of_original_stage_actions
    {I : Type v} (shape : ComplexShape I) (p : Nat.Primes)
    {source target : HomologicalComplex AddCommGrpCat.{u} shape}
    (f : source ⟶ target) (cone : Cone (cochainStageTower shape p target))
    (candidate : cone.pt ⟶ (cochainCompletionCone shape p target).pt)
    (agrees : ∀ j, candidate ≫ (cochainCompletionCone shape p target).π.app j = cone.π.app j) :=
  let limit := cochainCompletionIsLimit shape p target
  And.intro (limit.uniq cone candidate agrees) (cochain_completion_map_from_tower shape p f)

private abbrev binary : Nat.Primes := ⟨2,Nat.prime_two⟩

private def integerInclusion : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℚ :=
  AddCommGrpCat.ofHom (Int.castAddHom ℚ)

private theorem an_injective_action_erases_a_nonzero_original_stage_charge :
    Function.Injective integerInclusion ∧
      stageProjection (L := ℤ) binary 0 1 ≠ 0 ∧
      (stageFunctor binary 0).map integerInclusion (stageProjection (L := ℤ) binary 0 1) = 0 := by
  refine ⟨?_,?_,?_⟩
  · intro left right equal
    change (left : ℚ) = (right : ℚ) at equal
    exact Int.cast_injective equal
  · intro erased
    change (powerRange (L := ℤ) binary 0).mkQ 1 = 0 at erased
    obtain ⟨divided, paid⟩ := (Submodule.Quotient.mk_eq_zero _).mp erased
    change (2 : ℤ)^1 • divided = 1 at paid
    rw [pow_one, zsmul_eq_mul] at paid
    omega
  · let action : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap
    change stageMap binary 0 action (stageProjection (L := ℤ) binary 0 1) = 0
    rw [← LinearMap.comp_apply, stageMap_projection, LinearMap.comp_apply]
    change (powerRange (L := ℚ) binary 0).mkQ 1 = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨(1/2 : ℚ),?_⟩
    change (2 : ℤ)^1 • (1/2 : ℚ) = 1
    norm_num [zsmul_eq_mul]

end CP749Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP749Independent

open CofinalRelationGeneratedComplex SourceOperationScalarInventoryLift
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def all_four_original_R_stages_read_the_two_limits_and_the_paid_whole :
    ∀ (ordinal : Nat) (index : Fin 4) (p : Nat.Primes) (j : Nat),
      type_of% (actual_paid_cochain_continuation observation nontrivial half depth ordinal
        (Fin.cast (actual_paid_stage_count observation nontrivial half depth ordinal).symm index) p j) :=
  fun ordinal index p j =>
    let paid := actual_paid_cochain_continuation observation nontrivial half depth ordinal
      (Fin.cast (actual_paid_stage_count observation nontrivial half depth ordinal).symm index) p j
    PProd.mk (paid.1.1, paid.1.2) <|
      And.intro paid.2.1 <| And.intro paid.2.2.1 <| And.intro paid.2.2.2.1 <|
        And.intro paid.2.2.2.2.1 paid.2.2.2.2.2

private def independent_original_R_Division_K_and_literal_model_next
    (ordinal : Nat) (p : Nat.Primes) (coefficient : ℤ) :=
  And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1 <|
    And.intro (actual_original_K_read observation nontrivial half depth ordinal) <|
    And.intro (actual_root_relation_consumer observation nontrivial half depth ordinal)
      (actual_paid_syntax_model_next observation nontrivial half depth ordinal p coefficient)

end OriginalKCofinalFullBranchFibre.RootRelation.CP749Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP749Independent

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)
open SourceOperationCompletion

private def the_fixed_target_reads_its_original_cochain_and_terminal
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth))) (p : Nat.Primes) :=
  let runtime := C.mathRuntime depth (count+1)
  let prior := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).2
  let next := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime.tick.next).2
  let firstRoot := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let nextRoot := RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence
  let retained := tick_paid_prefix (R.old depth) (R.origin depth) (R.reader depth) runtime
  And.intro (continuation_cochain_from_tower firstRoot prior nextRoot next retained p) <|
    And.intro (actual_actor_cofinal_continuation depth count within p)
      (TopologyTrace.actual_actor_cofinal_terminal depth p)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP749Independent

#eval IO.println "CP749_CONTROL + the_coherent_map_is_the_universal_lift_of_original_stage_actions"
#eval IO.println "CP749_CONTROL + all_four_original_R_stages_read_the_two_limits_and_the_paid_whole"
#eval IO.println "CP749_CONTROL + independent_original_R_Division_K_and_literal_model_next"
#eval IO.println "CP749_CONTROL + the_fixed_target_reads_its_original_cochain_and_terminal"
#eval IO.println "CP749_CONTROL - an_injective_action_erases_a_nonzero_original_stage_charge"
#eval IO.println "CP749_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
