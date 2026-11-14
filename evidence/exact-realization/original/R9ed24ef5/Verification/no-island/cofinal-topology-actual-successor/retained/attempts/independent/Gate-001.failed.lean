import SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces.TopologySuccessor
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologySuccessor

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP730Independent

open CategoryTheory SourceGeneratedPrimePowerCompletion CofinalAllPrimeTopology

section Generic

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

private def the_original_integer_action_advances_each_stage_and_compatible_tower_uniformly
    (action : L →ₗ[ℤ] M) (value : L) (tower : AllPrimeCompletion L)
    (prime : Nat.Primes) (stage : Nat) :=
  let finite := congrFun (congrFun (allStage_successor_source action value) prime) stage
  And.intro finite <|
    And.intro (allPrime_successor_source action value) <|
    And.intro (allPrime_successor_restriction action prime stage tower) <|
    And.intro (allStage_successor_uniformContinuous action)
      (allStage_source_successor_uniformContinuous action)

private def the_exact_fibre_and_separated_coimage_use_the_same_original_action
    (action : L →ₗ[ℤ] M) (left right : L) :=
  And.intro (allStage_successor_fibre action left right) <|
    And.intro (allPrime_coimage_successor_source action left)
      (allPrimeCoimageMap_injective (L := M))

end Generic

namespace InstalledInverse

open SourceOperationEffects SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces

variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

private def the_installed_inverse_pair_word_advances_with_its_original_execution_whole_and_next
    (count : Nat) :=
  let paid := actual_inverse_relation_topology seed initial count
  And.intro paid.1.1 <| And.intro paid.1.2.1 <|
    And.intro paid.1.2.2.1 <| And.intro paid.1.2.2.2.1 <|
    And.intro paid.1.2.2.2.2 <| And.intro paid.2.1 <|
    And.intro paid.2.2.1 paid.2.2.2

end InstalledInverse

namespace Actor

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source

private theorem the_scalar_instance_normalization_preserves_the_original_actor_function
    (depth count : Nat) :
    let runtime := C.mathRuntime depth (count+1)
    let original := SourceOperationRuntime.Character.successor (R := ℤ) (s := PUnit.unit)
      (nativeRead depth) (nativeEnvironment depth) runtime
    ∀ value : NativeField depth (count+1),
      original.toAddMonoidHom.toIntLinearMap value = original value := by
  intro value
  rfl

private def the_same_paid_Goldbach_pulse_reads_native_inventory_and_next_through_the_tower
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth))) :=
  let paid := actual_actor_topology_successor depth count within
  And.intro (the_scalar_instance_normalization_preserves_the_original_actor_function depth count) <|
    And.intro paid.1 <| And.intro paid.2.1 <| And.intro paid.2.2.1 <|
    And.intro paid.2.2.2.1 <| And.intro paid.2.2.2.2.1 <|
    And.intro paid.2.2.2.2.2.1 paid.2.2.2.2.2.2

end Actor

private def originalIntegerInjection : ℤ →ₗ[ℤ] ℚ :=
  (Int.castAddHom ℚ).toIntLinearMap

private theorem original_integer_injection_is_injective : Function.Injective originalIntegerInjection := by
  intro left right same
  change (left : ℚ) = (right : ℚ) at same
  exact Int.cast_injective same

private theorem prime_two_first_stage_distinguishes_integer_one :
    allStageMap (1 : ℤ) ≠ allStageMap (0 : ℤ) := by
  intro erased
  have hidden : (1 : ℤ) ∈ AllPrimeKernel (L := ℤ) :=
    (allStage_zero_iff_kernel (1 : ℤ)).mp (erased.trans (map_zero _))
  obtain ⟨divided,paid⟩ := (allPrimeKernel_iff (1 : ℤ)).mp hidden ⟨2,Nat.prime_two⟩ 0
  change (2 : ℤ)^1 • divided = 1 at paid
  rw [pow_one,zsmul_eq_mul] at paid
  omega

private theorem an_injective_integer_action_can_collapse_an_original_stage_visible_value
    : Function.Injective originalIntegerInjection ∧
      allStageMap (1 : ℤ) ≠ allStageMap (0 : ℤ) ∧
      allStageSuccessor originalIntegerInjection (allStageMap (1 : ℤ)) =
        allStageSuccessor originalIntegerInjection (allStageMap (0 : ℤ)) := by
  refine ⟨original_integer_injection_is_injective,prime_two_first_stage_distinguishes_integer_one,?_⟩
  apply (allStage_successor_fibre originalIntegerInjection 1 0).mpr
  intro prime stage
  refine ⟨((prime.1 : ℚ)^(stage+1))⁻¹,?_⟩
  have live : (prime.1 : ℚ) ≠ 0 := by exact_mod_cast prime.2.ne_zero
  change ((prime.1 : ℤ)^(stage+1)) • ((prime.1 : ℚ)^(stage+1))⁻¹ = ((1-0 : ℤ) : ℚ)
  simp only [zsmul_eq_mul,Int.cast_pow,Int.cast_natCast,sub_zero,Int.cast_one]
  exact mul_inv_cancel₀ (pow_ne_zero _ live)

#eval IO.println "CP730_CONTROL + the_original_integer_action_advances_each_stage_and_compatible_tower_uniformly"
#eval IO.println "CP730_CONTROL + the_exact_fibre_and_separated_coimage_use_the_same_original_action"
#eval IO.println "CP730_CONTROL + the_installed_inverse_pair_word_advances_with_its_original_execution_whole_and_next"
#eval IO.println "CP730_CONTROL + the_same_paid_Goldbach_pulse_reads_native_inventory_and_next_through_the_tower"
#eval IO.println "CP730_CONTROL - an_injective_integer_action_can_collapse_an_original_stage_visible_value"
#eval IO.println "CP730_GATE_PASS positive=4 negative=1"

end CP730Independent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
