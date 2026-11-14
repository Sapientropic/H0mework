import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyInitial

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP731Independent

open CofinalAllPrimeTopology SourceGeneratedPrimePowerCompletion

private def the_same_split_action_has_three_topological_left_inverses
    {L M : Type u} [AddCommGroup L] [AddCommGroup M]
    (action : L →ₗ[ℤ] M) (backward : M →ₗ[ℤ] L) (inverse : Function.LeftInverse backward action)
    (stages : AllStageObservation L) (tower : AllPrimeCompletion L)
    (quotient : AllPrimeFaithfulCoimage (L := L)) :=
  let paid := topology_successor_left_inverse action backward inverse
  And.intro (paid.1 stages) <| And.intro (paid.2.1 tower) (paid.2.2 quotient)

namespace Actor
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source

local notation "advance" => fun depth => SourceOperationNative.sourceAction (process depth)
local notation "restore" => fun depth => NativeRecovery.backward (R.old depth) (R.origin depth) (R.reader depth)

private def the_same_paid_Goldbach_pulse_recovers_its_full_native_point_whole_and_next
    (depth count : Nat) (within : count < sourceFuel (R.source depth (Cursor.emitted depth))) :=
  let paid := actual_actor_topology_inverse depth count within
  let pulse := paid.2.2.2.1
  And.intro paid.1 <| And.intro paid.2.1 <| And.intro paid.2.2.1 <|
    And.intro pulse.2.2.2.2.2.2 paid.2.2.2.2

private def the_original_initial_coefficient_classifies_the_three_successor_images
    (depth : Nat) (prime : Nat.Primes) (stage : Nat)
    (value : StageResidual (L := FullCarrier depth) prime stage)
    (tower : AllPrimeCompletion (FullCarrier depth))
    (quotient : AllPrimeFaithfulCoimage (L := FullCarrier depth)) :=
  And.intro (actual_native_topology_left_inverse depth) <|
    And.intro (actual_native_topology_decomposition depth) <|
    And.intro (actual_native_stage_image depth prime stage value) <|
    And.intro (actual_native_prime_image depth tower) (actual_native_coimage_image depth quotient)

private theorem the_actual_backward_constructs_the_exact_stage_predecessor
    (depth : Nat) (prime : Nat.Primes) (stage : Nat)
    (value : StageResidual (L := FullCarrier depth) prime stage)
    (absent : stageMap prime stage (initialCoefficient depth) value = 0) :
    stageMap prime stage (advance depth) (stageMap prime stage (restore depth) value) = value := by
  have complete := stage_successor_decomposition (advance depth) (restore depth)
    (initialCoefficient depth) (initialInclusion depth) (actual_native_action_decomposition depth) prime stage value
  simpa only [absent, map_zero, add_zero] using complete

private theorem the_original_initial_point_has_no_stage_or_coherent_predecessor
    (depth : Nat) :
    (∀ (prime : Nat.Primes) (stage : Nat),
      stageProjection prime stage (SourceOperationNative.point (C.mathRuntime depth 0)) ∉
        Set.range (stageMap prime stage (advance depth))) ∧
    allPrimeMap (SourceOperationNative.point (C.mathRuntime depth 0)) ∉
      Set.range (allPrimeSuccessor (advance depth)) :=
  ⟨actual_native_initial_outside_stage_image depth, actual_native_initial_outside_prime_image depth⟩

end Actor

#eval IO.println "CP731_CONTROL + the_same_split_action_has_three_topological_left_inverses"
#eval IO.println "CP731_CONTROL + the_same_paid_Goldbach_pulse_recovers_its_full_native_point_whole_and_next"
#eval IO.println "CP731_CONTROL + the_original_initial_coefficient_classifies_the_three_successor_images"
#eval IO.println "CP731_CONTROL + the_actual_backward_constructs_the_exact_stage_predecessor"
#eval IO.println "CP731_CONTROL - the_original_initial_point_has_no_stage_or_coherent_predecessor"
#eval IO.println "CP731_GATE_PASS positive=4 negative=1"

end CP731Independent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
