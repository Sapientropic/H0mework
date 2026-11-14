import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFactorialCompletion
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP753Independent

open CategoryTheory CategoryTheory.Limits CofinalAllPrimeTopology SourceGeneratedPrimePowerCompletion
open scoped Pointwise
open private principal_smul_top from SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus

private def every_positive_modulus_reads_its_actual_factorization_and_divisibility_arrow
    {L : Type u} [AddCommGroup L] {lower upper : Nat} (lowerLive : lower ≠ 0) (upperLive : upper ≠ 0)
    (written : lower ∣ upper) (source : L) (family : AllPrimeCompletion L) :=
  And.intro (composite_modulus_factorization lowerLive) <|
    And.intro (modulus_read_naturality lowerLive upperLive written family) <|
    And.intro (modulus_map_projection written source)
      (modulus_projection_eq_iff upper upperLive source family)

private def the_entire_factorial_and_prime_limits_restore_both_ways_and_transport_the_original_action
    {L M : Type u} [AddCommGroup L] [AddCommGroup M]
    (family : AllPrimeCompletion L) (coherent : FactorialCompletion (L := L)) (source : L)
    (action : L →ₗ[ℤ] M) (prime : Nat.Primes) (stage address : Nat)
    (written : prime.val^(stage+1) ∣ factorialModulus address) :=
  let read := factorialCompletionEquiv (L := L)
  And.intro (read.symm_apply_apply family) <| And.intro (read.apply_symm_apply coherent) <|
    And.intro (factorial_from_primes_restriction address family) <|
    And.intro (factorial_to_primes_restriction prime stage address written coherent) <|
    And.intro (factorial_from_primes_canonical source) <|
    And.intro (factorial_canonical_restriction address source)
      (factorial_action_readback action family)

private theorem one_is_visible_at_the_literal_factorial_modulus_two :
    modulusProjection (L := ℤ) (factorialModulus 1) 1 ≠ 0 := by
  intro erased
  have inRange := (Submodule.Quotient.mk_eq_zero _).mp erased
  change (1 : ℤ) ∈ Ideal.span {(2 : ℤ)} • (⊤ : Submodule ℤ ℤ) at inRange
  rw [principal_smul_top] at inRange
  obtain ⟨divided, paid⟩ := inRange
  change (2 : ℤ) • divided = 1 at paid
  rw [zsmul_eq_mul] at paid
  have impossible (value : ℤ) : 2 * value ≠ 1 := by omega
  exact impossible divided paid

private theorem the_literal_factorial_arrow_forbids_mod_two_one_and_mod_six_zero
    (value : FactorialCompletion (L := ℤ)) :
    ¬ ((factorialRestriction (L := ℤ) 1).hom value =
          modulusProjection (L := ℤ) (factorialModulus 1) 1 ∧
        (factorialRestriction (L := ℤ) 2).hom value =
          modulusProjection (L := ℤ) (factorialModulus 2) 0) := by
  rintro ⟨modTwo,modSix⟩
  let ordered : (1 : Nat) ≤ 2 := by decide
  let edge := (homOfLE ordered).op
  have written := ConcreteCategory.congr_hom (limit.w (factorialTower (L := ℤ)) edge) value
  change ((factorialTower (L := ℤ)).map edge).hom ((factorialRestriction (L := ℤ) 2).hom value) =
    (factorialRestriction (L := ℤ) 1).hom value at written
  rw [modSix,modTwo] at written
  have erased := (factorial_edge_projection (L := ℤ) ordered (0 : ℤ)).symm.trans written
  exact one_is_visible_at_the_literal_factorial_modulus_two (erased.symm.trans (map_zero _))

end CP753Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP753Independent

open SourceOperationScalarInventoryLift CofinalAllPrimeTopology
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

open private paidEvaluation from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

set_option cleanup.letToHave false in
private def the_original_R_family_keeps_each_paid_charge_Division_K_and_literal_whole_next
    (ordinal : Nat) (family : AllPrimeCokernel (paidEvaluation observation nontrivial half depth ordinal)) :=
  let paid := actual_paid_factorial_next observation nontrivial half depth ordinal family
  PProd.mk paid.1 <| And.intro paid.2 <|
    And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1
      (actual_original_K_read observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.RootRelation.CP753Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP753Independent

open CofinalAllPrimeTopology SourceOperationCompletion SourceOperationPaidRelations CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)

set_option cleanup.letToHave false in
private def the_fixed_target_transports_its_original_paid_trace_through_the_factorial_limit
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth))) (prime : Nat.Primes) :=
  let runtime := C.mathRuntime depth (count+1)
  let prior := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).2
  let later := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime.tick.next).2
  let first := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let next := RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence
  let retained := tick_paid_prefix (R.old depth) (R.origin depth) (R.reader depth) runtime
  let before := prefixHistory first (exposure prior)
  let after := prefixHistory next (exposure later)
  let action := (continuationTransition first next retained).completionMap before after
  let original := before.completionProjection (terminalGenerator first prior)
  let family := allPrimeMap original
  And.intro (factorial_from_primes_canonical original) <|
    And.intro (factorial_action_readback action family) <|
    And.intro (actual_actor_cofinal_continuation depth count within prime)
      (TopologyTrace.actual_actor_cofinal_terminal depth prime)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP753Independent

#eval IO.println "CP753_CONTROL + every_positive_modulus_reads_its_actual_factorization_and_divisibility_arrow"
#eval IO.println "CP753_CONTROL + the_entire_factorial_and_prime_limits_restore_both_ways_and_transport_the_original_action"
#eval IO.println "CP753_CONTROL + the_original_R_family_keeps_each_paid_charge_Division_K_and_literal_whole_next"
#eval IO.println "CP753_CONTROL + the_fixed_target_transports_its_original_paid_trace_through_the_factorial_limit"
#eval IO.println "CP753_CONTROL - the_literal_factorial_arrow_forbids_mod_two_one_and_mod_six_zero"
#eval IO.println "CP753_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
