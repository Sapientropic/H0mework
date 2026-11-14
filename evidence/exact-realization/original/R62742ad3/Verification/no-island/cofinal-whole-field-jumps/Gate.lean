import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFactorialField
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP756Independent

open CategoryTheory CofinalAllPrimeTopology SourceGeneratedPrimePowerCompletion

private def signed_representatives_have_the_exact_whole_effect_jump
    {A : Type u} [AddCommGroup A] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (coordinate : A ≃ₗ[ℤ] ℤ) (effect : A →ₗ[ℤ] E) (live : effect (coordinate.symm 1) ≠ 0)
    (value : FactorialCompletion (L := A)) (stage : Nat) :=
  let representative := factorialBalancedLift coordinate value
  let reads := fun address => (factorial_balanced_lift coordinate value address).1
  And.intro (factorial_balanced_lift coordinate value stage) <|
    And.intro (factorial_effect_jump coordinate effect value representative reads stage)
      (factorial_effect_jump_lt_iff coordinate effect live value representative reads stage)

private theorem the_original_signed_diagonal_stabilizes_after_H1
    {A : Type u} [AddCommGroup A] {H : ModuleCat.{u} ℤ}
    (coordinate : A ≃ₗ[ℤ] ℤ) (read : H ≃ₗ[ℤ] FactorialCompletion (L := A)) (source : A) :
    ∃ base : Nat, ∀ stage ≥ base,
      factorialBalancedLift coordinate (read (read.symm (factorialCanonicalMap source))) stage = source := by
  rw [read.apply_symm_apply]
  exact factorial_balanced_diagonal coordinate source

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩
private abbrev ternary : Nat.Primes := ⟨3, Nat.prime_three⟩

private theorem the_isolated_H1_unit_forces_an_arbitrarily_late_whole_jump
    {A : Type u} [AddCommGroup A] {H : ModuleCat.{u} ℤ}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (coordinate : A ≃ₗ[ℤ] ℤ) (unit : A) (unitRead : coordinate unit = 1)
    (read : H ≃ₗ[ℤ] FactorialCompletion (L := A)) (effect : A →ₗ[ℤ] E)
    (raw : E) (writesUnit : effect (coordinate.symm 1) = raw) (liveRaw : raw ≠ 0) (base : Nat) :
    let isolated := factorialFromPrimes (isolatedPrimeUnit coordinate binary)
    let value := read (read.symm isolated)
    (factorialToPrimes value) binary = canonicalLinearMap binary unit ∧
      (factorialToPrimes value) ternary = 0 ∧
      ∃ stage ≥ base, (factorialModulus stage : ℝ)*‖raw‖ ≤
        ‖effect (factorialBalancedLift coordinate value (stage+1)) -
          effect (factorialBalancedLift coordinate value stage)‖ := by
  have separated : ternary ≠ binary := by decide
  have same := (congrArg coordinate.symm unitRead).symm.trans (coordinate.symm_apply_apply unit)
  have live : effect (coordinate.symm 1) ≠ 0 := fun erased => liveRaw (writesUnit.symm.trans erased)
  dsimp only
  rw [read.apply_symm_apply, factorial_to_primes_from_primes]
  refine ⟨(if_pos rfl).trans (congrArg (canonicalLinearMap binary) same), if_neg separated, ?_⟩
  exact (factorial_nonintegral_effect_jumps coordinate effect live _
    (factorial_isolated_prime_unit_outside coordinate separated) base).imp (fun stage result =>
      ⟨result.1, (congrArg (fun x : E => (factorialModulus stage : ℝ)*‖x‖) writesUnit).symm.le.trans result.2⟩)

end CP756Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP756Independent

open CategoryTheory BurnolPhysicalState SourceOperationCompletion SourceOperationScalarInventoryLift CofinalAllPrimeTopology
open OriginalKDirectRCofinalDivision (actual_division_position_gap_mixed_next)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls
  (actual_source_scalar_action_generated actual_born_division_same_whole)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

set_option cleanup.letToHave false in
private def the_original_H1_writes_both_slots_and_the_native_whole_with_exact_Division
    (ordinal stage : Nat) :=
  fun charge small =>
    let spacing := actual_paid_factorial_whole_spacing observation nontrivial half depth ordinal charge stage
    let written := actual_paid_factorial_field_next observation nontrivial half depth ordinal charge small
    let division := actual_division_position_gap_mixed_next observation nontrivial half depth ordinal
    let scalar := actual_source_scalar_action_generated observation nontrivial half depth ordinal
      (1/3 : ℂ) (by norm_num) (by norm_num)
    let independent := actual_born_division_same_whole observation nontrivial half depth ordinal
    PProd.mk spacing.1 <| PProd.mk written.1 <|
      And.intro spacing.2 <| And.intro written.2 <|
      And.intro division.2.2.2.2.1 <| And.intro scalar independent

set_option cleanup.letToHave false in
private def the_original_negative_diagonal_returns_its_signed_source_and_negative_raw (ordinal : Nat) :=
  let read := (actualPaidFactorialHomologyIso observation nontrivial half depth ordinal).toLinearEquiv
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  let unit := sourceClass observation nontrivial half depth ordinal
  let signed := -unit
  let coefficient : coordinate signed = -1 :=
    (map_neg coordinate unit).trans (congrArg (fun n : ℤ => -n)
      (actual_paid_completion_source_unit observation nontrivial half depth ordinal))
  let next : BurnolL2 := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)
  let written := (actual_factorial_whole_source observation nontrivial half depth ordinal signed).trans
    ((congrArg (fun n : ℤ => n • next) coefficient).trans (neg_one_zsmul next))
  And.intro (ConstructiveRoot.CP756Independent.the_original_signed_diagonal_stabilizes_after_H1 coordinate read signed)
    written

set_option cleanup.letToHave false in
private def the_original_R_isolated_binary_unit_forces_late_whole_norm_jumps
    (ordinal base : Nat) :=
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  let unit := sourceClass observation nontrivial half depth ordinal
  let read := (actualPaidFactorialHomologyIso observation nontrivial half depth ordinal).toLinearEquiv
  let whole := factorialWholeAction observation nontrivial half depth ordinal
  let next : BurnolL2 := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)
  ConstructiveRoot.CP756Independent.the_isolated_H1_unit_forces_an_arbitrarily_late_whole_jump coordinate unit
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal) read whole next
    (actual_factorial_whole_unit observation nontrivial half depth ordinal)
    (KernelWrite.NativeDelta.Terminal.actual_raw_ne_zero observation nontrivial half depth (ordinal+1)) base

end OriginalKCofinalFullBranchFibre.RootRelation.CP756Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP756Independent

open CofinalAllPrimeTopology SourceOperationCompletion SourceOperationPaidRelations CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)

set_option cleanup.letToHave false in
private def the_fixed_target_keeps_its_signed_factorial_source_paid_trace_and_terminal
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
  let coordinate := paidCompletionEquiv first prior
  And.intro (factorial_balanced_diagonal coordinate original) <|
    And.intro (factorial_action_canonical action original) <|
    And.intro (actual_actor_cofinal_continuation depth count within prime)
      (TopologyTrace.actual_actor_cofinal_terminal depth prime)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP756Independent

#eval IO.println "CP756_CONTROL + signed_representatives_have_the_exact_whole_effect_jump"
#eval IO.println "CP756_CONTROL + the_original_H1_writes_both_slots_and_the_native_whole_with_exact_Division"
#eval IO.println "CP756_CONTROL + the_original_negative_diagonal_returns_its_signed_source_and_negative_raw"
#eval IO.println "CP756_CONTROL + the_fixed_target_keeps_its_signed_factorial_source_paid_trace_and_terminal"
#eval IO.println "CP756_CONTROL - the_original_R_isolated_binary_unit_forces_late_whole_norm_jumps"
#eval IO.println "CP756_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
