import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFiniteModulus
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP752Independent

open CofinalAllPrimeTopology SourceGeneratedPrimePowerCompletion

private def the_exact_composite_fibre_and_equivalence_read_every_selected_coordinate
    {L : Type u} [AddCommGroup L] (primes : Finset Nat.Primes) (level : primes → Nat)
    (left right : L) (family : (p : primes) → StageResidual (L := L) p.val (level p)) :=
  let read := finitePrimeEquiv (L := L) primes level
  And.intro (finite_prime_fibre primes level left right) <|
    And.intro (read.apply_symm_apply family) (finite_prime_equiv_projection primes level left)

private def the_bounded_representative_is_unique_and_reads_lower_and_acted_coordinates
    {L M : Type u} [AddCommGroup L] [AddCommGroup M]
    (primes : Finset Nat.Primes) (level : primes → Nat) (coordinate : L ≃ₗ[ℤ] ℤ)
    (value : AllPrimeCompletion L) (candidate : L)
    (candidateBounds : 0 ≤ coordinate candidate ∧ coordinate candidate < compositeModulus primes level)
    (candidateReads : finitePrimeProjection primes level candidate = finitePrimeRestriction primes level value)
    (action : L →ₗ[ℤ] M) (p : primes) (lower : Nat) (within : lower ≤ level p) :=
  let source := finitePrimeIntegralLift primes level coordinate value
  let normalized := finite_prime_integral_lift primes level coordinate value
  And.intro (finite_prime_integral_unique primes level coordinate candidateBounds normalized.2
    (candidateReads.trans normalized.1.symm)) <|
    And.intro (finite_prime_lift_lower primes level value p lower within)
      (finite_prime_successor primes level action value source normalized.1)

private abbrev binary : Nat.Primes := ⟨2,Nat.prime_two⟩
private abbrev ternary : Nat.Primes := ⟨3,Nat.prime_three⟩

private theorem a_paid_unit_loses_its_ternary_coordinate_when_only_binary_is_kept
    {L : Type u} [AddCommGroup L] (coordinate : L ≃ₗ[ℤ] ℤ) (unit : L) (unitRead : coordinate unit = 1) :
    let two : Finset Nat.Primes := {binary}
    let both : Finset Nat.Primes := insert ternary two
    finitePrimeProjection two (fun _ => 1) ((4 : ℤ) • unit) = finitePrimeProjection two (fun _ => 1) 0 ∧
      finitePrimeProjection both (fun _ => 1) ((4 : ℤ) • unit) ≠ finitePrimeProjection both (fun _ => 1) 0 := by
  let two : Finset Nat.Primes := {binary}
  let both : Finset Nat.Primes := insert ternary two
  let word : L := (4 : ℤ) • unit
  change finitePrimeProjection two (fun _ => 1) word = finitePrimeProjection two (fun _ => 1) 0 ∧
    finitePrimeProjection both (fun _ => 1) word ≠ finitePrimeProjection both (fun _ => 1) 0
  have modFour : stageProjection binary 1 word = 0 := by
    apply (stageProjection_eq_zero_iff binary 1 word).mpr
    refine ⟨unit,?_⟩
    change ((2 : Nat) : ℤ)^(1+1) • unit = (4 : ℤ) • unit
    norm_num
  have modNine : stageProjection ternary 1 word ≠ 0 := by
    intro erased
    obtain ⟨divided,paid⟩ := (stageProjection_eq_zero_iff ternary 1 word).mp erased
    have reads := congrArg coordinate paid
    change coordinate (((3 : Nat) : ℤ)^(1+1) • divided) = coordinate ((4 : ℤ) • unit) at reads
    have written : (9 : ℤ) * coordinate divided = 4 := by
      norm_num [map_smul,smul_eq_mul,unitRead] at reads ⊢
      exact reads
    have impossible (value : ℤ) : 9 * value ≠ 4 := by omega
    exact impossible (coordinate divided) written
  constructor
  · funext p
    have only : p = ⟨binary,Finset.mem_singleton_self binary⟩ :=
      Subtype.ext (Finset.mem_singleton.mp p.property)
    subst p
    change stageProjection binary 1 word = stageProjection binary 1 0
    exact modFour.trans (map_zero _).symm
  · intro same
    let atThree : both := ⟨ternary,by exact Finset.mem_insert_self _ _⟩
    have read := congrFun same atThree
    change stageProjection ternary 1 word = stageProjection ternary 1 0 at read
    exact modNine (read.trans (map_zero _))

end CP752Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP752Independent

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
private def the_complete_original_R_family_advances_one_charge_with_the_native_square_and_whole
    (ordinal : Nat) (primes : Finset Nat.Primes) (level : primes → Nat)
    (family : AllPrimeCokernel (paidEvaluation observation nontrivial half depth ordinal)) :=
  let paid := actual_paid_finite_charge_next observation nontrivial half depth ordinal primes level family
  let same : paid.1 = actualPaidFiniteCharge observation nontrivial half depth ordinal primes level family := rfl
  PProd.mk paid.1 <| And.intro same <| And.intro paid.2 <|
    And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1
      (actual_original_K_read observation nontrivial half depth ordinal)

private def deleting_prime_three_changes_the_original_R_finite_charge_read (ordinal : Nat) :=
  ConstructiveRoot.CP752Independent.a_paid_unit_loses_its_ternary_coordinate_when_only_binary_is_kept
    (actualPaidCompletion observation nontrivial half depth ordinal)
    (sourceClass observation nontrivial half depth ordinal)
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.RootRelation.CP752Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP752Independent

open CofinalAllPrimeTopology SourceOperationCompletion SourceOperationPaidRelations CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)

set_option cleanup.letToHave false in
private def the_fixed_target_acts_on_the_finite_read_of_its_actual_paid_trace_and_terminal
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth)))
    (primes : Finset Nat.Primes) (level : primes → Nat) (prime : Nat.Primes) :=
  let runtime := C.mathRuntime depth (count+1)
  let prior := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).2
  let later := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime.tick.next).2
  let first := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let next := RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence
  let retained := tick_paid_prefix (R.old depth) (R.origin depth) (R.reader depth) runtime
  let before := prefixHistory first (exposure prior)
  let after := prefixHistory next (exposure later)
  let action := (continuationTransition first next retained).completionMap before after
  let coordinate := paidCompletionEquiv first prior
  let value := allPrimeMap (before.completionProjection (terminalGenerator first prior))
  let charge := finitePrimeIntegralLift primes level coordinate value
  let bounded := finite_prime_integral_lift primes level coordinate value
  And.intro bounded <| And.intro (finite_prime_successor primes level action value charge bounded.1) <|
    And.intro (actual_actor_cofinal_continuation depth count within prime)
      (TopologyTrace.actual_actor_cofinal_terminal depth prime)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP752Independent

#eval IO.println "CP752_CONTROL + the_exact_composite_fibre_and_equivalence_read_every_selected_coordinate"
#eval IO.println "CP752_CONTROL + the_bounded_representative_is_unique_and_reads_lower_and_acted_coordinates"
#eval IO.println "CP752_CONTROL + the_complete_original_R_family_advances_one_charge_with_the_native_square_and_whole"
#eval IO.println "CP752_CONTROL + the_fixed_target_acts_on_the_finite_read_of_its_actual_paid_trace_and_terminal"
#eval IO.println "CP752_CONTROL - deleting_prime_three_changes_the_original_R_finite_charge_read"
#eval IO.println "CP752_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
