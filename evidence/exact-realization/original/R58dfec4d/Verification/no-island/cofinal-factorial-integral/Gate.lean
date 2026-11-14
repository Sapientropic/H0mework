import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFactorialIntegral
import SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.BoundedFactorial
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP755Independent

open CategoryTheory CofinalAllPrimeTopology SourceGeneratedPrimePowerCompletion

private def the_fixed_inventory_eventually_reads_the_entire_factorial_fibre
    {A : Type u} [AddCommGroup A] (inventory : Finset A)
    (value : FactorialCompletion (L := A)) (coordinate : A ≃ₗ[ℤ] ℤ) :=
  And.intro (factorial_integral_inventory_fibre inventory value) <|
    And.intro (factorial_integral_inventory_iff inventory value)
      (factorial_integral_source_iff coordinate value)

private theorem the_original_diagonal_has_a_bounded_H1_read
    {A : Type u} [AddCommGroup A] {H : ModuleCat.{u} ℤ}
    (coordinate : A ≃ₗ[ℤ] ℤ) (read : H ≃ₗ[ℤ] FactorialCompletion (L := A)) (source : A) :
    ∃ bound base : Nat, ∀ stage ≥ base, ∃ candidate : A, (coordinate candidate).natAbs ≤ bound ∧
      modulusProjection (factorialModulus stage) candidate =
        (factorialRestriction (L := A) stage).hom (read (read.symm (factorialCanonicalMap source))) := by
  rw [read.apply_symm_apply]
  exact (factorial_integral_source_iff coordinate _).1
    ⟨source, rfl, fun _ same => factorial_canonical_injective coordinate same⟩

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩
private abbrev ternary : Nat.Primes := ⟨3, Nat.prime_three⟩

private theorem an_isolated_original_unit_rejects_every_bounded_inventory_after_H1
    {A : Type u} [AddCommGroup A] {H : ModuleCat.{u} ℤ}
    (coordinate : A ≃ₗ[ℤ] ℤ) (unit : A) (unitRead : coordinate unit = 1)
    (read : H ≃ₗ[ℤ] FactorialCompletion (L := A)) (bound base : Nat) :
    let value := factorialFromPrimes (isolatedPrimeUnit coordinate binary)
    let recovered := read (read.symm value)
    (factorialToPrimes recovered) binary = canonicalLinearMap binary unit ∧
      (factorialToPrimes recovered) ternary = 0 ∧
      ∃ stage ≥ base, ∀ source : A, (coordinate source).natAbs ≤ bound →
        modulusProjection (factorialModulus stage) source ≠ (factorialRestriction (L := A) stage).hom recovered := by
  have separated : ternary ≠ binary := by decide
  have same := (congrArg coordinate.symm unitRead).symm.trans (coordinate.symm_apply_apply unit)
  dsimp only
  rw [read.apply_symm_apply, factorial_to_primes_from_primes]
  refine ⟨(if_pos rfl).trans (congrArg (canonicalLinearMap binary) same), if_neg separated, ?_⟩
  exact factorial_integral_residual coordinate _ (factorial_isolated_prime_unit_outside coordinate separated) bound base

end CP755Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP755Independent

open CategoryTheory SourceOperationCompletion SourceOperationScalarInventoryLift CofinalAllPrimeTopology
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

set_option cleanup.letToHave false in
private def the_original_R_diagonal_returns_its_literal_source (ordinal : Nat) :=
  let read := (actualPaidFactorialHomologyIso observation nontrivial half depth ordinal).toLinearEquiv
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  let unit := sourceClass observation nontrivial half depth ordinal
  let original := factorialCanonicalMap unit
  let charge := read.symm original
  let bounded := ConstructiveRoot.CP755Independent.the_original_diagonal_has_a_bounded_H1_read coordinate read unit
  let written := actual_paid_factorial_integral_next observation nontrivial half depth ordinal charge bounded
  let same := written.2.1.2 unit (read.apply_symm_apply original).symm
  And.intro same.symm written.2

set_option cleanup.letToHave false in
private def every_bounded_original_R_H1_writes_the_unique_source_and_literal_next
    (ordinal : Nat) :=
  fun charge bounded =>
    let written := actual_paid_factorial_integral_next observation nontrivial half depth ordinal charge bounded
    PProd.mk written.1 <| And.intro written.2 <|
      And.intro (the_original_R_diagonal_returns_its_literal_source observation nontrivial half depth ordinal) <|
      And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1
        (actual_original_K_read observation nontrivial half depth ordinal)

set_option cleanup.letToHave false in
private def the_original_R_isolated_binary_unit_has_no_bounded_factorial_budget
    (ordinal bound base : Nat) :=
  let unit := sourceClass observation nontrivial half depth ordinal
  let read := (actualPaidFactorialHomologyIso observation nontrivial half depth ordinal).toLinearEquiv
  ConstructiveRoot.CP755Independent.an_isolated_original_unit_rejects_every_bounded_inventory_after_H1
    (actualPaidCompletion observation nontrivial half depth ordinal) unit
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal) read bound base

end OriginalKCofinalFullBranchFibre.RootRelation.CP755Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP755Independent

open CofinalAllPrimeTopology SourceOperationCompletion SourceOperationPaidRelations CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)

set_option cleanup.letToHave false in
private def the_fixed_target_carries_its_original_terminal_through_the_bounded_factorial_fibre
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
  And.intro (factorial_integral_inventory_fibre {original} (factorialCanonicalMap original)) <|
    And.intro (factorial_action_canonical action original) <|
    And.intro (actual_actor_cofinal_continuation depth count within prime)
      (TopologyTrace.actual_actor_cofinal_terminal depth prime)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP755Independent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SaturationMonoid.UniversalBSDRationalKummerCokernel.CP755Independent

open CategoryTheory UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology
open UniversalBSDRationalKummerCohomology.RationalKummerBoundaryCochainData
open UniversalBSDRationalMordellWeilHeight (rationalNaiveHeight)
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CofinalAllPrimeTopology

open private level level_pos point_evaluation_injective from
  SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel

set_option cleanup.letToHave false in
private def the_same_curve_Northcott_fibre_reads_the_original_geometric_Kummer_class
    (source : RationalEllipticCurveSource) (point : RationalPoints source)
    (prime : Nat.Primes) (j : Nat) :=
  let lifts := fun p : Nat.Primes => actual_kummer_completion_lifts source p (canonicalLinearMap p point)
  let family : RationalKummerFamily source := fun p => Classical.choose (lifts p)
  let matchAt := fun p : Nat.Primes => fun address : Nat =>
    let chosen := Classical.choose_spec (lifts p)
    let native := (allPrime_restriction p address point).symm.trans
      (congrArg (restriction (L := RationalPoints source) p address).hom chosen.symm)
    (actual_kummer_completion_read source p address (family p) point native).symm
  let bound := rationalNaiveHeight source point
  let tail : ∃ base : Nat, ∀ address ≥ base, ∃ member : RationalPoints source,
      rationalNaiveHeight source member ≤ bound ∧ rationalKummerMatchesAt source family address member :=
    ⟨0, fun address _ => ⟨point, le_rfl, fun p => matchAt p.val (modulusDepth (factorialModulus address) p)⟩⟩
  And.intro (actual_kummer_bounded_factorial_fibre source family bound) <|
    And.intro (actual_kummer_bounded_factorial_source source family bound tail)
      (actual_kummer_cokernel_class source prime j point)

end SaturationMonoid.UniversalBSDRationalKummerCokernel.CP755Independent

#eval IO.println "CP755_CONTROL + the_fixed_inventory_eventually_reads_the_entire_factorial_fibre"
#eval IO.println "CP755_CONTROL + every_bounded_original_R_H1_writes_the_unique_source_and_literal_next"
#eval IO.println "CP755_CONTROL + the_same_curve_Northcott_fibre_reads_the_original_geometric_Kummer_class"
#eval IO.println "CP755_CONTROL + the_fixed_target_carries_its_original_terminal_through_the_bounded_factorial_fibre"
#eval IO.println "CP755_CONTROL - the_original_R_isolated_binary_unit_has_no_bounded_factorial_budget"
#eval IO.println "CP755_GATE_PASS positive=4 negative=1"
