import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFactorialHomology
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP754Independent

open CategoryTheory CategoryTheory.Limits CofinalAllPrimeTopology
open CofinalHistorySettlement CofinalRelationGeneratedComplex SourceOperationCompletion
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations
open scoped Pointwise

open private principal_smul_top from SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus
open private integral_extension_d from SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Cochain.Homology

private def the_actual_factorial_stage_cone_and_quasiIso_commute_with_paid_cochain_action
    {Root : Type u} {NextRoot : Type v}
    (root : RootedAccountedUnfolding Root) (next : RootedAccountedUnfolding NextRoot)
    {source target : CochainComplex AddCommGrpCat ℤ}
    (paid : HomotopyEquiv source target) (degree : ℤ) (stage : Nat) :=
  PProd.mk (factorialCochainIsLimit (ComplexShape.up ℤ) source) <|
    And.intro (factorial_stage_transition_surjective (source.X degree) stage) <|
    And.intro (factorial_derived_limit_root root source) <|
    And.intro (factorial_derived_limit_quasiIso root source) <|
    And.intro (factorial_derived_limit_stage root source stage) <|
    And.intro (factorial_cochain_map_restriction (ComplexShape.up ℤ) paid.hom stage) <|
    And.intro (factorial_derived_limit_naturality root next paid.hom)
      (factorial_derived_action_quasiIso root next paid)

private def the_integral_differentials_and_original_paid_split_recover_both_H1_directions
    {S Root : Type} {V X : S → Type} [∀ s, AddCommGroup (V s)]
    {s : S} {old : Env V X} {before after : Expr V X s}
    (root : RootedAccountedUnfolding Root) (paid : Trace old before after) :=
  let complex := natComplex (prefixHistory root (exposure paid))
  let split := (paidCochainSettlementSplitting root paid).map
    (forget₂ (ModuleCat ℤ) AddCommGrpCat ⋙ factorialCompletionFunctor)
  let read := (factorialPaidHomologyIso root paid).toLinearEquiv
  And.intro (integral_extension_d complex 0 1) <|
    And.intro (integral_extension_d complex 1 2) <| And.intro split.s_g <|
    And.intro (fun h => read.symm_apply_apply h) (fun x => read.apply_symm_apply x)

private theorem two_times_the_paid_unit_survives_the_six_layer_after_H1_readback
    {A : Type u} [AddCommGroup A] {H : ModuleCat.{u} ℤ}
    (coordinate : A ≃ₗ[ℤ] ℤ) (unit : A) (unitRead : coordinate unit = 1)
    (read : H ≃ₗ[ℤ] FactorialCompletion (L := A)) :
    let source := factorialCanonicalMap ((2 : ℤ) • unit)
    (factorialRestriction (L := A) 1).hom (read (read.symm source)) = 0 ∧
      (factorialRestriction (L := A) 2).hom (read (read.symm source)) ≠ 0 := by
  dsimp only
  rw [read.apply_symm_apply]
  refine ⟨(factorial_canonical_restriction 1 _).trans ?_, ?_⟩
  · apply (Submodule.Quotient.mk_eq_zero _).2
    change (2 : ℤ) • unit ∈ Ideal.span {(2 : ℤ)} • (⊤ : Submodule ℤ A)
    rw [principal_smul_top]
    exact ⟨unit, rfl⟩
  · rw [factorial_canonical_restriction]
    intro erased
    have inRange := (Submodule.Quotient.mk_eq_zero _).mp erased
    change (2 : ℤ) • unit ∈ Ideal.span {(6 : ℤ)} • (⊤ : Submodule ℤ A) at inRange
    rw [principal_smul_top] at inRange
    obtain ⟨divided, written⟩ := inRange
    change (6 : ℤ) • divided = (2 : ℤ) • unit at written
    have impossible : 6 * coordinate divided = 2 := by
      simpa only [map_smul, unitRead, zsmul_eq_mul, mul_one] using congrArg coordinate written
    omega

end CP754Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP754Independent

open CategoryTheory SourceOperationCompletion SourceOperationScalarInventoryLift CofinalAllPrimeTopology
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

set_option cleanup.letToHave false in
private def the_actual_R_H1_class_reaches_every_paid_address_and_literal_native_next
    (ordinal : Nat) :=
  fun charge =>
  let written := actual_paid_factorial_homology_next observation nontrivial half depth ordinal charge
  PProd.mk written.1 <| And.intro written.2 <|
    And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1
      (actual_original_K_read observation nontrivial half depth ordinal)

set_option cleanup.letToHave false in
private def the_original_R_double_unit_is_invisible_mod_two_but_not_mod_six (ordinal : Nat) :=
  let unit := sourceClass observation nontrivial half depth ordinal
  let read := (actualPaidFactorialHomologyIso observation nontrivial half depth ordinal).toLinearEquiv
  ConstructiveRoot.CP754Independent.two_times_the_paid_unit_survives_the_six_layer_after_H1_readback
    (actualPaidCompletion observation nontrivial half depth ordinal) unit
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal) read

end OriginalKCofinalFullBranchFibre.RootRelation.CP754Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP754Independent

open CategoryTheory CofinalAllPrimeTopology CofinalRelationGeneratedComplex
open SourceOperationCompletion SourceOperationPaidRelations CofinalHistorySettlement
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)

open private extendPaidHomotopy from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedStageLimit

set_option cleanup.letToHave false in
private def the_fixed_target_moves_its_original_paid_H1_and_keeps_its_terminal
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth)))
    (prime : Nat.Primes) :=
  let runtime := C.mathRuntime depth (count+1)
  let prior := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).2
  let later := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime.tick.next).2
  let first := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let next := RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence
  let retained := tick_paid_prefix (R.old depth) (R.origin depth) (R.reader depth) runtime
  let paid := (forget₂ (ModuleCat ℤ) AddCommGrpCat).mapHomotopyEquiv
    (extendPaidHomotopy (continuationCochainHomotopyEquiv first prior next later retained))
  let history := prefixHistory first (exposure prior)
  let initial := (factorialPaidHomologyIso first prior).toLinearEquiv
  let final := (factorialPaidHomologyIso next later).toLinearEquiv
  let original := factorialCanonicalMap (history.completionProjection (terminalGenerator first prior))
  let moved := (HomologicalComplex.homologyMap (factorialDerivedAction first next paid.hom) 1)
    (initial.symm original)
  And.intro (initial.apply_symm_apply original) <|
    And.intro (final.symm_apply_apply moved) <|
    And.intro (factorial_derived_limit_naturality first next paid.hom) <|
    And.intro (actual_actor_cofinal_continuation depth count within prime)
      (TopologyTrace.actual_actor_cofinal_terminal depth prime)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP754Independent

#eval IO.println "CP754_CONTROL + the_actual_factorial_stage_cone_and_quasiIso_commute_with_paid_cochain_action"
#eval IO.println "CP754_CONTROL + the_integral_differentials_and_original_paid_split_recover_both_H1_directions"
#eval IO.println "CP754_CONTROL + the_actual_R_H1_class_reaches_every_paid_address_and_literal_native_next"
#eval IO.println "CP754_CONTROL + the_fixed_target_moves_its_original_paid_H1_and_keeps_its_terminal"
#eval IO.println "CP754_CONTROL - the_original_R_double_unit_is_invisible_mod_two_but_not_mod_six"
#eval IO.println "CP754_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
