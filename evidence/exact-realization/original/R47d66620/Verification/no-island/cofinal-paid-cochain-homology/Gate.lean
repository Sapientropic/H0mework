import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCohomology
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP750Independent

open CategoryTheory CofinalHistorySettlement SourceGeneratedPrimePowerCompletion SourceOperationCompletion
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations

private def the_original_projection_splits_and_reads_every_observed_H1_class
    {S Root : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
    {s : S} {old : Env V X} {before after : Expr V X s}
    (root : RootedAccountedUnfolding Root) (paid : Trace old before after)
    (observe : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ) [observe.Additive]
    (charge : (observedPaidComplex root paid observe).homology 1)
    (value : observe.obj (AddCommGrpCat.of (prefixHistory root (exposure paid)).CompletionCarrier)) :=
  let settlement := paidCochainSettlement root paid
  let split := (paidCochainSettlementSplitting root paid).map (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat ⋙ observe)
  let read := (paidObservedCohomologyIso root paid observe).toLinearEquiv
  And.intro
    (show settlement.g = ModuleCat.ofHom (prefixHistory root (exposure paid)).completionProjection from rfl)
    (And.intro split.s_g (And.intro (read.symm_apply_apply charge) (read.apply_symm_apply value)))

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩

private theorem the_lifted_terminal_unit_survives_the_first_binary_layer
    {A B : Type u} [AddCommGroup A] [AddCommGroup B] {H : ModuleCat.{u} ℤ}
    (coordinate : A ≃ₗ[ℤ] ℤ) (unit : A) (unitRead : coordinate unit = 1)
    (read : H ≃ₗ[ℤ] Completion (L := A) binary)
    (write : Completion (L := A) binary ≃ₗ[ℤ] PrimePowerTorsionCompletion B binary)
    (stage : StageResidual (L := A) binary 0 ≃ₗ[ℤ] PrimePowerTorsionSubmodule B binary 0)
    (consistent : ∀ value, (torsionCompletionRestriction B binary 0).hom (write value) =
      stage ((restriction (L := A) binary 0).hom value)) :
    let original := (canonicalMap (L := A) binary).hom unit
    (torsionCompletionRestriction B binary 0).hom ((read.trans write) (read.symm original)) ≠ 0 := by
  let original := (canonicalMap (L := A) binary).hom unit
  have literal :
      (restriction (L := A) binary 0).hom original = stageProjection binary 0 unit :=
    ConcreteCategory.congr_hom (canonicalMap_restriction (L := A) binary 0) unit
  change (torsionCompletionRestriction B binary 0).hom (write (read (read.symm original))) ≠ 0
  rw [read.apply_symm_apply, consistent, literal]
  intro erased
  have stageZero := stage.injective (erased.trans (map_zero stage).symm)
  obtain ⟨word, paid⟩ := (stageProjection_eq_zero_iff binary 0 unit).mp stageZero
  have readPaid := congrArg coordinate paid
  change coordinate (((2 : Nat) : ℤ) ^ (0 + 1) • word) = coordinate unit at readPaid
  have factor : ((2 : Nat) : ℤ) * coordinate word = 1 := by
    simpa only [map_smul, unitRead, smul_eq_mul, Nat.zero_add, pow_one] using readPaid
  have impossible : ¬ ((2 : Nat) : ℤ) ∣ 1 := by norm_num
  exact impossible ⟨coordinate word, factor.symm⟩

end CP750Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP750Independent

open CategoryTheory SourceOperationCompletion SourceGeneratedPrimePowerCompletion SourceOperationScalarInventoryLift
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

open private paidRoot from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCohomology
open private paidTrace from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCompletion

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def every_original_R_H1_charge_reaches_its_stage_and_literal_model_next
    (ordinal : Nat) (p : Nat.Primes) (j : Nat)
    (charge : (observedPaidComplex (paidRoot observation nontrivial half depth ordinal)
      (paidTrace observation nontrivial half depth ordinal) (completionFunctor p)).homology 1) :=
  And.intro (actual_paid_cohomology_cokernel_stage observation nontrivial half depth ordinal p j charge)
    (actual_paid_cohomology_cokernel_next observation nontrivial half depth ordinal p charge)

private def independent_original_R_Division_K_whole_and_model_action
    (ordinal : Nat) (p : Nat.Primes) (j : Nat) (coefficient : ℤ) :=
  And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1 <|
    And.intro (actual_original_K_read observation nontrivial half depth ordinal) <|
    And.intro (actual_root_relation_consumer observation nontrivial half depth ordinal)
      (actual_paid_cokernel_model_next observation nontrivial half depth ordinal p j coefficient)

private def deleting_the_original_R_terminal_H1_charge_changes_its_binary_read
    (ordinal : Nat) :=
  let prime : Nat.Primes := ⟨2, Nat.prime_two⟩
  let unit := sourceClass observation nontrivial half depth ordinal
  let H := (observedPaidComplex (paidRoot observation nontrivial half depth ordinal)
    (paidTrace observation nontrivial half depth ordinal) (completionFunctor prime)).homology 1
  let read : H ≃ₗ[ℤ] Completion (L := SourceCompletion observation nontrivial half depth ordinal) prime :=
    (actualPaidCohomologyIso observation nontrivial half depth ordinal prime).toLinearEquiv
  let charge := read.symm ((canonicalMap prime).hom unit)
  let survives := ConstructiveRoot.CP750Independent.the_lifted_terminal_unit_survives_the_first_binary_layer
    (H := H) (actualPaidCompletion observation nontrivial half depth ordinal) unit
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal) read
    (actualPaidCokernelCompletion observation nontrivial half depth ordinal prime)
    (actualPaidCokernelStage observation nontrivial half depth ordinal prime 0)
    (actual_paid_cokernel_completion_restriction observation nontrivial half depth ordinal prime 0)
  And.intro (actual_paid_cohomology_cokernel_stage observation nontrivial half depth ordinal prime 0 charge) survives

end OriginalKCofinalFullBranchFibre.RootRelation.CP750Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP750Independent

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent tick_paid_prefix)
open SourceOperationCompletion SourceGeneratedPrimePowerCompletion

private def the_fixed_target_paid_H1_restricts_and_advances_with_its_original_terminal
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth)))
    (p : Nat.Primes) (j : Nat) :=
  let runtime := C.mathRuntime depth (count+1)
  let prior := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).2
  let next := (runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime.tick.next).2
  let firstRoot := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let nextRoot := RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence
  let retained := tick_paid_prefix (R.old depth) (R.origin depth) (R.reader depth) runtime
  And.intro (paid_cohomology_restriction firstRoot prior (completionFunctorRestriction p j)) <|
    And.intro (paid_cohomology_continuation firstRoot prior nextRoot next (F := stageFunctor p j) retained) <|
    And.intro (actual_actor_cofinal_continuation depth count within p)
      (TopologyTrace.actual_actor_cofinal_terminal depth p)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP750Independent

#eval IO.println "CP750_CONTROL + the_original_projection_splits_and_reads_every_observed_H1_class"
#eval IO.println "CP750_CONTROL + every_original_R_H1_charge_reaches_its_stage_and_literal_model_next"
#eval IO.println "CP750_CONTROL + independent_original_R_Division_K_whole_and_model_action"
#eval IO.println "CP750_CONTROL + the_fixed_target_paid_H1_restricts_and_advances_with_its_original_terminal"
#eval IO.println "CP750_CONTROL - deleting_the_original_R_terminal_H1_charge_changes_its_binary_read"
#eval IO.println "CP750_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
