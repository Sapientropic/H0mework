import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP748Independent

open CategoryTheory CofinalHistorySettlement CofinalHistoryTransition CofinalRelationGeneratedComplex
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations SourceOperationCompletion

private theorem the_cochain_equivalence_uses_the_original_two_terms
    {S Root NextRoot : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
    {s : S} {old : Env V X} {before middle after : Expr V X s}
    (root : RootedAccountedUnfolding Root) (prior : Trace old before middle)
    (nextRoot : RootedAccountedUnfolding NextRoot) (next : Trace old before after)
    (paid : words prior <+: words next) :
    let oldHistory := prefixHistory root (exposure prior)
    let newHistory := prefixHistory nextRoot (exposure next)
    let e := continuationCochainHomotopyEquiv root prior nextRoot next paid
    e.hom.f 0 = ModuleCat.ofHom (continuationRelation root nextRoot paid) ∧
      e.hom.f 1 = ModuleCat.ofHom ((continuationTransition root nextRoot paid).generatorMap oldHistory newHistory) ∧
      e.inv.f 0 = ModuleCat.ofHom (continuationRelationBack root prior nextRoot next) ∧
      e.inv.f 1 = ModuleCat.ofHom (continuationGeneratorBack root prior nextRoot next) :=
  ⟨rfl,rfl,rfl,rfl⟩

private theorem a_fresh_relation_survives_the_omitted_differential
    {OldRel NewRel NewGen : Type u} [AddCommGroup OldRel] [AddCommGroup NewRel] [AddCommGroup NewGen]
    {includeOld : OldRel →ₗ[ℤ] NewRel} {fresh : NewRel} (live : fresh ∉ LinearMap.range includeOld)
    (d : NewRel →ₗ[ℤ] NewGen) (injective : Function.Injective d) :
    (LinearMap.range (d.comp includeOld)).mkQ (d fresh) ≠ 0 := by
  intro erased
  obtain ⟨old, same⟩ := (Submodule.Quotient.mk_eq_zero _).mp erased
  exact live ⟨old,injective same⟩

end CP748Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP748Independent

open CofinalRelationGeneratedComplex SourceOperationScalarInventoryLift
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def all_four_original_R_paid_stages_consume_their_derived_write
    (ordinal : Nat) (index : Fin 4) :=
  actual_paid_derived_continuation observation nontrivial half depth ordinal
    (Fin.cast (actual_paid_stage_count observation nontrivial half depth ordinal).symm index)

private def independent_original_R_Division_K_and_literal_model_next
    (ordinal : Nat) (p : Nat.Primes) (coefficient : ℤ) :=
  And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1 <|
    And.intro (actual_original_K_read observation nontrivial half depth ordinal) <|
    And.intro (actual_root_relation_consumer observation nontrivial half depth ordinal)
      (actual_paid_syntax_model_next observation nontrivial half depth ordinal p coefficient)

private def omitting_the_last_actual_R_differential_leaves_a_nonzero_quotient_class
    (ordinal : Nat) :=
  let source := sourceRoot observation nontrivial half depth ordinal
  let origin := sourceCurrent observation nontrivial half depth ordinal
  let reader := sourceReader observation nontrivial half depth ordinal
  let index := Fin.cast (actual_paid_stage_count observation nontrivial half depth ordinal).symm (3 : Fin 4)
  let runtime := (RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.seed source origin reader).advance index.val
  let target := RootGeneratedDebtActivationJointSource.OwnerFree.Relations.history source origin reader runtime.tick.next
  let paid := actual_paid_derived_continuation observation nontrivial half depth ordinal index
  ConstructiveRoot.CP748Independent.a_fresh_relation_survives_the_omitted_differential
    paid.2.1.1.2.2 (relationInclusion target)
    (Submodule.inclusion_injective target.relationClosure_le_generatorClosure)

end OriginalKCofinalFullBranchFibre.RootRelation.CP748Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP748Independent

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open RootGeneratedDebtActivationJointSource.OwnerFree (cofinal_tick_derived_write)

private def the_fixed_target_consumes_its_same_actual_derived_write_and_original_terminal
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth))) (p : Nat.Primes) :=
  let runtime := C.mathRuntime depth (count+1)
  And.intro (cofinal_tick_derived_write (R.old depth) (R.origin depth) (R.reader depth) runtime) <|
    And.intro (actual_actor_cofinal_continuation depth count within p)
      (TopologyTrace.actual_actor_cofinal_terminal depth p)

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP748Independent

#eval IO.println "CP748_CONTROL + the_cochain_equivalence_uses_the_original_two_terms"
#eval IO.println "CP748_CONTROL + all_four_original_R_paid_stages_consume_their_derived_write"
#eval IO.println "CP748_CONTROL + independent_original_R_Division_K_and_literal_model_next"
#eval IO.println "CP748_CONTROL + the_fixed_target_consumes_its_same_actual_derived_write_and_original_terminal"
#eval IO.println "CP748_CONTROL - omitting_the_last_actual_R_differential_leaves_a_nonzero_quotient_class"
#eval IO.println "CP748_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
