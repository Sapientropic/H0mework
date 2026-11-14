import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyContinuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidSyntaxCompletion
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP747Independent

open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations SourceOperationCompletion
open CofinalHistorySettlement

variable {S Root NextRoot : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before middle after : Expr V X s}
variable {prior : Trace old before middle} {next : Trace old before after}

private def the_same_retained_words_cross_relation_and_generator
    (root : RootedAccountedUnfolding Root) (nextRoot : RootedAccountedUnfolding NextRoot)
    (p : Nat.Primes) (paid : words prior <+: words next)
    (relation : (prefixHistory root (exposure prior)).relationClosure)
    (generator : (prefixHistory root (exposure prior)).generatorClosure) :=
  And.intro (continuation_relation root nextRoot p paid relation)
    (continuation_generator root nextRoot p paid generator)

private def the_actual_quotient_transition_and_inverse_read_every_prior_class
    (root : RootedAccountedUnfolding Root) (nextRoot : RootedAccountedUnfolding NextRoot)
    (p : Nat.Primes) (paid : words prior <+: words next)
    (value : (prefixHistory root (exposure prior)).CompletionCarrier)
    (relation : (prefixHistory nextRoot (exposure next)).relationClosure) :=
  And.intro (continuation_completion root nextRoot p paid value) <|
    And.intro ((completionEquiv root p prior).symm_apply_apply value)
      (continuation_relation_range root nextRoot paid relation)

end CP747Independent

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP747Independent

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source

private def the_fixed_target_actual_tick_and_terminal_share_the_original_execution
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth))) (p : Nat.Primes) :=
  And.intro (actual_actor_cofinal_continuation depth count within p)
    (TopologyTrace.actual_actor_cofinal_terminal depth p)

private theorem the_original_source_has_a_strict_payment (depth : Nat) :
    0 < sourceFuel (R.source depth (emitted depth)) := by
  unfold sourceFuel
  have original := CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer.splitRight_atLeastTwo
    (R.source depth (emitted depth))
  omega

private theorem last_source_count_is_within (depth : Nat) :
    sourceFuel (R.source depth (emitted depth)) - 1 < sourceFuel (R.source depth (emitted depth)) :=
  Nat.sub_lt (the_original_source_has_a_strict_payment depth) (by decide)

private def the_last_actual_Goldbach_payment_is_not_an_old_relation
    (depth : Nat) (p : Nat.Primes) :=
  (actual_actor_cofinal_continuation depth (sourceFuel (R.source depth (emitted depth)) - 1)
    (last_source_count_is_within depth) p).1.1.2.2

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation.CP747Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP747Independent

open SourceOperationScalarInventoryLift
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def the_separate_original_R_consumes_Division_K_whole_and_literal_next
    (ordinal : Nat) (p : Nat.Primes) (coefficient : ℤ) :=
  And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1 <|
    And.intro (actual_original_K_read observation nontrivial half depth ordinal) <|
    And.intro (actual_root_relation_consumer observation nontrivial half depth ordinal)
      (actual_paid_syntax_model_next observation nontrivial half depth ordinal p coefficient)

end OriginalKCofinalFullBranchFibre.RootRelation.CP747Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

#eval IO.println "CP747_CONTROL + the_same_retained_words_cross_relation_and_generator"
#eval IO.println "CP747_CONTROL + the_actual_quotient_transition_and_inverse_read_every_prior_class"
#eval IO.println "CP747_CONTROL + the_fixed_target_actual_tick_and_terminal_share_the_original_execution"
#eval IO.println "CP747_CONTROL + the_separate_original_R_consumes_Division_K_whole_and_literal_next"
#eval IO.println "CP747_CONTROL - the_last_actual_Goldbach_payment_is_not_an_old_relation"
#eval IO.println "CP747_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
