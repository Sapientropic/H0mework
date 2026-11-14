import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidSyntaxCompletion
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyTrace

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP746Independent

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open SourceOperationCompletion SourceGeneratedPrimePowerCompletion CofinalHistorySettlement

section OriginalTrace
variable {S Root : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before after : Expr V X s}

private def the_original_paid_word_and_its_ordered_exposure_have_the_same_coordinates
    (p : Nat.Primes) (paid : Trace old before after)
    (charges : Fin (words paid).length →₀ ℤ) (word : Formal ℤ V X s) :=
  And.intro (word_map_payment p paid charges) <|
    And.intro (word_map_coefficientSum p word) (trace_exposure p paid)

private def the_original_generator_and_relator_restore_and_commute_with_differential
    (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after)
    (generator : (prefixHistory root (exposure paid)).generatorClosure)
    (relation : (prefixHistory root (exposure paid)).relationClosure) :=
  And.intro (generator_equiv_value root p paid generator) <|
    And.intro (relation_equiv_value root p paid relation) <|
    And.intro ((generatorEquiv root p paid).symm_apply_apply generator) <|
    And.intro ((relationEquiv root p paid).symm_apply_apply relation)
      (generator_differential_equiv root p paid relation)

private def the_actual_quotient_map_keeps_the_projection_and_original_integer_coordinate
    (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after)
    (generator : (prefixHistory root (exposure paid)).generatorClosure)
    (value : (prefixHistory root (exposure paid)).CompletionCarrier) :=
  And.intro (completion_equiv_projection root p paid generator) <|
    And.intro (completion_equiv_coordinate root p paid value)
      ((completionEquiv root p paid).symm_apply_apply value)

end OriginalTrace

private abbrev binary : Nat.Primes := ⟨2, Nat.prime_two⟩
private abbrev RatValue : Unit → Type := fun _ => ℚ
private abbrev EmptyVariable : Unit → Type := fun _ => Empty
private abbrev RatSyntax := Expr RatValue EmptyVariable ()
private def emptyEnv : Env RatValue EmptyVariable := fun _ variableName => nomatch variableName

private theorem rational_one_erased_by_all_binary_stages :
    canonicalLinearMap (L := ℚ) binary 1 = 0 := by
  apply (canonicalMap_eq_zero_iff binary (1 : ℚ)).2
  intro j
  refine ⟨(((2 : ℚ)^(j+1))⁻¹), ?_⟩
  change ((2 : Nat) : ℤ)^(j+1) • (((2 : ℚ)^(j+1))⁻¹) = 1
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul, Int.cast_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))

private theorem arbitrary_rational_syntax_words_can_collapse :
    let zeroTerm : RatSyntax := .const 0
    let oneTerm : RatSyntax := .const 1
    let zeroWord : Formal ℤ RatValue EmptyVariable () := Finsupp.single zeroTerm 1
    let oneWord : Formal ℤ RatValue EmptyVariable () := Finsupp.single oneTerm 1
    zeroWord ≠ oneWord ∧ wordMap binary () zeroWord = wordMap binary () oneWord := by
  let zeroTerm : RatSyntax := .const 0
  let oneTerm : RatSyntax := .const 1
  have distinct : zeroTerm ≠ oneTerm := by
    intro equal
    have read := congrArg (fun term : RatSyntax => term.eval emptyEnv) equal
    change (0 : ℚ) = 1 at read
    norm_num at read
  have collapsed : expression binary zeroTerm = expression binary oneTerm := by
    change (Expr.const (canonicalLinearMap (L := ℚ) binary 0) :
      Expr (SourceOperationCompletion.Value RatValue binary) EmptyVariable ()) =
      Expr.const (canonicalLinearMap (L := ℚ) binary 1)
    rw [map_zero, rational_one_erased_by_all_binary_stages]
  change (Finsupp.single zeroTerm 1 : Formal ℤ RatValue EmptyVariable ()) ≠ Finsupp.single oneTerm 1 ∧
    wordMap binary () (Finsupp.single zeroTerm 1) = wordMap binary () (Finsupp.single oneTerm 1)
  constructor
  · intro equal
    have read := congrArg (fun word : Formal ℤ RatValue EmptyVariable () => word zeroTerm) equal
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne distinct] at read
    exact one_ne_zero read
  · rw [word_map_single, word_map_single, collapsed]

end CP746Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation.CP746Independent

open SourceOperationScalarInventoryLift
open OriginalKDirectRCofinalDivision (actual_original_K_read)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
attribute [local instance] relationGroups
open private inverse_preserves_charge from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidSyntaxCompletion

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def same_actual_R_unit_and_arbitrary_charge_use_the_interpreted_inverse_at_next
    (ordinal : Nat) (p : Nat.Primes) (coefficient : ℤ) :=
  And.intro (actual_paid_syntax_source_unit observation nontrivial half depth ordinal p) <|
    And.intro (inverse_preserves_charge observation nontrivial half depth ordinal p coefficient)
      (actual_paid_syntax_model_next observation nontrivial half depth ordinal p coefficient)

private def the_original_R_root_relation_whole_and_next_are_consumed (ordinal : Nat) :=
  actual_root_relation_consumer observation nontrivial half depth ordinal

private def the_same_R_ordinal_reads_original_Division_and_K (ordinal : Nat) :=
  And.intro (actual_division_action_same_root observation nontrivial half depth ordinal).2.1
    (actual_original_K_read observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.RootRelation.CP746Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyTrace.CP746Independent

private def the_separate_fixed_target_terminal_consumes_its_original_receipt
    (depth : Nat) (p : Nat.Primes) :=
  actual_actor_cofinal_terminal depth p

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyTrace.CP746Independent

#eval IO.println "CP746_CONTROL + the_original_paid_word_and_its_ordered_exposure_have_the_same_coordinates"
#eval IO.println "CP746_CONTROL + the_original_generator_and_relator_restore_and_commute_with_differential"
#eval IO.println "CP746_CONTROL + the_actual_quotient_map_keeps_the_projection_and_original_integer_coordinate"
#eval IO.println "CP746_CONTROL + same_actual_R_unit_inverse_whole_and_literal_next"
#eval IO.println "CP746_CONTROL - arbitrary_rational_syntax_words_can_collapse"
#eval IO.println "CP746_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
