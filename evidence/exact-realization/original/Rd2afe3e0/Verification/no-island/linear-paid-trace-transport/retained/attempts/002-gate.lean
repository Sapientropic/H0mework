import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyRelations

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 650000
set_option linter.defProp false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP806Independent

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationPaidRelations CofinalHistorySettlement CofinalRelationGeneratedComplex CategoryTheory

section Generic
universe u
variable {S A B : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {environment : Env V X}
variable {op : V s →+ V s} {body : Expr V X s} {total input : V s}
variable {parent : Trace environment (.linear op body) (.const total)}
variable {child : Trace environment body (.const input)}

private theorem ordered_child_and_signed_payment
    (cut : Trace.LinearInterleaving op parent child) (charges : Fin (words child).length →₀ ℤ) :
    words parent = (words child).map (linearWord op) ++
      [Finsupp.single (.linear op (.const input)) 1 - Finsupp.single (.const total) 1] ∧
    (∀ address : Fin (words child).length,
      (words parent).get (Fin.castLE (linear_count_le cut) address) =
        linearWord op ((words child).get address)) ∧
    writePayment parent (linearPayment cut charges) = linearWord op (writePayment child charges) :=
  ⟨linear_words cut, linear_word_at cut, linear_write_payment cut charges⟩

local notation "history" "[" root "," trace "]" => prefixHistory root (exposure trace)

private theorem relation_retraction_and_differential (childRoot : RootedAccountedUnfolding A)
    (parentRoot : RootedAccountedUnfolding B) (cut : Trace.LinearInterleaving op parent child)
    (r : history[childRoot,child].relationClosure) :
    linearRelationBack childRoot parentRoot cut (linearRelation childRoot parentRoot cut r) = r ∧
    linearGenerator childRoot parentRoot cut (relationInclusion history[childRoot,child] r) =
      relationInclusion history[parentRoot,parent] (linearRelation childRoot parentRoot cut r) :=
  ⟨linear_relation_recover childRoot parentRoot cut r, linear_differential childRoot parentRoot cut r⟩
end Generic

section Actual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open OriginalKDirectRCofinalDivision
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "actualTrace" => CountedCayleyProgramme.terminalTrace observation nontrivial half depth ordinal
local notation "actualChild" => CountedCayleyProgramme.countChild observation nontrivial half depth ordinal
local notation "prefixRoot" => RootedAccountedUnfolding.zero ((authority).emitted origin)
local notation "history" "[" root "," trace "]" => prefixHistory root (exposure trace)

private theorem actual_count_child_has_integer_retraction (N : Nat) (positive : 0 < N) (n : Nat)
    (relation : history[prefixRoot,(actualChild N positive n).trace].relationClosure) :
    let fibre := CountedCayleyRelations.countedRelationFibre observation nontrivial half depth ordinal N positive n
    fibre.2.val (fibre.1 relation) = relation :=
  (CountedCayleyRelations.countedRelationFibre observation nontrivial half depth ordinal N positive n).2.property relation

private def actual_count_child_has_paid_cochain (N : Nat) (positive : 0 < N) (n : Nat) :
    natComplex history[prefixRoot,(actualChild N positive n).trace] ⟶
      natComplex history[prefixRoot,actualTrace N positive n] :=
  CountedCayleyRelations.countedCochain observation nontrivial half depth ordinal N positive n

private def actual_boundary_and_original_whole_next (N : Nat) (positive : 0 < N) (n : Nat)
    (increment : Env CountedCellHistory.CellValue CountedCellHistory.Var) :=
  let payment := CountedCayleyWriteback.actual_entrance_writeback observation nontrivial half depth ordinal
    N positive n increment
  let localWholeNext := payment.2.2.2.2.2.2.2.1
  let originalMacro := payment.2.2.2.2.2.2.2.2.2.2.2
  And.intro (CountedCayleyRelations.terminal_boundary_effect observation nontrivial half depth ordinal
      N positive n increment) <|
    And.intro payment.1 <| And.intro payment.2.1 <|
    And.intro localWholeNext.2.2.1 <| And.intro localWholeNext.2.2.2 <|
    And.intro originalMacro.2.2.2.2.2.2.2.1 <|
    And.intro originalMacro.2.2.2.2.2.2.2.2.1 originalMacro.2.2.2.2.2.2.2.2.2

private theorem actual_parent_only_charge_cannot_descend (N : Nat) (positive : 0 < N) (n : Nat) :
    let actual := actualTrace N positive n
    let cut := actual.splitLinear
    ∃ relation, relation ∉ LinearMap.range (linearRelation prefixRoot prefixRoot cut.interleaving) := by
  let actual := actualTrace N positive n
  let cut := actual.splitLinear
  have live : (words cut.trace).length < (words actual).length := by
    rw [linear_words cut.interleaving, List.length_append, List.length_map]
    exact Nat.lt_succ_self _
  let address : Fin (words actual).length := ⟨(words cut.trace).length, live⟩
  let payment := relationPaymentEquiv prefixRoot actual
  refine ⟨payment (Finsupp.single address (1 : ℤ)), ?_⟩
  intro descends
  have erased := (linear_relation_range prefixRoot prefixRoot cut.interleaving _).mp descends address (Nat.le_refl _)
  change payment.symm (payment (Finsupp.single address (1 : ℤ))) address = 0 at erased
  rw [payment.symm_apply_apply, Finsupp.single_eq_same] at erased
  exact one_ne_zero erased

end Actual
end CP806Independent

#eval IO.println "CP806_CONTROL + ordered_child_and_signed_payment"
#eval IO.println "CP806_CONTROL + relation_retraction_and_differential"
#eval IO.println "CP806_CONTROL + actual_count_child_has_integer_retraction"
#eval IO.println "CP806_CONTROL + actual_count_child_has_paid_cochain"
#eval IO.println "CP806_CONTROL + actual_boundary_and_original_whole_next"
#eval IO.println "CP806_CONTROL - actual_parent_only_charge_cannot_descend"
#eval IO.println "CP806_GATE_PASS positive=5 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
