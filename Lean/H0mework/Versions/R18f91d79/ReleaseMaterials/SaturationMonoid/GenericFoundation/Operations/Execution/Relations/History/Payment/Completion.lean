import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Closure
import H0mework.Versions.MF.Realization.Perfectification.Cofinal.LivingLawRootGeneratedCofinalRelationComplexKernel

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open CofinalHistorySettlement CofinalRelationGeneratedComplex

open private rankCharge cumulativeRank from
  H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment

variable {Sorts Root : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {before after : Expr Value Var sort}

local notation "Word" => Formal ℤ Value Var sort
local notation "Hₚ" "(" root "," trace ")" => prefixHistory root (exposure trace)

private theorem read_terminal (trace : Trace environment before after) (coefficient : ℤ) :
    readPayment trace (Finsupp.single after coefficient) = 0 := by
  ext index
  have length := complete_steps trace
  have remainingEq := trace.remaining_eq
  have inside := index.isLt
  let rank := remaining before - index.val
  have higher : remaining after < rank := by dsimp only [rank]; omega
  have zero : rankCharge (remaining after) rank = 0 := by
    change (Finsupp.lapply rank : (Nat →₀ ℤ) →ₗ[ℤ] ℤ)
      ((Finset.range (remaining after)).sum fun k => Finsupp.single (k+1) 1) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k member
    have kBound := Finset.mem_range.mp member
    exact Finsupp.single_eq_of_ne (by omega)
  change cumulativeRank (Finsupp.single after coefficient) rank = 0
  simp only [cumulativeRank, Finsupp.linearCombination_single, Finsupp.smul_apply, zero, smul_zero]

/-- The generated differential and the actual endpoint split the whole generated word. -/
theorem paid_differential_split (root : RootedAccountedUnfolding Root)
    (trace : Trace environment before after) (word : (Hₚ(root, trace)).generatorClosure) :
    (show (Hₚ(root, trace)).generatorClosure from
      ((natComplex (Hₚ(root, trace))).d 0 1).hom
        (relationPaymentEquiv root trace (readPayment trace word.val))) +
      coefficientSum word.val • terminalGenerator root trace = word := by
  have difference := word_sub_terminal_in_relation root trace word
  rw [payment_relation_closure] at difference
  obtain ⟨charges, paid⟩ := difference
  have recovered : charges = readPayment trace word.val := by
    calc
      charges = readPayment trace (writePayment trace charges) := (read_write_payment trace charges).symm
      _ = _ := by rw [paid, map_sub, read_terminal, sub_zero]
  rw [natComplex_d_zero_one]
  apply Subtype.ext
  change writePayment trace (readPayment trace word.val) +
    coefficientSum word.val • (Finsupp.single after 1 : Word) = word.val
  rw [← recovered, paid, Finsupp.smul_single, smul_eq_mul, mul_one, sub_add_cancel]

private theorem coefficientSum_on_payment (trace : Trace environment before after) :
    coefficientSum.comp (writePayment trace) = 0 := by
  apply Finsupp.lhom_ext
  intro index scalar
  let cut := paidCut trace index
  have edge : (words trace).get index = Finsupp.single cut.entry 1 - Finsupp.single cut.exit 1 :=
    (stepOccurrence_word trace index).symm.trans (paidCut_word trace index)
  simp only [LinearMap.comp_apply, writePayment, Finsupp.linearCombination_single,
    edge, map_smul, map_sub, coefficientSum, one_smul, sub_self, smul_zero, LinearMap.zero_apply]

/-- The existing completion has the actual terminal word as its integral coordinate. -/
def paidCompletionEquiv (root : RootedAccountedUnfolding Root) (trace : Trace environment before after) :
    (Hₚ(root, trace)).CompletionCarrier ≃ₗ[ℤ] ℤ := by
  let read := coefficientSum.comp (Hₚ(root, trace)).generatorClosure.subtype
  have zero : (Hₚ(root, trace)).relationInGeneratorClosure ≤ LinearMap.ker read := by
    intro word relation
    change word.val ∈ (Hₚ(root, trace)).relationClosure at relation
    rw [payment_relation_closure] at relation
    obtain ⟨charges, paid⟩ := relation
    change coefficientSum word.val = 0
    rw [← paid]
    exact LinearMap.congr_fun (coefficientSum_on_payment trace) charges
  let forward := (Hₚ(root, trace)).relationInGeneratorClosure.liftQ read zero
  let reverse := (Hₚ(root, trace)).completionProjection.comp
    (LinearMap.toSpanSingleton ℤ _ (terminalGenerator root trace))
  refine LinearEquiv.ofLinearMap forward reverse (LinearMap.ext fun coefficient => ?_)
    (LinearMap.ext fun quotient => ?_)
  · change coefficientSum (coefficient • (Finsupp.single after 1 : Word)) = coefficient
    simp only [map_smul, coefficientSum, Finsupp.linearCombination_single, smul_eq_mul, mul_one]
  · obtain ⟨word, rfl⟩ := (Hₚ(root, trace)).relationInGeneratorClosure.mkQ_surjective quotient
    change (Hₚ(root, trace)).completionProjection (coefficientSum word.val • terminalGenerator root trace) =
      (Hₚ(root, trace)).completionProjection word
    have equation := congrArg (Hₚ(root, trace)).completionProjection (paid_differential_split root trace word)
    rwa [map_add, completion_kills_generated_differential, zero_add] at equation

theorem paid_completion_source (root : RootedAccountedUnfolding Root)
    (trace : Trace environment before after) (word : (Hₚ(root, trace)).generatorClosure) :
    paidCompletionEquiv root trace ((Hₚ(root, trace)).completionProjection word) = coefficientSum word.val := rfl

theorem paid_completion_terminal (root : RootedAccountedUnfolding Root)
    (trace : Trace environment before after) (coefficient : ℤ) :
    (paidCompletionEquiv root trace).symm coefficient =
      (Hₚ(root, trace)).completionProjection (coefficient • terminalGenerator root trace) := rfl

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
