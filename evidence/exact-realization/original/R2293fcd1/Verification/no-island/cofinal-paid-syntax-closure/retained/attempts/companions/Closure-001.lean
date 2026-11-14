import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Payment
import SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Completion

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open CofinalHistorySettlement CofinalRelationGeneratedComplex

open private read_terminal coefficientSum_on_payment from
  SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Completion

variable {S Root : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before after : Expr V X s}

local notation "history" "[" root "," paid "]" => prefixHistory root (exposure paid)

private def generatorCoordinates (root : RootedAccountedUnfolding Root) (paid : Trace old before after) :
    history[root, paid].generatorClosure ≃ₗ[ℤ] ((Fin (words paid).length →₀ ℤ) × ℤ) := by
  let read := ((readPayment paid).comp history[root, paid].generatorClosure.subtype).prod
    (coefficientSum.comp history[root, paid].generatorClosure.subtype)
  let write := ((natComplex history[root, paid]).d 0 1).hom.comp (relationPaymentEquiv root paid).toLinearMap
  let terminal := LinearMap.toSpanSingleton ℤ _ (terminalGenerator root paid)
  let restore := write.coprod terminal
  refine LinearEquiv.ofLinearMap read restore (LinearMap.ext ?_) (LinearMap.ext ?_)
  · rintro ⟨charges, coefficient⟩
    have recovered : (restore (charges, coefficient)).val =
        writePayment paid charges + Finsupp.single after coefficient := by
      change writePayment paid charges + coefficient • (Finsupp.single after 1 : Formal ℤ V X s) = _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    change (readPayment paid (restore (charges, coefficient)).val,
      coefficientSum (restore (charges, coefficient)).val) = (charges, coefficient)
    rw [recovered]
    apply Prod.ext
    · change readPayment paid (writePayment paid charges + Finsupp.single after coefficient) = charges
      rw [map_add, read_write_payment paid charges, read_terminal paid coefficient, add_zero]
    · have balanced := LinearMap.congr_fun (coefficientSum_on_payment paid) charges
      change coefficientSum (writePayment paid charges) = 0 at balanced
      change coefficientSum (writePayment paid charges + Finsupp.single after coefficient) = coefficient
      simp only [map_add, balanced, zero_add, coefficientSum, Finsupp.linearCombination_single, smul_eq_mul, mul_one]
  · intro word
    exact paid_differential_split root paid word

private theorem generator_restore_value (root : RootedAccountedUnfolding Root) (paid : Trace old before after)
    (charges : Fin (words paid).length →₀ ℤ) (coefficient : ℤ) :
    ((generatorCoordinates root paid).symm (charges, coefficient)).val =
      writePayment paid charges + Finsupp.single after coefficient := by
  change writePayment paid charges + coefficient • (Finsupp.single after 1 : Formal ℤ V X s) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The actual interpreted word is reversible on the complete generator closure of this paid history. -/
def generatorEquiv (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after) :
    history[root, paid].generatorClosure ≃ₗ[ℤ] history[root, trace p paid].generatorClosure :=
  (generatorCoordinates root paid).trans
    (((paymentEquiv p paid).prodCongr (LinearEquiv.refl ℤ ℤ)).trans
      (generatorCoordinates root (trace p paid)).symm)

theorem generator_equiv_value (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after)
    (word : history[root, paid].generatorClosure) :
    (generatorEquiv root p paid word).val = wordMap p s word.val := by
  let read := generatorCoordinates root paid
  let coords := read word
  have source : word.val = writePayment paid coords.1 + Finsupp.single after coords.2 :=
    (congrArg Subtype.val (read.symm_apply_apply word)).symm.trans
      (generator_restore_value root paid coords.1 coords.2)
  change ((generatorCoordinates root (trace p paid)).symm
      (paymentEquiv p paid coords.1, coords.2)).val = wordMap p s word.val
  calc
    _ = writePayment (trace p paid) (paymentEquiv p paid coords.1) +
        Finsupp.single (expression p after) coords.2 := generator_restore_value root (trace p paid) _ _
    _ = wordMap p s (writePayment paid coords.1 + Finsupp.single after coords.2) := by
      rw [map_add, word_map_payment, word_map_single]
    _ = _ := congrArg (wordMap p s) source.symm

def relationEquiv (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after) :
    history[root, paid].relationClosure ≃ₗ[ℤ] history[root, trace p paid].relationClosure :=
  (relationPaymentEquiv root paid).symm.trans
    ((paymentEquiv p paid).trans (relationPaymentEquiv root (trace p paid)))

theorem relation_equiv_value (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after)
    (word : history[root, paid].relationClosure) :
    (relationEquiv root p paid word).val = wordMap p s word.val := by
  let read := relationPaymentEquiv root paid
  let coords := read.symm word
  have source : writePayment paid coords = word.val := congrArg Subtype.val (read.apply_symm_apply word)
  change writePayment (trace p paid) (paymentEquiv p paid coords) = wordMap p s word.val
  exact (word_map_payment p paid coords).symm.trans (congrArg (wordMap p s) source)

/-- Both ends of the original generated differential use the same interpreted paid word. -/
theorem generator_differential_equiv (root : RootedAccountedUnfolding Root) (p : Nat.Primes)
    (paid : Trace old before after) (word : history[root, paid].relationClosure) :
    generatorEquiv root p paid (((natComplex history[root, paid]).d 0 1).hom word) =
      ((natComplex history[root, trace p paid]).d 0 1).hom (relationEquiv root p paid word) := by
  rw [natComplex_d_zero_one, natComplex_d_zero_one]
  apply Subtype.ext
  exact (generator_equiv_value root p paid _).trans (relation_equiv_value root p paid word).symm

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
