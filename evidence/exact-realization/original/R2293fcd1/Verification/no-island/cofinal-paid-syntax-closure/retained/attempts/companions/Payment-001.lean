import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Trace
import SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Closure

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open CofinalHistorySettlement

variable {S : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before after : Expr V X s}
variable (p : Nat.Primes)

private def paymentIndex (paid : Trace old before after) :
    Fin (words paid).length ≃ Fin (words (trace p paid)).length :=
  finCongr (by rw [trace_words, List.length_map])

/-- The interpreted history uses the original step positions for every integer payment. -/
def paymentEquiv (paid : Trace old before after) :
    (Fin (words paid).length →₀ ℤ) ≃ₗ[ℤ] (Fin (words (trace p paid)).length →₀ ℤ) :=
  Finsupp.domLCongr (paymentIndex p paid)

theorem word_map_payment (paid : Trace old before after) (charges : Fin (words paid).length →₀ ℤ) :
    wordMap p s (writePayment paid charges) = writePayment (trace p paid) (paymentEquiv p paid charges) := by
  have maps : (wordMap p s).comp (writePayment paid) =
      (writePayment (trace p paid)).comp (paymentEquiv p paid).toLinearMap := by
    apply Finsupp.lhom_ext
    intro index coefficient
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, paymentEquiv, Finsupp.domLCongr_single,
      writePayment, Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun word => coefficient • word) (trace_word_at p paid index).symm
  exact LinearMap.congr_fun maps charges

theorem word_map_coefficientSum (word : Formal ℤ V X s) : coefficientSum (wordMap p s word) = coefficientSum word := by
  have maps : (coefficientSum (Value := Value V p) (Var := X) (sort := s)).comp (wordMap p s) = coefficientSum := by
    apply Finsupp.lhom_ext
    intro term coefficient
    simp only [LinearMap.comp_apply, word_map_single, coefficientSum, Finsupp.linearCombination_single]
  exact LinearMap.congr_fun maps word

def eventMap : PresentedRelationEventAt (Expr V X s) → PresentedRelationEventAt (Expr (Value V p) X s)
  | .generator term => .generator (expression p term)
  | .relation word => .relation (wordMap p s word)

private theorem paid_events_map (paid : Trace old before after) :
    RootedAccountedUnfolding.mapBranches (eventMap p) (events paid) = events (trace p paid) := by
  induction paid with
  | nil term => rfl
  | @cons first middle last _ tail previous =>
    change AccountedBranches.cons (.zero (.relation
      (wordMap p s (Finsupp.single first 1 - Finsupp.single middle 1))))
        (RootedAccountedUnfolding.mapBranches (eventMap p) (events tail)) =
      AccountedBranches.cons (.zero (.relation
        (Finsupp.single (expression p first) 1 - Finsupp.single (expression p middle) 1))) (events (trace p tail))
    rw [map_sub, word_map_single, word_map_single, previous]

theorem trace_exposure (paid : Trace old before after) :
    (exposure paid).map (eventMap p) = exposure (trace p paid) :=
  congrArg (RootedAccountedUnfolding.occur (.generator (expression p before))) (paid_events_map p paid)

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
