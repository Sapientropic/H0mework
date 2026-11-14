import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Expression
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open SourceGeneratedPrimePowerCompletion

section Trace

variable {S : Type u} {V : S → Type v} {X : S → Type w} [∀ s, AddCommGroup (V s)]
variable (p : Nat.Primes)

theorem expression_remaining {s : S} (term : Expr V X s) :
    remaining (expression p term) = remaining term := by
  induction term <;> simp_all only [expression, remaining]

/-- Interpret the original paid constructor and its two source endpoints. -/
def step {old : Env V X} {s : S} {before after : Expr V X s}
    (paid : Step old before after) :
    Step (environment p old) (expression p before) (expression p after) := by
  induction paid with
  | bind name => exact .bind name
  | @addConst sort left right =>
    simpa only [expression, map_add] using
      (Step.addConst (environment := environment p old)
        (canonicalLinearMap p left) (canonicalLinearMap p right))
  | @linearConst source target operation value =>
    simpa only [expression, linear_source] using
      (Step.linearConst (environment := environment p old) (linear p operation) (canonicalLinearMap p value))
  | @bilinearConst leftSort rightSort target operation left right =>
    simpa only [expression, bilinear_source] using
      (Step.bilinearConst (environment := environment p old) (bilinear p operation)
        (canonicalLinearMap p left) (canonicalLinearMap p right))
  | addLeft _ previous => exact .addLeft previous
  | addRight _ previous => exact .addRight previous
  | linear operation _ previous => exact Step.linear (environment := environment p old) (linear p operation) previous
  | bilinearLeft operation _ previous => exact Step.bilinearLeft (environment := environment p old) (bilinear p operation) previous
  | bilinearRight operation _ previous => exact Step.bilinearRight (environment := environment p old) (bilinear p operation) previous

/-- Interpret the actual trace, preserving the order of all paid steps. -/
def trace {old : Env V X} {s : S} {before after : Expr V X s}
    (paid : Trace old before after) :
    Trace (environment p old) (expression p before) (expression p after) :=
  match paid with
  | .nil term => .nil (expression p term)
  | .cons first rest => .cons (step p first) (trace rest)

theorem trace_length {old : Env V X} {s : S} {before after : Expr V X s} (paid : Trace old before after) :
    (trace p paid).length = paid.length := by
  induction paid <;> simp_all only [trace, Trace.length]

end Trace

section Words

variable {S : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable (p : Nat.Primes)

def wordMap (s : S) : Formal ℤ V X s →ₗ[ℤ] Formal ℤ (Value V p) X s :=
  Finsupp.lmapDomain ℤ ℤ (expression p)

theorem word_map_single {s : S} (term : Expr V X s) (coefficient : ℤ) :
    wordMap p s (Finsupp.single term coefficient) = Finsupp.single (expression p term) coefficient := by
  simp only [wordMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem trace_words {old : Env V X} {s : S} {before after : Expr V X s} (paid : Trace old before after) :
    words (trace p paid) = (words paid).map (wordMap p s) := by
  induction paid with
  | nil => rfl
  | @cons first middle last _ tail previous =>
    change (Finsupp.single (expression p first) 1 - Finsupp.single (expression p middle) 1) ::
        words (trace p tail) =
      wordMap p s (Finsupp.single first 1 - Finsupp.single middle 1) :: (words tail).map (wordMap p s)
    rw [map_sub, word_map_single, word_map_single, previous]

/-- The exact original paid slot is preserved by the word interpretation. -/
theorem trace_word_at {old : Env V X} {s : S} {before after : Expr V X s} (paid : Trace old before after)
    (index : Fin (words paid).length) :
    (words (trace p paid)).get ⟨index.val, by simpa only [trace_words, List.length_map] using index.isLt⟩ =
      wordMap p s ((words paid).get index) := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [trace_words, List.getElem_map]

end Words

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
