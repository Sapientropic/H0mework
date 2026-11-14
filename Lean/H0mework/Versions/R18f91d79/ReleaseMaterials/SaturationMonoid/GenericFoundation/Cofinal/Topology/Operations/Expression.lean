import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Bilinear.Completion
import H0mework.Realization.Operations.Effects

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open CategoryTheory SourceOperationEffects SourceGeneratedPrimePowerCompletion

variable {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable (p : Nat.Primes)

def linear (operation : A →+ B) : Completion (L := A) p →+ Completion (L := B) p :=
  (inducedCompletionLinearMap p operation.toIntLinearMap).toAddMonoidHom

private def intBilinear (operation : A →+ B →+ C) : A →ₗ[ℤ] B →ₗ[ℤ] C :=
  (AddMonoidHom.mk' (fun value => (operation value).toIntLinearMap) (fun left right => by
    apply LinearMap.ext
    intro value
    exact congrArg (fun map : B →+ C => map value) (map_add operation left right))).toIntLinearMap

def bilinear (operation : A →+ B →+ C) :
    Completion (L := A) p →+ Completion (L := B) p →+ Completion (L := C) p :=
  LinearMap.toAddMonoidHom'.comp (completionBilinear (intBilinear operation) p).toAddMonoidHom

theorem linear_source (operation : A →+ B) (value : A) :
    linear p operation (canonicalLinearMap p value) = canonicalLinearMap p (operation value) :=
  ConcreteCategory.congr_hom (canonicalMap_naturality p operation.toIntLinearMap) value

theorem bilinear_source (operation : A →+ B →+ C) (left : A) (right : B) :
    bilinear p operation (canonicalLinearMap p left) (canonicalLinearMap p right) =
      canonicalLinearMap p (operation left right) :=
  completion_bilinear_source (intBilinear operation) p left right

variable {S : Type u} {V : S → Type v} {X : S → Type w} [∀ s, AddCommGroup (V s)]

abbrev Value (V : S → Type v) [∀ s, AddCommGroup (V s)] (p : Nat.Primes) (s : S) : Type v :=
  Completion (L := V s) p

def environment (old : Env V X) : Env (Value V p) X :=
  fun sort variableName => canonicalLinearMap p (old sort variableName)

/-- Interpret each actual primitive on the existing completion, retaining its source variables. -/
def expression {sort : S} : Expr V X sort → Expr (Value V p) X sort
  | .var name => .var name
  | .const value => .const (canonicalLinearMap p value)
  | .add left right => .add (expression left) (expression right)
  | .linear operation body => .linear (linear p operation) (expression body)
  | .bilinear operation left right => .bilinear (bilinear p operation) (expression left) (expression right)

theorem expression_eval {sort : S} (term : Expr V X sort) (old : Env V X) :
    (expression p term).eval (environment p old) = canonicalLinearMap p (term.eval old) := by
  induction term with
  | var name => rfl
  | const value => rfl
  | add left right leftRead rightRead =>
    simp only [expression, Expr.eval, leftRead, rightRead, map_add]
  | linear operation body read =>
    simpa only [expression, Expr.eval, read] using linear_source p operation (body.eval old)
  | bilinear operation left right leftRead rightRead =>
    simpa only [expression, Expr.eval, leftRead, rightRead] using
      bilinear_source p operation (left.eval old) (right.eval old)

theorem expression_effect {sort : S} (term : Expr V X sort) (old increment : Env V X) :
    (expression p term).effect (environment p old) (environment p increment) =
      canonicalLinearMap p (term.effect old increment) := by
  have combined : environment p old + environment p increment = environment p (old+increment) := by
    funext s name
    exact (map_add (canonicalLinearMap p) (old s name) (increment s name)).symm
  have actual := (expression p term).eval_update (environment p old) (environment p increment)
  rw [combined, expression_eval, term.eval_update, map_add, expression_eval] at actual
  exact (add_left_cancel actual).symm

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
