import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Source
import H0mework.Realization.Operations.Substitution.Complex
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift SourceOperationScalarCochain
open RootLawDependentJointStateController
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
def binding : ∀ target, ChangedVar (Variable root visit recognition) target →
    Expr (Value root visit recognition) (ChangedVar (Variable root visit recognition)) target
  | .origin, (datum, coordinate) => .var (nextNode root visit recognition datum,coordinate)
  | .result, (empty, _) => PEmpty.elim empty
  | .children, (empty, _) => PEmpty.elim empty
abbrev environment := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
  (binding root visit recognition) (mixed root visit recognition)
def followingEnvironment : Env (Value root visit recognition) (Variable root visit recognition)
  | .origin, datum => Finsupp.single (nextNode root visit recognition (nextNode root visit recognition datum)) 1
  | .result, empty => PEmpty.elim empty
  | .children, empty => PEmpty.elim empty

theorem source_environment : environment root visit recognition =
    mixedEnvironment (updatedEnvironment root visit recognition)
      (followingEnvironment root visit recognition-updatedEnvironment root visit recognition) := by
  funext target name
  cases target with
  | origin =>
      rcases name with ⟨datum,coordinate⟩
      cases coordinate <;> rfl
  | result => exact PEmpty.elim name.1
  | children => exact PEmpty.elim name.1

def complex := SourceOperationScalarPresentation.SourceSubstitution.complexMorphism (R:=ℤ)
  (s:=SourceOperationNative.Tree.Fold.Slot.result) (binding root visit recognition) (mixed root visit recognition)
abbrev actionWord (word : Word root visit recognition) := substitution (R:=ℤ) (binding root visit recognition) word

theorem word_equation (word : Word root visit recognition) : evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result) (mixed root visit recognition)
    (actionWord root visit recognition word) = evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result) (environment root visit recognition) word :=
  LinearMap.congr_fun (evaluation_substitution (R:=ℤ) (binding root visit recognition) (mixed root visit recognition)) word

def material := (node root visit recognition,nextNode root visit recognition (node root visit recognition),
  SourceTemporalMaterial.Action.actual root (node root visit recognition).2,
  binding root visit recognition,environment root visit recognition,complex root visit recognition)
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
