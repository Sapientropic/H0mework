import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Source
import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Realization.Logic.SourceScope

set_option autoImplicit false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual

namespace Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering
namespace F
export Lower.SourceFamily.Foresight
  (value Word action read sourceMap Model source_fibre source_prefix readPrefix environment)
end F
namespace L
export SaturationMonoid.SourceOperationLogic (Scope q q_surjective q_eq_iff)
end L

section Semantics
variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {t : S}

def SemanticEq (left right : Formal ℤ V X t) : Prop :=
  ∀ env : Env V X, evaluation (R:=ℤ) env left = evaluation (R:=ℤ) env right

theorem rendered_semantics (word : Formal ℤ V X t) :
    SemanticEq (Finsupp.single (Coefficients.expression word) 1) word := by
  intro env
  simp only [evaluation, Finsupp.linearCombination_single, one_smul]
  exact Coefficients.expression_eval word env

theorem semantic_effect (left right : Formal ℤ V X t)
    (same : SemanticEq left right) (old increment : Env V X) :
    effectEvaluator (R:=ℤ) old increment left = effectEvaluator (R:=ℤ) old increment right := by
  apply add_left_cancel (a := evaluation (R:=ℤ) old left)
  have generatedLeft := LinearMap.congr_fun (evaluation_update (R:=ℤ) old increment) left
  have generatedRight := LinearMap.congr_fun (evaluation_update (R:=ℤ) old increment) right
  exact generatedLeft.symm.trans ((same (old+increment)).trans
    (generatedRight.trans (congrArg (fun value => value + effectEvaluator (R:=ℤ) old increment right) (same old).symm)))

theorem semantic_lift (left right : Formal ℤ V X t)
    (same : SemanticEq left right) : SemanticEq (liftMap left) (liftMap right) := by
  intro env
  let old : Env V X := fun sort name => (env sort name).1
  let increment : Env V X := fun sort name => (env sort name).2
  have pairEnv : env = pairEnvironment old increment := by
    funext sort name
    exact Prod.eta (env sort name)
  rw [pairEnv]
  have leftValue := LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=t) old increment) left
  have rightValue := LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=t) old increment) right
  exact leftValue.trans ((Prod.ext (same old) (semantic_effect left right same old increment)).trans rightValue.symm)
end Semantics

variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t, X t → Expr W X t)
variable (state : Lower.SourceFamily.Foresight.Tail.State (W:=W) (X:=X) (s:=s))
local instance modelModule (t : S) (k : Nat) : Module ℤ (F.Model binding state t k) :=
  (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding state t k)).module

theorem semantic_advance (t : S) (k : Nat) (left right : F.Word binding state t k)
    (same : SemanticEq left right) (distance : Nat) :
    SemanticEq (AlgebraicDependent.advance (F.action binding state t) k distance left)
      (AlgebraicDependent.advance (F.action binding state t) k distance right) := by
  induction distance with
  | zero => exact same
  | succ distance prior =>
    exact semantic_lift _ _ prior

theorem rendered_source (t : S) (k : Nat) (word : F.Word binding state t k) :
    F.sourceMap binding state t k (Finsupp.single (Coefficients.expression word) 1) =
      F.sourceMap binding state t k word := by
  apply (F.source_fibre binding state t k _ _).mpr
  intro distance
  exact semantic_advance binding state t k _ _ (rendered_semantics word) distance
    (F.environment binding state (k+distance))

abbrev Scope (t : S) (k : Nat) := L.Scope (F.sourceMap binding state t k)

def sourceWord (t : S) (k : Nat) (point : Scope binding state t k) : F.Word binding state t k :=
  Classical.choose (L.q_surjective (F.sourceMap binding state t k) point)

theorem source_word (t : S) (k : Nat) (point : Scope binding state t k) :
    L.q (F.sourceMap binding state t k) (sourceWord binding state t k point) = point :=
  Classical.choose_spec (L.q_surjective (F.sourceMap binding state t k) point)

def rendered (t : S) (k : Nat) (point : Scope binding state t k) :=
  Coefficients.expression (sourceWord binding state t k point)

theorem scope_renderer (t : S) (k : Nat) (point : Scope binding state t k) :
    L.q (F.sourceMap binding state t k) (Finsupp.single (rendered binding state t k point) 1) = point := by
  apply Eq.trans _ (source_word binding state t k point)
  apply (L.q_eq_iff (F.sourceMap binding state t k) _ _).mpr
  rw [LinearMap.mem_ker, map_sub]
  exact sub_eq_zero.mpr (rendered_source binding state t k (sourceWord binding state t k point))

theorem all_future_reads (t : S) (k : Nat) (point : Scope binding state t k) (distance : Nat) :
    F.read binding state t (k+distance)
      (AlgebraicDependent.advance (F.action binding state t) k distance
        (Finsupp.single (rendered binding state t k point) 1)) =
    F.read binding state t (k+distance)
      (AlgebraicDependent.advance (F.action binding state t) k distance (sourceWord binding state t k point)) :=
  (F.source_fibre binding state t k _ _).mp
    (rendered_source binding state t k (sourceWord binding state t k point)) distance

theorem renderer_head (t : S) (k : Nat) (point : Scope binding state t k) :
    F.readPrefix binding state t k 0
      (F.sourceMap binding state t k (Finsupp.single (rendered binding state t k point) 1)) ⟨0,by omega⟩ =
    (rendered binding state t k point).eval (F.environment binding state k) := by
  rw [F.source_prefix]
  change evaluation (R:=ℤ) (F.environment binding state k)
    (Finsupp.single (rendered binding state t k point) 1) = _
  exact (rendered_semantics (sourceWord binding state t k point) (F.environment binding state k)).trans
    (Coefficients.expression_eval (sourceWord binding state t k point) (F.environment binding state k)).symm


end Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
