import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Source.Core
import H0mework.Realization.ObservationActions.WordsModel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.SourceCore
 (carry read sigma nativeCursor jointSource sourceTags actionBinding joint_semantic)
end P
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState OccurrenceIndex)
end I
namespace F
export Lower.SourceFamily.Foresight (Model completion)
end F
namespace A
export SourceGeneratedActionWords (Model projection advance advance_source readout readout_source projection_fibre run run_source)
end A
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (index:I.OccurrenceIndex n frame)
abbrev Word := Formal ℤ (PairValue (Lower.Value W n)) X s
abbrev Target := AlgebraicDependent.completion (P.carry (V:=Lower.Value W n) (X:=X) (s:=s))
 (P.read (P.sigma binding n) (P.nativeCursor n frame index)) 0 ×
 F.Model binding (I.nativeState n seed frame) s 0
local instance nativeModule:Module ℤ (F.Model binding (I.nativeState n seed frame) s 0):=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (F.completion binding (I.nativeState n seed frame) s 0)).module
local instance targetModule:Module ℤ (Target binding n seed frame index):=Prod.instModule

def actions : PUnit.{u+1}→Word (W:=W) (X:=X) (s:=s) n→ₗ[ℤ]Word (W:=W) (X:=X) (s:=s) n :=
 fun _=>substitution (R:=ℤ) (P.actionBinding binding n)
def original := P.jointSource binding n seed frame index
abbrev Model := A.Model (actions (s:=s) binding n) (original binding n seed frame index) PUnit.unit
abbrev source := A.projection (actions (s:=s) binding n) (original binding n seed frame index) PUnit.unit
def operator := A.advance (actions (s:=s) binding n) (original binding n seed frame index) PUnit.unit PUnit.unit
def restriction := A.readout (actions (s:=s) binding n) (original binding n seed frame index) PUnit.unit []

theorem operator_source (word:Word (W:=W) (X:=X) (s:=s) n):
 operator binding n seed frame index (source binding n seed frame index word)=
 source binding n seed frame index (substitution (R:=ℤ) (P.actionBinding binding n) word) :=
 A.advance_source _ _ _ _ word

theorem empty_restriction (word:Word (W:=W) (X:=X) (s:=s) n):
 restriction binding n seed frame index (source binding n seed frame index word)=
 P.jointSource binding n seed frame index word :=
 A.readout_source _ _ _ [] word

theorem complete_fibre (left right:Word (W:=W) (X:=X) (s:=s) n):
 source binding n seed frame index left=source binding n seed frame index right ↔
 ∀word:List PUnit.{u+1},original binding n seed frame index
  (A.run (actions (s:=s) binding n) word left)=original binding n seed frame index
  (A.run (actions (s:=s) binding n) word right):=
 A.projection_fibre _ _ _ _ _

theorem kernel_invariant (word:Word (W:=W) (X:=X) (s:=s) n)
 (zero:source binding n seed frame index word=0):
 source binding n seed frame index (substitution (R:=ℤ) (P.actionBinding binding n) word)=0 :=
 (operator_source binding n seed frame index word).symm.trans
 ((congrArg (operator binding n seed frame index) zero).trans (map_zero _))

def actionMorphism:SourceGeneratedScalarDifferentialResidual.Morphism
 (source binding n seed frame index) (source binding n seed frame index) where
 sourceMap:=substitution (R:=ℤ) (P.actionBinding binding n)
 targetMap:=operator binding n seed frame index
 commutes:=by
  apply LinearMap.ext
  intro word
  exact (operator_source binding n seed frame index word).symm
abbrev scopeOperator:=inducedResidualMap (actionMorphism binding n seed frame index)
theorem scope_source (word:Word (W:=W) (X:=X) (s:=s) n):
 scopeOperator binding n seed frame index (SourceOperationLogic.q (source binding n seed frame index) word)=
 SourceOperationLogic.q (source binding n seed frame index)
  (substitution (R:=ℤ) (P.actionBinding binding n) word) :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (actionMorphism binding n seed frame index)) word

def restrictionMorphism:SourceGeneratedScalarDifferentialResidual.Morphism
 (source binding n seed frame index) (original binding n seed frame index) where
 sourceMap:=LinearMap.id
 targetMap:=restriction binding n seed frame index
 commutes:=by
  apply LinearMap.ext
  intro word
  exact (empty_restriction binding n seed frame index word).symm
abbrev scopeRestriction:=inducedResidualMap (restrictionMorphism binding n seed frame index)
theorem scope_restriction_source (word:Word (W:=W) (X:=X) (s:=s) n):
 scopeRestriction binding n seed frame index (SourceOperationLogic.q (source binding n seed frame index) word)=
 SourceOperationLogic.q (original binding n seed frame index) word :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (restrictionMorphism binding n seed frame index)) word

section Semantics
variable (left right:Word (W:=W) (X:=X) (s:=s) n)
variable (same:Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq left right)
include same
private theorem semantic_substitution:
 Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq
  (substitution (R:=ℤ) (P.actionBinding binding n) left)
  (substitution (R:=ℤ) (P.actionBinding binding n) right) :=by
 intro env
 exact (LinearMap.congr_fun (evaluation_substitution (R:=ℤ) (P.actionBinding binding n) env) left).trans
  ((same (SourceSubstitution.sourceEnvironment (P.actionBinding binding n) env)).trans
   (LinearMap.congr_fun (evaluation_substitution (R:=ℤ) (P.actionBinding binding n) env) right).symm)
private theorem semantic_run (word:List PUnit.{u+1}):
 Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq
  (A.run (actions (s:=s) binding n) word left) (A.run (actions (s:=s) binding n) word right) :=by
 induction word generalizing left right with
 | nil=>exact same
 | cons letter rest previous=>
  exact previous _ _ (semantic_substitution binding n left right same)
theorem semantic:
 source binding n seed frame index left=source binding n seed frame index right :=by
 apply (complete_fibre binding n seed frame index left right).mpr
 intro word
 exact P.joint_semantic binding n seed frame index _ _ (semantic_run binding n left right same word)
end Semantics

theorem renderer (word:Word (W:=W) (X:=X) (s:=s) n):
 source binding n seed frame index (Finsupp.single (Coefficients.expression word) 1)=
 source binding n seed frame index word :=
 semantic binding n seed frame index _ _ (Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.rendered_semantics word)

def sourceMaterial := (P.sourceTags n frame index,
 source binding n seed frame index,operator binding n seed frame index,restriction binding n seed frame index,
 scopeOperator binding n seed frame index,scopeRestriction binding n seed frame index)
end Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
