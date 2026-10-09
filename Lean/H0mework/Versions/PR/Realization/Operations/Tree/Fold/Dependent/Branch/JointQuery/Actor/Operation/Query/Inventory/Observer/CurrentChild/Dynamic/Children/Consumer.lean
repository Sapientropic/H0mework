import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Observed.Consumer
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Children
open CurrentChild
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Dynamic.Frame root visit recognition) (read : Dynamic.Read root visit recognition frame)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Dynamic.C.Occurrence frame (current:=current))
abbrev baseEnvironment := Observed.baseEnvironment root visit recognition frame read supplied
abbrev childEnvironment := Observed.childEnvironment root visit recognition frame read supplied

private theorem embed_value {slot : Observer.Slot root recognition}
 (term : Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) slot) :
 (CurrentChild.embed root visit recognition term).eval (read supplied) =
 term.eval (baseEnvironment root visit recognition frame read supplied) := by
 induction term with
 | var => rfl
 | const => rfl
 | add first second one two => exact congrArg₂ (·+·) one two
 | linear operation argument previous => exact congrArg operation previous
 | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two
private theorem child_embed_value {slot : Inventory.Slot root recognition}
 (term : Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition) slot) :
 (Observer.embed root visit recognition term).eval (baseEnvironment root visit recognition frame read supplied) =
 term.eval (childEnvironment root visit recognition frame read supplied) := by
 induction term with
 | var => rfl
 | const => rfl
 | add first second one two => exact congrArg₂ (·+·) one two
 | linear operation argument previous => exact congrArg operation previous
 | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two


private def oldRead : Output root visit recognition →+ Observer.Output root visit recognition where
 toFun value := value.1
 map_zero' := rfl
 map_add' _ _ := rfl

theorem child_term_value (source : SourceActor root recognition) :
 (Dynamic.childTerm root visit recognition source).eval (read supplied) =
 oldInjection root visit recognition (Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition source.1.1).eval
   (childEnvironment root visit recognition frame read supplied))) := by
 change oldInjection root visit recognition ((embed root visit recognition
  (Observer.oldOutputEmbed root visit recognition (Inventory.childExpressionAtCode root visit recognition source.1.1))).eval _) = _
 rw [embed_value]
 change oldInjection root visit recognition (Observer.oldInjection root visit recognition
  ((Observer.embed root visit recognition (Inventory.childExpressionAtCode root visit recognition source.1.1)).eval
   (baseEnvironment root visit recognition frame read supplied))) = _
 rw [child_embed_value]

theorem child_term_fee (source : SourceActor root recognition) : remaining (Dynamic.childTerm root visit recognition source) =
 Inventory.childCostAtCode root recognition source.1.1+2 := by
 simp only [Dynamic.childTerm,oldOutputEmbed,remaining,Actor.Extension.embed_charge,Observer.oldOutputEmbed,
  Observer.embed_charge,Inventory.child_expression_cost]

private theorem mapped_zero {X G : Type u} [AddCommMonoid G] (terms : List X) (read : X → G)
 (zero : ∀ term ∈ terms, read term=0) : (terms.map read).sum=0 := by
 apply List.sum_eq_zero
 intro value belongs
 rcases List.mem_map.mp belongs with ⟨term,present,rfl⟩
 exact zero term present

private theorem old_term_value : oldRead root visit recognition
 ((oldTerm root visit recognition U7 calculus anchor).eval (read supplied)) =
 (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
  (baseEnvironment root visit recognition frame read supplied) := by
 change (embed root visit recognition (Observer.Action.observerSyntax root visit recognition U7 calculus anchor)).eval _ = _
 exact embed_value root visit recognition frame read supplied _

private theorem child_read_value (source : SourceActor root recognition) : oldRead root visit recognition
 ((Dynamic.childTerm root visit recognition source).eval (read supplied)) =
 Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition source.1.1).eval
   (childEnvironment root visit recognition frame read supplied)) :=
 congrArg (oldRead root visit recognition) (child_term_value root visit recognition frame read supplied source)

theorem paid_old_output : (paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1.1 =
 (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
  (baseEnvironment root visit recognition frame read supplied) +
 ((supportFor root visit recognition frame read supplied).map (fun source => Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition source.1.1).eval
   (childEnvironment root visit recognition frame read supplied)))).sum := by
 rw [paid_value_for]
 change oldRead root visit recognition (((termsFor root visit recognition U7 calculus anchor frame read supplied).map
  (fun term => term.eval (read supplied))).sum) = _
 rw [map_list_sum]
 simp only [termsFor,List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
 have actorZero : oldRead root visit recognition ((actorTerm root visit recognition).eval (read supplied))=0 := rfl
 have obsZero : ∀ term ∈ observationsFor root visit recognition frame read supplied,
  oldRead root visit recognition (term.eval (read supplied))=0 := by
  intro term present
  rcases List.mem_flatten.mp present with ⟨terms,inTerms,inTerm⟩
  rcases List.mem_map.mp inTerms with ⟨index,_,rfl⟩
  rcases List.mem_ofFn.mp inTerm with ⟨kind,same⟩
  rw [←same]
  rfl
 have gramZero : ∀ term ∈ gramsFor root visit recognition frame read supplied,
  oldRead root visit recognition (term.eval (read supplied))=0 := by
  intro term present
  rcases List.mem_flatMap.mp present with ⟨first,_,inside⟩
  rcases List.mem_map.mp inside with ⟨second,_,rfl⟩
  rfl
 rw [old_term_value,actorZero,mapped_zero _ _ obsZero,mapped_zero _ _ gramZero]
 simp only [zero_add,add_zero,childrenFor,List.map_map,Function.comp_def,child_read_value]

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Children
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
