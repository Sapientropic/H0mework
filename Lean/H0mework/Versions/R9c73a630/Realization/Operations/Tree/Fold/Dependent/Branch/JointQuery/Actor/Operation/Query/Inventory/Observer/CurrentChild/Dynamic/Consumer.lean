import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch (Node node nextNode constructor)
namespace Fresh
export SourceOperationNative.Tree.Fold.Dependent.Branch.Fresh (Outcome.complete)
end Fresh
end B
namespace Q
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery (Value Variable expression)
end Q
abbrev coreSlot : CurrentChild.Slot root recognition := .inl (CurrentActor.coreSlot root recognition)
def orbitPair (count : Nat) (datum : B.Node root visit recognition) :=
 (Finsupp.single ((B.nextNode root visit recognition)^[count] datum) (1:ℤ),
  Finsupp.single ((B.nextNode root visit recognition)^[count+1] datum) (1:ℤ) -
   Finsupp.single ((B.nextNode root visit recognition)^[count] datum) (1:ℤ))
def actorAtCount (count : Nat) := B.Fresh.Outcome.complete root recognition visit
 (B.constructor root visit recognition ((B.nextNode root visit recognition)^[count] (B.node root visit recognition)) [])
private def liftCore {slot : SourceOperationNative.Tree.Fold.Slot.{u}}
 (term : Expr (Q.Value root visit recognition) (Q.Variable root visit recognition) slot) :
 Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition)
 (.inl (.inl (.inl (.inl (.inl slot))))) :=
 CurrentChild.embed root visit recognition (Observer.embed root visit recognition (Inventory.embed root visit recognition
  (Actor.Extension.embed (Actor.Value root visit recognition) (Actor.Variable root visit recognition) (Query.Output root visit recognition)
   (Actor.Extension.embed (Q.Value root visit recognition) (Q.Variable root visit recognition) (Actor.Output root visit recognition) term))))
private theorem liftCore_eval {slot : SourceOperationNative.Tree.Fold.Slot.{u}}
 (term : Expr (Q.Value root visit recognition) (Q.Variable root visit recognition) slot)
 (env : Env (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition)) :
 (liftCore root visit recognition term).eval env =
 term.eval (fun target name => env (.inl (.inl (.inl (.inl (.inl target))))) name) := by
 induction term with
 | var => rfl
 | const => rfl
 | add first second one two => exact congrArg₂ (·+·) one two
 | linear operation argument previous => exact congrArg operation previous
 | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two
private theorem core_query_pair (env : Env (Q.Value root visit recognition) (Q.Variable root visit recognition)) :
 (Q.expression root visit recognition).eval env (0:Fin 2) =
 SourceOperationScalarInventoryLift.pairBilinear (SourceNativeBinary.lift (B.constructor root visit recognition))
  (env .origin (B.node root visit recognition,.old) (0:Fin 2)) (Finsupp.single [] (1:ℤ),0) := by
 change SourceOperationScalarInventoryLift.pairBilinear (SourceNativeBinary.lift (B.constructor root visit recognition))
  (env .origin (B.node root visit recognition,.old) (0:Fin 2)) (Finsupp.single [] (1:ℤ),0) + (0+0) = _
 simp only [add_zero]

theorem actor_projection_eval
 (env : Env (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition)) (count : Nat)
 (sourceOrigin : ∀ datum : B.Node root visit recognition,
  env (coreSlot root recognition) (datum,.old) (0:Fin 2) = orbitPair root visit recognition count datum) :
 ((CurrentChild.actorTerm root visit recognition).eval env).2.1.2 =
 (Finsupp.single (actorAtCount root visit recognition count) 1,
  Finsupp.single (actorAtCount root visit recognition (count+1)) 1 -
   Finsupp.single (actorAtCount root visit recognition count) 1) := by
 change (Actor.projection root visit recognition
  ((liftCore root visit recognition (Q.expression root visit recognition)).eval env)).2 = _
 rw [liftCore_eval]
 change Actor.completePairMap root visit recognition ((Q.expression root visit recognition).eval
  (fun target name => env (.inl (.inl (.inl (.inl (.inl target))))) name) (0:Fin 2)) = _
 rw [core_query_pair]
 have origin := sourceOrigin (B.node root visit recognition)
 rw [origin]
 rw [SourceOperationScalarInventoryLift.pairBilinear_apply]
 change (Finsupp.mapDomain (B.Fresh.Outcome.complete root recognition visit)
  (SourceNativeBinary.lift (B.constructor root visit recognition)
   ((orbitPair root visit recognition count (B.node root visit recognition)).1) (Finsupp.single [] (1:ℤ))),
  Finsupp.mapDomain (B.Fresh.Outcome.complete root recognition visit)
   (SourceNativeBinary.lift (B.constructor root visit recognition)
    ((orbitPair root visit recognition count (B.node root visit recognition)).1) 0 +
    SourceNativeBinary.lift (B.constructor root visit recognition)
     ((orbitPair root visit recognition count (B.node root visit recognition)).2) (Finsupp.single [] (1:ℤ)) +
    SourceNativeBinary.lift (B.constructor root visit recognition)
     ((orbitPair root visit recognition count (B.node root visit recognition)).2) 0)) = _
 simp only [orbitPair,map_zero,zero_add,add_zero,map_sub,AddMonoidHom.sub_apply,
  SourceNativeBinary.lift_point,Finsupp.mapDomain_sub,Finsupp.mapDomain_single]
 rfl

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Frame root visit recognition) (read : Read root visit recognition frame)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : C.Occurrence frame (current:=current))

theorem actor_paid_value : (actorPaidFor root visit recognition frame read supplied).2.2.1 =
 (CurrentChild.actorTerm root visit recognition).eval (read supplied) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem actor_paid_fee : (actorPaidFor root visit recognition frame read supplied).2.1.2.length =
 remaining (CurrentChild.actorTerm root visit recognition) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem actor_word_of_origin (count : Nat)
 (sourceOrigin : ∀ datum : B.Node root visit recognition,
  read supplied (coreSlot root recognition) (datum,.old) (0:Fin 2) = orbitPair root visit recognition count datum) :
 actorWordFor root visit recognition frame read supplied =
 Finsupp.single (actorAtCount root visit recognition (count+1)) 1 := by
 unfold actorWordFor
 rw [actor_paid_value]
 have actors := actor_projection_eval root visit recognition (read supplied) count sourceOrigin
 rw [actors]
 exact add_sub_cancel _ _
theorem support_of_origin (count : Nat)
 (sourceOrigin : ∀ datum : B.Node root visit recognition,
  read supplied (coreSlot root recognition) (datum,.old) (0:Fin 2) = orbitPair root visit recognition count datum) :
 supportFor root visit recognition frame read supplied = [actorAtCount root visit recognition (count+1)] := by
 classical
 unfold supportFor
 rw [actor_word_of_origin root visit recognition frame read supplied count sourceOrigin]
 simp

theorem programme_value (terms : List (Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition)
 (CurrentChild.resultSlot root recognition))) :
 (CurrentChild.programme root visit recognition terms).eval (read supplied) =
 (terms.map (fun term => term.eval (read supplied))).sum := by
 induction terms with
 | nil => rfl
 | cons first rest previous =>
   simpa only [CurrentChild.programme,Expr.eval,List.map_cons,List.sum_cons] using
    congrArg (fun value : CurrentChild.Output root visit recognition => first.eval (read supplied)+value) previous

theorem programme_charge (terms : List (Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition)
 (CurrentChild.resultSlot root recognition))) :
 remaining (CurrentChild.programme root visit recognition terms) = (terms.map remaining).sum+terms.length :=
 CurrentChild.programme_charge _ _ _ _
theorem paid_value_for : (paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1 =
 ((termsFor root visit recognition U7 calculus anchor frame read supplied).map (fun term => term.eval (read supplied))).sum :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans (programme_value _ _ _ _ _ _ _)
theorem paid_fee_for : (paidFor root visit recognition U7 calculus anchor frame read supplied).2.1.2.length =
 ((termsFor root visit recognition U7 calculus anchor frame read supplied).map remaining).sum+
 (termsFor root visit recognition U7 calculus anchor frame read supplied).length :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans (programme_charge _ _ _ _)
theorem trace_fee_for : (traceFor root visit recognition U7 calculus anchor frame read supplied).length =
 remaining (expressionFor root visit recognition U7 calculus anchor frame read supplied) := execution_length _ _
theorem source_material_for : (paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.2 =
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
  (E.Shared.base frame).root.toAuthoritativeRoot supplied := rfl

theorem catalogue_of_origin (count : Nat)
 (sourceOrigin : ∀ datum : B.Node root visit recognition,
  read supplied (coreSlot root recognition) (datum,.old) (0:Fin 2) = orbitPair root visit recognition count datum) :
 indicesFor root visit recognition frame read supplied =
 CurrentChild.indices root recognition (actorAtCount root visit recognition (count+1)) := by
 unfold indicesFor
 rw [support_of_origin root visit recognition frame read supplied count sourceOrigin]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
