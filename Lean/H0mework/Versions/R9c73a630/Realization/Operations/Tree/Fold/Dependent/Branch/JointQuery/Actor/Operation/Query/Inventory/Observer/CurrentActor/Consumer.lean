import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentActor.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentActor
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)

namespace Lower
variable (frame : Observer.Action.Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Observer.Action.C.Occurrence frame (current:=current))
theorem binding_origin_shift (datum : B.Node root visit recognition) :
    Observer.Action.generatedEnvironmentAt root visit recognition frame supplied
      (coreSlot root recognition) (datum,.old) (0:Fin 2) =
    Observer.Action.environmentAt root visit recognition frame supplied
      (coreSlot root recognition) (B.nextNode root visit recognition datum,.old) (0:Fin 2) := rfl
end Lower

theorem orbit_shift (count : Nat) (datum : B.Node root visit recognition) :
    (B.nextNode root visit recognition)^[count] (B.nextNode root visit recognition datum) =
      B.nextNode root visit recognition ((B.nextNode root visit recognition)^[count] datum) :=
  (Function.iterate_succ_apply (B.nextNode root visit recognition) count datum).symm.trans
    (Function.iterate_succ_apply' (B.nextNode root visit recognition) count datum)

theorem source_paid_value (stage : Nat) : (paidAt root visit recognition U7 calculus anchor stage).2.2.1 =
    (actorTerm root visit recognition).eval (ActiveRaw.activeEnvironment root visit recognition U7 calculus anchor stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem source_paid_fee (stage : Nat) : (paidAt root visit recognition U7 calculus anchor stage).2.1.2.length =
    remaining (actorTerm root visit recognition) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem source_trace_fee (stage : Nat) : (traceAt root visit recognition U7 calculus anchor stage).length =
    remaining (actorTerm root visit recognition) := execution_length _ _
theorem source_material (stage : Nat) : (paidAt root visit recognition U7 calculus anchor stage).2.2.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      (Observer.Live.E.Shared.base (Observer.Live.frameAt root visit recognition U7 calculus anchor stage)).root.toAuthoritativeRoot
      (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage)) := rfl


private def orbitPair (count : Nat) (datum : B.Node root visit recognition) :=
  (Finsupp.single ((B.nextNode root visit recognition)^[count] datum) (1:ℤ),
    Finsupp.single ((B.nextNode root visit recognition)^[count+1] datum) (1:ℤ) -
    Finsupp.single ((B.nextNode root visit recognition)^[count] datum) (1:ℤ))
private theorem orbit_pair_shift (count : Nat) (datum : B.Node root visit recognition) :
    orbitPair root visit recognition count (B.nextNode root visit recognition datum) =
      orbitPair root visit recognition (count+1) datum := by
  unfold orbitPair
  rw [←Function.iterate_succ_apply,←Function.iterate_succ_apply]

private abbrev inventoryCoreSlot : Inventory.Slot root recognition := .inl (.inl (.inl .origin))
private def inventoryUniform (frame : Inventory.Action.Frame root visit recognition) (count : Nat) : Prop :=
  ∀ (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered)
    (supplied : Inventory.Action.C.Occurrence frame (current:=current)) (datum : B.Node root visit recognition),
    Inventory.Action.environmentAt root visit recognition frame supplied (inventoryCoreSlot root recognition) (datum,.old) (0:Fin 2) =
      orbitPair root visit recognition count datum
private def observerUniform (frame : Observer.Action.Frame root visit recognition) (count : Nat) : Prop :=
  ∀ (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered)
    (supplied : Observer.Action.C.Occurrence frame (current:=current)) (datum : B.Node root visit recognition),
    Observer.Action.environmentAt root visit recognition frame supplied (coreSlot root recognition) (datum,.old) (0:Fin 2) =
      orbitPair root visit recognition count datum

private theorem inventory_shift (frame : Inventory.Action.Frame root visit recognition)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Inventory.Action.C.Occurrence frame (current:=current)) (datum : B.Node root visit recognition) :
    Inventory.Action.generatedEnvironmentAt root visit recognition frame supplied
      (inventoryCoreSlot root recognition) (datum,.old) (0:Fin 2) =
    Inventory.Action.environmentAt root visit recognition frame supplied
      (inventoryCoreSlot root recognition) (B.nextNode root visit recognition datum,.old) (0:Fin 2) := rfl

private theorem inventory_origin_uniform (stage : Nat) :
    inventoryUniform root visit recognition (Inventory.Live.frameAt root visit recognition U7 calculus stage)
      (inventoryBirthCount root visit recognition U7 calculus stage) := by
  induction stage with
  | zero => intro current supplied datum; rfl
  | succ stage previous =>
    change inventoryUniform root visit recognition
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
        (Inventory.Live.frameAt root visit recognition U7 calculus stage)
        (Inventory.Live.programme root visit recognition U7 calculus))
      (match (Inventory.Live.frameAt root visit recognition U7 calculus stage).action with
        | .inr _ => inventoryBirthCount root visit recognition U7 calculus stage
        | .inl _ => inventoryBirthCount root visit recognition U7 calculus stage+1)
    unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
    cases (Inventory.Live.frameAt root visit recognition U7 calculus stage).action with
    | inr paid => exact previous
    | inl settled =>
      intro current supplied datum
      change Inventory.Action.generatedEnvironmentAt root visit recognition
        (Inventory.Live.E.epoch (Inventory.Live.frameAt root visit recognition U7 calculus stage))
        (Inventory.Live.E.Shared.actualOccurrence (Inventory.Live.frameAt root visit recognition U7 calculus stage))
        (inventoryCoreSlot root recognition) (datum,.old) (0:Fin 2) = _
      exact (inventory_shift root visit recognition _ _ datum).trans
        ((previous _ (Inventory.Live.E.Shared.actualOccurrence (Inventory.Live.frameAt root visit recognition U7 calculus stage))
          (B.nextNode root visit recognition datum)).trans
          (orbit_pair_shift root visit recognition (inventoryBirthCount root visit recognition U7 calculus stage) datum))

theorem uniform_origin (stage : Nat) : UniformOriginLaw root visit recognition U7 calculus anchor stage := by
  change observerUniform root visit recognition (Observer.Live.frameAt root visit recognition U7 calculus anchor stage)
    (birthCount root visit recognition U7 calculus anchor stage)
  induction stage with
  | zero =>
    intro current supplied datum
    change Inventory.Action.environmentAt root visit recognition
      (Inventory.Live.frameAt root visit recognition U7 calculus anchor)
      (Inventory.Live.E.Shared.actualOccurrence (Inventory.Live.frameAt root visit recognition U7 calculus anchor))
      (inventoryCoreSlot root recognition) (datum,.old) (0:Fin 2) = _
    exact inventory_origin_uniform root visit recognition U7 calculus anchor _ _ datum
  | succ stage previous =>
    change observerUniform root visit recognition
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
        (Observer.Live.frameAt root visit recognition U7 calculus anchor stage)
        (Observer.Live.programme root visit recognition U7 calculus anchor))
      (match (Observer.Live.frameAt root visit recognition U7 calculus anchor stage).action with
        | .inr _ => birthCount root visit recognition U7 calculus anchor stage
        | .inl _ => birthCount root visit recognition U7 calculus anchor stage+1)
    unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
    cases (Observer.Live.frameAt root visit recognition U7 calculus anchor stage).action with
    | inr paid => exact previous
    | inl settled =>
      intro current supplied datum
      change Observer.Action.generatedEnvironmentAt root visit recognition
        (Observer.Live.E.epoch (Observer.Live.frameAt root visit recognition U7 calculus anchor stage))
        (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage))
        (coreSlot root recognition) (datum,.old) (0:Fin 2) = _
      exact (Lower.binding_origin_shift root visit recognition _ _ datum).trans
        ((previous _ (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage))
          (B.nextNode root visit recognition datum)).trans
          (orbit_pair_shift root visit recognition (birthCount root visit recognition U7 calculus anchor stage) datum))

theorem actual_origin (stage : Nat) : OriginLaw root visit recognition U7 calculus anchor stage :=
  uniform_origin root visit recognition U7 calculus anchor stage _
    (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage))


namespace Q
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery (Value Variable expression)
end Q
private def liftCore {slot : SourceOperationNative.Tree.Fold.Slot.{u}}
    (term : Expr (Q.Value root visit recognition) (Q.Variable root visit recognition) slot) :
    Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) (.inl (.inl (.inl (.inl slot)))) :=
  Observer.embed root visit recognition (Inventory.embed root visit recognition
    (Actor.Extension.embed (Actor.Value root visit recognition) (Actor.Variable root visit recognition) (Query.Output root visit recognition)
      (Actor.Extension.embed (Q.Value root visit recognition) (Q.Variable root visit recognition) (Actor.Output root visit recognition) term)))
private theorem liftCore_eval {slot : SourceOperationNative.Tree.Fold.Slot.{u}}
    (term : Expr (Q.Value root visit recognition) (Q.Variable root visit recognition) slot)
    (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition)) :
    (liftCore root visit recognition term).eval env =
      term.eval (fun target name => env (.inl (.inl (.inl (.inl target)))) name) := by
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

private theorem actor_eval (stage : Nat)
    (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition))
    (sourceOrigin : ∀ datum : B.Node root visit recognition,
      env (coreSlot root recognition) (datum,.old) (0:Fin 2) =
        orbitPair root visit recognition (birthCount root visit recognition U7 calculus anchor stage) datum) :
    ((actorTerm root visit recognition).eval env).2 =
      (Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1,
       Finsupp.single (nextActorAt root visit recognition U7 calculus anchor stage) 1 -
         Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1) := by
  change (Actor.projection root visit recognition
    ((liftCore root visit recognition (Q.expression root visit recognition)).eval
      env)).2 = _
  rw [liftCore_eval]
  change Actor.completePairMap root visit recognition ((Q.expression root visit recognition).eval
    (fun target name => env
      (.inl (.inl (.inl (.inl target)))) name) (0:Fin 2)) = _
  rw [core_query_pair]
  have origin := sourceOrigin (B.node root visit recognition)
  rw [origin]
  rw [SourceOperationScalarInventoryLift.pairBilinear_apply]
  change (Finsupp.mapDomain (B.Fresh.Outcome.complete root recognition visit)
    (SourceNativeBinary.lift (B.constructor root visit recognition)
      ((orbitPair root visit recognition (birthCount root visit recognition U7 calculus anchor stage)
        (B.node root visit recognition)).1) (Finsupp.single [] (1:ℤ))),
    Finsupp.mapDomain (B.Fresh.Outcome.complete root recognition visit)
      (SourceNativeBinary.lift (B.constructor root visit recognition)
        ((orbitPair root visit recognition (birthCount root visit recognition U7 calculus anchor stage)
          (B.node root visit recognition)).1) 0 +
       SourceNativeBinary.lift (B.constructor root visit recognition)
        ((orbitPair root visit recognition (birthCount root visit recognition U7 calculus anchor stage)
          (B.node root visit recognition)).2) (Finsupp.single [] (1:ℤ)) +
       SourceNativeBinary.lift (B.constructor root visit recognition)
        ((orbitPair root visit recognition (birthCount root visit recognition U7 calculus anchor stage)
          (B.node root visit recognition)).2) 0)) = _
  simp only [orbitPair,map_zero,zero_add,add_zero,map_sub,AddMonoidHom.sub_apply,
    SourceNativeBinary.lift_point,Finsupp.mapDomain_sub,Finsupp.mapDomain_single]
  simp only [actorAt,nextActorAt,coreNodeAt,Function.iterate_succ_apply']


theorem supplied_actor (stage : Nat)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
      (Observer.Live.frameAt root visit recognition U7 calculus anchor stage).registered}
    (supplied : Observer.Action.C.Occurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (current:=current)) :
    (Lower.paidAt root visit recognition (Observer.Live.frameAt root visit recognition U7 calculus anchor stage) supplied).2.2.1.2 =
      (Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1,
       Finsupp.single (nextActorAt root visit recognition U7 calculus anchor stage) 1 -
         Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1) := by
  have paidValue := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Observer.Live.E.Shared.base (Observer.Live.frameAt root visit recognition U7 calculus anchor stage)).root.toAuthoritativeRoot
    (fun {_current} occurrence => Lower.rawAt root visit recognition
      (Observer.Live.frameAt root visit recognition U7 calculus anchor stage) occurrence) supplied
  exact (congrArg (fun value : Actor.Output root visit recognition => value.2) paidValue).trans
    (actor_eval root visit recognition U7 calculus anchor stage
      (Observer.Action.environmentAt root visit recognition
        (Observer.Live.frameAt root visit recognition U7 calculus anchor stage) supplied)
      (uniform_origin root visit recognition U7 calculus anchor stage current supplied))

theorem actual_actor (stage : Nat) : ActorLaw root visit recognition U7 calculus anchor stage :=
  supplied_actor root visit recognition U7 calculus anchor stage
    (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage))

theorem actual_next_actor (stage : Nat) :
    (paidAt root visit recognition U7 calculus anchor stage).2.2.1.2.1 +
      (paidAt root visit recognition U7 calculus anchor stage).2.2.1.2.2 =
        Finsupp.single (nextActorAt root visit recognition U7 calculus anchor stage) 1 := by
  have sourcePair := actual_actor root visit recognition U7 calculus anchor stage
  change (paidAt root visit recognition U7 calculus anchor stage).2.2.1.2 =
    (Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1,
      Finsupp.single (nextActorAt root visit recognition U7 calculus anchor stage) 1 -
        Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1) at sourcePair
  rw [sourcePair]
  exact add_sub_cancel _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentActor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
