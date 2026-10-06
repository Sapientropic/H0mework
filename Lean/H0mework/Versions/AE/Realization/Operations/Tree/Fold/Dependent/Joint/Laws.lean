import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
mutual
 theorem programme_updated (sourceTree : RootedAccountedUnfolding (Node root visit recognition successor transition)) :
     (F.program (constructor root visit recognition successor transition) sourceTree).eval
       (updatedEnvironment root visit recognition successor transition) =
       Finsupp.single ((sourceTree.map (nextNode root visit recognition successor transition)).fold
         (constructor root visit recognition successor transition)) 1 := by
   cases sourceTree with
   | occur node branches =>
     change SourceNativeBinary.lift (constructor root visit recognition successor transition)
       (Finsupp.single (nextNode root visit recognition successor transition node) 1)
       ((SourceOperationNative.Tree.Fold.children (constructor root visit recognition successor transition) branches).eval
         (updatedEnvironment root visit recognition successor transition)) = _
     rw [children_updated]
     exact SourceNativeBinary.lift_point _ _ _
 theorem children_updated (branches : AccountedBranches (Node root visit recognition successor transition)) :
     (SourceOperationNative.Tree.Fold.children (constructor root visit recognition successor transition) branches).eval
       (updatedEnvironment root visit recognition successor transition) =
       Finsupp.single (RootedAccountedUnfolding.foldBranches (constructor root visit recognition successor transition)
         (RootedAccountedUnfolding.mapBranches (nextNode root visit recognition successor transition) branches)) 1 := by
   cases branches with
   | nil => rfl
   | cons head tail =>
     change SourceNativeBinary.lift List.cons
       ((F.program (constructor root visit recognition successor transition) head).eval
         (updatedEnvironment root visit recognition successor transition))
       ((SourceOperationNative.Tree.Fold.children (constructor root visit recognition successor transition) tail).eval
         (updatedEnvironment root visit recognition successor transition)) = _
     rw [programme_updated, children_updated]
     exact SourceNativeBinary.lift_point _ _ _
end
theorem original_tree : (tree root visit recognition successor transition alignment).map Prod.fst =
    D.nativeTree (step root visit recognition) successor transition alignment := by
  rw [tree, RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _

mutual
 theorem fold_original (sourceTree : RootedAccountedUnfolding (Node root visit recognition successor transition)) :
     (sourceTree.fold (constructor root visit recognition successor transition)).1 =
       (sourceTree.map Prod.fst).fold (effectFoldAt (step root visit recognition) successor transition.history) := by
   cases sourceTree with
   | occur node branches =>
     change effectFoldAt (step root visit recognition) successor transition.history node.1
       ((RootedAccountedUnfolding.foldBranches (constructor root visit recognition successor transition) branches).map Prod.fst) = _
     rw [fold_children_original]
     rfl
 theorem fold_children_original (branches : AccountedBranches (Node root visit recognition successor transition)) :
     (RootedAccountedUnfolding.foldBranches (constructor root visit recognition successor transition) branches).map Prod.fst =
       RootedAccountedUnfolding.foldBranches (effectFoldAt (step root visit recognition) successor transition.history)
         (RootedAccountedUnfolding.mapBranches Prod.fst branches) := by
   cases branches with
   | nil => rfl
   | cons head tail =>
     change ((head.fold (constructor root visit recognition successor transition)).1 ::
       (RootedAccountedUnfolding.foldBranches (constructor root visit recognition successor transition) tail).map Prod.fst) = _
     rw [fold_original, fold_children_original]
     rfl
end
mutual
 theorem fold_time (sourceTree : RootedAccountedUnfolding (Node root visit recognition successor transition)) :
     (sourceTree.fold (constructor root visit recognition successor transition)).2.1 =
       sourceTree.map (fun node => T.actual root node.2) := by
   cases sourceTree with
   | occur node branches =>
     change RootedAccountedUnfolding.occur (T.actual root node.2)
       (branchesOfList ((RootedAccountedUnfolding.foldBranches (constructor root visit recognition successor transition) branches).map (fun child => child.2.1))) = _
     rw [fold_children_time]
     rfl
 theorem fold_children_time (branches : AccountedBranches (Node root visit recognition successor transition)) :
     branchesOfList ((RootedAccountedUnfolding.foldBranches (constructor root visit recognition successor transition) branches).map (fun child => child.2.1)) =
       RootedAccountedUnfolding.mapBranches (fun node => T.actual root node.2) branches := by
   cases branches with
   | nil => rfl
   | cons head tail =>
     change AccountedBranches.cons (head.fold (constructor root visit recognition successor transition)).2.1
       (branchesOfList ((RootedAccountedUnfolding.foldBranches (constructor root visit recognition successor transition) tail).map (fun child => child.2.1))) = _
     rw [fold_time, fold_children_time]
     rfl
end
theorem full_inventory : (raw root visit recognition successor transition alignment).expression.eval
    (raw root visit recognition successor transition alignment).environment =
      (Finsupp.single (sourceOutcome root visit recognition successor transition alignment) 1,
       Finsupp.single (targetOutcome root visit recognition successor transition alignment) 1 -
         Finsupp.single (sourceOutcome root visit recognition successor transition alignment) 1) := by
  rw [show (raw root visit recognition successor transition alignment).expression.eval
    (raw root visit recognition successor transition alignment).environment = _ from
      SourceOperationScalarInventoryLift.eval_liftExpr (programme root visit recognition successor transition alignment)
        F.environment (delta root visit recognition successor transition)]
  apply Prod.ext
  · exact F.program_value _ _
  · have generated := Expr.eval_update (programme root visit recognition successor transition alignment)
      F.environment (delta root visit recognition successor transition)
    rw [show F.environment + delta root visit recognition successor transition = updatedEnvironment root visit recognition successor transition
      from add_sub_cancel _ _] at generated
    rw [programme_updated, F.program_value] at generated
    exact eq_sub_of_add_eq (by rw [add_comm]; exact generated.symm)
abbrev sourceTrace := execution F.environment (programme root visit recognition successor transition alignment)
abbrev nextTrace := execution (updatedEnvironment root visit recognition successor transition)
  (programme root visit recognition successor transition alignment)
open SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
open SourceOperationLogic SourceOperationLogic.FibreLift
abbrev oldWord := SourceOperationScalarPresentation.relationMap (R:=ℤ) F.environment
  (sourceTrace root visit recognition successor transition alignment).relationWords
abbrev nextWord := SourceOperationScalarPresentation.relationMap (R:=ℤ)
  (updatedEnvironment root visit recognition successor transition)
  (nextTrace root visit recognition successor transition alignment).relationWords
abbrev morphism := updateMorphism (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
  F.environment (delta root visit recognition successor transition)
def target : Fibre (evaluation (R:=ℤ) (F.environment + delta root visit recognition successor transition))
    (q (evaluation (R:=ℤ) (F.environment + delta root visit recognition successor transition))
      (oldWord root visit recognition successor transition alignment)) :=
  ⟨oldWord root visit recognition successor transition alignment + nextWord root visit recognition successor transition alignment, by
    apply (q_eq_iff _ _ _).mpr
    rw [LinearMap.mem_ker, add_sub_cancel_left]
    rw [show F.environment + delta root visit recognition successor transition = updatedEnvironment root visit recognition successor transition
      from add_sub_cancel _ _]
    exact (nextTrace root visit recognition successor transition alignment).relation_old (R:=ℤ)⟩
abbrev reverse := liftingResidual (morphism root visit recognition successor transition)
  (oldWord root visit recognition successor transition alignment) (target root visit recognition successor transition alignment)
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
