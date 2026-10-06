import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt sourceFeed)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
open RootInquiryCompletion
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (no_refill wellFounded activePayment)
end P
abbrev outcome := constructor root visit recognition (node root visit recognition) []
abbrev nextOutcome := constructor root visit recognition (nextNode root visit recognition (node root visit recognition)) []
theorem programme_old : (programme root visit recognition).eval (environment root visit recognition) =
    Finsupp.single (outcome root visit recognition) 1 := F.program_value _ _
theorem programme_next : (programme root visit recognition).eval (updatedEnvironment root visit recognition) =
    Finsupp.single (nextOutcome root visit recognition) 1 := by
  change SourceNativeBinary.lift (constructor root visit recognition)
    (Finsupp.single (nextNode root visit recognition (node root visit recognition)) 1)
    (Finsupp.single [] 1) = _
  exact SourceNativeBinary.lift_point _ _ _
theorem raw_inventory : (raw root visit recognition).expression.eval (raw root visit recognition).environment =
    (Finsupp.single (outcome root visit recognition) 1,
      Finsupp.single (nextOutcome root visit recognition) 1 - Finsupp.single (outcome root visit recognition) 1) := by
  rw [show (raw root visit recognition).expression.eval (raw root visit recognition).environment = _ from
    eval_liftExpr (programme root visit recognition) (environment root visit recognition) (delta root visit recognition)]
  apply Prod.ext
  · exact programme_old root visit recognition
  · have generated := Expr.eval_update (programme root visit recognition) (environment root visit recognition) (delta root visit recognition)
    rw [show environment root visit recognition + delta root visit recognition = updatedEnvironment root visit recognition from add_sub_cancel _ _] at generated
    rw [programme_old, programme_next] at generated
    exact eq_sub_of_add_eq (by rw [add_comm]; exact generated.symm)

theorem source_payload : (outcome root visit recognition).1 = D.sourceFeed (step root visit recognition) := rfl

theorem unchanged_payload : (nextOutcome root visit recognition).1 = (outcome root visit recognition).1 := rfl

theorem normal_inventory : O.value root.toAuthoritativeRoot visit.current (installedReader root visit recognition) =
    (Finsupp.single (outcome root visit recognition) 1,
      Finsupp.single (nextOutcome root visit recognition) 1 - Finsupp.single (outcome root visit recognition) 1) :=
  (O.value_source root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).trans
    (raw_inventory root visit recognition)

theorem normal_payload : Finsupp.mapDomain (Outcome.fst root visit recognition)
    (O.value root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).1 =
      Finsupp.single (D.sourceFeed (step root visit recognition)) (1 : ℤ) := by
  rw [normal_inventory]
  exact Finsupp.mapDomain_single

theorem payload_effect_zero : Finsupp.mapDomain (Outcome.fst root visit recognition)
    (O.value root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).2 = 0 := by
  rw [normal_inventory, Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  change Finsupp.single (nextOutcome root visit recognition).historical (1 : ℤ) -
    Finsupp.single (outcome root visit recognition).historical 1 = 0
  rw [unchanged_payload,sub_self]

theorem cost : (O.trace root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).length = 2 :=
  (O.paid_history root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).trans (by rfl)

theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition) count) :=
  P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition) count

theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition)) :=
  P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition)

abbrev payment (count : Fin 2) := P.activePayment root.toAuthoritativeRoot visit.current (installedReader root visit recognition)
  ⟨count.1, by exact count.2⟩

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
abbrev actualRoot := C.sourceRoot (sourceRoot root visit recognition) (sourceVisit root visit recognition)
theorem material_read (count : Nat) : (face root visit recognition U7 calculus count).rootRead = material root visit recognition := rfl

theorem recovered_payload (count : Nat) : (face root visit recognition U7 calculus count).rootRead.1.1 =
    D.sourceFeed (step root visit recognition) := rfl

theorem parent_next (count : Nat) : root.generatedNextCurrentAt
    (SourceTemporalMaterial.decode root.toAuthoritativeRoot.toLedgerRoot (face root visit recognition U7 calculus count).rootRead.1.2) =
      root.generatedNextCurrentAt visit :=
  congrArg root.generatedNextCurrentAt (SourceTemporalMaterial.decode_encode _ _)

theorem all_stage_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition) count

theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset) ∧
    type_of% (M.activated_answer (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset) ∧
    type_of% (M.activated_next (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset) :=
  ⟨M.activated_query (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset,
    M.activated_answer (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset,
    M.activated_next (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset⟩
end SourceOperationNative.Tree.Fold.Dependent.Branch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
