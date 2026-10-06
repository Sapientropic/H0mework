import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Tick
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
theorem combined_seed_next (count : Nat) : ∀ event ∈ (combinedSeed root visit recognition count).trace,
    event ∈ (combinedSeed root visit recognition (count+1)).trace := by
  intro event belongs
  change event ∈ PresentedRelationEventAt.relation (relationWord root visit recognition) ::
    ((seed root visit recognition count).trace ++ ((paidExposure root visit recognition count).trace ++ [])) at belongs
  change event ∈ PresentedRelationEventAt.relation (relationWord root visit recognition) ::
    ((seed root visit recognition (count+1)).trace ++ ((paidExposure root visit recognition (count+1)).trace ++ []))
  rcases List.mem_cons.mp belongs with same | rest
  · exact List.mem_cons.mpr (.inl same)
  · apply List.mem_cons_of_mem
    rcases List.mem_append.mp rest with incoming | paid
    · exact List.mem_append_left _ incoming
    · apply List.mem_append_right
      rcases List.mem_append.mp paid with old | impossible
      · apply List.mem_append_left
        exact RootGeneratedDebtActivationJointSource.OwnerFree.Relations.tick_paid_exposure
          (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition)
            (paidRuntime root visit recognition count) event old
      · cases impossible

def transition (count : Nat) : CofinalHistoryTransition.GeneratedTransition
    (combined root visit recognition count) (combined root visit recognition (count+1)) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _ (combined_seed_next root visit recognition count)) (by
      intro word belongs
      change (combined root visit recognition (count+1)).completionProjection
        ⟨word.val, SourceOperationPaidRelations.generators_next _ _ _ _
          (combined_seed_next root visit recognition count) word.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _
        (combined_seed_next root visit recognition count) belongs)

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
